/*
 * AWS IoT Device SDK for Embedded C 202412.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/* Standard includes. */
#include <stdio.h>
#include <stdlib.h>

/* Logging configuration for the PKCS #11 library. */
#ifndef LIBRARY_LOG_NAME
    #define LIBRARY_LOG_NAME    "PKCS11_RNG_DEMO"
#endif

#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_INFO
#endif

#include "logging_stack.h"

/* PKCS #11 includes. */
#include "core_pkcs11.h"
#include "pkcs11.h"

/**
 * @brief This function details how to use the PKCS #11 "Management" functions to
 * manage the internal state machine of the PKCS #11 implementation. These
 * functions are all defined in
 * https://docs.oasis-open.org/pkcs11/pkcs11-base/v2.40/os/pkcs11-base-v2.40-os.html
 * Please consult the standard for more information regarding these functions.
 *
 * The standard has grouped the functions presented in this demo as:
 * General Purpose Functions
 * Slot and Token Management Functions
 * Session Management Functions
 * Random Number Generation Functions
 */
CK_RV PKCS11ManagementAndRNGDemo( void )
{
    /* We will use the terminology as defined in the standard, Cryptoki is in
     * reference to the Cryptographic Token Interface defined in the PKCS #11
     * standard. An implementation of Cryptoki is referred to as a
     * "Cryptoki library". */
    LogInfo( ( "Starting PKCS #11 Management and Random Number Generation"
               " Demo." ) );

    /* CK_RV is the return type for a Cryptoki function. Generally the underlying
     * type is a CK_ULONG, it can also be a CKR_VENDOR_DEFINED type. */
    CK_RV result = CKR_OK;

    /* The CK_FUNCTION_LIST is a structure that contains the Cryptoki version
     * and a function pointer to each function in the Cryptoki API. If the
     * function pointer is NULL it is unimplemented. */
    CK_FUNCTION_LIST_PTR functionList = NULL;

    /* This Cryptoki library does not implement any initialization arguments. At the time of
     * writing this demo, the purpose of these optional arguments is to provide
     * function pointers for mutex operations. */
    CK_C_INITIALIZE_ARGS initArgs = { 0 };

    /* A slot ID is an integer that defines a slot. The Cryptoki definition of
     * a slot is "A logical reader that potentially contains a token."
     *
     * Essentially it is an abstraction for accessing the token. The reason for
     * this is Some tokens are a physical "card' that needs to be inserted into
     * a slot for the device to read.
     *
     * A concrete example of a slot could be a USB Hardware Security Module (HSM),
     * which generally appears as a singular slot, and abstracts it's internal "token".
     *
     * Some implementations have multiple slots mapped to a single token, or maps
     * a slot per token. */
    CK_SLOT_ID * slotId = NULL;

    /* A session is defined to be "The logical connection between an application
     * and a token."
     *
     * The session can either be private or public, and differentiates
     * your application from the other users of the token. */
    CK_SESSION_HANDLE session = CK_INVALID_HANDLE;

    /* Helper variables. */
    CK_BYTE randomData[ 10 ] = { 0 };
    uint32_t index = 0;
    CK_ULONG slotCount = 0;

    /* We use the function list returned by C_GetFunctionList to see what functions
     * the Cryptoki library supports. We use asserts to ensure that all the
     * functionality needed in this demo is available. */
    result = C_GetFunctionList( &functionList );

    if( result == CKR_OK )
    {
        LogInfo( ( "Cryptoki Major Version: %u Minor Version: %u",
                   functionList->version.major,
                   functionList->version.minor ) );

        /* C_Initialize will initialize the Cryptoki library and the hardware it
         * abstracts. */
        result = functionList->C_Initialize( &initArgs );
    }

    /* C_GetSlotList will retrieve an array of CK_SLOT_IDs.
     * This Cryptoki library does not implement slots, but it is important to
     * highlight how Cryptoki can be used to interface with real hardware.
     *
     * By setting the first argument "tokenPresent" to true, we only retrieve
     * slots that have a token. If the second argument "pSlotList" is NULL, the
     * third argument "pulCount" will be modified to contain the total slots. */
    if( result == CKR_OK )
    {
        result = functionList->C_GetSlotList( CK_TRUE,
                                              NULL,
                                              &slotCount );
    }

    /* Since C_GetSlotList does not allocate the memory itself for getting a list
     * of CK_SLOT_ID, we allocate one for it to populate with the list of
     * slot ids. */
    if( result == CKR_OK )
    {
        slotId = ( CK_SLOT_ID * ) malloc( sizeof( CK_SLOT_ID ) * ( slotCount ) );

        if( slotId == NULL )
        {
            result = CKR_HOST_MEMORY;
        }
    }

    /* Now since pSlotList is not NULL, C_GetSlotList will populate it with the
     * available slots. */
    if( result == CKR_OK )
    {
        result = functionList->C_GetSlotList( CK_TRUE,
                                              slotId,
                                              &slotCount );
    }

    /* Since this Cryptoki library does not actually implement the concept of slots,
     * but we will use the first available slot, so the demo code conforms to
     * Cryptoki.
     *
     * C_OpenSession will establish a session between the application and
     * the token and we can then use the returned CK_SESSION_HANDLE for
     * cryptographic operations with the token.
     *
     * For legacy reasons, Cryptoki demands that the CKF_SERIAL_SESSION bit
     * is always set. */
    if( result == CKR_OK )
    {
        result = functionList->C_OpenSession( slotId[ 0 ],
                                              CKF_SERIAL_SESSION | CKF_RW_SESSION,
                                              NULL, /* Application defined pointer. */
                                              NULL, /* Callback function. */
                                              &session );
    }

    /* C_Login is called to log the user in to the token. The login status is
     * shared between sessions, so logging in once is sufficient for all the sessions
     * tied to the token. Most of the behavior for C_Login is defined by the token
     * so it may be necessary to modify calls to C_Login when switching to a different
     * Cryptoki library or token.
     *
     * This Cryptoki library does not implement C_Login, and only defines the function
     * for compatibility reasons.
     */
    if( result == CKR_OK )
    {
        result = functionList->C_Login( session,
                                        CKU_USER,
                                        ( CK_UTF8CHAR_PTR ) "0000",
                                        sizeof( "0000" ) - 1UL );
    }

    /* C_GenerateRandom generates random or pseudo random data. As arguments it
     * takes the application session, and a pointer to a byte buffer, as well as
     * the length of the byte buffer. Then it will fill this buffer with random
     * bytes. */

    if( result == CKR_OK )
    {
        result = functionList->C_GenerateRandom( session,
                                                 randomData,
                                                 sizeof( randomData ) );

        for( index = 0; index < sizeof( randomData ); index++ )
        {
            LogInfo( ( "Generated random number: %x", randomData[ index ] ) );
        }
    }

    /* C_CloseSession closes the session that was established between the
     * application and the token. This will clean up the resources that maintained
     * the link between the application and the token. If the application wishes
     * to use the token again, it will need to open a new session. */
    if( result == CKR_OK )
    {
        result = functionList->C_CloseSession( session );
    }

    /* C_Finalize signals to the Cryptoki library that the application is done
     * using it. It should always be the last call to the Cryptoki library.
     * NULL should always be passed as the argument, as the parameter is currently
     * just reserved for future revisions.
     *
     * Calling this function in a multi threaded environment can lead to undefined
     * behavior if other threads are accessing the Cryptoki library. */
    if( result == CKR_OK )
    {
        result = functionList->C_Finalize( NULL );
    }

    LogInfo( ( "Finished PKCS #11 Management and Random Number Generation"
               " Demo." ) );

    free( slotId );
    return result;
}

/**
 * @brief Entry point of demo.
 *
 * The example shown above uses PKCS #11 APIs to manage state and generate random numbers.
 */
int main( void )
{
    return PKCS11ManagementAndRNGDemo();
}

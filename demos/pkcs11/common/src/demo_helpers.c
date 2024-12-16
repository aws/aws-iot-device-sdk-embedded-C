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

/**
 * @file demo_helpers.c
 * @brief Common functions used between the PKCS #11 demos.
 */
/* Standard includes. */
#include <stdio.h>
#include <string.h>

/* Log includes. */
#include "logging_levels.h"
#ifndef LIBRARY_LOG_NAME
    #define LIBRARY_LOG_NAME    "PKCS11_DEMO_HELPERS"
#endif

#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_INFO
#endif

#include "logging_stack.h"

/* PKCS #11 includes. */
#include "core_pkcs11.h"
#include "pkcs11.h"

/* mbed TLS includes. */
#include "mbedtls/pk.h"
#include "mbedtls/oid.h"

/* Helpers include. */
#include "demo_helpers.h"


/*
 * @brief macro to help print public key hex to serial.
 */
#define BYTES_TO_DISPLAY_PER_ROW    16
/*-----------------------------------------------------------*/

CK_RV start( CK_SESSION_HANDLE * session,
             CK_SLOT_ID ** slotId )
{
    CK_RV result = CKR_OK;

    CK_FUNCTION_LIST_PTR functionList = NULL;
    CK_C_INITIALIZE_ARGS initArgs = { 0 };
    CK_SESSION_HANDLE tempSession = CK_INVALID_HANDLE;
    CK_ULONG slotCount = 0;
    CK_SLOT_ID * innerSlotId = NULL;

    result = C_GetFunctionList( &functionList );

    if( result == CKR_OK )
    {
        result = functionList->C_Initialize( &initArgs );
    }

    if( result == CKR_OK )
    {
        result = functionList->C_GetSlotList( CK_TRUE,
                                              NULL,
                                              &slotCount );
    }

    innerSlotId = malloc( sizeof( CK_SLOT_ID ) * ( slotCount ) );

    if( innerSlotId == NULL )
    {
        result = CKR_HOST_MEMORY;
    }

    if( result == CKR_OK )
    {
        result = functionList->C_GetSlotList( CK_TRUE,
                                              innerSlotId,
                                              &slotCount );
    }

    if( result == CKR_OK )
    {
        result = functionList->C_OpenSession( innerSlotId[ 0 ],
                                              CKF_SERIAL_SESSION | CKF_RW_SESSION,
                                              NULL, /* Application defined pointer. */
                                              NULL, /* Callback function. */
                                              &tempSession );
    }

    if( result == CKR_OK )
    {
        result = functionList->C_Login( tempSession,
                                        CKU_USER,
                                        ( CK_UTF8CHAR_PTR ) "0000",
                                        sizeof( "0000" ) - 1UL );
    }

    *slotId = innerSlotId;
    *session = tempSession;

    return result;
}
/*-----------------------------------------------------------*/

void end( CK_SESSION_HANDLE session,
          CK_SLOT_ID * slotId )
{
    C_CloseSession( session );
    C_Finalize( NULL );
    free( slotId );
}
/*-----------------------------------------------------------*/

void writeHexBytesToConsole( const char * description,
                             CK_BYTE * data,
                             CK_ULONG dataLength )
{
    /* This function is simply a helper function to print the raw hex values
     * of an EC public key. Its explanation is not within the scope of the demos
     * and is sparsely commented. */
    char byteRow[ 1 + ( BYTES_TO_DISPLAY_PER_ROW * 2 ) + ( BYTES_TO_DISPLAY_PER_ROW / 2 ) ];
    char * nextChar = byteRow;
    uint32_t index = 0;
    uint8_t byteValue = 0;

    ( void ) description;

    /* Write help text to the console. */
    LogInfo( ( "%s, %lu bytes:", description, dataLength ) );

    /* Iterate over the bytes of the encoded public key. */
    for( index = 0; index < dataLength; index++ )
    {
        /* Convert one byte to ASCII hex. */
        byteValue = *( data + index );
        snprintf( nextChar,
                  sizeof( byteRow ) - ( nextChar - byteRow ),
                  "%02x",
                  byteValue );
        nextChar += 2;

        /* Check for the end of a two-byte display word. */
        if( 0 == ( ( index + 1 ) % sizeof( uint16_t ) ) )
        {
            *nextChar = ' ';
            nextChar++;
        }

        /* Check for the end of a row. */
        if( 0 == ( ( index + 1 ) % BYTES_TO_DISPLAY_PER_ROW ) )
        {
            *nextChar = '\0';
            LogInfo( ( "%s", byteRow ) );
            nextChar = byteRow;
        }
    }

    /* Check for a partial line to print. */
    if( nextChar > byteRow )
    {
        *nextChar = '\0';
        LogInfo( ( "%s", byteRow ) );
    }
}
/*-----------------------------------------------------------*/

CK_RV exportPublicKey( CK_SESSION_HANDLE session,
                       CK_OBJECT_HANDLE publicKeyHandle,
                       CK_BYTE ** derPublicKey,
                       CK_ULONG * derPublicKeyLength )
{
    /* This function is simply a helper function to export the raw hex values
     * of an EC public key into a buffer. It's explanation is not within the
     * scope of the demos and is sparsely commented. */
    CK_RV result;
    CK_FUNCTION_LIST_PTR functionList;
    CK_KEY_TYPE keyType = 0;
    CK_ATTRIBUTE template = { 0 };
    uint8_t ecP256AsnOid[] =
    {
        0x30, 0x59, 0x30, 0x13, 0x06, 0x07, 0x2a, 0x86,
        0x48, 0xce, 0x3d, 0x02, 0x01, 0x06, 0x08, 0x2a,
        0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07, 0x03,
        0x42, 0x00
    };
    uint8_t unusedKeyTag[] = { 0x04, 0x41 };

    /* This variable is used only for its size. This gets rid of compiler warnings. */
    ( void ) unusedKeyTag;

    result = C_GetFunctionList( &functionList );

    /* Query the key type. */
    if( CKR_OK == result )
    {
        template.type = CKA_KEY_TYPE;
        template.pValue = &keyType;
        template.ulValueLen = sizeof( keyType );
        result = functionList->C_GetAttributeValue( session,
                                                    publicKeyHandle,
                                                    &template,
                                                    1 );
    }

    /* Scope to ECDSA keys only, since there's currently no use case for
     * onboard keygen and certificate enrollment for RSA. */
    if( ( CKR_OK == result ) && ( CKK_ECDSA == keyType ) )
    {
        /* Query the size of the public key. */
        template.type = CKA_EC_POINT;
        template.pValue = NULL;
        template.ulValueLen = 0;
        result = functionList->C_GetAttributeValue( session,
                                                    publicKeyHandle,
                                                    &template,
                                                    1 );

        /* Allocate a buffer large enough for the full, encoded public key. */
        if( CKR_OK == result )
        {
            /* Add space for the full DER header. */
            template.ulValueLen += sizeof( ecP256AsnOid ) - sizeof( unusedKeyTag );
            *derPublicKeyLength = template.ulValueLen;

            /* Get a heap buffer. */
            *derPublicKey = malloc( template.ulValueLen );

            /* Check for resource exhaustion. */
            if( NULL == *derPublicKey )
            {
                result = CKR_HOST_MEMORY;
            }
        }

        /* Export the public key. */
        if( CKR_OK == result )
        {
            template.pValue = *derPublicKey + sizeof( ecP256AsnOid ) - sizeof( unusedKeyTag );
            template.ulValueLen -= ( sizeof( ecP256AsnOid ) - sizeof( unusedKeyTag ) );
            result = functionList->C_GetAttributeValue( session,
                                                        publicKeyHandle,
                                                        &template,
                                                        1 );
        }

        /* Prepend the full DER header. */
        if( CKR_OK == result )
        {
            memcpy( *derPublicKey, ecP256AsnOid, sizeof( ecP256AsnOid ) );
        }
    }

    /* Free memory if there was an error after allocation. */
    if( ( NULL != *derPublicKey ) && ( CKR_OK != result ) )
    {
        free( *derPublicKey );
        *derPublicKey = NULL;
    }

    return result;
}
/*-----------------------------------------------------------*/

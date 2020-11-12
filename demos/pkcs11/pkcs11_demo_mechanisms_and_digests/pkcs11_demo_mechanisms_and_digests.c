/*
 * AWS IoT Device SDK for Embedded C V202011.00
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
 *
 * http://aws.amazon.com/freertos
 * http://www.FreeRTOS.org
 */

/* Standard includes. */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>

/* Logging configuration for the PKCS #11 Demo. */
#ifndef LIBRARY_LOG_NAME
    #define LIBRARY_LOG_NAME    "PKCS11_MECH_AND_DIGEST_DEMO"
#endif

#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_INFO
#endif

#include "logging_stack.h"

/* PKCS #11 includes. */
#include "core_pkcs11.h"
#include "pkcs11.h"

/* Demo includes. */
#include "demo_helpers.h"

/**
 * @brief This function details what Cryptoki mechanisms are, how to query a slot's
 * support for them, and how to use those mechanisms to generate a hash of a buffer.
 * This can then be used as a message digest.
 *
 * http://docs.oasis-open.org/pkcs11/pkcs11-base/v2.40/os/pkcs11-base-v2.40-os.html
 * please consult the standard for more information.
 *
 * The standard has grouped the functions presented in this demo as:
 * Slot and token management functions.
 * Message digesting functions.
 *
 */
void PKCS11MechanismsAndDigestDemo( void )
{
    /*
     * This demo builds upon the demo found in "management_and_rng.c". It borrows
     * code and terminology defined and explained, and it is recommended to complete
     * the "management and rng" demo before this one.
     */
    LogInfo( ( "Starting PKCS #11 Mechanisms and Digest Demo." ) );

    CK_SESSION_HANDLE session = CK_INVALID_HANDLE;
    CK_SLOT_ID * slotId = 0;
    CK_FUNCTION_LIST_PTR functionList = NULL;
    CK_ULONG index = 0;
    CK_RV result = CKR_OK;
    CK_BYTE hashFormatBuffer[ pkcs11SHA256_DIGEST_LENGTH * 2 ] = { 0 };
    CK_BYTE_PTR formatPtr = NULL;

    /* The PKCS #11 standard defines a mechanism to be a "A process for
     * implementing a cryptographic operation." For example the SHA-256 algorithm
     * will be the mechanism used in this demo to perform a digest (hash operation).
     *
     * The mechanism types are defined in "pkcs11t.h", and are prefixed CKM_, to
     * provide a portable way to identify mechanisms.
     */
    CK_MECHANISM_TYPE xMechanismType = 0;

    /* This variable is not directly used, but is instantiated for demonstration
     * purposes.
     */
    ( void ) xMechanismType;

    /* The CK_MECHANISM_INFO allows the application to retrieve the minimum and
     * maximum key sizes supported by the mechanism (could be in bits or bytes).
     * The structure also has a flags field, that is populated with bit flags
     * for what features the mechanism supports.
     */
    CK_MECHANISM_INFO MechanismInfo = { 0 };

    /* The CK_MECHANISM type contains the mechanism type, as well as a pointer
     * for mechanism parameters and a CK_ULONG indicating the length of the
     * parameters.
     */
    CK_MECHANISM xDigestMechanism = { 0 };

    /* The digest will return a hash of the known SHA-256 hash size, 32 bytes.
     * Please see this page for further explanation of the SHA-256 hash.
     * https://en.wikipedia.org/wiki/SHA-2
     */
    CK_BYTE digestResult[ pkcs11SHA256_DIGEST_LENGTH ] = { 0 };
    CK_ULONG digestLength = pkcs11SHA256_DIGEST_LENGTH;

    CK_BYTE knownMessage[] = "Hello world!";

    start( &session, &slotId );
    result = C_GetFunctionList( &functionList );
    assert( CKR_OK == result );
    assert( functionList->C_GetMechanismInfo != NULL );
    assert( functionList->C_DigestInit != NULL );
    assert( functionList->C_DigestUpdate != NULL );
    assert( functionList->C_DigestFinal != NULL );

    /*************************** RSA Capabilities ***************************/
    result = functionList->C_GetMechanismInfo( slotId[ 0 ],
                                                  CKM_RSA_PKCS,
                                                  &MechanismInfo );
    assert( CKR_OK == result );

    /* Check to see if the slot supports signing. This capability is important
     * because we want to use the Cryptoki API to sign messages, without directly
     * accessing the private key. This concept will be explained further in the
     * "sign_verify.c" demo, but for now we will just check that the slot has the
     * capabilities we need. See https://en.wikipedia.org/wiki/Public-key_cryptography
     * for more information regarding private keys and public keys.
     */
    if( 0 != ( CKF_SIGN & MechanismInfo.flags ) )
    {
        LogInfo( ( "This Cryptoki library supports signing messages with RSA" \
                   " private keys." ) );
    }
    else
    {
        LogInfo( ( "This Cryptoki library does not support signing messages" \
                   " with RSA private keys." ) );
    }

    /* This Cryptoki library assumes that RSA private keys are 2048 bit . */
    assert( MechanismInfo.ulMaxKeySize >= pkcs11RSA_2048_MODULUS_BITS );
    assert( MechanismInfo.ulMinKeySize <= pkcs11RSA_2048_MODULUS_BITS );

    /* Check for pre-padded signature verification support, this feature will
     * be used in the "sign_verify.c" demo.
     */
    result = functionList->C_GetMechanismInfo( slotId[ 0 ],
                                                  CKM_RSA_X_509,
                                                  &MechanismInfo );

    /* If this fails, the slot is not able to verify the signature using
     * a RSA public key. Please see https://en.wikipedia.org/wiki/Public_key_infrastructure
     * for more information regarding PKI (Public Key Infrastructure).
     */
    if( 0 != ( CKF_VERIFY & MechanismInfo.flags ) )
    {
        LogInfo( ( "This Cryptoki library supports verifying messages with RSA" \
                   " public keys." ) );
    }
    else
    {
        LogInfo( ( "This Cryptoki library does not support verifying messages" \
                   " with RSA public keys." ) );
    }

    /* This Cryptoki library assumes that RSA public keys are 2048 bit . */
    assert( MechanismInfo.ulMaxKeySize >= pkcs11RSA_2048_MODULUS_BITS );
    assert( MechanismInfo.ulMinKeySize <= pkcs11RSA_2048_MODULUS_BITS );

    /*************************** ECDSA Capabilities ***************************/
    result = functionList->C_GetMechanismInfo( slotId[ 0 ],
                                                  CKM_ECDSA,
                                                  &MechanismInfo );
    assert( CKR_OK == result );

    if( 0 != ( CKF_SIGN & MechanismInfo.flags ) )
    {
        LogInfo( ( "This Cryptoki library supports signing messages with" \
                   " ECDSA private keys." ) );
    }
    else
    {
        LogInfo( ( "This Cryptoki library does not support signing messages" \
                   " with ECDSA private keys." ) );
    }

    if( 0 != ( CKF_VERIFY & MechanismInfo.flags ) )
    {
        LogInfo( ( "This Cryptoki library supports verifying messages with" \
                   " ECDSA public keys." ) );
    }
    else
    {
        LogInfo( ( "This Cryptoki library does not support verifying" \
                   " messages with ECDSA public keys." ) );
    }

    assert( MechanismInfo.ulMaxKeySize >= pkcs11ECDSA_P256_KEY_BITS );
    assert( MechanismInfo.ulMinKeySize <= pkcs11ECDSA_P256_KEY_BITS );

    /************************** Digest Capabilities **************************/
    result = functionList->C_GetMechanismInfo( slotId[ 0 ],
                                                  CKM_SHA256,
                                                  &MechanismInfo );
    assert( CKR_OK == result );

    if( 0 != ( CKF_DIGEST & MechanismInfo.flags ) )
    {
        LogInfo( ( "The Cryptoki library supports the " \
                   "SHA-256 algorithm." ) );
    }
    else
    {
        LogInfo( ( "The Cryptoki library doesn't support the " \
                   "SHA-256 algorithm." ) );
    }

    /***************************** Buffer Digest *****************************/
    /* Hash with SHA256 mechanism. */
    xDigestMechanism.mechanism = CKM_SHA256;

    /* Initializes the digest operation and sets what mechanism will be used
     * for the digest. */
    result = functionList->C_DigestInit( session,
                                            &xDigestMechanism );
    assert( CKR_OK == result );


    /* Pass a pointer to the buffer of bytes to be hashed, and it's size. */
    result = functionList->C_DigestUpdate( session,
                                              knownMessage,
                                              /* Strip NULL Terminator. */
                                              sizeof( knownMessage ) - 1 );
    assert( CKR_OK == result );

    /* Retrieve the digest buffer. Since the mechanism is a SHA-256 algorithm,
     * the size will always be 32 bytes. If the size cannot be known ahead of time,
     * a NULL value to the second parameter pDigest, will set the third parameter,
     * pulDigestLen to the number of required bytes. */
    result = functionList->C_DigestFinal( session,
                                             digestResult,
                                             &digestLength );
    assert( CKR_OK == result );

    /* This will now print out the digest of the known message. You can compare
     * the hash generated by the Cryptoki library in a UNIX shell by using the
     * command '$ echo -n "{knownMessage}" | shasum -a 256'
     * this command should generate the same hash. */
    LogInfo( ( "Known message: %s", ( char * ) knownMessage ) );

    formatPtr = &hashFormatBuffer[ 0 ];

    for( index = 0; index < digestLength; index++ )
    {
        formatPtr += sprintf( ( char * ) formatPtr, "%x", digestResult[ index ] );
    }

    LogInfo( ( "Hash of known message using SHA256: %s.", hashFormatBuffer ) );
    LogInfo( ( "Finished PKCS #11 Mechanisms and Digest Demo." ) );

    /* Avoid compiler warnings if asserts are disabled. */
    ( void ) result;

    end( session, slotId );
}

/**
 * @brief Entry point of demo.
 *
 * The example shown above uses PKCS #11 APIs to specify mechanisms and how to create a digest.
 */
int main( void )
{
    PKCS11MechanismsAndDigestDemo();
    return 0;
}

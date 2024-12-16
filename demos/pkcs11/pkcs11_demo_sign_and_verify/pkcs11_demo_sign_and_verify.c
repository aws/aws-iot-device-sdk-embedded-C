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

/* Standard include. */
#include <stdio.h>
#include <stdlib.h>

/* Logging stack includes. */
#include "logging_levels.h"

#ifndef LIBRARY_LOG_NAME
    #define LIBRARY_LOG_NAME    "PKCS11_SIGN_VERIFY_DEMO"
#endif

#ifndef LIBRARY_LOG_LEVEL
    #define LIBRARY_LOG_LEVEL    LOG_INFO
#endif

#include "logging_stack.h"

/* PKCS #11 includes. */
#include "core_pkcs11.h"
#include "pkcs11.h"
#include "core_pki_utils.h"

/* Demo includes. */
#include "demo_helpers.h"

/**
 * @brief This function details how to use the PKCS #11 "Sign and Verify" functions to
 * create and interact with digital signatures.
 * The functions described are all defined in
 * https://docs.oasis-open.org/pkcs11/pkcs11-base/v2.40/os/pkcs11-base-v2.40-os.html
 * Please consult the standard for more information regarding these functions.
 *
 * The standard has grouped the functions presented in this demo as:
 * Object Management Functions
 * Signing and MACing Functions
 */
CK_RV PKCS11SignVerifyDemo( void )
{
    /* This demo will use the generated private and public key from the
     * "objects.c" demo and use them to sign and verify the integrity of a
     * message digest. This demo will use concepts from all the other demos,
     * and is recommended be done last.
     *
     * The intention of this demo is how to use PKCS #11's Crypotki API to do
     * these signature operations, not to explain when and why they should be
     * used. For a deeper understanding of that please read:
     * https://en.wikipedia.org/wiki/Public_key_infrastructure
     * https://en.wikipedia.org/wiki/Transport_Layer_Security
     * https://en.wikipedia.org/wiki/Digital_signature
     */
    LogInfo( ( "Starting PKCS #11 Sign and Verify Demo." ) );

    /* Helper / previously explained variables. */
    CK_RV result = CKR_OK;
    CK_SESSION_HANDLE session = CK_INVALID_HANDLE;
    CK_ULONG index = 0;
    CK_OBJECT_HANDLE privateKeyHandle = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE publicKeyHandle = CK_INVALID_HANDLE;
    CK_FUNCTION_LIST_PTR functionList = NULL;
    CK_BYTE * derPublicKey = NULL;
    CK_ULONG derPublicKeyLength = 0;
    CK_BYTE signatureFormatBuffer[ pkcs11SHA256_DIGEST_LENGTH * 2 ] = { 0 };
    CK_BYTE_PTR formatPtr = NULL;

    /* Digest variables. See "mechanisms_and_digests" for an explanation. */
    CK_BYTE knownMessage[] = { "Hello world" };
    CK_BYTE digestResult[ pkcs11SHA256_DIGEST_LENGTH ] = { 0 };
    CK_ULONG digestLength = pkcs11SHA256_DIGEST_LENGTH;
    CK_MECHANISM xDigestMechanism = { 0 };

    /* Signing variables. */
    /* The ECDSA mechanism will be used to sign the message digest. */
    CK_MECHANISM mechanism = { CKM_ECDSA, NULL, 0 };

    /* This signature buffer will be used to store the signature created by the
     * private key. (64 bytes). We pad it with an extra 8 bytes so it can be
     * converted to an ASN.1 encoding. */
    CK_BYTE signature[ pkcs11ECDSA_P256_SIGNATURE_LENGTH + 8 ] = { 0 };
    CK_ULONG signatureLength = sizeof( signature );

    /* Ensure the Cryptoki library has the necessary functions implemented. */
    result = C_GetFunctionList( &functionList );

    /* Instead of using the start helper, we will  use the "core_pkcs11.h"
     * functions that help wrap around some common PKCS #11 use cases.
     *
     * This function will:
     * Initialize the PKCS #11 module if it is not already.
     * Initialize a PKCS #11 session.
     */
    if( result == CKR_OK )
    {
        result = xInitializePkcs11Session( &session );
    }

    /* This function will:
     * Initialize the PKCS #11 module if it is not already.
     * Initialize the token to be used.
     *
     * Note: By default this function will always initialize the token in the
     * first slot in the slot list. If it desired to use a different slot, it
     * is necessary to modify the implementation of this function to use a
     * different slot. */
    if( result == CKR_OK )
    {
        result = xInitializePkcs11Token();
    }

    /***************************** Find Objects *****************************/

    /* This function will:
     * Find an object, given it's label.
     *
     * This is done using the FindObjects group of functions defined as
     * "Object Management Functions" in PKCS #11.
     *
     * This will acquire the object handle for the private key created in the
     * "objects.c" demo.
     */
    if( result == CKR_OK )
    {
        result = xFindObjectWithLabelAndClass( session,
                                               pkcs11demoPRIVATE_KEY_LABEL,
                                               sizeof( pkcs11demoPRIVATE_KEY_LABEL ) - 1,
                                               CKO_PRIVATE_KEY,
                                               &privateKeyHandle );
    }

    /* Acquire the object handle for the public key created in the "objects.c"
     * demo. */
    if( result == CKR_OK )
    {
        result = xFindObjectWithLabelAndClass( session,
                                               pkcs11demoPUBLIC_KEY_LABEL,
                                               sizeof( pkcs11demoPUBLIC_KEY_LABEL ) - 1,
                                               CKO_PUBLIC_KEY,
                                               &publicKeyHandle );
    }

    if( ( privateKeyHandle == CK_INVALID_HANDLE ) || ( publicKeyHandle == CK_INVALID_HANDLE ) )
    {
        LogError( ( "IMPORTANT: The demo could not find the key and certificate"
                    " generated by the pkcs11_demo_objects demo. It is"
                    " necessary to FIRST run the objects demo, to create a key"
                    " and certificate. Once this is done make sure to run the"
                    " sign_and_verify demo from a folder containing those files"
                    ", so it can access the key and certificate in the file"
                    " system." ) );
        result = CKR_OBJECT_HANDLE_INVALID;
    }

    /***************************** Buffer Digest *****************************/
    xDigestMechanism.mechanism = CKM_SHA256;

    /* Initializes the digest operation and sets what mechanism will be used
     * for the digest. */
    if( result == CKR_OK )
    {
        result = functionList->C_DigestInit( session,
                                             &xDigestMechanism );
    }

    /* Pass a pointer to the buffer of bytes to be hashed, and it's size. */
    if( result == CKR_OK )
    {
        result = functionList->C_DigestUpdate( session,
                                               knownMessage,
                                               /* Strip NULL Terminator. */
                                               sizeof( knownMessage ) - 1 );
    }

    /* Retrieve the digest buffer length. When passing in a NULL pointer as the
     * second argument, instead of a point to a buffer, this will signal the
     * Cryptoki library to fill the third parameter with the required amount of
     * bytes to store the resulting digest.
     */
    if( result == CKR_OK )
    {
        result = functionList->C_DigestFinal( session,
                                              NULL,
                                              &digestLength );
    }

    /* Now that digestLength contains the required byte length, retrieve the
     * digest buffer.
     */
    if( result == CKR_OK )
    {
        result = functionList->C_DigestFinal( session,
                                              digestResult,
                                              &digestLength );
    }

    /********************************* Sign **********************************/

    /* Initializes the sign operation and sets what mechanism will be used
     * for signing the message digest. Specify what object handle to use for this
     * operation, in this case the private key object handle. */
    if( result == CKR_OK )
    {
        LogInfo( ( "Signing known message: %s",
                   ( char * ) knownMessage ) );

        result = functionList->C_SignInit( session,
                                           &mechanism,
                                           privateKeyHandle );
    }

    /* Sign the message digest that was created with the C_Digest series of
     * functions. A signature will be created using the private key specified in
     * C_SignInit and put in the byte buffer signature. */
    if( result == CKR_OK )
    {
        result = functionList->C_Sign( session,
                                       digestResult,
                                       pkcs11SHA256_DIGEST_LENGTH,
                                       signature,
                                       &signatureLength );
    }

    /********************************* Verify **********************************/

    /* Verify the signature created by C_Sign. First we will verify that the
     * same Cryptoki library was able to trust itself.
     *
     * C_VerifyInit will begin the verify operation, by specifying what mechanism
     * to use (CKM_ECDSA, the same as the sign operation) and then specifying
     * which public key handle to use.
     */
    if( result == CKR_OK )
    {
        result = functionList->C_VerifyInit( session,
                                             &mechanism,
                                             publicKeyHandle );
    }

    /* Given the signature and it's length, the Cryptoki will use the public key
     * to verify that the signature was created by the corresponding private key.
     * If C_Verify returns CKR_OK, it means that the sender of the message has
     * the same private key as the private key that was used to generate the
     * public key, and we can trust that the message we received was from that
     * sender.
     *
     * Note that we are not using the actual message, but the digest that we
     * created earlier of the message, for the verification.
     */
    if( result == CKR_OK )
    {
        result = functionList->C_Verify( session,
                                         digestResult,
                                         pkcs11SHA256_DIGEST_LENGTH,
                                         signature,
                                         signatureLength );

        if( result == CKR_OK )
        {
            LogInfo( ( "The signature of the digest was verified with the"
                       " public key and can be trusted." ) );
        }
        else
        {
            LogInfo( ( "Unable to verify the signature with the given public"
                       " key, the message cannot be trusted." ) );
        }
    }

    /* Export public key as hex bytes and print the hex representation of the
     * public key.
     *
     * We need to export the public key so that it can be used by a different
     * device to verify messages signed by the private key of the device that
     * generated the key pair.
     *
     * To do this, we will output the hex representation of the public key.
     * Then create an empty text file called "DevicePublicKeyAsciiHex.txt".
     *
     * Copy and paste the hex value of the public key into this text file.
     *
     * Then we will need to convert the text file to binary using the xxd tool.
     *
     * xxd will take a text file that contains hex data and output a binary of
     * the hex in the file. See "$ man xxd" for more information about xxd.
     *
     * Copy the below command into the terminal.
     * "$ xxd -r -ps DevicePublicKeyAsciiHex.txt DevicePublicKeyDer.bin"
     *
     * Now that we have the binary encoding of the public key, we will convert
     * it to PEM using OpenSSL.
     *
     * The following command will create a PEM file of the public key called
     * "public_key.pem"
     *
     * "$ openssl ec -inform der -in DevicePublicKeyDer.bin -pubin -pubout -outform pem -out public_key.pem"
     *
     * Now we can use the extracted public key to verify the signature of the
     * device's private key.
     *
     * WARNING: Running the object generation demo will create a new key pair,
     * and make it necessary to redo these steps!
     *
     */
    if( result == CKR_OK )
    {
        LogInfo( ( "Verifying with public key." ) );
        exportPublicKey( session,
                         publicKeyHandle,
                         &derPublicKey,
                         &derPublicKeyLength );
        writeHexBytesToConsole( "Public Key in Hex Format",
                                derPublicKey,
                                derPublicKeyLength );

        /* exportPublicKey allocates memory which needs to be freed. */
        if( derPublicKey != NULL )
        {
            free( derPublicKey );
        }
    }

    /* This utility function converts the PKCS #11 signature into an ASN.1
     * encoded binary der signature. This is necessary so we can export the
     * signature and verify it with OpenSSL, otherwise OpenSSL will not be able
     * to parse the buffer.
     *
     * See https://en.wikipedia.org/wiki/ASN.1 for more information about the
     * ASN.1 encoding format.
     */
    if( result == CKR_OK )
    {
        PKI_pkcs11SignatureTombedTLSSignature( signature, ( size_t * ) &signatureLength );

        /* The following loop will output the signature in hex.
         *
         * In order to get the signature exported in binary form copy the output
         * of the loop, and paste it to an empty text file.
         *
         * Then we will need to convert the text file to binary using the xxd tool.
         *
         * The following commands outline this process.
         * Write buffer to signature.txt
         * xxd will take a text file that contains hex data and output a binary of
         * the hex in the file. See "$ man xxd" for more information about xxd.
         *
         * Copy the below command into the terminal.
         * "$ xxd -r -ps signature.txt signature.bin"
         *
         * Next, we need to copy the original message that the Cryptoki library
         * signed, the following shell command will create the message without any
         * newlines, so the messages are similar.
         *
         * The contents of the echo command can be replaced with whatever data was
         * in the known message, but the example uses "Hello world" to make it easier
         * for copy and pasting.
         *
         * "$ echo -n "Hello world" > msg.txt"
         *
         * Now we will use OpenSSL to verify that the signature we created can be
         * trusted by another device using the public key we created and then
         * extracted earlier.
         *
         * "$ openssl dgst -sha256 -verify public_key.pem -signature signature.bin msg.txt"
         * This command should output "Verified OK" and we then know we can trust
         * the sender of the message!
         */
        formatPtr = &signatureFormatBuffer[ 0 ];

        for( index = 0; index < digestLength; index++ )
        {
            formatPtr += sprintf( ( char * ) formatPtr, "%x", signature[ index ] );
        }

        LogInfo( ( "Created signature: %s", signatureFormatBuffer ) );
        LogInfo( ( "Finished PKCS #11 Sign and Verify Demo." ) );
    }

    return result;
}

/**
 * @brief Entry point of demo.
 *
 * The example shown above uses PKCS #11 APIs to demonstrate how to sign and verify a message
 */
int main( void )
{
    return PKCS11SignVerifyDemo();
}

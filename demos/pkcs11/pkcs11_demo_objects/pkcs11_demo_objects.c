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
#include <string.h>

/* Logging configuration for the PKCS #11 Demo. */
#include "logging_levels.h"
#ifndef LIBRARY_LOG_NAME
    #define LIBRARY_LOG_NAME    "PKCS11_OBJECTS_DEMO"
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

/* Demo includes. */
#include "demo_helpers.h"

/* RSA certificate that has been generated off the device.
 * This key will be used as an example for importing an object onto the device.
 * This is useful when the device itself cannot create credentials or for storing
 * a well known CA certificate.
 */
#define pkcs11demo_RSA_CERTIFICATE                                       \
    ""                                                                   \
    "-----BEGIN CERTIFICATE-----\n"                                      \
    "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\n" \
    "xg07nhvDeydwB48xXrPQ1KutrRyh\n"                                     \
    "-----END CERTIFICATE-----"

/* Add C++ guards for C linkage in case this file is being compiled as C++
 * for a CI check. */
/* *INDENT-OFF* */
#ifdef __cplusplus
    extern "C" {
#endif
/* *INDENT-ON* */

/* This function can be found in
 * corePKCS11/source/dependency/3rdparty/mbedtls_utils/mbedtls_utils.c.
 * It will be used to convert the RSA certificate from PEM format
 * to DER format. */
extern int convert_pem_to_der( const unsigned char * pucInput,
                               size_t xLen,
                               unsigned char * pucOutput,
                               size_t * pxOlen );
/* *INDENT-OFF* */
#ifdef __cplusplus
    }
#endif
/* *INDENT-ON* */

/*-----------------------------------------------------------*/


/**
 * @brief objectImporting covers how to import a RSA certificate that was
 * not generated by the Cryptoki library.
 *
 */
static CK_RV objectImporting( void );

/**
 * @brief objectGeneration covers how to create a public key and private key pair
 * with Cryptoki defined attributes using C_GenerateKeyPair.
 *
 * @note The "sign-verify.c" demo has a dependency on the objects created
 * in this function, and will not work without first running this function.
 */
static CK_RV objectGeneration( void );


/**
 * This function details how to use the PKCS #11 "Object" functions to
 * manage the objects abstracted by cryptoki.
 *
 * https://docs.oasis-open.org/pkcs11/pkcs11-base/v2.40/os/pkcs11-base-v2.40-os.html
 * please consult the standard for more information.
 *
 * The standard has grouped the functions presented in this demo as:
 * Object Management Functions.
 *
 */
CK_RV PKCS11ObjectDemo( void )
{
    CK_RV result = CKR_OK;

    LogInfo( ( "Starting PKCS #11 Objects Demo." ) );

    /* PKCS #11 defines objects as "An item that is stored on a token. May be
     * data, a certificate, or a key." This demo will show how to create objects
     * that are managed by Cryptoki. */
    result = objectImporting();

    if( result == CKR_OK )
    {
        result = objectGeneration();
    }

    LogInfo( ( "Finished PKCS #11 Objects Demo." ) );

    return result;
}

static CK_RV objectImporting( void )
{
    LogInfo( ( "---------Importing Objects---------" ) );
    LogInfo( ( "Importing RSA Certificate..." ) );

    /* Helper variables and variables that have been covered. */
    CK_RV result = CKR_OK;
    CK_SESSION_HANDLE session = CK_INVALID_HANDLE;
    CK_SLOT_ID * slotId = 0;
    CK_FUNCTION_LIST_PTR functionList = NULL;
    uint8_t * derObject = NULL;
    size_t derLen = 0;
    CK_BBOOL tokenStorage = CK_TRUE;
    CK_OBJECT_HANDLE certHandle = CK_INVALID_HANDLE;
    CK_BYTE subject[] = "TestSubject";


    /* The PKCS11_CertificateTemplate_t is a custom struct defined in "core_pkcs11.h"
     * in order to make it easier to import a certificate. This struct will be
     * populated with the parameters necessary to import the certificate into the
     * Cryptoki library.
     */
    PKCS11_CertificateTemplate_t certificateTemplate;

    /* The object class is specified as a certificate to help the Cryptoki library
     * parse the arguments.
     */
    CK_OBJECT_CLASS xCertificateClass = CKO_CERTIFICATE;

    /* The certificate type is an x509 certificate, which is the only type
     * supported by this stack. To read more about x509 certificates one can
     * read the following:
     *
     * https://en.wikipedia.org/wiki/X.509
     * https://www.ssl.com/faqs/what-is-an-x-509-certificate/
     *
     */
    CK_CERTIFICATE_TYPE xCertificateType = CKC_X_509;

    /* The label will help the application identify which object it would like
     * to access.
     */
    CK_BYTE label[] = pkcs11demoCERT_LABEL;

    /* Specify certificate class. */
    certificateTemplate.xObjectClass.type = CKA_CLASS;
    certificateTemplate.xObjectClass.pValue = &xCertificateClass;
    certificateTemplate.xObjectClass.ulValueLen = sizeof( xCertificateClass );

    /* Specify certificate subject. */
    certificateTemplate.xSubject.type = CKA_SUBJECT;
    certificateTemplate.xSubject.pValue = subject;
    certificateTemplate.xSubject.ulValueLen = strlen( ( const char * ) subject );

    /* Point to contents of certificate. */
    certificateTemplate.xValue.type = CKA_VALUE;
    certificateTemplate.xValue.pValue = ( CK_VOID_PTR ) pkcs11demo_RSA_CERTIFICATE;
    certificateTemplate.xValue.ulValueLen = ( CK_ULONG ) sizeof( pkcs11demo_RSA_CERTIFICATE );

    /* Specify certificate label. */
    certificateTemplate.xLabel.type = CKA_LABEL;
    certificateTemplate.xLabel.pValue = ( CK_VOID_PTR ) label;
    certificateTemplate.xLabel.ulValueLen = strlen( ( const char * ) label );

    /* Specify certificate type as x509. */
    certificateTemplate.xCertificateType.type = CKA_CERTIFICATE_TYPE;
    certificateTemplate.xCertificateType.pValue = &xCertificateType;
    certificateTemplate.xCertificateType.ulValueLen = sizeof( CK_CERTIFICATE_TYPE );

    /* Specify that the certificate should be on a token. */
    certificateTemplate.xTokenObject.type = CKA_TOKEN;
    certificateTemplate.xTokenObject.pValue = &tokenStorage;
    certificateTemplate.xTokenObject.ulValueLen = sizeof( tokenStorage );

    result = start( &session, &slotId );

    /* Ensure the Cryptoki library has the necessary functions implemented. */
    if( result == CKR_OK )
    {
        result = C_GetFunctionList( &functionList );
    }

    /* Convert the certificate to DER format if it was in PEM. The DER key
     * should be about 3/4 the size of the PEM key, so mallocing the PEM key
     * size is sufficient. */
    derObject = ( uint8_t * ) malloc( certificateTemplate.xValue.ulValueLen );

    if( derObject == NULL )
    {
        result = CKR_HOST_MEMORY;
    }

    if( result == CKR_OK )
    {
        derLen = certificateTemplate.xValue.ulValueLen;
        ( void ) convert_pem_to_der( ( unsigned char * ) certificateTemplate.xValue.pValue,
                                     certificateTemplate.xValue.ulValueLen,
                                     derObject,
                                     &derLen );
    }

    /* Set the template pointers to refer to the DER converted objects. */
    certificateTemplate.xValue.pValue = derObject;
    certificateTemplate.xValue.ulValueLen = derLen;

    /* Create an object using the encoded client certificate. */
    LogInfo( ( "Creating x509 certificate with label: %s ",
               pkcs11demoCERT_LABEL ) );

    /* Once the Cryptoki library has finished importing the new x509 certificate
     * a CK_OBJECT_HANDLE is associated with it. The application can now use this
     * to refer to the object in following operations.
     *
     * certHandle in the below example will have it's value modified to
     * be the CK_OBJECT_HANDLE.
     *
     * Compare the hard coded x509, in PEM format, with the DER formatted
     * x509 certificate that is created by the Cryptoki library, with the following
     * OpenSSL command:
     * "$ openssl x509 -in FreeRTOS_P11_Certificate.dat -inform der -text"
     *
     * See this explanation for the difference between the PEM format and the
     * DER format:
     * https://stackoverflow.com/questions/22743415/what-are-the-differences-between-pem-cer-and-der/22743616
     *
     */
    if( result == CKR_OK )
    {
        result = functionList->C_CreateObject( session,
                                               ( CK_ATTRIBUTE_PTR ) &certificateTemplate,
                                               sizeof( certificateTemplate ) / sizeof( CK_ATTRIBUTE ),
                                               &certHandle );
    }

    LogInfo( ( "FreeRTOS_P11_Certificate.dat has been created in the current "
               " directory" ) );

    free( derObject );
    end( session, slotId );
    LogInfo( ( "Finished Importing RSA Certificate." ) );
    LogInfo( ( "---------Finished Importing Objects---------" ) );

    return result;
}

static CK_RV objectGeneration( void )
{
    LogInfo( ( "---------Generating Objects---------" ) );

    /* Helper variables. */
    CK_RV result = CKR_OK;
    CK_SESSION_HANDLE session = CK_INVALID_HANDLE;
    CK_SLOT_ID * slotId = 0;
    CK_FUNCTION_LIST_PTR functionList = NULL;
    CK_BYTE * derPublicKey = NULL;
    CK_ULONG derPublicKeyLength = 0;
    CK_BBOOL trueVar = CK_TRUE;

    /* Specify the mechanism to use in the key pair generation. Mechanisms are
     * previously explained in the "mechanims_and_digests.c" demo. */
    CK_MECHANISM mechanism =
    {
        CKM_EC_KEY_PAIR_GEN, NULL_PTR, 0
    };

    /* The EC curve used in this demo will be the named EC curve prime256v1.
     * For further explanations of EC Cryptography please see the following:
     * https://en.wikipedia.org/wiki/Elliptic-curve_cryptography
     * https://wiki.openssl.org/index.php/Elliptic_Curve_Cryptography
     */
    CK_BYTE ecParams[] = pkcs11DER_ENCODED_OID_P256;

    /* Specify the key type to be EC. */
    CK_KEY_TYPE keyType = CKK_EC;

    /* Object handles are a token specific identifier for an object. They are
     * used so the application's sessions can specify which object to interact
     * with. Non-zero values are valid, 0 is always invalid, and is defined as
     * CK_INVALID_HANDLE
     *
     * The lifetime of the handle is not necessarily the same as the lifetime of
     * the object.
     */
    CK_OBJECT_HANDLE privateKeyHandle = CK_INVALID_HANDLE;
    CK_OBJECT_HANDLE publicKeyHandle = CK_INVALID_HANDLE;


    /* Labels are application defined strings that are used to identify an
     * object. It should not be NULL terminated. */
    CK_BYTE publicKeyLabel[] = { pkcs11demoPUBLIC_KEY_LABEL };
    CK_BYTE privateKeyLabel[] = { pkcs11demoPRIVATE_KEY_LABEL };

    /* CK_ATTTRIBUTE's contain an attribute type, a value, and the length of
     * the value. An array of CK_ATTRIBUTEs is called a template. They are used
     * for creating, searching, and manipulating for objects. The order of the
     * template does not matter.
     *
     * In the below template we are creating a public key:
     *      Specify the key type as EC.
     *      The key will be able to verify a message.
     *      Specify the EC Curve.
     *      Assign a label to the object that will be created.
     */
    CK_ATTRIBUTE publicKeyTemplate[] =
    {
        { CKA_KEY_TYPE,  &keyType,       sizeof( keyType )            },
        { CKA_VERIFY,    &trueVar,       sizeof( trueVar )            },
        { CKA_EC_PARAMS, ecParams,       sizeof( ecParams )           },
        { CKA_LABEL,     publicKeyLabel, sizeof( publicKeyLabel ) - 1 }
    };

    /* In the below template we are creating a private key:
     *      The key type is EC.
     *      The key is a token object.
     *      The key will be a private key.
     *      The key will be able to sign messages.
     *      Assign a label to the object that will be created.
     */
    CK_ATTRIBUTE privateKeyTemplate[] =
    {
        { CKA_KEY_TYPE, &keyType,        sizeof( keyType )             },
        { CKA_TOKEN,    &trueVar,        sizeof( trueVar )             },
        { CKA_PRIVATE,  &trueVar,        sizeof( trueVar )             },
        { CKA_SIGN,     &trueVar,        sizeof( trueVar )             },
        { CKA_LABEL,    privateKeyLabel, sizeof( privateKeyLabel ) - 1 }
    };

    if( result == CKR_OK )
    {
        start( &session, &slotId );
    }

    result = C_GetFunctionList( &functionList );

    LogInfo( ( "Creating private key with label: %s ",
               pkcs11demoPRIVATE_KEY_LABEL ) );
    LogInfo( ( "Creating public key with label: %s ",
               pkcs11demoPUBLIC_KEY_LABEL ) );

    /* This function will generate a new EC private and public key pair. You can
     * use " $openssl ec -inform der -in FreeRTOS_P11_Key.dat -text " to see
     * the structure of the keys that were generated.
     */
    if( result == CKR_OK )
    {
        result = functionList->C_GenerateKeyPair( session,
                                                  &mechanism,
                                                  publicKeyTemplate,
                                                  sizeof( publicKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                                  privateKeyTemplate,
                                                  sizeof( privateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                                  &publicKeyHandle,
                                                  &privateKeyHandle );
    }

    LogInfo( ( "FreeRTOS_P11_Key.dat has been created in the "
               "current directory" ) );
    LogInfo( ( "Extracting public key bytes..." ) );

    /* Export public key as hex bytes and print the hex representation of the
     * public key. */
    exportPublicKey( session,
                     publicKeyHandle,
                     &derPublicKey,
                     &derPublicKeyLength );
    writeHexBytesToConsole( "Public Key in Hex Format",
                            derPublicKey,
                            derPublicKeyLength );

    /* exportPublicKey allocates memory which must be freed. */
    if( derPublicKey != NULL )
    {
        free( derPublicKey );
    }

    LogInfo( ( "---------Finished Generating Objects---------" ) );
    end( session, slotId );

    return result;
}

/**
 * @brief Entry point of demo.
 *
 * The example shown above uses PKCS #11 APIs to interact with objects.
 */
int main( void )
{
    return PKCS11ObjectDemo();
}

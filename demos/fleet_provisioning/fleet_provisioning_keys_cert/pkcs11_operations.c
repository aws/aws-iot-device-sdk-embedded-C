/*
 * AWS IoT Device SDK for Embedded C 202412.00
 * Copyright (C) 2021 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file pkcs11_operations.c
 *
 * @brief This file provides wrapper functions for PKCS11 operations.
 */

/* Standard includes. */
#include <errno.h>
#include <assert.h>

/* Config include. */
#include "demo_config.h"

/* Interface include. */
#include "pkcs11_operations.h"

/* PKCS #11 include. */
#include "core_pkcs11_config.h"
#include "core_pki_utils.h"
#include "mbedtls_utils.h"

/* MbedTLS include. */
#include "mbedtls/ctr_drbg.h"
#include "mbedtls/entropy.h"
#include "entropy_poll.h"
#include "mbedtls/error.h"
#include "mbedtls/oid.h"
#include "mbedtls/pk.h"
#include "pk_wrap.h"
#include "mbedtls/sha256.h"
#include "mbedtls/x509_crt.h"
#include "mbedtls/x509_csr.h"

/**
 * @brief Size of buffer in which to hold the certificate signing request (CSR).
 */
#define CLAIM_CERT_BUFFER_LENGTH           2048

/**
 * @brief Size of buffer in which to hold the certificate signing request (CSR).
 */
#define CLAIM_PRIVATE_KEY_BUFFER_LENGTH    2048

/* Length parameters for importing RSA-2048 private keys. */
#define MODULUS_LENGTH                     pkcs11RSA_2048_MODULUS_BITS / 8
#define E_LENGTH                           3
#define D_LENGTH                           pkcs11RSA_2048_MODULUS_BITS / 8
#define PRIME_1_LENGTH                     128
#define PRIME_2_LENGTH                     128
#define EXPONENT_1_LENGTH                  128
#define EXPONENT_2_LENGTH                  128
#define COEFFICIENT_LENGTH                 128

#define EC_PARAMS_LENGTH                   10
#define EC_D_LENGTH                        32

/**
 * @brief Struct for holding parsed RSA-2048 private keys.
 */
typedef struct RsaParams_t
{
    CK_BYTE modulus[ MODULUS_LENGTH + 1 ];
    CK_BYTE e[ E_LENGTH + 1 ];
    CK_BYTE d[ D_LENGTH + 1 ];
    CK_BYTE prime1[ PRIME_1_LENGTH + 1 ];
    CK_BYTE prime2[ PRIME_2_LENGTH + 1 ];
    CK_BYTE exponent1[ EXPONENT_1_LENGTH + 1 ];
    CK_BYTE exponent2[ EXPONENT_2_LENGTH + 1 ];
    CK_BYTE coefficient[ COEFFICIENT_LENGTH + 1 ];
} RsaParams_t;

/**
 * @brief Struct containing parameters needed by the signing callback.
 */
typedef struct SigningCallbackContext
{
    CK_SESSION_HANDLE p11Session;
    CK_OBJECT_HANDLE p11PrivateKey;
} SigningCallbackContext_t;

/*-----------------------------------------------------------*/

/**
 * @brief Reads a file into the given buffer.
 *
 * @param[in] path Path of the file.
 * @param[out] pBuffer Buffer to read file contents into.
 * @param[in] bufferLength Length of #pBuffer.
 * @param[out] pOutWrittenLength Length of contents written to #pBuffer.
 */
static bool readFile( const char * path,
                      char * pBuffer,
                      size_t bufferLength,
                      size_t * pOutWrittenLength );

/**
 * @brief Delete the specified crypto object from storage.
 *
 * @param[in] session The PKCS #11 session.
 * @param[in] pkcsLabelsPtr The list of labels to remove.
 * @param[in] pClass The list of corresponding classes.
 * @param[in] count The length of #pkcsLabelsPtr and #pClass.
 */
static CK_RV destroyProvidedObjects( CK_SESSION_HANDLE session,
                                     CK_BYTE_PTR * pkcsLabelsPtr,
                                     CK_OBJECT_CLASS * pClass,
                                     CK_ULONG count );


/**
 * @brief Import the specified ECDSA private key into storage.
 *
 * @param[in] session The PKCS #11 session.
 * @param[in] label The label to store the key.
 * @param[in] mbedPkContext The private key to store.
 */
static CK_RV provisionPrivateECKey( CK_SESSION_HANDLE session,
                                    const char * label,
                                    mbedtls_pk_context * mbedPkContext );



/**
 * @brief Import the specified RSA private key into storage.
 *
 * @param[in] session The PKCS #11 session.
 * @param[in] label The label to store the key.
 * @param[in] mbedPkContext The private key to store.
 */
static CK_RV provisionPrivateRSAKey( CK_SESSION_HANDLE session,
                                     const char * label,
                                     mbedtls_pk_context * mbedPkContext );


/**
 * @brief Import the specified private key into storage.
 *
 * @param[in] session The PKCS #11 session.
 * @param[in] privateKey The private key to store, in PEM format.
 * @param[in] privateKeyLength The length of the key, including null terminator.
 * @param[in] label The label to store the key.
 */
static CK_RV provisionPrivateKey( CK_SESSION_HANDLE session,
                                  const char * privateKey,
                                  size_t privateKeyLength,
                                  const char * label );

/**
 * @brief Import the specified X.509 client certificate into storage.
 *
 * @param[in] session The PKCS #11 session.
 * @param[in] certificate The certificate to store, in PEM format.
 * @param[in] certificateLength The length of the certificate, including the null terminator.
 * @param[in] label The label to store the certificate.
 */
static CK_RV provisionCertificate( CK_SESSION_HANDLE session,
                                   const char * certificate,
                                   size_t certificateLength,
                                   const char * label );

/*-----------------------------------------------------------*/

static bool readFile( const char * path,
                      char * pBuffer,
                      size_t bufferLength,
                      size_t * pOutWrittenLength )
{
    FILE * file;
    size_t length = 0;
    bool status = true;

    /* Get the file descriptor for the CSR file. */
    file = fopen( path, "rb" );

    if( file == NULL )
    {
        LogError( ( "Error opening file at path: %s. Error: %s.",
                    path, strerror( errno ) ) );
        status = false;
    }
    else
    {
        int result;
        /* Seek to the end of the file, so that we can get the file size. */
        result = fseek( file, 0L, SEEK_END );

        if( result == -1 )
        {
            LogError( ( "Failed while moving to end of file. Path: %s. Error: %s.",
                        path, strerror( errno ) ) );
            status = false;
        }
        else
        {
            long lenResult = -1;
            /* Get the current position which is the file size. */
            lenResult = ftell( file );

            if( lenResult == -1 )
            {
                LogError( ( "Failed to get length of file. Path: %s. Error: %s.", path,
                            strerror( errno ) ) );
                status = false;
            }
            else
            {
                length = ( size_t ) lenResult;
            }
        }

        if( status == true )
        {
            if( length > bufferLength )
            {
                LogError( ( "Buffer too small for file. Buffer size: %ld. Required size: %ld.",
                            bufferLength, length ) );
                status = false;
            }
        }

        if( status == true )
        {
            /* Return to the beginning of the file. */
            result = fseek( file, 0L, SEEK_SET );

            if( result == -1 )
            {
                LogError( ( "Failed to move to beginning of file. Path: %s. Error: %s.",
                            path, strerror( errno ) ) );
                status = false;
            }
        }

        if( status == true )
        {
            size_t written = 0;
            /* Read the CSR into our buffer. */
            written = fread( pBuffer, 1, length, file );

            if( written != length )
            {
                LogError( ( "Failed reading file. Path: %s. Error: %s.", path,
                            strerror( errno ) ) );
                status = false;
            }
            else
            {
                *pOutWrittenLength = length;
            }
        }

        fclose( file );
    }

    return status;
}

/*-----------------------------------------------------------*/

static CK_RV destroyProvidedObjects( CK_SESSION_HANDLE session,
                                     CK_BYTE_PTR * pkcsLabelsPtr,
                                     CK_OBJECT_CLASS * pClass,
                                     CK_ULONG count )
{
    CK_RV result;
    CK_FUNCTION_LIST_PTR functionList;
    CK_OBJECT_HANDLE objectHandle;
    CK_BYTE * labelPtr;
    CK_ULONG index = 0;

    result = C_GetFunctionList( &functionList );

    if( result != CKR_OK )
    {
        LogError( ( "Could not get a PKCS #11 function pointer." ) );
    }
    else
    {
        for( index = 0; index < count; index++ )
        {
            labelPtr = pkcsLabelsPtr[ index ];

            result = xFindObjectWithLabelAndClass( session, ( char * ) labelPtr,
                                                   strlen( ( char * ) labelPtr ),
                                                   pClass[ index ], &objectHandle );

            while( ( result == CKR_OK ) && ( objectHandle != CK_INVALID_HANDLE ) )
            {
                result = functionList->C_DestroyObject( session, objectHandle );

                /* PKCS #11 allows a module to maintain multiple objects with the same
                 * label and type. The intent of this loop is to try to delete all of
                 * them. However, to avoid getting stuck, we won't try to find another
                 * object of the same label/type if the previous delete failed. */
                if( result == CKR_OK )
                {
                    result = xFindObjectWithLabelAndClass( session, ( char * ) labelPtr,
                                                           strlen( ( char * ) labelPtr ),
                                                           pClass[ index ], &objectHandle );
                }
                else
                {
                    break;
                }
            }
        }
    }

    return result;
}

/*-----------------------------------------------------------*/

static CK_RV provisionPrivateECKey( CK_SESSION_HANDLE session,
                                    const char * label,
                                    mbedtls_pk_context * mbedPkContext )
{
    CK_RV result = CKR_OK;
    CK_FUNCTION_LIST_PTR functionList = NULL;
    CK_BYTE * DPtr = NULL;        /* Private value D. */
    CK_BYTE * ecParamsPtr = NULL; /* DER-encoding of an ANSI X9.62 Parameters value */
    int mbedResult = 0;
    CK_BBOOL trueObject = CK_TRUE;
    CK_KEY_TYPE privateKeyType = CKK_EC;
    CK_OBJECT_CLASS privateKeyClass = CKO_PRIVATE_KEY;
    CK_OBJECT_HANDLE objectHandle = CK_INVALID_HANDLE;
    mbedtls_ecp_keypair * keyPair = ( mbedtls_ecp_keypair * ) mbedPkContext->pk_ctx;

    result = C_GetFunctionList( &functionList );

    if( result != CKR_OK )
    {
        LogError( ( "Could not get a PKCS #11 function pointer." ) );
    }
    else
    {
        DPtr = ( CK_BYTE * ) malloc( EC_D_LENGTH );

        if( DPtr == NULL )
        {
            result = CKR_HOST_MEMORY;
        }
    }

    if( result == CKR_OK )
    {
        mbedResult = mbedtls_mpi_write_binary( &( keyPair->d ), DPtr, EC_D_LENGTH );

        if( mbedResult != 0 )
        {
            LogError( ( "Failed to parse EC private key components." ) );
            result = CKR_ATTRIBUTE_VALUE_INVALID;
        }
    }

    if( result == CKR_OK )
    {
        if( keyPair->grp.id == MBEDTLS_ECP_DP_SECP256R1 )
        {
            ecParamsPtr = ( CK_BYTE * ) ( "\x06\x08" MBEDTLS_OID_EC_GRP_SECP256R1 );
        }
        else
        {
            result = CKR_CURVE_NOT_SUPPORTED;
        }
    }

    if( result == CKR_OK )
    {
        CK_ATTRIBUTE privateKeyTemplate[] =
        {
            { CKA_CLASS,     NULL /* &privateKeyClass*/, sizeof( CK_OBJECT_CLASS )    },
            { CKA_KEY_TYPE,  NULL /* &privateKeyType*/,  sizeof( CK_KEY_TYPE )        },
            { CKA_LABEL,     ( void * ) label,           ( CK_ULONG ) strlen( label ) },
            { CKA_TOKEN,     NULL /* &trueObject*/,      sizeof( CK_BBOOL )           },
            { CKA_SIGN,      NULL /* &trueObject*/,      sizeof( CK_BBOOL )           },
            { CKA_EC_PARAMS, NULL /* ecParamsPtr*/,      EC_PARAMS_LENGTH             },
            { CKA_VALUE,     NULL /* DPtr*/,             EC_D_LENGTH                  }
        };

        /* Aggregate initializers must not use the address of an automatic variable. */
        privateKeyTemplate[ 0 ].pValue = &privateKeyClass;
        privateKeyTemplate[ 1 ].pValue = &privateKeyType;
        privateKeyTemplate[ 3 ].pValue = &trueObject;
        privateKeyTemplate[ 4 ].pValue = &trueObject;
        privateKeyTemplate[ 5 ].pValue = ecParamsPtr;
        privateKeyTemplate[ 6 ].pValue = DPtr;

        result = functionList->C_CreateObject( session,
                                               ( CK_ATTRIBUTE_PTR ) &privateKeyTemplate,
                                               sizeof( privateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                               &objectHandle );
    }

    if( DPtr != NULL )
    {
        free( DPtr );
    }

    return result;
}

/*-----------------------------------------------------------*/

static CK_RV provisionPrivateRSAKey( CK_SESSION_HANDLE session,
                                     const char * label,
                                     mbedtls_pk_context * mbedPkContext )
{
    CK_RV result = CKR_OK;
    CK_FUNCTION_LIST_PTR functionList = NULL;
    int mbedResult = 0;
    CK_KEY_TYPE privateKeyType = CKK_RSA;
    mbedtls_rsa_context * rsaContext = ( mbedtls_rsa_context * ) mbedPkContext->pk_ctx;
    CK_OBJECT_CLASS privateKeyClass = CKO_PRIVATE_KEY;
    RsaParams_t * rsaParams = NULL;
    CK_BBOOL trueObject = CK_TRUE;
    CK_OBJECT_HANDLE objectHandle = CK_INVALID_HANDLE;

    result = C_GetFunctionList( &functionList );

    if( result != CKR_OK )
    {
        LogError( ( "Could not get a PKCS #11 function pointer." ) );
    }
    else
    {
        rsaParams = ( RsaParams_t * ) malloc( sizeof( RsaParams_t ) );

        if( rsaParams == NULL )
        {
            result = CKR_HOST_MEMORY;
        }
    }

    if( result == CKR_OK )
    {
        memset( rsaParams, 0, sizeof( RsaParams_t ) );

        mbedResult = mbedtls_rsa_export_raw( rsaContext,
                                             rsaParams->modulus, MODULUS_LENGTH + 1,
                                             rsaParams->prime1, PRIME_1_LENGTH + 1,
                                             rsaParams->prime2, PRIME_2_LENGTH + 1,
                                             rsaParams->d, D_LENGTH + 1,
                                             rsaParams->e, E_LENGTH + 1 );

        if( mbedResult != 0 )
        {
            LogError( ( "Failed to parse RSA private key components." ) );
            result = CKR_ATTRIBUTE_VALUE_INVALID;
        }

        /* Export Exponent 1, Exponent 2, Coefficient. */
        mbedResult |= mbedtls_mpi_write_binary( ( mbedtls_mpi const * ) &rsaContext->DP, rsaParams->exponent1, EXPONENT_1_LENGTH + 1 );
        mbedResult |= mbedtls_mpi_write_binary( ( mbedtls_mpi const * ) &rsaContext->DQ, rsaParams->exponent2, EXPONENT_2_LENGTH + 1 );
        mbedResult |= mbedtls_mpi_write_binary( ( mbedtls_mpi const * ) &rsaContext->QP, rsaParams->coefficient, COEFFICIENT_LENGTH + 1 );

        if( mbedResult != 0 )
        {
            LogError( ( "Failed to parse RSA private key Chinese Remainder Theorem variables." ) );
            result = CKR_ATTRIBUTE_VALUE_INVALID;
        }
    }

    if( result == CKR_OK )
    {
        /* When importing the fields, the pointer is incremented by 1
         * to remove the leading 0 padding (if it existed) and the original field
         * length is used */

        CK_ATTRIBUTE privateKeyTemplate[] =
        {
            { CKA_CLASS,            NULL /* &privateKeyClass */, sizeof( CK_OBJECT_CLASS )    },
            { CKA_KEY_TYPE,         NULL /* &privateKeyType */,  sizeof( CK_KEY_TYPE )        },
            { CKA_LABEL,            ( void * ) label,            ( CK_ULONG ) strlen( label ) },
            { CKA_TOKEN,            NULL /* &trueObject */,      sizeof( CK_BBOOL )           },
            { CKA_SIGN,             NULL /* &trueObject */,      sizeof( CK_BBOOL )           },
            { CKA_MODULUS,          rsaParams->modulus + 1,      MODULUS_LENGTH               },
            { CKA_PRIVATE_EXPONENT, rsaParams->d + 1,            D_LENGTH                     },
            { CKA_PUBLIC_EXPONENT,  rsaParams->e + 1,            E_LENGTH                     },
            { CKA_PRIME_1,          rsaParams->prime1 + 1,       PRIME_1_LENGTH               },
            { CKA_PRIME_2,          rsaParams->prime2 + 1,       PRIME_2_LENGTH               },
            { CKA_EXPONENT_1,       rsaParams->exponent1 + 1,    EXPONENT_1_LENGTH            },
            { CKA_EXPONENT_2,       rsaParams->exponent2 + 1,    EXPONENT_2_LENGTH            },
            { CKA_COEFFICIENT,      rsaParams->coefficient + 1,  COEFFICIENT_LENGTH           }
        };

        /* Aggregate initializers must not use the address of an automatic variable. */
        privateKeyTemplate[ 0 ].pValue = &privateKeyClass;
        privateKeyTemplate[ 1 ].pValue = &privateKeyType;
        privateKeyTemplate[ 3 ].pValue = &trueObject;
        privateKeyTemplate[ 4 ].pValue = &trueObject;

        result = functionList->C_CreateObject( session,
                                               ( CK_ATTRIBUTE_PTR ) &privateKeyTemplate,
                                               sizeof( privateKeyTemplate ) / sizeof( CK_ATTRIBUTE ),
                                               &objectHandle );
    }

    if( NULL != rsaParams )
    {
        free( rsaParams );
    }

    return result;
}

/*-----------------------------------------------------------*/

static CK_RV provisionPrivateKey( CK_SESSION_HANDLE session,
                                  const char * privateKey,
                                  size_t privateKeyLength,
                                  const char * label )
{
    CK_RV result = CKR_OK;
    mbedtls_pk_type_t mbedKeyType = MBEDTLS_PK_NONE;
    int mbedResult = 0;
    mbedtls_pk_context mbedPkContext = { 0 };
    mbedtls_ctr_drbg_context ctr_drbg = { 0 };
    mbedtls_entropy_context entropy = { 0 };

    mbedtls_pk_init( &mbedPkContext );
    mbedtls_entropy_init( &entropy );
    mbedtls_ctr_drbg_init( &ctr_drbg );
    mbedtls_ctr_drbg_seed( &ctr_drbg, mbedtls_entropy_func, &entropy, NULL, 0 );
    mbedResult = mbedtls_pk_parse_key( &mbedPkContext, ( const uint8_t * ) privateKey,
                                       privateKeyLength, NULL, 0, mbedtls_ctr_drbg_random, &ctr_drbg );

    if( mbedResult != 0 )
    {
        LogError( ( "Unable to parse private key." ) );
        result = CKR_ARGUMENTS_BAD;
    }

    /* Determine whether the key to be imported is RSA or EC. */
    if( result == CKR_OK )
    {
        mbedKeyType = mbedtls_pk_get_type( &mbedPkContext );

        if( mbedKeyType == MBEDTLS_PK_RSA )
        {
            result = provisionPrivateRSAKey( session, label, &mbedPkContext );
        }
        else if( ( mbedKeyType == MBEDTLS_PK_ECDSA ) ||
                 ( mbedKeyType == MBEDTLS_PK_ECKEY ) ||
                 ( mbedKeyType == MBEDTLS_PK_ECKEY_DH ) )
        {
            result = provisionPrivateECKey( session, label, &mbedPkContext );
        }
        else
        {
            LogError( ( "Invalid private key type provided. Only RSA-2048 and "
                        "EC P-256 keys are supported." ) );
            result = CKR_ARGUMENTS_BAD;
        }
    }

    mbedtls_pk_free( &mbedPkContext );

    return result;
}

/*-----------------------------------------------------------*/

static CK_RV provisionCertificate( CK_SESSION_HANDLE session,
                                   const char * certificate,
                                   size_t certificateLength,
                                   const char * label )
{
    PKCS11_CertificateTemplate_t certificateTemplate;
    CK_OBJECT_CLASS certificateClass = CKO_CERTIFICATE;
    CK_CERTIFICATE_TYPE certificateType = CKC_X_509;
    CK_FUNCTION_LIST_PTR functionList = NULL;
    CK_RV result = CKR_OK;
    uint8_t * derObject = NULL;
    int32_t conversion = 0;
    size_t derLen = 0;
    CK_BBOOL tokenStorage = CK_TRUE;
    CK_BYTE subject[] = "TestSubject";
    CK_OBJECT_HANDLE objectHandle = CK_INVALID_HANDLE;

    /* Initialize the client certificate template. */
    certificateTemplate.xObjectClass.type = CKA_CLASS;
    certificateTemplate.xObjectClass.pValue = &certificateClass;
    certificateTemplate.xObjectClass.ulValueLen = sizeof( certificateClass );
    certificateTemplate.xSubject.type = CKA_SUBJECT;
    certificateTemplate.xSubject.pValue = subject;
    certificateTemplate.xSubject.ulValueLen = strlen( ( const char * ) subject );
    certificateTemplate.xValue.type = CKA_VALUE;
    certificateTemplate.xValue.pValue = ( CK_VOID_PTR ) certificate;
    certificateTemplate.xValue.ulValueLen = ( CK_ULONG ) certificateLength;
    certificateTemplate.xLabel.type = CKA_LABEL;
    certificateTemplate.xLabel.pValue = ( CK_VOID_PTR ) label;
    certificateTemplate.xLabel.ulValueLen = strlen( label );
    certificateTemplate.xCertificateType.type = CKA_CERTIFICATE_TYPE;
    certificateTemplate.xCertificateType.pValue = &certificateType;
    certificateTemplate.xCertificateType.ulValueLen = sizeof( CK_CERTIFICATE_TYPE );
    certificateTemplate.xTokenObject.type = CKA_TOKEN;
    certificateTemplate.xTokenObject.pValue = &tokenStorage;
    certificateTemplate.xTokenObject.ulValueLen = sizeof( tokenStorage );

    if( certificate == NULL )
    {
        LogError( ( "Certificate cannot be null." ) );
        result = CKR_ATTRIBUTE_VALUE_INVALID;
    }

    if( result == CKR_OK )
    {
        result = C_GetFunctionList( &functionList );

        if( result != CKR_OK )
        {
            LogError( ( "Could not get a PKCS #11 function pointer." ) );
        }
    }

    if( result == CKR_OK )
    {
        /* Convert the certificate to DER format from PEM. The DER key should
         * be about 3/4 the size of the PEM key, so mallocing the PEM key size
         * is sufficient. */
        derObject = ( uint8_t * ) malloc( certificateTemplate.xValue.ulValueLen );
        derLen = certificateTemplate.xValue.ulValueLen;

        if( derObject != NULL )
        {
            conversion = convert_pem_to_der( ( unsigned char * ) certificateTemplate.xValue.pValue,
                                             certificateTemplate.xValue.ulValueLen,
                                             derObject, &derLen );

            if( 0 != conversion )
            {
                LogError( ( "Failed to convert provided certificate." ) );
                result = CKR_ARGUMENTS_BAD;
            }
        }
        else
        {
            LogError( ( "Failed to allocate buffer for converting certificate to DER." ) );
            result = CKR_HOST_MEMORY;
        }
    }

    if( result == CKR_OK )
    {
        /* Set the template pointers to refer to the DER converted objects. */
        certificateTemplate.xValue.pValue = derObject;
        certificateTemplate.xValue.ulValueLen = derLen;

        /* Best effort clean-up of the existing object, if it exists. */
        destroyProvidedObjects( session, ( CK_BYTE_PTR * ) &label, &certificateClass, 1 );

        /* Create an object using the encoded client certificate. */
        LogInfo( ( "Writing certificate into label \"%s\".", label ) );

        result = functionList->C_CreateObject( session,
                                               ( CK_ATTRIBUTE_PTR ) &certificateTemplate,
                                               sizeof( certificateTemplate ) / sizeof( CK_ATTRIBUTE ),
                                               &objectHandle );
    }

    if( derObject != NULL )
    {
        free( derObject );
    }

    return result;
}

/*-----------------------------------------------------------*/

bool loadClaimCredentials( CK_SESSION_HANDLE p11Session,
                           const char * pClaimCertPath,
                           const char * pClaimCertLabel,
                           const char * pClaimPrivKeyPath,
                           const char * pClaimPrivKeyLabel )
{
    bool status;
    char claimCert[ CLAIM_CERT_BUFFER_LENGTH ] = { 0 };
    size_t claimCertLength = 0;
    char claimPrivateKey[ CLAIM_PRIVATE_KEY_BUFFER_LENGTH ] = { 0 };
    size_t claimPrivateKeyLength = 0;
    CK_RV ret;

    assert( pClaimCertPath != NULL );
    assert( pClaimCertLabel != NULL );
    assert( pClaimPrivKeyPath != NULL );
    assert( pClaimPrivKeyLabel != NULL );

    status = readFile( pClaimCertPath, claimCert, CLAIM_CERT_BUFFER_LENGTH,
                       &claimCertLength );

    if( status == true )
    {
        status = readFile( pClaimPrivKeyPath, claimPrivateKey,
                           CLAIM_PRIVATE_KEY_BUFFER_LENGTH, &claimPrivateKeyLength );
    }

    if( status == true )
    {
        ret = provisionPrivateKey( p11Session, claimPrivateKey,
                                   claimPrivateKeyLength + 1, /* MbedTLS includes null character in length for PEM objects. */
                                   pClaimPrivKeyLabel );
        status = ( ret == CKR_OK );
    }

    if( status == true )
    {
        ret = provisionCertificate( p11Session, claimCert,
                                    claimCertLength + 1, /* MbedTLS includes null character in length for PEM objects. */
                                    pClaimCertLabel );
        status = ( ret == CKR_OK );
    }

    return status;
}

/*-----------------------------------------------------------*/

bool loadCertificate( CK_SESSION_HANDLE p11Session,
                      const char * pCertificate,
                      const char * pLabel,
                      size_t certificateLength )
{
    CK_RV ret;

    assert( pCertificate != NULL );
    assert( pLabel != NULL );

    ret = provisionCertificate( p11Session,
                                pCertificate,
                                certificateLength + 1, /* MbedTLS includes null character in length for PEM objects. */
                                pLabel );

    return( ret == CKR_OK );
}

/*-----------------------------------------------------------*/

bool loadPrivateKey( CK_SESSION_HANDLE p11Session,
                     const char * pPrivateKey,
                     const char * pLabel,
                     size_t privateKeyLength )
{
    CK_RV ret;

    assert( pPrivateKey != NULL );
    assert( pLabel != NULL );

    ret = provisionPrivateKey( p11Session,
                               pPrivateKey,
                               privateKeyLength + 1, /* MbedTLS includes null character in length for PEM objects. */
                               pLabel );

    return( ret == CKR_OK );
}

/*-----------------------------------------------------------*/

bool pkcs11CloseSession( CK_SESSION_HANDLE p11Session )
{
    CK_RV result = CKR_OK;
    CK_FUNCTION_LIST_PTR functionList = NULL;

    result = C_GetFunctionList( &functionList );

    if( result == CKR_OK )
    {
        result = functionList->C_CloseSession( p11Session );
    }

    if( result == CKR_OK )
    {
        result = functionList->C_Finalize( NULL );
    }

    return( result == CKR_OK );
}

/*-----------------------------------------------------------*/

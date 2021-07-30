/*
 * FreeRTOS V202107.00
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
 * https://www.FreeRTOS.org
 * https://github.com/FreeRTOS
 *
 */

/* Standard includes. */
#include <string.h>
#include <assert.h>

/* TLS transport header. */
#include "mbedtls_pkcs11_posix.h"

/* MbedTLS includes. */
#include "mbedtls/error.h"

/* PKCS #11 includes. */
#include "core_pki_utils.h"

/*-----------------------------------------------------------*/

/**
 * @brief Each compilation unit that consumes the NetworkContext must define it.
 * It should contain a single pointer as seen below whenever the header file
 * of this transport implementation is included to your project.
 *
 * @note When using multiple transports in the same compilation unit,
 *       define this pointer as void *.
 */
struct NetworkContext
{
    MbedtlsPkcs11Context_t * pParams;
};

/*-----------------------------------------------------------*/

/**
 * @brief Represents string to be logged when mbedTLS returned error
 * does not contain a high-level code.
 */
static const char * pNoHighLevelMbedTlsCodeStr = "<No-High-Level-Code>";

/**
 * @brief Represents string to be logged when mbedTLS returned error
 * does not contain a low-level code.
 */
static const char * pNoLowLevelMbedTlsCodeStr = "<No-Low-Level-Code>";

/**
 * @brief Utility for converting the high-level code in an mbedTLS error to string,
 * if the code-contains a high-level code; otherwise, using a default string.
 */
#define mbedtlsHighLevelCodeOrDefault( mbedTlsCode )       \
    ( mbedtls_high_level_strerr( mbedTlsCode ) != NULL ) ? \
    mbedtls_high_level_strerr( mbedTlsCode ) : pNoHighLevelMbedTlsCodeStr

/**
 * @brief Utility for converting the level-level code in an mbedTLS error to string,
 * if the code-contains a level-level code; otherwise, using a default string.
 */
#define mbedtlsLowLevelCodeOrDefault( mbedTlsCode )       \
    ( mbedtls_low_level_strerr( mbedTlsCode ) != NULL ) ? \
    mbedtls_low_level_strerr( mbedTlsCode ) : pNoLowLevelMbedTlsCodeStr

/*-----------------------------------------------------------*/

/**
 * @brief Initialize the MbedTLS structures in a network connection.
 *
 * @param[in] pContext The SSL context to initialize.
 */
static void contextInit( MbedtlsPkcs11Context_t * pContext );

/**
 * @brief Free the MbedTLS structures in a network connection.
 *
 * @param[in] pContext The SSL context to free.
 */
static void contextFree( MbedtlsPkcs11Context_t * pContext );

/**
 * @brief Set up TLS on a TCP connection.
 *
 * @param[in] pMbedtlsPkcs11Context Network context.
 * @param[in] pHostName Remote host name, used for server name indication.
 * @param[in] pMbedtlsPkcs11Credentials TLS setup parameters.
 *
 * @return #MBEDTLS_PKCS11_SUCCESS, #MBEDTLS_PKCS11_INSUFFICIENT_MEMORY, #MBEDTLS_PKCS11_INVALID_CREDENTIALS,
 * #MBEDTLS_PKCS11_HANDSHAKE_FAILED, or #MBEDTLS_PKCS11_INTERNAL_ERROR.
 */
static MbedtlsPkcs11Status_t configureMbedtls( MbedtlsPkcs11Context_t * pMbedtlsPkcs11Context,
                                               const char * pHostName,
                                               const MbedtlsPkcs11Credentials_t * pMbedtlsPkcs11Credentials );

/**
 * @brief Callback that wraps PKCS #11 for pseudo-random number generation.
 *
 * @param[in] pCtx Caller context.
 * @param[in] pRandom Byte array to fill with random data.
 * @param[in] randomLength Length of byte array.
 *
 * @return Zero on success.
 */
static int32_t generateRandomBytes( void * pCtx,
                                    unsigned char * pRandom,
                                    size_t randomLength );

/**
 * @brief Helper for reading the specified certificate object, if present,
 * out of storage, into RAM, and then into an mbedTLS certificate context
 * object.
 *
 * @param[in] pContext Caller TLS context.
 * @param[in] pLabelName PKCS #11 certificate object label.
 * @param[in] class PKCS #11 certificate object class.
 * @param[out] pCertificateContext Certificate context.
 *
 * @return Zero on success.
 */
static int32_t readCertificateIntoContext( MbedtlsPkcs11Context_t * pContext,
                                           char * pLabelName,
                                           CK_OBJECT_CLASS class,
                                           mbedtls_x509_crt * pCertificateContext );

/**
 * @brief Helper for setting up potentially hardware-based cryptographic context.
 *
 * @param pCtx Caller context.
 * @param pPrivateKeyLabel PKCS #11 label for the private key.
 *
 * @return Zero on success.
 */
static CK_RV initializeClientKeys( MbedtlsPkcs11Context_t * pCtx,
                                   char * pPrivateKeyLabel );

/**
 * @brief Sign a cryptographic hash with the private key.
 *
 * @param[in] pContext Crypto context.
 * @param[in] mdAlg Unused.
 * @param[in] pHash Length in bytes of hash to be signed.
 * @param[in] hashLen Byte array of hash to be signed.
 * @param[out] pSig RSA signature bytes.
 * @param[in] pSigLen Length in bytes of signature buffer.
 * @param[in] pRng Unused.
 * @param[in] pRngContext Unused.
 *
 * @return Zero on success.
 */
static int32_t privateKeySigningCallback( void * pContext,
                                          mbedtls_md_type_t mdAlg,
                                          const unsigned char * pHash,
                                          size_t hashLen,
                                          unsigned char * pSig,
                                          size_t * pSigLen,
                                          int32_t ( * pRng )( void *,
                                                              unsigned char *,
                                                              size_t ),
                                          void * pRngContext );


/*-----------------------------------------------------------*/

static void contextInit( MbedtlsPkcs11Context_t * pContext )
{
    assert( pContext != NULL );

    mbedtls_net_init( &( pContext->socketContext ) );
    mbedtls_ssl_init( &( pContext->context ) );
    mbedtls_ssl_config_init( &( pContext->config ) );
    mbedtls_x509_crt_init( &( pContext->rootCa ) );
    mbedtls_x509_crt_init( &( pContext->clientCert ) );

    C_GetFunctionList( &( pContext->pP11FunctionList ) );
}
/*-----------------------------------------------------------*/

static void contextFree( MbedtlsPkcs11Context_t * pContext )
{
    if( pContext != NULL )
    {
        mbedtls_net_free( &( pContext->socketContext ) );
        mbedtls_ssl_free( &( pContext->context ) );
        mbedtls_ssl_config_free( &( pContext->config ) );
        mbedtls_x509_crt_free( &( pContext->rootCa ) );
        mbedtls_x509_crt_free( &( pContext->clientCert ) );

        pContext->pP11FunctionList->C_CloseSession( pContext->p11Session );
    }
}

/*-----------------------------------------------------------*/

static MbedtlsPkcs11Status_t configureMbedtls( MbedtlsPkcs11Context_t * pMbedtlsPkcs11Context,
                                               const char * pHostName,
                                               const MbedtlsPkcs11Credentials_t * pMbedtlsPkcs11Credentials )
{
    MbedtlsPkcs11Status_t returnStatus = MBEDTLS_PKCS11_SUCCESS;
    int32_t mbedtlsError = 0;
    CK_RV result = CKR_OK;

    assert( pMbedtlsPkcs11Context != NULL );
    assert( pHostName != NULL );
    assert( pMbedtlsPkcs11Credentials != NULL );
    assert( pMbedtlsPkcs11Credentials->pRootCaPath != NULL );

    /* Initialize the MbedTLS context structures. */
    contextInit( pMbedtlsPkcs11Context );
    pMbedtlsPkcs11Context->p11Session = pMbedtlsPkcs11Credentials->p11Session;

    mbedtlsError = mbedtls_ssl_config_defaults( &( pMbedtlsPkcs11Context->config ),
                                                MBEDTLS_SSL_IS_CLIENT,
                                                MBEDTLS_SSL_TRANSPORT_STREAM,
                                                MBEDTLS_SSL_PRESET_DEFAULT );

    if( mbedtlsError != 0 )
    {
        LogError( ( "Failed to set default SSL configuration: mbedTLSError= %s : %s.",
                    mbedtlsHighLevelCodeOrDefault( mbedtlsError ),
                    mbedtlsLowLevelCodeOrDefault( mbedtlsError ) ) );

        /* Per MbedTLS docs, mbedtls_ssl_config_defaults only fails on memory allocation. */
        returnStatus = MBEDTLS_PKCS11_INSUFFICIENT_MEMORY;
    }

    if( returnStatus == MBEDTLS_PKCS11_SUCCESS )
    {
        /* Set up the certificate security profile, starting from the default value. */
        pMbedtlsPkcs11Context->certProfile = mbedtls_x509_crt_profile_default;

        /* Set SSL authmode and the RNG context. */
        mbedtls_ssl_conf_authmode( &( pMbedtlsPkcs11Context->config ),
                                   MBEDTLS_SSL_VERIFY_REQUIRED );
        mbedtls_ssl_conf_rng( &( pMbedtlsPkcs11Context->config ),
                              generateRandomBytes,
                              pMbedtlsPkcs11Context );
        mbedtls_ssl_conf_cert_profile( &( pMbedtlsPkcs11Context->config ),
                                       &( pMbedtlsPkcs11Context->certProfile ) );

        /* Parse the server root CA certificate into the SSL context. */
        mbedtlsError = mbedtls_x509_crt_parse_file( &( pMbedtlsPkcs11Context->rootCa ),
                                                    pMbedtlsPkcs11Credentials->pRootCaPath );

        if( mbedtlsError != 0 )
        {
            LogError( ( "Failed to parse server root CA certificate: mbedTLSError= %s : %s.",
                        mbedtlsHighLevelCodeOrDefault( mbedtlsError ),
                        mbedtlsLowLevelCodeOrDefault( mbedtlsError ) ) );

            returnStatus = MBEDTLS_PKCS11_INVALID_CREDENTIALS;
        }
        else
        {
            mbedtls_ssl_conf_ca_chain( &( pMbedtlsPkcs11Context->config ),
                                       &( pMbedtlsPkcs11Context->rootCa ),
                                       NULL );
        }
    }

    if( returnStatus == MBEDTLS_PKCS11_SUCCESS )
    {
        /* Setup the client private key. */
        result = initializeClientKeys( pMbedtlsPkcs11Context,
                                       pMbedtlsPkcs11Credentials->pPrivateKeyLabel );

        if( result != CKR_OK )
        {
            LogError( ( "Failed to setup key handling by PKCS #11." ) );

            returnStatus = MBEDTLS_PKCS11_INVALID_CREDENTIALS;
        }
        else
        {
            /* Setup the client certificate. */
            mbedtlsError = readCertificateIntoContext( pMbedtlsPkcs11Context,
                                                       pMbedtlsPkcs11Credentials->pClientCertLabel,
                                                       CKO_CERTIFICATE,
                                                       &( pMbedtlsPkcs11Context->clientCert ) );

            if( mbedtlsError != 0 )
            {
                LogError( ( "Failed to get certificate from PKCS #11 module." ) );

                returnStatus = MBEDTLS_PKCS11_INVALID_CREDENTIALS;
            }
            else
            {
                ( void ) mbedtls_ssl_conf_own_cert( &( pMbedtlsPkcs11Context->config ),
                                                    &( pMbedtlsPkcs11Context->clientCert ),
                                                    &( pMbedtlsPkcs11Context->privKey ) );
            }
        }
    }

    if( ( returnStatus == MBEDTLS_PKCS11_SUCCESS ) && ( pMbedtlsPkcs11Credentials->pAlpnProtos != NULL ) )
    {
        /* Include an application protocol list in the TLS ClientHello
         * message. */
        mbedtlsError = mbedtls_ssl_conf_alpn_protocols( &( pMbedtlsPkcs11Context->config ),
                                                        pMbedtlsPkcs11Credentials->pAlpnProtos );

        if( mbedtlsError != 0 )
        {
            LogError( ( "Failed to configure ALPN protocol in MbedTLS: mbedTLSError= %s : %s.",
                        mbedtlsHighLevelCodeOrDefault( mbedtlsError ),
                        mbedtlsLowLevelCodeOrDefault( mbedtlsError ) ) );

            returnStatus = MBEDTLS_PKCS11_INTERNAL_ERROR;
        }
    }

    if( returnStatus == MBEDTLS_PKCS11_SUCCESS )
    {
        /* Initialize the MbedTLS secured connection context. */
        mbedtlsError = mbedtls_ssl_setup( &( pMbedtlsPkcs11Context->context ),
                                          &( pMbedtlsPkcs11Context->config ) );

        if( mbedtlsError != 0 )
        {
            LogError( ( "Failed to set up MbedTLS SSL context: mbedTLSError= %s : %s.",
                        mbedtlsHighLevelCodeOrDefault( mbedtlsError ),
                        mbedtlsLowLevelCodeOrDefault( mbedtlsError ) ) );

            returnStatus = MBEDTLS_PKCS11_INTERNAL_ERROR;
        }
        else
        {
            /* Set the underlying IO for the TLS connection. */
            mbedtls_ssl_set_bio( &( pMbedtlsPkcs11Context->context ),
                                 ( void * ) &( pMbedtlsPkcs11Context->socketContext ),
                                 mbedtls_net_send,
                                 mbedtls_net_recv,
                                 mbedtls_net_recv_timeout );
        }
    }

    if( returnStatus == MBEDTLS_PKCS11_SUCCESS )
    {
        /* Enable SNI if requested. */
        if( pMbedtlsPkcs11Credentials->disableSni == false )
        {
            mbedtlsError = mbedtls_ssl_set_hostname( &( pMbedtlsPkcs11Context->context ),
                                                     pHostName );

            if( mbedtlsError != 0 )
            {
                LogError( ( "Failed to set server name: mbedTLSError= %s : %s.",
                            mbedtlsHighLevelCodeOrDefault( mbedtlsError ),
                            mbedtlsLowLevelCodeOrDefault( mbedtlsError ) ) );

                returnStatus = MBEDTLS_PKCS11_INTERNAL_ERROR;
            }
        }
    }

    /* Set Maximum Fragment Length if enabled. */
    #ifdef MBEDTLS_SSL_MAX_FRAGMENT_LENGTH
        if( returnStatus == MBEDTLS_PKCS11_SUCCESS )
        {
            /* Enable the max fragment extension. 4096 bytes is currently the largest fragment size permitted.
             * See RFC 8449 https://tools.ietf.org/html/rfc8449 for more information.
             *
             * Smaller values can be found in "mbedtls/include/ssl.h".
             */
            mbedtlsError = mbedtls_ssl_conf_max_frag_len( &( pMbedtlsPkcs11Context->config ), MBEDTLS_SSL_MAX_FRAG_LEN_4096 );

            if( mbedtlsError != 0 )
            {
                LogError( ( "Failed to maximum fragment length extension: mbedTLSError= %s : %s.",
                            mbedtlsHighLevelCodeOrDefault( mbedtlsError ),
                            mbedtlsLowLevelCodeOrDefault( mbedtlsError ) ) );
                returnStatus = MBEDTLS_PKCS11_INTERNAL_ERROR;
            }
        }
    #endif /* ifdef MBEDTLS_SSL_MAX_FRAGMENT_LENGTH */

    if( returnStatus != MBEDTLS_PKCS11_SUCCESS )
    {
        contextFree( pMbedtlsPkcs11Context );
    }
    else
    {
        LogInfo( ( "(Network connection %p) TLS handshake successful.",

                   pNetworkContext ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int32_t generateRandomBytes( void * pCtx,
                                    unsigned char * pRandom,
                                    size_t randomLength )
{
    /* Must cast from void pointer to conform to MbedTLS API. */
    MbedtlsPkcs11Context_t * pContext = ( MbedtlsPkcs11Context_t * ) pCtx;
    CK_RV xResult;


    xResult = pContext->pP11FunctionList->C_GenerateRandom( pContext->p11Session, pRandom, randomLength );

    if( xResult != CKR_OK )
    {
        LogError( ( "Failed to generate random bytes from the PKCS #11 module." ) );
    }

    return ( int32_t ) xResult;
}

/*----------------------------------------------------------*/

static int32_t readCertificateIntoContext( MbedtlsPkcs11Context_t * pContext,
                                           char * pLabelName,
                                           CK_OBJECT_CLASS class,
                                           mbedtls_x509_crt * pCertificateContext )
{
    CK_RV pkcs11Ret = CKR_OK;
    CK_ATTRIBUTE template = { 0 };
    CK_OBJECT_HANDLE certificateHandle = 0;
    int32_t mbedtlsRet = 0;

    /* Get the handle of the certificate. */
    pkcs11Ret = xFindObjectWithLabelAndClass( pContext->p11Session,
                                              pLabelName,
                                              strlen( pLabelName ),
                                              class,
                                              &certificateHandle );

    if( ( CKR_OK == pkcs11Ret ) && ( certificateHandle == CK_INVALID_HANDLE ) )
    {
        pkcs11Ret = CKR_OBJECT_HANDLE_INVALID;
    }

    /* Query the certificate size. */
    if( CKR_OK == pkcs11Ret )
    {
        template.type = CKA_VALUE;
        template.ulValueLen = 0;
        template.pValue = NULL;
        pkcs11Ret = pContext->pP11FunctionList->C_GetAttributeValue( pContext->p11Session,
                                                                     certificateHandle,
                                                                     &template,
                                                                     1 );
    }

    /* Create a buffer for the certificate. */
    if( CKR_OK == pkcs11Ret )
    {
        template.pValue = malloc( template.ulValueLen );

        if( NULL == template.pValue )
        {
            pkcs11Ret = CKR_HOST_MEMORY;
        }
    }

    /* Export the certificate. */
    if( CKR_OK == pkcs11Ret )
    {
        pkcs11Ret = pContext->pP11FunctionList->C_GetAttributeValue( pContext->p11Session,
                                                                     certificateHandle,
                                                                     &template,
                                                                     1 );
    }

    /* Decode the certificate. */
    if( CKR_OK == pkcs11Ret )
    {
        mbedtlsRet = mbedtls_x509_crt_parse( pCertificateContext,
                                             ( const unsigned char * ) template.pValue,
                                             template.ulValueLen );
    }

    /* Free memory. */
    free( template.pValue );

    return mbedtlsRet;
}

/*-----------------------------------------------------------*/

/**
 * @brief Helper for setting up potentially hardware-based cryptographic context
 * for the client TLS certificate and private key.
 *
 * @param pCtx Caller context.
 *
 * @return Zero on success.
 */
static CK_RV initializeClientKeys( MbedtlsPkcs11Context_t * pCtx,
                                   char * pPrivateKeyLabel )
{
    CK_RV ret = CKR_OK;
    CK_ATTRIBUTE template[ 2 ] = { 0 };
    mbedtls_pk_type_t keyAlgo = ( mbedtls_pk_type_t ) ~0;

    /* Get the handle of the device private key. */
    ret = xFindObjectWithLabelAndClass( pCtx->p11Session,
                                        pPrivateKeyLabel,
                                        strlen( pPrivateKeyLabel ),
                                        CKO_PRIVATE_KEY,
                                        &pCtx->p11PrivateKey );

    if( ( CKR_OK == ret ) && ( pCtx->p11PrivateKey == CK_INVALID_HANDLE ) )
    {
        ret = CK_INVALID_HANDLE;
        LogError( ( "Could not find private key." ) );
    }

    /* Query the device private key type. */
    if( ret == CKR_OK )
    {
        template[ 0 ].type = CKA_KEY_TYPE;
        template[ 0 ].pValue = &pCtx->keyType;
        template[ 0 ].ulValueLen = sizeof( CK_KEY_TYPE );
        ret = pCtx->pP11FunctionList->C_GetAttributeValue( pCtx->p11Session,
                                                           pCtx->p11PrivateKey,
                                                           template,
                                                           1 );
    }

    /* Map the PKCS #11 key type to an mbedTLS algorithm. */
    if( ret == CKR_OK )
    {
        switch( pCtx->keyType )
        {
            case CKK_RSA:
                keyAlgo = MBEDTLS_PK_RSA;
                break;

            case CKK_EC:
                keyAlgo = MBEDTLS_PK_ECKEY;
                break;

            default:
                ret = CKR_ATTRIBUTE_VALUE_INVALID;
                break;
        }
    }

    /* Map the mbedTLS algorithm to its internal metadata. */
    if( ret == CKR_OK )
    {
        memcpy( &pCtx->privKeyInfo, mbedtls_pk_info_from_type( keyAlgo ), sizeof( mbedtls_pk_info_t ) );

        pCtx->privKeyInfo.sign_func = privateKeySigningCallback;
        pCtx->privKey.pk_info = &pCtx->privKeyInfo;
        pCtx->privKey.pk_ctx = pCtx;
    }

    return ret;
}

/*-----------------------------------------------------------*/

static int32_t privateKeySigningCallback( void * pContext,
                                          mbedtls_md_type_t mdAlg,
                                          const unsigned char * pHash,
                                          size_t hashLen,
                                          unsigned char * pSig,
                                          size_t * pSigLen,
                                          int32_t ( * pRng )( void *,
                                                              unsigned char *,
                                                              size_t ),
                                          void * pRngContext )
{
    CK_RV ret = CKR_OK;
    int32_t result = 0;
    MbedtlsPkcs11Context_t * pMbedtlsPkcs11Context = ( MbedtlsPkcs11Context_t * ) pContext;
    CK_MECHANISM mech = { 0 };
    CK_BYTE toBeSigned[ 256 ];
    CK_ULONG toBeSignedLen = sizeof( toBeSigned );

    /* Unreferenced parameters. */
    ( void ) ( pRng );
    ( void ) ( pRngContext );
    ( void ) ( mdAlg );

    /* Sanity check buffer length. */
    if( hashLen > sizeof( toBeSigned ) )
    {
        ret = CKR_ARGUMENTS_BAD;
    }

    /* Format the hash data to be signed. */
    if( CKK_RSA == pMbedtlsPkcs11Context->keyType )
    {
        mech.mechanism = CKM_RSA_PKCS;

        /* mbedTLS expects hashed data without padding, but PKCS #11 C_Sign function performs a hash
         * & sign if hash algorithm is specified.  This helper function applies padding
         * indicating data was hashed with SHA-256 while still allowing pre-hashed data to
         * be provided. */
        ret = vAppendSHA256AlgorithmIdentifierSequence( ( const uint8_t * ) pHash, toBeSigned );
        toBeSignedLen = pkcs11RSA_SIGNATURE_INPUT_LENGTH;
    }
    else if( CKK_EC == pMbedtlsPkcs11Context->keyType )
    {
        mech.mechanism = CKM_ECDSA;
        memcpy( toBeSigned, pHash, hashLen );
        toBeSignedLen = hashLen;
    }
    else
    {
        ret = CKR_ARGUMENTS_BAD;
    }

    if( CKR_OK == ret )
    {
        /* Use the PKCS#11 module to sign. */
        ret = pMbedtlsPkcs11Context->pP11FunctionList->C_SignInit( pMbedtlsPkcs11Context->p11Session,
                                                                   &mech,
                                                                   pMbedtlsPkcs11Context->p11PrivateKey );
    }

    if( CKR_OK == ret )
    {
        *pSigLen = sizeof( toBeSigned );
        ret = pMbedtlsPkcs11Context->pP11FunctionList->C_Sign( ( CK_SESSION_HANDLE ) pMbedtlsPkcs11Context->p11Session,
                                                               toBeSigned,
                                                               toBeSignedLen,
                                                               pSig,
                                                               ( CK_ULONG_PTR ) pSigLen );
    }

    if( ( ret == CKR_OK ) && ( CKK_EC == pMbedtlsPkcs11Context->keyType ) )
    {
        /* PKCS #11 for P256 returns a 64-byte signature with 32 bytes for R and 32 bytes for S.
         * This must be converted to an ASN.1 encoded array. */
        if( *pSigLen != pkcs11ECDSA_P256_SIGNATURE_LENGTH )
        {
            ret = CKR_FUNCTION_FAILED;
        }

        if( ret == CKR_OK )
        {
            PKI_pkcs11SignatureTombedTLSSignature( pSig, pSigLen );
        }
    }

    if( ret != CKR_OK )
    {
        LogError( ( "Failed to sign message using PKCS #11 with error code %lu.", ( unsigned long ) ret ) );
    }

    return result;
}

/*-----------------------------------------------------------*/

MbedtlsPkcs11Status_t Mbedtls_Pkcs11_Connect( NetworkContext_t * pNetworkContext,
                                              const char * pHostName,
                                              uint16_t port,
                                              const MbedtlsPkcs11Credentials_t * pMbedtlsPkcs11Credentials )
{
    MbedtlsPkcs11Context_t * pMbedtlsPkcs11Context = NULL;
    MbedtlsPkcs11Status_t returnStatus = MBEDTLS_PKCS11_SUCCESS;
    int32_t mbedtlsError = 0;

    if( ( pNetworkContext == NULL ) ||
        ( pNetworkContext->pParams == NULL ) ||
        ( pHostName == NULL ) ||
        ( pMbedtlsPkcs11Credentials == NULL ) )
    {
        LogError( ( "Invalid input parameter(s): Arguments cannot be NULL. pNetworkContext=%p, "
                    "pHostName=%p, pMbedtlsPkcs11Credentials=%p.",
                    ( void * ) pNetworkContext,
                    ( const void * ) pHostName,
                    ( const void * ) pMbedtlsPkcs11Credentials ) );
        returnStatus = MBEDTLS_PKCS11_INVALID_PARAMETER;
    }
    else if( ( pMbedtlsPkcs11Credentials->pRootCaPath == NULL ) )
    {
        LogError( ( "pRootCaPath cannot be NULL." ) );
        returnStatus = MBEDTLS_PKCS11_INVALID_PARAMETER;
    }
    else if( ( pMbedtlsPkcs11Credentials->pClientCertLabel == NULL ) )
    {
        LogError( ( "pClientCertLabel cannot be NULL." ) );
        returnStatus = MBEDTLS_PKCS11_INVALID_PARAMETER;
    }
    else if( ( pMbedtlsPkcs11Credentials->pPrivateKeyLabel == NULL ) )
    {
        LogError( ( "pPrivateKeyLabel cannot be NULL." ) );
        returnStatus = MBEDTLS_PKCS11_INVALID_PARAMETER;
    }
    else
    {
        /* Empty else for MISRA 15.7 compliance. */
        pMbedtlsPkcs11Context = pNetworkContext->pParams;
    }

    /* Configure MbedTLS. */
    if( returnStatus == MBEDTLS_PKCS11_SUCCESS )
    {
        returnStatus = configureMbedtls( pMbedtlsPkcs11Context, pHostName, pMbedtlsPkcs11Credentials );
    }

    /* Establish a TCP connection with the server. */
    if( returnStatus == MBEDTLS_PKCS11_SUCCESS )
    {
        mbedtlsError = mbedtls_net_connect( &( pMbedtlsPkcs11Context->socketContext ),
                                            pHostName,
                                            "8883",
                                            MBEDTLS_NET_PROTO_TCP );

        if( mbedtlsError != 0 )
        {
            LogError( ( "Failed to connect to %s with error %d.",
                        pHostName,
                        mbedtlsError ) );
            returnStatus = MBEDTLS_PKCS11_CONNECT_FAILURE;
        }
    }

    if( returnStatus == MBEDTLS_PKCS11_SUCCESS )
    {
        uint32_t sslVerifyRet = -1U;

        /* Perform the TLS handshake. */
        do
        {
            mbedtlsError = mbedtls_ssl_handshake( &( pMbedtlsPkcs11Context->context ) );
        } while( ( mbedtlsError == MBEDTLS_ERR_SSL_WANT_READ ) ||
                 ( mbedtlsError == MBEDTLS_ERR_SSL_WANT_WRITE ) );

        if( mbedtlsError == 0 )
        {
            sslVerifyRet = mbedtls_ssl_get_verify_result( &( pMbedtlsPkcs11Context->context ) );
        }

        if( sslVerifyRet != 0 )
        {
            LogError( ( "Failed to perform TLS handshake: mbedTLSError= %s : %s.",
                        mbedtlsHighLevelCodeOrDefault( mbedtlsError ),
                        mbedtlsLowLevelCodeOrDefault( mbedtlsError ) ) );

            returnStatus = MBEDTLS_PKCS11_HANDSHAKE_FAILED;
        }
    }

    /* Clean up on failure. */
    if( returnStatus != MBEDTLS_PKCS11_SUCCESS )
    {
        contextFree( pMbedtlsPkcs11Context );
    }
    else
    {
        LogInfo( ( "(Network connection %p) Connection to %s established.",
                   pNetworkContext,
                   pHostName ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

void Mbedtls_Pkcs11_Disconnect( NetworkContext_t * pNetworkContext )
{
    MbedtlsPkcs11Context_t * pMbedtlsPkcs11Context = NULL;
    int tlsStatus = 0;

    if( ( pNetworkContext != NULL ) && ( pNetworkContext->pParams != NULL ) )
    {
        pMbedtlsPkcs11Context = pNetworkContext->pParams;
        /* Attempting to terminate TLS connection. */
        tlsStatus = mbedtls_ssl_close_notify( &( pMbedtlsPkcs11Context->context ) );

        /* Ignore the WANT_READ and WANT_WRITE return values. */
        if( ( tlsStatus != MBEDTLS_ERR_SSL_WANT_READ ) &&
            ( tlsStatus != MBEDTLS_ERR_SSL_WANT_WRITE ) )
        {
            if( tlsStatus == 0 )
            {
                LogInfo( ( "(Network connection %p) TLS close-notify sent.",
                           pNetworkContext ) );
            }
            else
            {
                LogError( ( "(Network connection %p) Failed to send TLS close-notify: mbedTLSError= %s : %s.",
                            ( void * ) pNetworkContext,
                            mbedtlsHighLevelCodeOrDefault( tlsStatus ),
                            mbedtlsLowLevelCodeOrDefault( tlsStatus ) ) );
            }
        }
        else
        {
            /* WANT_READ and WANT_WRITE can be ignored. Logging for debugging purposes. */
            LogInfo( ( "(Network connection %p) TLS close-notify sent; ",
                       "received %s as the TLS status can be ignored for close-notify."
                       ( tlsStatus == MBEDTLS_ERR_SSL_WANT_READ ) ? "WANT_READ" : "WANT_WRITE",
                       pNetworkContext ) );
        }

        /* Free contexts. */
        contextFree( pMbedtlsPkcs11Context );
    }
}

/*-----------------------------------------------------------*/

int32_t Mbedtls_Pkcs11_Recv( NetworkContext_t * pNetworkContext,
                             void * pBuffer,
                             size_t bytesToRecv )
{
    MbedtlsPkcs11Context_t * pMbedtlsPkcs11Context = NULL;
    int32_t tlsStatus = 0;

    assert( ( pNetworkContext != NULL ) && ( pNetworkContext->pParams != NULL ) );

    pMbedtlsPkcs11Context = pNetworkContext->pParams;
    tlsStatus = ( int32_t ) mbedtls_ssl_read( &( pMbedtlsPkcs11Context->context ),
                                              pBuffer,
                                              bytesToRecv );

    if( ( tlsStatus == MBEDTLS_ERR_SSL_TIMEOUT ) ||
        ( tlsStatus == MBEDTLS_ERR_SSL_WANT_READ ) ||
        ( tlsStatus == MBEDTLS_ERR_SSL_WANT_WRITE ) )
    {
        LogDebug( ( "Failed to read data. However, a read can be retried on this error. "
                    "mbedTLSError= %s : %s.",
                    mbedtlsHighLevelCodeOrDefault( tlsStatus ),
                    mbedtlsLowLevelCodeOrDefault( tlsStatus ) ) );

        /* Mark these set of errors as a timeout. The libraries may retry read
         * on these errors. */
        tlsStatus = 0;
    }
    else if( tlsStatus < 0 )
    {
        LogError( ( "Failed to read data: mbedTLSError= %s : %s.",
                    mbedtlsHighLevelCodeOrDefault( tlsStatus ),
                    mbedtlsLowLevelCodeOrDefault( tlsStatus ) ) );
    }
    else
    {
        /* Empty else marker. */
    }

    return tlsStatus;
}

/*-----------------------------------------------------------*/

int32_t Mbedtls_Pkcs11_Send( NetworkContext_t * pNetworkContext,
                             const void * pBuffer,
                             size_t bytesToSend )
{
    MbedtlsPkcs11Context_t * pMbedtlsPkcs11Context = NULL;
    int32_t tlsStatus = 0;

    assert( ( pNetworkContext != NULL ) && ( pNetworkContext->pParams != NULL ) );

    pMbedtlsPkcs11Context = pNetworkContext->pParams;
    tlsStatus = ( int32_t ) mbedtls_ssl_write( &( pMbedtlsPkcs11Context->context ),
                                               pBuffer,
                                               bytesToSend );

    if( ( tlsStatus == MBEDTLS_ERR_SSL_TIMEOUT ) ||
        ( tlsStatus == MBEDTLS_ERR_SSL_WANT_READ ) ||
        ( tlsStatus == MBEDTLS_ERR_SSL_WANT_WRITE ) )
    {
        LogDebug( ( "Failed to send data. However, send can be retried on this error. "
                    "mbedTLSError= %s : %s.",
                    mbedtlsHighLevelCodeOrDefault( tlsStatus ),
                    mbedtlsLowLevelCodeOrDefault( tlsStatus ) ) );

        /* Mark these set of errors as a timeout. The libraries may retry send
         * on these errors. */
        tlsStatus = 0;
    }
    else if( tlsStatus < 0 )
    {
        LogError( ( "Failed to send data:  mbedTLSError= %s : %s.",
                    mbedtlsHighLevelCodeOrDefault( tlsStatus ),
                    mbedtlsLowLevelCodeOrDefault( tlsStatus ) ) );
    }
    else
    {
        /* Empty else marker. */
    }

    return tlsStatus;
}
/*-----------------------------------------------------------*/

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

/* Standard includes. */
#include <string.h>
#include <assert.h>

/* TLS transport header. */
#include "mbedtls_pkcs11_posix.h"

/* MbedTLS includes. */
#include "mbedtls/debug.h"
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
 * @brief Configure MbedTLS for TLS on a TCP connection using PKCS #11 for the
 * client credentials.
 *
 * @param[in] pMbedtlsPkcs11Context Network context.
 * @param[in] pHostName Remote host name, used for server name indication.
 * @param[in] pMbedtlsPkcs11Credentials TLS setup parameters.
 * @param[in] recvTimeoutMs Receive timeout for network socket.
 *
 * @return #MBEDTLS_PKCS11_SUCCESS, #MBEDTLS_PKCS11_INSUFFICIENT_MEMORY, #MBEDTLS_PKCS11_INVALID_CREDENTIALS,
 * #MBEDTLS_PKCS11_HANDSHAKE_FAILED, or #MBEDTLS_PKCS11_INTERNAL_ERROR.
 */
static MbedtlsPkcs11Status_t configureMbedtls( MbedtlsPkcs11Context_t * pMbedtlsPkcs11Context,
                                               const char * pHostName,
                                               const MbedtlsPkcs11Credentials_t * pMbedtlsPkcs11Credentials,
                                               uint32_t recvTimeoutMs );

/**
 * @brief Configure the client and Root CA in the MbedTLS SSL context.
 *
 * @param[in] pMbedtlsPkcs11Context Network context.
 * @param[in] pMbedtlsPkcs11Credentials TLS setup parameters.
 *
 * @return #MBEDTLS_PKCS11_SUCCESS on success,
 * #MBEDTLS_PKCS11_INVALID_CREDENTIALS on error.
 */
static MbedtlsPkcs11Status_t configureMbedtlsCertificates( MbedtlsPkcs11Context_t * pMbedtlsPkcs11Context,
                                                           const MbedtlsPkcs11Credentials_t * pMbedtlsPkcs11Credentials );

/**
 * @brief Configure the SNI and ALPN in the MbedTLS SSL context.
 *
 * @param[in] pMbedtlsPkcs11Context Network context.
 * @param[in] pMbedtlsPkcs11Credentials TLS setup parameters.
 * @param[in] pHostName Remote host name, used for server name indication.
 *
 * @return #MBEDTLS_PKCS11_SUCCESS on success,
 * #MBEDTLS_PKCS11_INVALID_CREDENTIALS on error.
 */
static MbedtlsPkcs11Status_t configureMbedtlsSniAlpn( MbedtlsPkcs11Context_t * pMbedtlsPkcs11Context,
                                                      const MbedtlsPkcs11Credentials_t * pMbedtlsPkcs11Credentials,
                                                      const char * pHostName );

/**
 * @brief Configure the Maximum Fragment Length in the MbedTLS SSL context.
 *
 * @param[in] pMbedtlsPkcs11Context Network context.
 *
 * @return #MBEDTLS_PKCS11_SUCCESS on success,
 * #MBEDTLS_PKCS11_INVALID_CREDENTIALS on error.
 */
static MbedtlsPkcs11Status_t configureMbedtlsFragmentLength( MbedtlsPkcs11Context_t * pMbedtlsPkcs11Context );

/**
 * @brief Callback that wraps PKCS #11 for pseudo-random number generation. This
 * is passed to MbedTLS.
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
 * @param[out] pCertificateContext Certificate context.
 *
 * @return True on success.
 */
static bool readCertificateIntoContext( MbedtlsPkcs11Context_t * pContext,
                                        char * pLabelName,
                                        mbedtls_x509_crt * pCertificateContext );

/**
 * @brief Helper for configuring MbedTLS to use client private key from PKCS #11.
 *
 * @param pContext Caller context.
 * @param pPrivateKeyLabel PKCS #11 label for the private key.
 *
 * @return True on success.
 */
static bool initializeClientKeys( MbedtlsPkcs11Context_t * pContext,
                                  const char * pPrivateKeyLabel );

/**
 * @brief Sign a cryptographic hash with the private key. This is passed as a
 * callback to MbedTLS.
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
static int32_t privateKeySigningCallback( mbedtls_pk_context * pContext,
                                          mbedtls_md_type_t mdAlg,
                                          const unsigned char * pHash,
                                          size_t hashLen,
                                          unsigned char * pSig,
                                          size_t sig_size,
                                          size_t * pSigLen,
                                          int32_t ( * pRng )( void *, unsigned char *, size_t ),
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
    }
}

/*-----------------------------------------------------------*/

static void mbedtlsDebugPrint( void * ctx,
                               int level,
                               const char * pFile,
                               int line,
                               const char * pStr )
{
    /* Unused parameters. */
    ( void ) ctx;
    ( void ) pFile;
    ( void ) line;

    /* Send the debug string to the portable logger. */
    printf( "mbedTLS: |%d| %s", level, pStr );
}

/*-----------------------------------------------------------*/

static MbedtlsPkcs11Status_t configureMbedtls( MbedtlsPkcs11Context_t * pMbedtlsPkcs11Context,
                                               const char * pHostName,
                                               const MbedtlsPkcs11Credentials_t * pMbedtlsPkcs11Credentials,
                                               uint32_t recvTimeoutMs )
{
    MbedtlsPkcs11Status_t returnStatus = MBEDTLS_PKCS11_SUCCESS;
    int32_t mbedtlsError = 0;

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
    else
    {
        /* Set up the certificate security profile, starting from the default value. */
        pMbedtlsPkcs11Context->certProfile = mbedtls_x509_crt_profile_default;

        /* Set SSL authmode and the RNG context. */
        mbedtls_ssl_conf_authmode( &( pMbedtlsPkcs11Context->config ), MBEDTLS_SSL_VERIFY_REQUIRED );
        mbedtls_ssl_conf_rng( &( pMbedtlsPkcs11Context->config ), generateRandomBytes, pMbedtlsPkcs11Context );
        mbedtls_ssl_conf_cert_profile( &( pMbedtlsPkcs11Context->config ), &( pMbedtlsPkcs11Context->certProfile ) );
        mbedtls_ssl_conf_read_timeout( &( pMbedtlsPkcs11Context->config ), recvTimeoutMs );
        mbedtls_ssl_conf_dbg( &pMbedtlsPkcs11Context->config, mbedtlsDebugPrint, NULL );
        mbedtls_debug_set_threshold( MBEDTLS_DEBUG_LOG_LEVEL );

        returnStatus = configureMbedtlsCertificates( pMbedtlsPkcs11Context, pMbedtlsPkcs11Credentials );
    }

    if( returnStatus == MBEDTLS_PKCS11_SUCCESS )
    {
        returnStatus = configureMbedtlsSniAlpn( pMbedtlsPkcs11Context, pMbedtlsPkcs11Credentials, pHostName );
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
    }

    if( returnStatus == MBEDTLS_PKCS11_SUCCESS )
    {
        /* Set the underlying IO for the TLS connection. */
        mbedtls_ssl_set_bio( &( pMbedtlsPkcs11Context->context ),
                             ( void * ) &( pMbedtlsPkcs11Context->socketContext ),
                             mbedtls_net_send,
                             mbedtls_net_recv,
                             mbedtls_net_recv_timeout );

        returnStatus = configureMbedtlsFragmentLength( pMbedtlsPkcs11Context );
    }

    if( returnStatus != MBEDTLS_PKCS11_SUCCESS )
    {
        contextFree( pMbedtlsPkcs11Context );
    }
    else
    {
        LogDebug( ( "Configured MbedTLS context." ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static MbedtlsPkcs11Status_t configureMbedtlsCertificates( MbedtlsPkcs11Context_t * pMbedtlsPkcs11Context,
                                                           const MbedtlsPkcs11Credentials_t * pMbedtlsPkcs11Credentials )

{
    MbedtlsPkcs11Status_t returnStatus = MBEDTLS_PKCS11_SUCCESS;
    int32_t mbedtlsError = 0;
    bool result;

    assert( pMbedtlsPkcs11Context != NULL );
    assert( pMbedtlsPkcs11Credentials != NULL );
    assert( pMbedtlsPkcs11Credentials->pRootCaPath != NULL );

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
        /* Setup the client private key. */
        result = initializeClientKeys( pMbedtlsPkcs11Context,
                                       pMbedtlsPkcs11Credentials->pPrivateKeyLabel );

        if( result == false )
        {
            LogError( ( "Failed to setup key handling by PKCS #11." ) );
            returnStatus = MBEDTLS_PKCS11_INVALID_CREDENTIALS;
        }
    }

    if( returnStatus == MBEDTLS_PKCS11_SUCCESS )
    {
        /* Setup the client certificate. */
        result = readCertificateIntoContext( pMbedtlsPkcs11Context,
                                             pMbedtlsPkcs11Credentials->pClientCertLabel,
                                             &( pMbedtlsPkcs11Context->clientCert ) );

        if( result == false )
        {
            LogError( ( "Failed to get certificate from PKCS #11 module." ) );
            returnStatus = MBEDTLS_PKCS11_INVALID_CREDENTIALS;
        }
    }

    if( returnStatus == MBEDTLS_PKCS11_SUCCESS )
    {
        ( void ) mbedtls_ssl_conf_own_cert( &( pMbedtlsPkcs11Context->config ),
                                            &( pMbedtlsPkcs11Context->clientCert ),
                                            &( pMbedtlsPkcs11Context->privKey ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static MbedtlsPkcs11Status_t configureMbedtlsSniAlpn( MbedtlsPkcs11Context_t * pMbedtlsPkcs11Context,
                                                      const MbedtlsPkcs11Credentials_t * pMbedtlsPkcs11Credentials,
                                                      const char * pHostName )
{
    MbedtlsPkcs11Status_t returnStatus = MBEDTLS_PKCS11_SUCCESS;
    int32_t mbedtlsError = 0;

    assert( pMbedtlsPkcs11Context != NULL );
    assert( pHostName != NULL );
    assert( pMbedtlsPkcs11Credentials != NULL );
    assert( pMbedtlsPkcs11Credentials->pRootCaPath != NULL );

    if( pMbedtlsPkcs11Credentials->pAlpnProtos != NULL )
    {
        /* Include an application protocol list in the TLS ClientHello message. */
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

    /* Enable SNI if requested. */
    if( ( returnStatus == MBEDTLS_PKCS11_SUCCESS ) &&
        ( pMbedtlsPkcs11Credentials->disableSni == false ) )
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

    return returnStatus;
}

/*-----------------------------------------------------------*/

static MbedtlsPkcs11Status_t configureMbedtlsFragmentLength( MbedtlsPkcs11Context_t * pMbedtlsPkcs11Context )
{
    MbedtlsPkcs11Status_t returnStatus = MBEDTLS_PKCS11_SUCCESS;
    int32_t mbedtlsError = 0;

    assert( pMbedtlsPkcs11Context != NULL );

    /* Set Maximum Fragment Length if enabled. */
    #ifdef MBEDTLS_SSL_MAX_FRAGMENT_LENGTH

        /* Enable the max fragment extension. 4096 bytes is currently the largest fragment size permitted.
         * See RFC 6066 https://tools.ietf.org/html/rfc6066#page-8 for more information.
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
    #endif /* ifdef MBEDTLS_SSL_MAX_FRAGMENT_LENGTH */
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

    assert( pCtx != NULL );
    assert( pRandom != NULL );

    xResult = pContext->pP11FunctionList->C_GenerateRandom( pContext->p11Session, pRandom, randomLength );

    if( xResult != CKR_OK )
    {
        LogError( ( "Failed to generate random bytes from the PKCS #11 module." ) );
    }

    return ( int32_t ) xResult;
}

/*----------------------------------------------------------*/

static bool readCertificateIntoContext( MbedtlsPkcs11Context_t * pContext,
                                        char * pLabelName,
                                        mbedtls_x509_crt * pCertificateContext )
{
    CK_RV pkcs11Ret = CKR_OK;
    CK_ATTRIBUTE template = { 0 };
    CK_OBJECT_HANDLE certificateHandle = 0;
    int32_t mbedtlsRet = -1;

    assert( pContext != NULL );
    assert( pLabelName != NULL );
    assert( pCertificateContext != NULL );

    /* Get the handle of the certificate. */
    pkcs11Ret = xFindObjectWithLabelAndClass( pContext->p11Session,
                                              pLabelName,
                                              strlen( pLabelName ),
                                              CKO_CERTIFICATE,
                                              &certificateHandle );

    if( ( pkcs11Ret == CKR_OK ) && ( certificateHandle == CK_INVALID_HANDLE ) )
    {
        pkcs11Ret = CKR_OBJECT_HANDLE_INVALID;
    }

    /* Query the certificate size. */
    if( pkcs11Ret == CKR_OK )
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
    if( pkcs11Ret == CKR_OK )
    {
        template.pValue = malloc( template.ulValueLen );

        if( NULL == template.pValue )
        {
            LogError( ( "Failed to allocate %lu bytes of memory for certificate buffer.",
                        template.ulValueLen ) );
            pkcs11Ret = CKR_HOST_MEMORY;
        }
    }

    /* Export the certificate. */
    if( pkcs11Ret == CKR_OK )
    {
        pkcs11Ret = pContext->pP11FunctionList->C_GetAttributeValue( pContext->p11Session,
                                                                     certificateHandle,
                                                                     &template,
                                                                     1 );
    }

    /* Decode the certificate. */
    if( pkcs11Ret == CKR_OK )
    {
        mbedtlsRet = mbedtls_x509_crt_parse( pCertificateContext,
                                             ( const unsigned char * ) template.pValue,
                                             template.ulValueLen );
    }

    /* Free memory. */
    free( template.pValue );

    return( mbedtlsRet == 0 );
}

/*-----------------------------------------------------------*/

static bool initializeClientKeys( MbedtlsPkcs11Context_t * pContext,
                                  const char * pPrivateKeyLabel )
{
    CK_RV ret = CKR_OK;
    CK_ATTRIBUTE template[ 2 ] = { 0 };
    mbedtls_pk_type_t keyAlgo = 0;

    assert( pContext != NULL );
    assert( pPrivateKeyLabel != NULL );

    /* Get the handle of the device private key. */
    ret = xFindObjectWithLabelAndClass( pContext->p11Session,
                                        ( char * ) pPrivateKeyLabel,
                                        strlen( pPrivateKeyLabel ),
                                        CKO_PRIVATE_KEY,
                                        &pContext->p11PrivateKey );

    if( ( ret == CKR_OK ) && ( pContext->p11PrivateKey == CK_INVALID_HANDLE ) )
    {
        ret = CK_INVALID_HANDLE;
        LogError( ( "Could not find private key." ) );
    }

    /* Query the device private key type. */
    if( ret == CKR_OK )
    {
        template[ 0 ].type = CKA_KEY_TYPE;
        template[ 0 ].pValue = &pContext->keyType;
        template[ 0 ].ulValueLen = sizeof( &pContext->keyType );
        ret = pContext->pP11FunctionList->C_GetAttributeValue( pContext->p11Session,
                                                               pContext->p11PrivateKey,
                                                               template,
                                                               1 );
    }

    /* Map the PKCS #11 key type to an mbedTLS algorithm. */
    if( ret == CKR_OK )
    {
        switch( pContext->keyType )
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
        memcpy( &pContext->privKeyInfo, mbedtls_pk_info_from_type( keyAlgo ), sizeof( mbedtls_pk_info_t ) );

        pContext->privKeyInfo.sign_func = privateKeySigningCallback;
        pContext->privKey.pk_info = &pContext->privKeyInfo;
        pContext->privKey.pk_ctx = pContext;
    }

    return( ret == CKR_OK );
}

/*-----------------------------------------------------------*/

static int32_t privateKeySigningCallback( mbedtls_pk_context * pContext,
                                          mbedtls_md_type_t mdAlg,
                                          const unsigned char * pHash,
                                          size_t hashLen,
                                          unsigned char * pSig,
                                          size_t sig_size,
                                          size_t * pSigLen,
                                          int32_t ( * pRng )( void *,
                                                              unsigned char *,
                                                              size_t ),
                                          void * pRngContext )
{
    CK_RV ret = CKR_OK;
    int32_t result = 0;
    MbedtlsPkcs11Context_t * pMbedtlsPkcs11Context = ( MbedtlsPkcs11Context_t * ) pContext->pk_ctx;
    CK_MECHANISM mech = { 0 };
    /* Buffer big enough to hold data to be signed. */
    CK_BYTE toBeSigned[ 256 ];
    CK_ULONG toBeSignedLen = sizeof( toBeSigned );

    /* Unreferenced parameters. */
    ( void ) ( pRng );
    ( void ) ( pRngContext );
    ( void ) ( mdAlg );
    ( void ) ( sig_size );

    assert( pContext != NULL );
    assert( pHash != NULL );
    assert( pSigLen != NULL );

    /* Sanity check buffer length. */
    if( hashLen > sizeof( toBeSigned ) )
    {
        ret = CKR_ARGUMENTS_BAD;
    }

    /* Format the hash data to be signed. */
    if( pMbedtlsPkcs11Context->keyType == CKK_RSA )
    {
        mech.mechanism = CKM_RSA_PKCS;

        /* mbedTLS expects hashed data without padding, but PKCS #11 C_Sign function performs a hash
         * & sign if hash algorithm is specified.  This helper function applies padding
         * indicating data was hashed with SHA-256 while still allowing pre-hashed data to
         * be provided. */
        ret = vAppendSHA256AlgorithmIdentifierSequence( ( const uint8_t * ) pHash, toBeSigned );
        toBeSignedLen = pkcs11RSA_SIGNATURE_INPUT_LENGTH;
    }
    else if( pMbedtlsPkcs11Context->keyType == CKK_EC )
    {
        mech.mechanism = CKM_ECDSA;
        memcpy( toBeSigned, pHash, hashLen );
        toBeSignedLen = hashLen;
    }
    else
    {
        ret = CKR_ARGUMENTS_BAD;
    }

    if( ret == CKR_OK )
    {
        /* Use the PKCS #11 module to sign. */
        ret = pMbedtlsPkcs11Context->pP11FunctionList->C_SignInit( pMbedtlsPkcs11Context->p11Session,
                                                                   &mech,
                                                                   pMbedtlsPkcs11Context->p11PrivateKey );
    }

    if( ret == CKR_OK )
    {
        *pSigLen = sizeof( toBeSigned );
        ret = pMbedtlsPkcs11Context->pP11FunctionList->C_Sign( pMbedtlsPkcs11Context->p11Session,
                                                               toBeSigned,
                                                               toBeSignedLen,
                                                               pSig,
                                                               ( CK_ULONG_PTR ) pSigLen );
    }

    if( ( ret == CKR_OK ) && ( pMbedtlsPkcs11Context->keyType == CKK_EC ) )
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
                                              const MbedtlsPkcs11Credentials_t * pMbedtlsPkcs11Credentials,
                                              uint32_t recvTimeoutMs )
{
    MbedtlsPkcs11Context_t * pMbedtlsPkcs11Context = NULL;
    MbedtlsPkcs11Status_t returnStatus = MBEDTLS_PKCS11_SUCCESS;
    int32_t mbedtlsError = 0;
    char portStr[ 6 ] = { 0 };

    if( ( pNetworkContext == NULL ) ||
        ( pNetworkContext->pParams == NULL ) ||
        ( pHostName == NULL ) ||
        ( pMbedtlsPkcs11Credentials == NULL ) ||
        ( pMbedtlsPkcs11Credentials->pRootCaPath == NULL ) ||
        ( pMbedtlsPkcs11Credentials->pClientCertLabel == NULL ) ||
        ( pMbedtlsPkcs11Credentials->pPrivateKeyLabel == NULL ) )
    {
        LogError( ( "Invalid input parameter(s): Arguments cannot be NULL. pNetworkContext=%p, "
                    "pHostName=%p, pMbedtlsPkcs11Credentials=%p.",
                    ( void * ) pNetworkContext,
                    ( const void * ) pHostName,
                    ( const void * ) pMbedtlsPkcs11Credentials ) );
        returnStatus = MBEDTLS_PKCS11_INVALID_PARAMETER;
    }
    else
    {
        snprintf( portStr, sizeof( portStr ), "%u", port );
        pMbedtlsPkcs11Context = pNetworkContext->pParams;

        /* Configure MbedTLS. */
        returnStatus = configureMbedtls( pMbedtlsPkcs11Context, pHostName, pMbedtlsPkcs11Credentials, recvTimeoutMs );
    }

    /* Establish a TCP connection with the server. */
    if( returnStatus == MBEDTLS_PKCS11_SUCCESS )
    {
        mbedtlsError = mbedtls_net_connect( &( pMbedtlsPkcs11Context->socketContext ),
                                            pHostName,
                                            portStr,
                                            MBEDTLS_NET_PROTO_TCP );

        if( mbedtlsError != 0 )
        {
            LogError( ( "Failed to connect to %s with error %d.", pHostName, mbedtlsError ) );
            returnStatus = MBEDTLS_PKCS11_CONNECT_FAILURE;
        }
    }

    if( returnStatus == MBEDTLS_PKCS11_SUCCESS )
    {
        /* Perform the TLS handshake. */
        do
        {
            mbedtlsError = mbedtls_ssl_handshake( &( pMbedtlsPkcs11Context->context ) );
        } while( ( mbedtlsError == MBEDTLS_ERR_SSL_WANT_READ ) ||
                 ( mbedtlsError == MBEDTLS_ERR_SSL_WANT_WRITE ) );

        if( ( mbedtlsError != 0 ) || ( mbedtls_ssl_get_verify_result( &( pMbedtlsPkcs11Context->context ) ) != 0U ) )
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
        LogInfo( ( "TLS Connection to %s established.", pHostName ) );
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

        if( tlsStatus == 0 )
        {
            LogInfo( ( "Closing TLS connection: TLS close-notify sent." ) );
        }
        else if( ( tlsStatus == MBEDTLS_ERR_SSL_WANT_READ ) ||
                 ( tlsStatus == MBEDTLS_ERR_SSL_WANT_WRITE ) )
        {
            /* WANT_READ or WANT_WRITE can be ignored. Logging for debugging purposes. */
            LogInfo( ( "TLS close-notify sent; "
                       "received %s as the TLS status which can be ignored for close-notify.",
                       ( tlsStatus == MBEDTLS_ERR_SSL_WANT_READ ) ? "WANT_READ" : "WANT_WRITE" ) );
        }
        else
        {
            /* Ignore the WANT_READ or WANT_WRITE return values. */
            LogError( ( "Failed to send TLS close-notify: mbedTLSError= %s : %s.",
                        mbedtlsHighLevelCodeOrDefault( tlsStatus ),
                        mbedtlsLowLevelCodeOrDefault( tlsStatus ) ) );
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

/*
 * AWS IoT Device SDK for Embedded C 202211.00
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
#include <stdint.h>
#include <errno.h>
#include <unistd.h>

/* TLS transport header. */
#include "mbedtls_posix.h"

/* MbedTLS includes. */
#include "mbedtls/debug.h"
#include "mbedtls/error.h"
#include "mbedtls/x509_csr.h"

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
    MbedtlsContext_t * pParams;
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
static void contextInit( MbedtlsContext_t * pContext );

/**
 * @brief Free the MbedTLS structures in a network connection.
 *
 * @param[in] pContext The SSL context to free.
 */
static void contextFree( MbedtlsContext_t * pContext );

/**
 * @brief Configure MbedTLS for TLS on a TCP connection using PKCS #11 for the
 * client credentials.
 *
 * @param[in] pMbedtlsContext Network context.
 * @param[in] pHostName Remote host name, used for server name indication.
 * @param[in] pMbedtlsCredentials TLS setup parameters.
 * @param[in] recvTimeoutMs Receive timeout for network socket.
 *
 * @return #MBEDTLS_SUCCESS, #MBEDTLS_INSUFFICIENT_MEMORY, #MBEDTLS_INVALID_CREDENTIALS,
 * #MBEDTLS_HANDSHAKE_FAILED, or #MBEDTLS_INTERNAL_ERROR.
 */
static MbedtlsStatus_t configureMbedtls( MbedtlsContext_t * pMbedtlsContext,
                                         const char * pHostName,
                                         const MbedtlsCredentials_t * pMbedtlsCredentials,
                                         uint32_t recvTimeoutMs );

/**
 * @brief Configure the client and Root CA in the MbedTLS SSL context.
 *
 * @param[in] pMbedtlsContext Network context.
 * @param[in] pMbedtlsCredentials TLS setup parameters.
 *
 * @return #MBEDTLS_SUCCESS on success,
 * #MBEDTLS_INVALID_CREDENTIALS on error.
 */
static MbedtlsStatus_t configureMbedtlsCertificates( MbedtlsContext_t * pMbedtlsContext,
                                                     const MbedtlsCredentials_t * pMbedtlsCredentials );

/**
 * @brief Configure the SNI and ALPN in the MbedTLS SSL context.
 *
 * @param[in] pMbedtlsContext Network context.
 * @param[in] pMbedtlsCredentials TLS setup parameters.
 * @param[in] pHostName Remote host name, used for server name indication.
 *
 * @return #MBEDTLS_SUCCESS on success,
 * #MBEDTLS_INVALID_CREDENTIALS on error.
 */
static MbedtlsStatus_t configureMbedtlsSniAlpn( MbedtlsContext_t * pMbedtlsContext,
                                                const MbedtlsCredentials_t * pMbedtlsCredentials,
                                                const char * pHostName );

/**
 * @brief Configure the Maximum Fragment Length in the MbedTLS SSL context.
 *
 * @param[in] pMbedtlsContext Network context.
 *
 * @return #MBEDTLS_SUCCESS on success,
 * #MBEDTLS_INVALID_CREDENTIALS on error.
 */
static MbedtlsStatus_t configureMbedtlsFragmentLength( MbedtlsContext_t * pMbedtlsContext );

/*-----------------------------------------------------------*/

static void contextInit( MbedtlsContext_t * pContext )
{
    assert( pContext != NULL );
    psa_crypto_init();

    mbedtls_net_init( &( pContext->socketContext ) );
    mbedtls_ssl_init( &( pContext->context ) );
    mbedtls_ssl_config_init( &( pContext->config ) );
    mbedtls_x509_crt_init( &( pContext->rootCa ) );
    mbedtls_x509_crt_init( &( pContext->clientCert ) );
    mbedtls_pk_init( &( pContext->privKey ) );
    mbedtls_entropy_init( &( pContext->entropyCtx ) );
    mbedtls_ctr_drbg_init( &( pContext->ctrDrbgCtx ) );
}
/*-----------------------------------------------------------*/

static void contextFree( MbedtlsContext_t * pContext )
{
    if( pContext != NULL )
    {
        mbedtls_net_free( &( pContext->socketContext ) );
        mbedtls_ssl_free( &( pContext->context ) );
        mbedtls_ssl_config_free( &( pContext->config ) );
        mbedtls_x509_crt_free( &( pContext->rootCa ) );
        mbedtls_x509_crt_free( &( pContext->clientCert ) );
        mbedtls_pk_free( &( pContext->privKey ) );
        mbedtls_entropy_free( &( pContext->entropyCtx ) );
        mbedtls_ctr_drbg_free( &( pContext->ctrDrbgCtx ) );
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
    fprintf( stderr, "mbedTLS: |%d| %s", level, pStr );
}

/*-----------------------------------------------------------*/

static MbedtlsStatus_t configureMbedtls( MbedtlsContext_t * pMbedtlsContext,
                                         const char * pHostName,
                                         const MbedtlsCredentials_t * pMbedtlsCredentials,
                                         uint32_t recvTimeoutMs )
{
    MbedtlsStatus_t returnStatus = MBEDTLS_SUCCESS;
    int mbedtlsError = 0;

    assert( pMbedtlsContext != NULL );
    assert( pHostName != NULL );
    assert( pMbedtlsCredentials != NULL );
    assert( pMbedtlsCredentials->pRootCaPath != NULL );

    /* Initialize the MbedTLS context structures. */
    contextInit( pMbedtlsContext );

    mbedtls_ctr_drbg_set_prediction_resistance( &( pMbedtlsContext->ctrDrbgCtx ),
                                                MBEDTLS_CTR_DRBG_PR_ON );

    mbedtlsError = mbedtls_ctr_drbg_seed( &( pMbedtlsContext->ctrDrbgCtx ),
                                          mbedtls_entropy_func,
                                          &( pMbedtlsContext->entropyCtx ),
                                          NULL,
                                          0 );

    if( mbedtlsError != 0 )
    {
        LogError( ( "Failed to seed mbedtls ctr-drgb random number generator: mbedTLSError= %s : %s.",
                    mbedtlsHighLevelCodeOrDefault( mbedtlsError ),
                    mbedtlsLowLevelCodeOrDefault( mbedtlsError ) ) );

        returnStatus = MBEDTLS_INTERNAL_ERROR;
    }

    if( returnStatus == MBEDTLS_SUCCESS )
    {
        mbedtlsError = mbedtls_ssl_config_defaults( &( pMbedtlsContext->config ),
                                                    MBEDTLS_SSL_IS_CLIENT,
                                                    MBEDTLS_SSL_TRANSPORT_STREAM,
                                                    MBEDTLS_SSL_PRESET_DEFAULT );


        if( mbedtlsError != 0 )
        {
            LogError( ( "Failed to set default SSL configuration: mbedTLSError= %s : %s.",
                        mbedtlsHighLevelCodeOrDefault( mbedtlsError ),
                        mbedtlsLowLevelCodeOrDefault( mbedtlsError ) ) );

            /* Per MbedTLS docs, mbedtls_ssl_config_defaults only fails on memory allocation. */
            returnStatus = MBEDTLS_INSUFFICIENT_MEMORY;
        }
    }

    if( returnStatus == MBEDTLS_SUCCESS )
    {
        /* Set up the certificate security profile, starting from the default value. */
        pMbedtlsContext->certProfile = mbedtls_x509_crt_profile_default;

        /* Set SSL authmode and the RNG context. */
        mbedtls_ssl_conf_authmode( &( pMbedtlsContext->config ),
                                   MBEDTLS_SSL_VERIFY_REQUIRED );

        mbedtls_ssl_conf_rng( &( pMbedtlsContext->config ),
                              mbedtls_ctr_drbg_random,
                              &( pMbedtlsContext->ctrDrbgCtx ) );

        mbedtls_ssl_conf_cert_profile( &( pMbedtlsContext->config ),
                                       &( pMbedtlsContext->certProfile ) );

        mbedtls_ssl_conf_read_timeout( &( pMbedtlsContext->config ),
                                       recvTimeoutMs );

        mbedtls_ssl_conf_dbg( &pMbedtlsContext->config,
                              mbedtlsDebugPrint,
                              NULL );

        mbedtls_debug_set_threshold( MBEDTLS_DEBUG_LOG_LEVEL );

        returnStatus = configureMbedtlsCertificates( pMbedtlsContext,
                                                     pMbedtlsCredentials );
    }

    if( returnStatus == MBEDTLS_SUCCESS )
    {
        returnStatus = configureMbedtlsSniAlpn( pMbedtlsContext, pMbedtlsCredentials, pHostName );
    }

    if( returnStatus == MBEDTLS_SUCCESS )
    {
        /* Initialize the MbedTLS secured connection context. */
        mbedtlsError = mbedtls_ssl_setup( &( pMbedtlsContext->context ),
                                          &( pMbedtlsContext->config ) );

        if( mbedtlsError != 0 )
        {
            LogError( ( "Failed to set up MbedTLS SSL context: mbedTLSError= %s : %s.",
                        mbedtlsHighLevelCodeOrDefault( mbedtlsError ),
                        mbedtlsLowLevelCodeOrDefault( mbedtlsError ) ) );
            returnStatus = MBEDTLS_INTERNAL_ERROR;
        }
    }

    if( returnStatus == MBEDTLS_SUCCESS )
    {
        /* Set the underlying IO for the TLS connection. */
        mbedtls_ssl_set_bio( &( pMbedtlsContext->context ),
                             ( void * ) &( pMbedtlsContext->socketContext ),
                             mbedtls_net_send,
                             mbedtls_net_recv,
                             mbedtls_net_recv_timeout );

        returnStatus = configureMbedtlsFragmentLength( pMbedtlsContext );
    }

    if( returnStatus != MBEDTLS_SUCCESS )
    {
        contextFree( pMbedtlsContext );
    }
    else
    {
        LogDebug( ( "Configured MbedTLS context." ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static MbedtlsStatus_t configureMbedtlsCertificates( MbedtlsContext_t * pMbedtlsContext,
                                                     const MbedtlsCredentials_t * pMbedtlsCredentials )

{
    MbedtlsStatus_t returnStatus = MBEDTLS_SUCCESS;
    int mbedtlsError = 0;

    assert( pMbedtlsContext != NULL );
    assert( pMbedtlsCredentials != NULL );
    assert( pMbedtlsCredentials->pRootCaPath != NULL );

    /* Parse the server root CA certificate into the SSL context. */
    mbedtlsError = mbedtls_x509_crt_parse_file( &( pMbedtlsContext->rootCa ),
                                                pMbedtlsCredentials->pRootCaPath );

    if( mbedtlsError != 0 )
    {
        LogError( ( "Failed to parse server root CA certificate: mbedTLSError= %s : %s.",
                    mbedtlsHighLevelCodeOrDefault( mbedtlsError ),
                    mbedtlsLowLevelCodeOrDefault( mbedtlsError ) ) );
        returnStatus = MBEDTLS_INVALID_CREDENTIALS;
    }
    else
    {
        mbedtls_ssl_conf_ca_chain( &( pMbedtlsContext->config ),
                                   &( pMbedtlsContext->rootCa ),
                                   NULL );

        mbedtlsError = mbedtls_pk_parse_keyfile(
            &( pMbedtlsContext->privKey ),
            pMbedtlsCredentials->pPrivateKeyPath,
            NULL,
            mbedtls_ctr_drbg_random,
            &( pMbedtlsContext->ctrDrbgCtx )
        );

        if( mbedtlsError != 0 )
        {
            LogError( ( "Failed to load private key from path %s", pMbedtlsCredentials->pPrivateKeyPath ) );
            returnStatus = MBEDTLS_INVALID_CREDENTIALS;
        }
    }

    if( returnStatus == MBEDTLS_SUCCESS )
    {
        /* Setup the client certificate. */
        mbedtlsError = mbedtls_x509_crt_parse_file(
            &( pMbedtlsContext->clientCert ),
            pMbedtlsCredentials->pClientCertPath
        );

        if( mbedtlsError != 0 )
        {
            LogError( ( "Failed to load client certificate from file: %s.",  pMbedtlsCredentials->pClientCertPath ) );
            returnStatus = MBEDTLS_INVALID_CREDENTIALS;
        }
    }

    if( returnStatus == MBEDTLS_SUCCESS )
    {
        ( void ) mbedtls_ssl_conf_own_cert( &( pMbedtlsContext->config ),
                                            &( pMbedtlsContext->clientCert ),
                                            &( pMbedtlsContext->privKey ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static MbedtlsStatus_t configureMbedtlsSniAlpn( MbedtlsContext_t * pMbedtlsContext,
                                                const MbedtlsCredentials_t * pMbedtlsCredentials,
                                                const char * pHostName )
{
    MbedtlsStatus_t returnStatus = MBEDTLS_SUCCESS;
    int mbedtlsError = 0;

    assert( pMbedtlsContext != NULL );
    assert( pHostName != NULL );
    assert( pMbedtlsCredentials != NULL );
    assert( pMbedtlsCredentials->pRootCaPath != NULL );

    if( pMbedtlsCredentials->pAlpnProtos != NULL )
    {
        /* Include an application protocol list in the TLS ClientHello message. */
        mbedtlsError = mbedtls_ssl_conf_alpn_protocols( &( pMbedtlsContext->config ),
                                                        pMbedtlsCredentials->pAlpnProtos );

        if( mbedtlsError != 0 )
        {
            LogError( ( "Failed to configure ALPN protocol in MbedTLS: mbedTLSError= %s : %s.",
                        mbedtlsHighLevelCodeOrDefault( mbedtlsError ),
                        mbedtlsLowLevelCodeOrDefault( mbedtlsError ) ) );
            returnStatus = MBEDTLS_INTERNAL_ERROR;
        }
    }

    /* Enable SNI if requested. */
    if( ( returnStatus == MBEDTLS_SUCCESS ) &&
        ( pMbedtlsCredentials->disableSni == false ) )
    {
        mbedtlsError = mbedtls_ssl_set_hostname( &( pMbedtlsContext->context ),
                                                 pHostName );

        if( mbedtlsError != 0 )
        {
            LogError( ( "Failed to set server name: mbedTLSError= %s : %s.",
                        mbedtlsHighLevelCodeOrDefault( mbedtlsError ),
                        mbedtlsLowLevelCodeOrDefault( mbedtlsError ) ) );
            returnStatus = MBEDTLS_INTERNAL_ERROR;
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static MbedtlsStatus_t configureMbedtlsFragmentLength( MbedtlsContext_t * pMbedtlsContext )
{
    MbedtlsStatus_t returnStatus = MBEDTLS_SUCCESS;
    int mbedtlsError = 0;

    assert( pMbedtlsContext != NULL );

    /* Set Maximum Fragment Length if enabled. */
    #ifdef MBEDTLS_SSL_MAX_FRAGMENT_LENGTH

        /* Enable the max fragment extension. 4096 bytes is currently the largest fragment size permitted.
         * See RFC 6066 https://tools.ietf.org/html/rfc6066#page-8 for more information.
         *
         * Smaller values can be found in "mbedtls/include/ssl.h".
         */
        mbedtlsError = mbedtls_ssl_conf_max_frag_len( &( pMbedtlsContext->config ), MBEDTLS_SSL_MAX_FRAG_LEN_4096 );

        if( mbedtlsError != 0 )
        {
            LogError( ( "Failed to maximum fragment length extension: mbedTLSError= %s : %s.",
                        mbedtlsHighLevelCodeOrDefault( mbedtlsError ),
                        mbedtlsLowLevelCodeOrDefault( mbedtlsError ) ) );
            returnStatus = MBEDTLS_INTERNAL_ERROR;
        }
    #endif /* ifdef MBEDTLS_SSL_MAX_FRAGMENT_LENGTH */
    return returnStatus;
}

/*-----------------------------------------------------------*/

MbedtlsStatus_t Mbedtls_Connect( NetworkContext_t * pNetworkContext,
                                 const char * pHostName,
                                 uint16_t port,
                                 const MbedtlsCredentials_t * pMbedtlsCredentials,
                                 uint32_t recvTimeoutMs )
{
    MbedtlsContext_t * pMbedtlsContext = NULL;
    MbedtlsStatus_t returnStatus = MBEDTLS_SUCCESS;
    int mbedtlsError = 0;
    char portStr[ 6 ] = { 0 };

    if( ( pNetworkContext == NULL ) ||
        ( pNetworkContext->pParams == NULL ) ||
        ( pHostName == NULL ) ||
        ( pMbedtlsCredentials == NULL ) ||
        ( pMbedtlsCredentials->pRootCaPath == NULL ) ||
        ( pMbedtlsCredentials->pClientCertPath == NULL ) ||
        ( pMbedtlsCredentials->pPrivateKeyPath == NULL ) )
    {
        LogError( ( "Invalid input parameter(s): Arguments cannot be NULL. pNetworkContext=%p, "
                    "pHostName=%p, pMbedtlsCredentials=%p.",
                    ( void * ) pNetworkContext,
                    ( const void * ) pHostName,
                    ( const void * ) pMbedtlsCredentials ) );
        returnStatus = MBEDTLS_INVALID_PARAMETER;
    }
    else
    {
        snprintf( portStr, sizeof( portStr ), "%u", port );
        pMbedtlsContext = pNetworkContext->pParams;

        /* Configure MbedTLS. */
        returnStatus = configureMbedtls( pMbedtlsContext, pHostName, pMbedtlsCredentials, recvTimeoutMs );
    }

    /* Establish a TCP connection with the server. */
    if( returnStatus == MBEDTLS_SUCCESS )
    {
        mbedtlsError = mbedtls_net_connect( &( pMbedtlsContext->socketContext ),
                                            pHostName,
                                            portStr,
                                            MBEDTLS_NET_PROTO_TCP );

        if( mbedtlsError != 0 )
        {
            LogError( ( "Failed to connect to %s with error %d.", pHostName, mbedtlsError ) );
            returnStatus = MBEDTLS_CONNECT_FAILURE;
        }
    }

    if( returnStatus == MBEDTLS_SUCCESS )
    {
        /* Perform the TLS handshake. */
        do
        {
            mbedtlsError = mbedtls_ssl_handshake( &( pMbedtlsContext->context ) );
        } while( ( mbedtlsError == MBEDTLS_ERR_SSL_WANT_READ ) ||
                 ( mbedtlsError == MBEDTLS_ERR_SSL_WANT_WRITE ) );

        if( ( mbedtlsError != 0 ) || ( mbedtls_ssl_get_verify_result( &( pMbedtlsContext->context ) ) != 0U ) )
        {
            LogError( ( "Failed to perform TLS handshake: mbedTLSError= %s : %s.",
                        mbedtlsHighLevelCodeOrDefault( mbedtlsError ),
                        mbedtlsLowLevelCodeOrDefault( mbedtlsError ) ) );
            returnStatus = MBEDTLS_HANDSHAKE_FAILED;
        }
    }

    /* Clean up on failure. */
    if( returnStatus != MBEDTLS_SUCCESS )
    {
        contextFree( pMbedtlsContext );
    }
    else
    {
        LogInfo( ( "TLS Connection to %s established.", pHostName ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

void Mbedtls_Disconnect( NetworkContext_t * pNetworkContext )
{
    MbedtlsContext_t * pMbedtlsContext = NULL;
    int tlsStatus = 0;

    if( ( pNetworkContext != NULL ) && ( pNetworkContext->pParams != NULL ) )
    {
        pMbedtlsContext = pNetworkContext->pParams;
        /* Attempting to terminate TLS connection. */
        tlsStatus = mbedtls_ssl_close_notify( &( pMbedtlsContext->context ) );

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
        contextFree( pMbedtlsContext );
    }
}

/*-----------------------------------------------------------*/

int Mbedtls_Recv( NetworkContext_t * pNetworkContext,
                      void * pBuffer,
                      size_t bytesToRecv )
{
    MbedtlsContext_t * pMbedtlsContext = NULL;
    int tlsStatus = 0;

    assert( ( pNetworkContext != NULL ) && ( pNetworkContext->pParams != NULL ) );

    pMbedtlsContext = pNetworkContext->pParams;
    tlsStatus = ( int ) mbedtls_ssl_read( &( pMbedtlsContext->context ),
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

int Mbedtls_Send( NetworkContext_t * pNetworkContext,
                      const void * pBuffer,
                      size_t bytesToSend )
{
    MbedtlsContext_t * pMbedtlsContext = NULL;
    int tlsStatus = 0;

    assert( ( pNetworkContext != NULL ) && ( pNetworkContext->pParams != NULL ) );

    pMbedtlsContext = pNetworkContext->pParams;
    tlsStatus = ( int ) mbedtls_ssl_write( &( pMbedtlsContext->context ),
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
        LogError( ( "Failed to send data: mbedTLSError= %s : %s.",
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

static MbedtlsStatus_t writeKeyToFile( const char * pKeyPath,
                                       mbedtls_pk_context * pPkCtx )
{
    unsigned char pKeyBuffer[ 2048 ];
    MbedtlsStatus_t status = MBEDTLS_SUCCESS;
    int result = 0;

    /* Serialize the private to a buffer */
    result = mbedtls_pk_write_key_pem( pPkCtx,
                                        pKeyBuffer,
                                        2048 );

    if( result < 0 )
    {
        LogError( ( "Failed to serialize EC key pair: result= %s : %s.",
                    mbedtlsHighLevelCodeOrDefault( result ),
                    mbedtlsLowLevelCodeOrDefault( result ) ) );

        status = MBEDTLS_INTERNAL_ERROR;
    }
    else
    {
        FILE * pKeyFile;
        size_t pemKeyLength = strnlen( ( char * ) pKeyBuffer, 2048 );

        pKeyFile = fopen( pKeyPath, "wb" );
        if( pKeyFile == NULL )
        {
            LogError( ( "Failed to open path: %s, result: %s.",
                        pKeyPath,
                        strerror( errno ) ) );

            status = MBEDTLS_INVALID_PARAMETER;
        }
        else
        {
            if( fwrite( pKeyBuffer, 1, pemKeyLength, pKeyFile ) != pemKeyLength )
            {
                LogError( ( "Failed to write %lu bytes path: %s, result: %s.",
                            ( unsigned long ) pemKeyLength,
                            pKeyPath,
                            strerror( errno ) ) );

                status = MBEDTLS_INTERNAL_ERROR;
            }

            if( fclose( pKeyFile ) != 0 )
            {
                LogError( ( "Failed to close file path: %s, result: %s.",
                            pKeyPath,
                            strerror( errno ) ) );

                status = MBEDTLS_INTERNAL_ERROR;
            }
        }
    }
    memset( pKeyBuffer, 0, 128 );

    return status;
}

/*-----------------------------------------------------------*/

MbedtlsStatus_t Mbedtls_GenerateECKey( const char * pPrivateKeyPath )
{
    MbedtlsStatus_t status = MBEDTLS_SUCCESS;
    mbedtls_entropy_context entropyCtx;
    mbedtls_ctr_drbg_context ctrDrbgCtx;
    mbedtls_pk_context pkCtx;
    int result = 0;

    assert( pPrivateKeyPath != NULL );
    // assert( access( pPrivateKeyPath, W_OK ) == 0 );

    /* Initialize mbedtls entropy, prng, and pk contexts */
    mbedtls_entropy_init( &entropyCtx );
    mbedtls_ctr_drbg_init( &ctrDrbgCtx );
    mbedtls_pk_init( &pkCtx );

    /* Seed the CTR-DRBG Pesudo Random Number Generator */
    mbedtls_ctr_drbg_set_prediction_resistance( &ctrDrbgCtx, MBEDTLS_CTR_DRBG_PR_ON );
    result = mbedtls_ctr_drbg_seed( &ctrDrbgCtx,
                                    mbedtls_entropy_func,
                                    &entropyCtx,
                                    NULL,
                                    0 );
    if( result != 0 )
    {
        LogError( ( "Failed to seed CTR-DRBG: result= %s : %s.",
                    mbedtlsHighLevelCodeOrDefault( result ),
                    mbedtlsLowLevelCodeOrDefault( result ) ) );
        status = MBEDTLS_INTERNAL_ERROR;
    }

    if( status == MBEDTLS_SUCCESS )
    {
        /* Setup / allocate the mbedtls PK context */
        result = mbedtls_pk_setup( &pkCtx,
                                   mbedtls_pk_info_from_type( MBEDTLS_PK_ECKEY ) );

        if( result != 0 )
        {
            LogError( ( "Failed to setup mbedtls pk context: result= %s : %s.",
                        mbedtlsHighLevelCodeOrDefault( result ),
                        mbedtlsLowLevelCodeOrDefault( result ) ) );
            status = MBEDTLS_INTERNAL_ERROR;
        }
    }

    if( status == MBEDTLS_SUCCESS )
    {
        /* Generate a new ECP key pair */
        result = mbedtls_ecp_gen_key( MBEDTLS_ECP_DP_SECP256R1,
                                      mbedtls_pk_ec( pkCtx ),
                                      mbedtls_ctr_drbg_random,
                                      &ctrDrbgCtx );

        if( result != 0 )
        {
            LogError( ( "Failed to generate an EC key: result= %s : %s.",
                        mbedtlsHighLevelCodeOrDefault( result ),
                        mbedtlsLowLevelCodeOrDefault( result ) ) );
            status = MBEDTLS_INTERNAL_ERROR;
        }
    }

    if( status == MBEDTLS_SUCCESS )
    {
        status = writeKeyToFile( pPrivateKeyPath, &pkCtx );
    }

    mbedtls_pk_free( &pkCtx );
    mbedtls_ctr_drbg_free( &ctrDrbgCtx );
    mbedtls_entropy_free( &entropyCtx );

    return status;
}

/*-----------------------------------------------------------*/

MbedtlsStatus_t Mbedtls_GenerateCSR( const char * pPrivateKeyPath,
                                     char * pCsrPemBuffer,
                                     size_t csrPemBufferLength )
{
    MbedtlsStatus_t status = MBEDTLS_SUCCESS;
    mbedtls_entropy_context entropyCtx;
    mbedtls_ctr_drbg_context ctrDrbgCtx;
    mbedtls_pk_context pkCtx;
    mbedtls_x509write_csr csrCtx;
    int result = 0;

    if( pPrivateKeyPath == NULL || pCsrPemBuffer == NULL )
    {
        return MBEDTLS_INVALID_PARAMETER;
    }

    /* Initialize mbedtls entropy, prng, pk, and csr contexts */
    mbedtls_entropy_init( &entropyCtx );
    mbedtls_ctr_drbg_init( &ctrDrbgCtx );
    mbedtls_pk_init( &pkCtx );
    mbedtls_x509write_csr_init( &csrCtx );

    /* Seed the CTR-DRBG Pesudo Random Number Generator */
    mbedtls_ctr_drbg_set_prediction_resistance( &ctrDrbgCtx, MBEDTLS_CTR_DRBG_PR_ON );
    result = mbedtls_ctr_drbg_seed( &ctrDrbgCtx,
                                    mbedtls_entropy_func,
                                    &entropyCtx,
                                    NULL,
                                    0 );
    if( result != 0 )
    {
        LogError( ( "Failed to seed CTR-DRBG: result= %s : %s.",
                    mbedtlsHighLevelCodeOrDefault( result ),
                    mbedtlsLowLevelCodeOrDefault( result ) ) );
        status = MBEDTLS_INTERNAL_ERROR;
    }

    if( status == MBEDTLS_SUCCESS )
    {
        /* Load private key from file */
        result = mbedtls_pk_parse_keyfile( &pkCtx,
                                           pPrivateKeyPath,
                                           NULL,
                                           mbedtls_ctr_drbg_random,
                                           &ctrDrbgCtx );

        if( result != 0 )
        {
            LogError( ( "Failed to read key from file: %s, result= %s : %s.",
                        pPrivateKeyPath,
                        mbedtlsHighLevelCodeOrDefault( result ),
                        mbedtlsLowLevelCodeOrDefault( result ) ) );
            status = MBEDTLS_INTERNAL_ERROR;
        }
    }

    if( status == MBEDTLS_SUCCESS )
    {
        /* Create CSR */
        mbedtls_x509write_csr_set_md_alg( &csrCtx, MBEDTLS_MD_SHA256 );
        mbedtls_x509write_csr_set_key( &csrCtx, &pkCtx );

        result = mbedtls_x509write_csr_set_key_usage( &csrCtx, MBEDTLS_X509_KU_DIGITAL_SIGNATURE );

        if( result == 0 )
        {
            result = mbedtls_x509write_csr_set_ns_cert_type( &csrCtx, MBEDTLS_X509_NS_CERT_TYPE_SSL_CLIENT );
        }

        if( result == 0 )
        {
            //TODO: Set this to device serial number / thing name
            result = mbedtls_x509write_csr_set_subject_name( &csrCtx, "CN=MyDevice" );
        }

        if( result == 0 )
        {
            result = mbedtls_x509write_csr_pem( &csrCtx,
                                                ( unsigned char * ) pCsrPemBuffer,
                                                csrPemBufferLength,
                                                mbedtls_ctr_drbg_random,
                                                &ctrDrbgCtx );
        }

        if( result < 0 )
        {
            LogError( ( "Failed to generate CSR. result= %s : %s.",
                        mbedtlsHighLevelCodeOrDefault( result ),
                        mbedtlsLowLevelCodeOrDefault( result ) ) );
            status = MBEDTLS_INTERNAL_ERROR;
        }
    }

    mbedtls_x509write_csr_free( &csrCtx );
    mbedtls_pk_free( &pkCtx );
    mbedtls_ctr_drbg_free( &ctrDrbgCtx );
    mbedtls_entropy_free( &entropyCtx );

    return status;
}

/*-----------------------------------------------------------*/



/*
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file iot_network_mbedtls.c
 * @brief Implementation of the network interface functions in iot_network.h
 * for mbed TLS.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdio.h>
#include <string.h>

/* mbed TLS network include. */
#include "iot_network_mbedtls.h"

/* mbed TLS includes. */
#include <mbedtls/ctr_drbg.h>
#include <mbedtls/entropy.h>
#include <mbedtls/error.h>
#include <mbedtls/net_sockets.h>
#include <mbedtls/pk.h>
#include <mbedtls/ssl.h>
#include <mbedtls/threading.h>
#include <mbedtls/x509_crt.h>

/* Error handling include. */
#include "private/iot_error.h"

/* Platform threads include. */
#include "platform/iot_threads.h"

/* Configure logs for the functions in this file. */
#ifdef IOT_LOG_LEVEL_NETWORK
    #define LIBRARY_LOG_LEVEL        IOT_LOG_LEVEL_NETWORK
#else
    #ifdef IOT_LOG_LEVEL_GLOBAL
        #define LIBRARY_LOG_LEVEL    IOT_LOG_LEVEL_GLOBAL
    #else
        #define LIBRARY_LOG_LEVEL    IOT_LOG_NONE
    #endif
#endif

#define LIBRARY_LOG_NAME    ( "NET" )
#include "iot_logging_setup.h"

/* Logging macro for mbed TLS errors. */
#if LIBRARY_LOG_LEVEL > IOT_LOG_NONE
    #define _logMbedtlsError( error, pConnection, pMessage )       \
    {                                                              \
        char pErrorMessage[ 80 ] = { 0 };                          \
        mbedtls_strerror( error, pErrorMessage, 80 );              \
                                                                   \
        if( pConnection != NULL )                                  \
        {                                                          \
            IotLogError( "(Network connection %p) %s error: %s. ", \
                         pConnection,                              \
                         pMessage,                                 \
                         pErrorMessage );                          \
        }                                                          \
        else                                                       \
        {                                                          \
            IotLogError( "%s error: %s. ",                         \
                         pMessage,                                 \
                         pErrorMessage );                          \
        }                                                          \
    }
#else /* if LIBRARY_LOG_LEVEL > IOT_LOG_NONE */
    #define _logMbedtlsError( error, pConnection, pMessage )
#endif /* if LIBRARY_LOG_LEVEL > IOT_LOG_NONE */

/*
 * Provide default values for undefined memory allocation functions.
 */
#ifndef IotNetwork_Malloc
    #include <stdlib.h>

/**
 * @brief Memory allocation. This function should have the same signature
 * as [malloc](http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html).
 */
    #define IotNetwork_Malloc    malloc
#endif
#ifndef IotNetwork_Free
    #include <stdlib.h>

/**
 * @brief Free memory. This function should have the same signature as
 * [free](http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html).
 */
    #define IotNetwork_Free    free
#endif

/*-----------------------------------------------------------*/

/**
 * @brief Represents a network connection.
 */
typedef struct _networkConnection
{
    bool secured;                                /**< @brief Whether this connection is secured. */
    mbedtls_net_context networkContext;          /**< @brief mbed TLS wrapper for system's sockets. */
    IotMutex_t networkMutex;                     /**< @brief Protects this network context from concurrent access. */

    IotNetworkReceiveCallback_t receiveCallback; /**< @brief Network receive callback, if any. */
    void * pReceiveContext;                      /**< @brief The context for the receive callback. */

    /**
     * @brief Secured connection context. Valid if `secured` is `true`.
     */
    struct
    {
        /* ALPN protocols formatted for mbed TLS. The second element of this array
         * is always NULL. */
        const char * pAlpnProtos[ 2 ];

        mbedtls_ssl_config config;   /**< @brief SSL connection configuration. */
        mbedtls_ssl_context context; /**< @brief SSL connection context. */

        /**
         * @brief Credentials for SSL connection.
         */
        struct
        {
            mbedtls_x509_crt rootCa;       /**< @brief Root CA certificate. */
            mbedtls_x509_crt clientCert;   /**< @brief Client certificate. */
            mbedtls_pk_context privateKey; /**< @brief Client certificate private key. */
        } credentials;
    } ssl;
} _networkConnection_t;

/*-----------------------------------------------------------*/

/**
 * @brief mbed TLS entropy context for generation of random numbers.
 */
static mbedtls_entropy_context _entropyContext;

/**
 * @brief mbed TLS CTR DRBG context for generation of random numbers.
 */
static mbedtls_ctr_drbg_context _ctrDrbgContext;

/**
 * @brief An #IotNetworkInterface_t that uses the functions in this file.
 */
const IotNetworkInterface_t IotNetworkMbedtls =
{
    .create             = IotNetworkMbedtls_Create,
    .setReceiveCallback = IotNetworkMbedtls_SetReceiveCallback,
    .send               = IotNetworkMbedtls_Send,
    .receive            = IotNetworkMbedtls_Receive,
    .close              = IotNetworkMbedtls_Close,
    .destroy            = IotNetworkMbedtls_Destroy
};

/*-----------------------------------------------------------*/

/**
 * @brief Initialize the mbed TLS structures in a network connection.
 *
 * @param[in] pNetworkConnection The network connection to initialize.
 */
static void _sslContextInit( _networkConnection_t * pNetworkConnection )
{
    mbedtls_ssl_config_init( &( pNetworkConnection->ssl.config ) );
    mbedtls_x509_crt_init( &( pNetworkConnection->ssl.credentials.rootCa ) );
    mbedtls_x509_crt_init( &( pNetworkConnection->ssl.credentials.clientCert ) );
    mbedtls_pk_init( &( pNetworkConnection->ssl.credentials.privateKey ) );
    mbedtls_ssl_init( &( pNetworkConnection->ssl.context ) );
}

/*-----------------------------------------------------------*/

/**
 * @brief Free the mbed TLS structures in a network connection.
 *
 * @param[in] pNetworkConnection The network connection with the contexts to free.
 */
static void _sslContextFree( _networkConnection_t * pNetworkConnection )
{
    mbedtls_ssl_free( &( pNetworkConnection->ssl.context ) );
    mbedtls_pk_free( &( pNetworkConnection->ssl.credentials.privateKey ) );
    mbedtls_x509_crt_free( &( pNetworkConnection->ssl.credentials.clientCert ) );
    mbedtls_x509_crt_free( &( pNetworkConnection->ssl.credentials.rootCa ) );
    mbedtls_ssl_config_free( &( pNetworkConnection->ssl.config ) );
}

/*-----------------------------------------------------------*/

/**
 * @brief Network receive thread.
 *
 * This thread polls the network socket and reads data when data is available.
 * It then invokes the receive callback, if any.
 *
 * @param[in] pArgument The connection associated with this receive thread.
 */
static void _receiveThread( void * pArgument )
{
    int pollStatus = 0;

    /* Cast function parameter to correct type. */
    _networkConnection_t * const pNetworkConnection = pArgument;

    /* Continuously poll the network connection for events. */
    while( true )
    {
        pollStatus = mbedtls_net_poll( &( pNetworkConnection->networkContext ),
                                       MBEDTLS_NET_POLL_READ,
                                       0xffffffff );

        if( pollStatus != MBEDTLS_NET_POLL_READ )
        {
            _logMbedtlsError( pollStatus, pNetworkConnection, "Error polling network connection." );
            break;
        }

        pNetworkConnection->receiveCallback( pNetworkConnection,
                                             pNetworkConnection->pReceiveContext );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Reads credentials from the filesystem.
 *
 * Uses mbed TLS to import the root CA certificate, client certificate, and
 * client certificate private key.
 * @param[in] pNetworkConnection Network connection for the imported credentials.
 * @param[in] pRootCaPath Path to the root CA certificate.
 * @param[in] pClientCertPath Path to the client certificate.
 * @param[in] pCertPrivateKeyPath Path to the client certificate private key.
 *
 * @return `true` if all credentials were successfully read; `false` otherwise.
 */
static bool _readCredentials( _networkConnection_t * pNetworkConnection,
                              const char * pRootCaPath,
                              const char * pClientCertPath,
                              const char * pCertPrivateKeyPath )
{
    IOT_FUNCTION_ENTRY( bool, true );
    int mbedtlsError = 0;

    /* Read the root CA certificate. */
    mbedtlsError = mbedtls_x509_crt_parse_file( &( pNetworkConnection->ssl.credentials.rootCa ),
                                                pRootCaPath );

    if( mbedtlsError < 0 )
    {
        _logMbedtlsError( mbedtlsError, pNetworkConnection, "Failed to read root CA certificate file." );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }
    else if( mbedtlsError > 0 )
    {
        IotLogWarn( "Failed to parse all certificates in %s; %d were parsed.",
                    pRootCaPath,
                    mbedtlsError );
    }

    /* Read the client certificate. */
    mbedtlsError = mbedtls_x509_crt_parse_file( &( pNetworkConnection->ssl.credentials.clientCert ),
                                                pClientCertPath );

    if( mbedtlsError < 0 )
    {
        _logMbedtlsError( mbedtlsError, pNetworkConnection, "Failed to read client certificate file." );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }
    else if( mbedtlsError > 0 )
    {
        IotLogWarn( "Failed to parse all certificates in %s; %d were parsed.",
                    pClientCertPath,
                    mbedtlsError );
    }

    /* Read the client certificate private key. */
    mbedtlsError = mbedtls_pk_parse_keyfile( &( pNetworkConnection->ssl.credentials.privateKey ),
                                             pCertPrivateKeyPath,
                                             NULL );

    if( mbedtlsError != 0 )
    {
        _logMbedtlsError( mbedtlsError, pNetworkConnection, "Failed to read client certificate private key file." );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    /* Set the credentials in the SSL configuration. */
    mbedtls_ssl_conf_ca_chain( &( pNetworkConnection->ssl.config ),
                               &( pNetworkConnection->ssl.credentials.rootCa ),
                               NULL );

    mbedtlsError = mbedtls_ssl_conf_own_cert( &( pNetworkConnection->ssl.config ),
                                              &( pNetworkConnection->ssl.credentials.clientCert ),
                                              &( pNetworkConnection->ssl.credentials.privateKey ) );

    if( mbedtlsError != 0 )
    {
        _logMbedtlsError( mbedtlsError, pNetworkConnection, "Failed to configure credentials." );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

/**
 * @brief Set up TLS on a TCP connection.
 *
 * @param[in] pNetworkConnection An established TCP connection.
 * @param[in] pServerName Remote host name, used for server name indication.
 * @param[in] pMbedtlsCredentials TLS setup parameters.
 *
 * @return #IOT_NETWORK_SUCCESS, #IOT_NETWORK_FAILURE, or #IOT_NETWORK_SYSTEM_ERROR.
 */
static IotNetworkError_t _tlsSetup( _networkConnection_t * pNetworkConnection,
                                    const char * pServerName,
                                    const IotNetworkCredentials_t * pMbedtlsCredentials )
{
    IOT_FUNCTION_ENTRY( IotNetworkError_t, IOT_NETWORK_SUCCESS );
    int mbedtlsError = 0;
    bool fragmentLengthValid = true;
    unsigned char mflCode = 0;
    uint32_t verifyResult = 0;

    /* Flags to track initialization. */
    bool sslContextInitialized = false;

    /* Initialize SSL configuration. */
    _sslContextInit( pNetworkConnection );
    sslContextInitialized = true;

    mbedtlsError = mbedtls_ssl_config_defaults( &( pNetworkConnection->ssl.config ),
                                                MBEDTLS_SSL_IS_CLIENT,
                                                MBEDTLS_SSL_TRANSPORT_STREAM,
                                                MBEDTLS_SSL_PRESET_DEFAULT );

    if( mbedtlsError != 0 )
    {
        _logMbedtlsError( mbedtlsError, pNetworkConnection, "Failed to set default SSL configuration." );

        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_FAILURE );
    }

    /* Set SSL authmode and the RNG context. */
    mbedtls_ssl_conf_authmode( &( pNetworkConnection->ssl.config ), MBEDTLS_SSL_VERIFY_REQUIRED );
    mbedtls_ssl_conf_rng( &( pNetworkConnection->ssl.config ), mbedtls_ctr_drbg_random, &_ctrDrbgContext );

    if( _readCredentials( pNetworkConnection,
                          pMbedtlsCredentials->pRootCa,
                          pMbedtlsCredentials->pClientCert,
                          pMbedtlsCredentials->pPrivateKey ) == false )
    {
        IotLogError( "(Network connection %p) Failed to read credentials.",
                     pNetworkConnection );

        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_FAILURE );
    }

    /* Set up ALPN if requested. */
    if( pMbedtlsCredentials->pAlpnProtos != NULL )
    {
        /* mbed TLS expects a NULL-terminated array of protocols. These pointers
         * must remain in-scope for the lifetime of the connection, so they are
         * stored as part of the connection context. */
        pNetworkConnection->ssl.pAlpnProtos[ 0 ] = pMbedtlsCredentials->pAlpnProtos;
        pNetworkConnection->ssl.pAlpnProtos[ 1 ] = NULL;

        mbedtlsError = mbedtls_ssl_conf_alpn_protocols( &( pNetworkConnection->ssl.config ),
                                                        pNetworkConnection->ssl.pAlpnProtos );

        if( mbedtlsError != 0 )
        {
            _logMbedtlsError( mbedtlsError, pNetworkConnection, "Failed to set ALPN protocols." );

            IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_FAILURE );
        }
    }

    /* Set TLS MFLN if requested. */
    if( pMbedtlsCredentials->maxFragmentLength > 0 )
    {
        /* Check for a supported fragment length. mbed TLS only supports 4 values. */
        switch( pMbedtlsCredentials->maxFragmentLength )
        {
            case 512UL:
                mflCode = MBEDTLS_SSL_MAX_FRAG_LEN_512;
                break;

            case 1024UL:
                mflCode = MBEDTLS_SSL_MAX_FRAG_LEN_1024;
                break;

            case 2048UL:
                mflCode = MBEDTLS_SSL_MAX_FRAG_LEN_2048;
                break;

            case 4096UL:
                mflCode = MBEDTLS_SSL_MAX_FRAG_LEN_4096;
                break;

            default:
                IotLogWarn( "Ignoring unsupported max fragment length %lu. Supported "
                            "values are 512, 1024, 2048, or 4096.",
                            pMbedtlsCredentials->maxFragmentLength );
                fragmentLengthValid = false;
                break;
        }

        /* Set MFLN if a valid fragment length is given. */
        if( fragmentLengthValid == true )
        {
            mbedtlsError = mbedtls_ssl_conf_max_frag_len( &( pNetworkConnection->ssl.config ),
                                                          mflCode );

            if( mbedtlsError != 0 )
            {
                _logMbedtlsError( mbedtlsError, pNetworkConnection, "Failed to set TLS MFLN." );

                IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_FAILURE );
            }
        }
    }

    /* Initialize the mbed TLS secured connection context. */
    mbedtlsError = mbedtls_ssl_setup( &( pNetworkConnection->ssl.context ),
                                      &( pNetworkConnection->ssl.config ) );

    if( mbedtlsError != 0 )
    {
        _logMbedtlsError( mbedtlsError, pNetworkConnection, "Failed to set up mbed TLS SSL context." );

        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_FAILURE );
    }

    /* Set the underlying IO for the TLS connection. */
    mbedtls_ssl_set_bio( &( pNetworkConnection->ssl.context ),
                         &( pNetworkConnection->networkContext ),
                         mbedtls_net_send,
                         NULL,
                         mbedtls_net_recv_timeout );

    /* Enable SNI if requested. */
    if( pMbedtlsCredentials->disableSni == false )
    {
        mbedtlsError = mbedtls_ssl_set_hostname( &( pNetworkConnection->ssl.context ),
                                                 pServerName );

        if( mbedtlsError != 0 )
        {
            _logMbedtlsError( mbedtlsError, pNetworkConnection, "Failed to set server name." );

            IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_FAILURE );
        }
    }

    /* Perform the TLS handshake. */
    do
    {
        mbedtlsError = mbedtls_ssl_handshake( &( pNetworkConnection->ssl.context ) );
    } while( ( mbedtlsError == MBEDTLS_ERR_SSL_WANT_READ ) || ( mbedtlsError == MBEDTLS_ERR_SSL_WANT_WRITE ) );

    if( mbedtlsError != 0 )
    {
        _logMbedtlsError( mbedtlsError, pNetworkConnection, "Failed to perform SSL handshake." );

        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_FAILURE );
    }

    /* Check result of certificate verification. */
    verifyResult = mbedtls_ssl_get_verify_result( &( pNetworkConnection->ssl.context ) );

    if( verifyResult != 0 )
    {
        IotLogError( "Failed to verify server certificate, result %lu.",
                     verifyResult );

        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_FAILURE );
    }

    /* Clean up on error. */
    IOT_FUNCTION_CLEANUP_BEGIN();

    if( status != IOT_NETWORK_SUCCESS )
    {
        if( sslContextInitialized == true )
        {
            _sslContextFree( pNetworkConnection );
        }
    }
    else
    {
        /* TLS setup succeeded; set the secured flag. */
        pNetworkConnection->secured = true;

        IotLogInfo( "(Network connection %p) TLS handshake successful.",
                    pNetworkConnection );
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkMbedtls_Init( void )
{
    int mbedtlsError = 0;
    IotNetworkError_t status = IOT_NETWORK_SUCCESS;

    /* Set the mutex functions for mbed TLS thread safety. */
    mbedtls_threading_set_alt( mbedtlsMutex_Init,
                               mbedtlsMutex_Free,
                               mbedtlsMutex_Lock,
                               mbedtlsMutex_Unlock );

    /* Initialize contexts for random number generation. */
    mbedtls_entropy_init( &_entropyContext );
    mbedtls_ctr_drbg_init( &_ctrDrbgContext );

    /* Seed the random number generator. */
    mbedtlsError = mbedtls_ctr_drbg_seed( &_ctrDrbgContext,
                                          mbedtls_entropy_func,
                                          &_entropyContext,
                                          NULL,
                                          0 );

    if( mbedtlsError != 0 )
    {
        status = IOT_NETWORK_FAILURE;
        _logMbedtlsError( mbedtlsError, NULL, "Failed to seed PRNG in initialization." );

        IotNetworkMbedtls_Cleanup();
    }
    else
    {
        IotLogInfo( "Network library initialized." );
    }

    return status;
}

/*-----------------------------------------------------------*/

void IotNetworkMbedtls_Cleanup( void )
{
    /* Free the contexts for random number generation. */
    mbedtls_ctr_drbg_free( &_ctrDrbgContext );
    mbedtls_entropy_free( &_entropyContext );

    /* Clear the mutex functions for mbed TLS thread safety. */
    mbedtls_threading_free_alt();

    IotLogInfo( "Network library cleanup done." );
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkMbedtls_Create( void * pConnectionInfo,
                                            void * pCredentialInfo,
                                            void ** pConnection )
{
    IOT_FUNCTION_ENTRY( IotNetworkError_t, IOT_NETWORK_SUCCESS );
    int mbedtlsError = 0;
    _networkConnection_t * pNewNetworkConnection = NULL;
    char pServerPort[ 6 ] = { 0 };

    /* Flags to track initialization. */
    bool networkContextInitialized = false, networkMutexCreated = false;

    /* Cast function parameters to correct types. */
    const IotNetworkServerInfo_t * const pServerInfo = pConnectionInfo;
    const IotNetworkCredentials_t * const pMbedtlsCredentials = pCredentialInfo;
    _networkConnection_t ** const pNetworkConnection = ( _networkConnection_t ** const ) pConnection;

    /* Allocate memory for a new connection. */
    pNewNetworkConnection = IotNetwork_Malloc( sizeof( _networkConnection_t ) );

    if( pNewNetworkConnection == NULL )
    {
        IotLogError( "Failed to allocate memory for new network connection." );

        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_NO_MEMORY );
    }

    /* Clear connection data. */
    memset( pNewNetworkConnection, 0x00, sizeof( _networkConnection_t ) );

    /* Initialize the network context mutex. */
    networkMutexCreated = IotMutex_Create( &( pNewNetworkConnection->networkMutex ),
                                           false );

    /* Initialize mbed TLS network context. */
    mbedtls_net_init( &( pNewNetworkConnection->networkContext ) );
    networkContextInitialized = true;

    /* mbed TLS expects the port to be a decimal string. */
    mbedtlsError = snprintf( pServerPort, 6, "%hu", pServerInfo->port );

    if( mbedtlsError < 0 )
    {
        IotLogError( "Failed to convert port %hu to decimal string.",
                     pServerInfo->port );

        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_FAILURE );
    }

    /* Establish a TCP connection. */
    mbedtlsError = mbedtls_net_connect( &( pNewNetworkConnection->networkContext ),
                                        pServerInfo->pHostName,
                                        pServerPort,
                                        MBEDTLS_NET_PROTO_TCP );

    if( mbedtlsError != 0 )
    {
        _logMbedtlsError( mbedtlsError, NULL, "Failed to establish connection." );

        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_FAILURE );
    }

    /* Set the mbed TLS network context to blocking mode. */
    mbedtlsError = mbedtls_net_set_block( &( pNewNetworkConnection->networkContext ) );

    if( mbedtlsError != 0 )
    {
        _logMbedtlsError( mbedtlsError, pNewNetworkConnection, "Failed to set blocking mode." );

        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_FAILURE );
    }

    /* Set up TLS if credentials are given. */
    if( pMbedtlsCredentials != NULL )
    {
        status = _tlsSetup( pNewNetworkConnection,
                            pServerInfo->pHostName,
                            pMbedtlsCredentials );
    }

    IOT_FUNCTION_CLEANUP_BEGIN();

    /* Clean up on error. */
    if( status != IOT_NETWORK_SUCCESS )
    {
        if( networkMutexCreated == true )
        {
            IotMutex_Destroy( &( pNewNetworkConnection->networkMutex ) );
        }

        if( networkContextInitialized == true )
        {
            mbedtls_net_free( &( pNewNetworkConnection->networkContext ) );
        }

        if( pNewNetworkConnection != NULL )
        {
            IotNetwork_Free( pNewNetworkConnection );
        }
    }
    else
    {
        IotLogInfo( "(Network connection %p) New network connection established.",
                    pNewNetworkConnection );

        /* Set the output parameter. */
        *pNetworkConnection = pNewNetworkConnection;
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkMbedtls_SetReceiveCallback( void * pConnection,
                                                        IotNetworkReceiveCallback_t receiveCallback,
                                                        void * pContext )
{
    IotNetworkError_t status = IOT_NETWORK_SUCCESS;

    /* Cast function parameter to correct type. */
    _networkConnection_t * const pNetworkConnection = pConnection;

    /* Set the callback and parameter. */
    pNetworkConnection->receiveCallback = receiveCallback;
    pNetworkConnection->pReceiveContext = pContext;

    /* Create the thread to receive incoming data. */
    if( Iot_CreateDetachedThread( _receiveThread,
                                  pNetworkConnection,
                                  IOT_THREAD_DEFAULT_PRIORITY,
                                  IOT_THREAD_DEFAULT_STACK_SIZE ) == false )
    {
        IotLogError( "(Network connection %p) Failed to create thread for receiving data.",
                     pNetworkConnection );

        status = IOT_NETWORK_SYSTEM_ERROR;
    }
    else
    {
    }

    return status;
}

/*-----------------------------------------------------------*/

size_t IotNetworkMbedtls_Send( void * pConnection,
                               const uint8_t * pMessage,
                               size_t messageLength )
{
    int mbedtlsError = 0;
    size_t bytesSent = 0;

    /* Cast function parameter to correct type. */
    _networkConnection_t * const pNetworkConnection = pConnection;

    IotLogDebug( "(Network connection %p) Sending %lu bytes.",
                 pNetworkConnection,
                 ( unsigned long ) messageLength );

    IotMutex_Lock( &( pNetworkConnection->networkMutex ) );

    /* Check that it's possible to send right now. */
    mbedtlsError = mbedtls_net_poll( &( pNetworkConnection->networkContext ),
                                     MBEDTLS_NET_POLL_WRITE,
                                     0 );

    if( mbedtlsError == MBEDTLS_NET_POLL_WRITE )
    {
        /* Choose the send function based on state of the SSL context. */
        if( pNetworkConnection->secured == true )
        {
            /* Secured send. */
            while( bytesSent < messageLength )
            {
                mbedtlsError = mbedtls_ssl_write( &( pNetworkConnection->ssl.context ),
                                                  pMessage + bytesSent,
                                                  messageLength - bytesSent );

                if( ( mbedtlsError == MBEDTLS_ERR_SSL_WANT_WRITE ) ||
                    ( mbedtlsError == MBEDTLS_ERR_SSL_WANT_READ ) )
                {
                    /* Call SSL write again with the same arguments. */
                    continue;
                }
                else if( mbedtlsError < 0 )
                {
                    /* Error sending, exit. */
                    break;
                }
                else
                {
                    bytesSent += ( size_t ) mbedtlsError;
                }
            }
        }
        else
        {
            /* Unsecured send. */
            mbedtlsError = mbedtls_net_send( &( pNetworkConnection->networkContext ),
                                             pMessage,
                                             messageLength );

            if( mbedtlsError > 0 )
            {
                bytesSent = ( size_t ) mbedtlsError;
            }
        }

        /* Log errors. */
        if( mbedtlsError < 0 )
        {
            _logMbedtlsError( mbedtlsError, pNetworkConnection, "Failed to send." );
            bytesSent = 0;
        }
    }
    else
    {
        _logMbedtlsError( mbedtlsError, pNetworkConnection, "Cannot send right now." );
    }

    IotMutex_Unlock( &( pNetworkConnection->networkMutex ) );

    return bytesSent;
}

/*-----------------------------------------------------------*/

size_t IotNetworkMbedtls_Receive( void * pConnection,
                                  uint8_t * pBuffer,
                                  size_t bytesRequested )
{
    int mbedtlsError = 0;
    size_t bytesReceived = 0;

    /* Cast function parameter to correct type. */
    _networkConnection_t * const pNetworkConnection = pConnection;

    IotMutex_Lock( &( pNetworkConnection->networkMutex ) );

    while( bytesReceived < bytesRequested )
    {
        /* Choose the receive function based on state of the SSL context. */
        if( pNetworkConnection->secured == true )
        {
            mbedtlsError = mbedtls_ssl_read( &( pNetworkConnection->ssl.context ),
                                             pBuffer + bytesReceived,
                                             bytesRequested - bytesReceived );
        }
        else
        {
            mbedtlsError = mbedtls_net_recv( &( pNetworkConnection->networkContext ),
                                             pBuffer + bytesReceived,
                                             bytesRequested - bytesReceived );
        }

        if( ( mbedtlsError == MBEDTLS_ERR_SSL_WANT_WRITE ) ||
            ( mbedtlsError == MBEDTLS_ERR_SSL_WANT_READ ) )
        {
            /* Call receive again with the same arguments. */
            continue;
        }
        else if( mbedtlsError < 0 )
        {
            /* Error receiving, exit. */
            _logMbedtlsError( mbedtlsError, pNetworkConnection, "Failed to receive." );
            break;
        }
        else
        {
            bytesReceived += ( size_t ) mbedtlsError;
        }
    }

    IotMutex_Unlock( &( pNetworkConnection->networkMutex ) );

    return bytesReceived;
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkMbedtls_Close( void * pConnection )
{
    return IOT_NETWORK_FAILURE;
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkMbedtls_Destroy( void * pConnection )
{
    return IOT_NETWORK_FAILURE;
}

/*-----------------------------------------------------------*/

void IotNetworkMbedtls_GetServerInfo( void * pConnection,
                                      IotMetricsTcpConnection_t * pServerInfo )
{
}

/*-----------------------------------------------------------*/

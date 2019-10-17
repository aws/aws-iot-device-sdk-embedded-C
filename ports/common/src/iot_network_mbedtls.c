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

#if !defined( _WIN32 ) && !defined( _WIN64 )
    #include <arpa/inet.h>
    #include <netdb.h>
    #include <sys/socket.h>
#endif

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
#include "iot_error.h"

/* Platform clock include. */
#include "platform/iot_clock.h"

/* Platform threads include. */
#include "platform/iot_threads.h"

/* Atomic include. */
#include "iot_atomic.h"

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
    #define _logLibraryError( error, pMessage )       \
    {                                                 \
        char pErrorMessage[ 80 ] = { 0 };             \
        mbedtls_strerror( error, pErrorMessage, 80 ); \
                                                      \
        IotLogError( "%s error: %s. ",                \
                     pMessage,                        \
                     pErrorMessage );                 \
    }

    #define _logConnectionError( error, pConnection, pMessage ) \
    {                                                           \
        char pErrorMessage[ 80 ] = { 0 };                       \
        mbedtls_strerror( error, pErrorMessage, 80 );           \
                                                                \
        IotLogError( "(Network connection %p) %s error: %s. ",  \
                     pConnection,                               \
                     pMessage,                                  \
                     pErrorMessage );                           \
    }
#else /* if LIBRARY_LOG_LEVEL > IOT_LOG_NONE */
    #define _logLibraryError( error, pMessage )
    #define _logConnectionError( error, pConnection, pMessage )
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

/**
 * @brief The timeout for the mbed TLS poll call in the receive thread.
 *
 * After the timeout expires, the receive thread will check will queries the
 * connection flags to ensure that the connection is still open. Therefore,
 * this flag represents the maximum time it takes for the receive thread to
 * detect a closed connection.
 *
 * This timeout is also used to wait for all receive threads to exit during
 * global cleanup.
 *
 * Since this value only affects the shutdown sequence, it generally does not
 * need to be changed.
 */
#ifndef IOT_NETWORK_MBEDTLS_POLL_TIMEOUT_MS
    #define IOT_NETWORK_MBEDTLS_POLL_TIMEOUT_MS    ( 1000UL )
#endif

/* Flags to track connection state. */
#define FLAG_SECURED                 ( 0x00000001UL ) /**< @brief Secured connection. */
#define FLAG_HAS_RECEIVE_CALLBACK    ( 0x00000002UL ) /**< @brief Connection has receive callback. */
#define FLAG_CONNECTION_DESTROYED    ( 0x00000004UL ) /**< @brief Connection has been destroyed. */

/*-----------------------------------------------------------*/

/**
 * @brief Represents a network connection.
 */
typedef struct _networkConnection
{
    uint32_t flags;                              /**< @brief Connection state flags. */
    mbedtls_net_context networkContext;          /**< @brief mbed TLS wrapper for system's sockets. */
    IotMutex_t contextMutex;                     /**< @brief Protects this network context from concurrent access. */

    IotNetworkReceiveCallback_t receiveCallback; /**< @brief Network receive callback, if any. */
    void * pReceiveContext;                      /**< @brief The context for the receive callback. */
    IotMutex_t callbackMutex;                    /**< @brief Synchronizes the receive callback with calls to destroy. */
    IotSemaphore_t destroyNotification;          /**< @brief Notifies the receive callback that the connection was destroyed. */

    /**
     * @brief Secured connection context. Valid if #FLAG_SECURED is set.
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
 * @brief Tracks the number of active receive threads.
 */
static uint32_t _receiveThreadCount = 0;

/**
 * @brief An #IotNetworkInterface_t that uses the functions in this file.
 */
static const IotNetworkInterface_t _networkMbedtls =
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
 * @brief Initializes a new mutex. Used by mbed TLS to provide thread-safety.
 *
 * Sets the valid member of `mbedtls_threading_mutex_t`.
 *
 * @param[in] pMutex The mutex to initialize.
 */
static void _mbedtlsMutexInit( mbedtls_threading_mutex_t * pMutex )
{
    pMutex->valid = IotMutex_Create( &( pMutex->mutex ), false );
}

/*-----------------------------------------------------------*/

/**
 * @brief Frees a mutex. Used by mbed TLS to provide thread-safety.
 *
 * @param[in] pMutex The mutex to destroy.
 */
static void _mbedtlsMutexFree( mbedtls_threading_mutex_t * pMutex )
{
    if( pMutex->valid == true )
    {
        IotMutex_Destroy( &( pMutex->mutex ) );
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Locks a mutex. Used by mbed TLS to provide thread-safety.
 *
 * @param[in] pMutex The mutex to lock.
 *
 * @return `0` on success; one of `MBEDTLS_ERR_THREADING_BAD_INPUT_DATA`
 * or `MBEDTLS_ERR_THREADING_MUTEX_ERROR` on error.
 */
static int _mbedtlsMutexLock( mbedtls_threading_mutex_t * pMutex )
{
    int status = 0;

    if( pMutex->valid == false )
    {
        status = MBEDTLS_ERR_THREADING_BAD_INPUT_DATA;
    }
    else
    {
        IotMutex_Lock( &( pMutex->mutex ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

/**
 * @brief Unlocks a mutex. Used by mbed TLS to provide thread-safety.
 *
 * @param[in] pMutex The mutex to unlock.
 *
 * @return `0` on success; one of `MBEDTLS_ERR_THREADING_BAD_INPUT_DATA`
 * or `MBEDTLS_ERR_THREADING_MUTEX_ERROR` on error.
 */
static int _mbedtlsMutexUnlock( mbedtls_threading_mutex_t * pMutex )
{
    int status = 0;

    if( pMutex->valid == false )
    {
        status = MBEDTLS_ERR_THREADING_BAD_INPUT_DATA;
    }
    else
    {
        IotMutex_Unlock( &( pMutex->mutex ) );
    }

    return status;
}

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
 * @brief Destroy a network connection.
 *
 * @param[in] pNetworkConnection The network connection to destroy.
 */
static void _destroyConnection( _networkConnection_t * pNetworkConnection )
{
    /* Clean up the SSL context of secured connections. */
    if( ( pNetworkConnection->flags & FLAG_SECURED ) == FLAG_SECURED )
    {
        _sslContextFree( pNetworkConnection );
    }

    /* Destroy synchronization objects. */
    IotMutex_Destroy( &( pNetworkConnection->contextMutex ) );
    IotMutex_Destroy( &( pNetworkConnection->callbackMutex ) );

    if( ( pNetworkConnection->flags & FLAG_HAS_RECEIVE_CALLBACK ) == FLAG_HAS_RECEIVE_CALLBACK )
    {
        IotSemaphore_Destroy( &( pNetworkConnection->destroyNotification ) );
    }

    /* Free memory. */
    IotNetwork_Free( pNetworkConnection );
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
    mbedtls_net_context context;

    /* Cast function parameter to correct type. */
    _networkConnection_t * const pNetworkConnection = pArgument;

    /* Record the context to poll. */
    IotMutex_Lock( &( pNetworkConnection->contextMutex ) );
    context = pNetworkConnection->networkContext;
    IotMutex_Unlock( &( pNetworkConnection->contextMutex ) );

    /* Continuously poll the network connection for events. */
    while( true )
    {
        pollStatus = mbedtls_net_poll( &context,
                                       MBEDTLS_NET_POLL_READ,
                                       IOT_NETWORK_MBEDTLS_POLL_TIMEOUT_MS );

        if( pollStatus < 0 )
        {
            /* Error during poll. */
            _logConnectionError( pollStatus, pNetworkConnection, "Error polling network connection." );
            break;
        }
        else
        {
            /* Invoke receive callback if data is available. */
            if( pollStatus == MBEDTLS_NET_POLL_READ )
            {
                IotMutex_Lock( &( pNetworkConnection->callbackMutex ) );

                /* Only run the receive callback if the connection has not been
                 * destroyed. */
                if( ( pNetworkConnection->flags & FLAG_CONNECTION_DESTROYED ) == 0 )
                {
                    pNetworkConnection->receiveCallback( pNetworkConnection,
                                                         pNetworkConnection->pReceiveContext );
                }

                IotMutex_Unlock( &( pNetworkConnection->callbackMutex ) );
            }
        }
    }

    /* Wait for the call to network destroy, then destroy the connection. */
    IotSemaphore_Wait( &( pNetworkConnection->destroyNotification ) );
    _destroyConnection( pNetworkConnection );

    IotLogDebug( "(Network connection %p) Receive thread terminating.", pNetworkConnection );

    ( void ) Atomic_Decrement_u32( &_receiveThreadCount );
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
        _logConnectionError( mbedtlsError, pNetworkConnection, "Failed to read root CA certificate file." );

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
        _logConnectionError( mbedtlsError, pNetworkConnection, "Failed to read client certificate file." );

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
        _logConnectionError( mbedtlsError, pNetworkConnection, "Failed to read client certificate private key file." );

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
        _logConnectionError( mbedtlsError, pNetworkConnection, "Failed to configure credentials." );

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
        _logConnectionError( mbedtlsError, pNetworkConnection, "Failed to set default SSL configuration." );

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
            _logConnectionError( mbedtlsError, pNetworkConnection, "Failed to set ALPN protocols." );

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
                _logConnectionError( mbedtlsError, pNetworkConnection, "Failed to set TLS MFLN." );

                IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_FAILURE );
            }
        }
    }

    /* Initialize the mbed TLS secured connection context. */
    mbedtlsError = mbedtls_ssl_setup( &( pNetworkConnection->ssl.context ),
                                      &( pNetworkConnection->ssl.config ) );

    if( mbedtlsError != 0 )
    {
        _logConnectionError( mbedtlsError, pNetworkConnection, "Failed to set up mbed TLS SSL context." );

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
            _logConnectionError( mbedtlsError, pNetworkConnection, "Failed to set server name." );

            IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_FAILURE );
        }
    }

    /* Perform the TLS handshake. */
    do
    {
        mbedtlsError = mbedtls_ssl_handshake( &( pNetworkConnection->ssl.context ) );
    } while( ( mbedtlsError == MBEDTLS_ERR_SSL_WANT_READ ) ||
             ( mbedtlsError == MBEDTLS_ERR_SSL_WANT_WRITE ) );

    if( mbedtlsError != 0 )
    {
        _logConnectionError( mbedtlsError, pNetworkConnection, "Failed to perform SSL handshake." );

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
        pNetworkConnection->flags |= FLAG_SECURED;

        IotLogInfo( "(Network connection %p) TLS handshake successful.",
                    pNetworkConnection );
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

const IotNetworkInterface_t * IotNetworkMbedtls_GetInterface( void )
{
    return &_networkMbedtls;
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkMbedtls_Init( void )
{
    IotNetworkError_t status = IOT_NETWORK_SUCCESS;
    int mbedtlsError = 0;

    /* Clear the counter of receive threads. */
    _receiveThreadCount = 0;

    /* Set the mutex functions for mbed TLS thread safety. */
    mbedtls_threading_set_alt( _mbedtlsMutexInit,
                               _mbedtlsMutexFree,
                               _mbedtlsMutexLock,
                               _mbedtlsMutexUnlock );

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
        _logLibraryError( mbedtlsError, "Failed to seed PRNG in initialization." );
        status = IOT_NETWORK_FAILURE;
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
    /* Atomically read the receive thread count by adding 0 to it. Sleep and
     * wait for all receive threads to exit. */
    while( Atomic_Add_u32( &_receiveThreadCount, 0 ) > 0 )
    {
        IotClock_SleepMs( IOT_NETWORK_MBEDTLS_POLL_TIMEOUT_MS );
    }

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
    bool networkContextInitialized = false, networkMutexCreated = false, callbackMutexCreated = false;

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
    networkMutexCreated = IotMutex_Create( &( pNewNetworkConnection->contextMutex ),
                                           false );

    if( networkMutexCreated == false )
    {
        IotLogError( "Failed to create mutex for network context." );

        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_FAILURE );
    }

    /* Initialize the mutex for the receive callback. */
    callbackMutexCreated = IotMutex_Create( &( pNewNetworkConnection->callbackMutex ),
                                            true );

    if( callbackMutexCreated == false )
    {
        IotLogError( "Failed to create mutex for receive callback." );

        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_FAILURE );
    }

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
        _logLibraryError( mbedtlsError, "Failed to establish connection." );

        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_FAILURE );
    }

    /* Set the mbed TLS network context to blocking mode. */
    mbedtlsError = mbedtls_net_set_block( &( pNewNetworkConnection->networkContext ) );

    if( mbedtlsError != 0 )
    {
        _logConnectionError( mbedtlsError, pNewNetworkConnection, "Failed to set blocking mode." );

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
            IotMutex_Destroy( &( pNewNetworkConnection->contextMutex ) );
        }

        if( callbackMutexCreated == true )
        {
            IotMutex_Destroy( &( pNewNetworkConnection->callbackMutex ) );
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
    IOT_FUNCTION_ENTRY( IotNetworkError_t, IOT_NETWORK_SUCCESS );

    /* Cast function parameter to correct type. */
    _networkConnection_t * const pNetworkConnection = pConnection;

    /* Flags to track initialization. */
    bool notifyInitialized = false, countIncremented = false;

    /* Initialize the semaphore that notifies the receive thread of connection
     * destruction. */
    notifyInitialized = IotSemaphore_Create( &( pNetworkConnection->destroyNotification ),
                                             0,
                                             1 );

    if( notifyInitialized == false )
    {
        IotLogError( "(Network connection %p) Failed to create semaphore for "
                     "receive thread.", pNetworkConnection );

        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
    }

    /* Set the callback and parameter. */
    pNetworkConnection->receiveCallback = receiveCallback;
    pNetworkConnection->pReceiveContext = pContext;

    /* Set the receive callback flag and increment the count of receive threads. */
    pNetworkConnection->flags |= FLAG_HAS_RECEIVE_CALLBACK;
    ( void ) Atomic_Increment_u32( &_receiveThreadCount );
    countIncremented = true;

    /* Create the thread to receive incoming data. */
    if( Iot_CreateDetachedThread( _receiveThread,
                                  pNetworkConnection,
                                  IOT_THREAD_DEFAULT_PRIORITY,
                                  IOT_THREAD_DEFAULT_STACK_SIZE ) == false )
    {
        IotLogError( "(Network connection %p) Failed to create thread for receiving data.",
                     pNetworkConnection );

        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
    }

    /* Clean up on error. */
    IOT_FUNCTION_CLEANUP_BEGIN();

    if( status != IOT_NETWORK_SUCCESS )
    {
        if( notifyInitialized == true )
        {
            IotSemaphore_Destroy( &( pNetworkConnection->destroyNotification ) );
        }

        if( countIncremented == true )
        {
            pNetworkConnection->flags &= ~FLAG_HAS_RECEIVE_CALLBACK;
            ( void ) Atomic_Decrement_u32( &_receiveThreadCount );
        }
    }
    else
    {
        IotLogDebug( "(Network connection %p) Receive callback set.",
                     pNetworkConnection );
    }

    IOT_FUNCTION_CLEANUP_END();
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

    IotMutex_Lock( &( pNetworkConnection->contextMutex ) );

    /* Check that it's possible to send right now. */
    mbedtlsError = mbedtls_net_poll( &( pNetworkConnection->networkContext ),
                                     MBEDTLS_NET_POLL_WRITE,
                                     0 );

    if( mbedtlsError == MBEDTLS_NET_POLL_WRITE )
    {
        /* Choose the send function based on state of the SSL context. */
        if( ( pNetworkConnection->flags & FLAG_SECURED ) == FLAG_SECURED )
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
            _logConnectionError( mbedtlsError, pNetworkConnection, "Failed to send." );
            bytesSent = 0;
        }
    }
    else
    {
        _logConnectionError( mbedtlsError, pNetworkConnection, "Cannot send right now." );
    }

    IotMutex_Unlock( &( pNetworkConnection->contextMutex ) );

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

    while( bytesReceived < bytesRequested )
    {
        IotMutex_Lock( &( pNetworkConnection->contextMutex ) );

        /* Choose the receive function based on state of the SSL context. */
        if( ( pNetworkConnection->flags & FLAG_SECURED ) == FLAG_SECURED )
        {
            mbedtlsError = mbedtls_ssl_read( &( pNetworkConnection->ssl.context ),
                                             pBuffer + bytesReceived,
                                             bytesRequested - bytesReceived );
        }
        else
        {
            mbedtlsError = mbedtls_net_recv_timeout( &( pNetworkConnection->networkContext ),
                                                     pBuffer + bytesReceived,
                                                     bytesRequested - bytesReceived,
                                                     IOT_NETWORK_MBEDTLS_POLL_TIMEOUT_MS );
        }

        IotMutex_Unlock( &( pNetworkConnection->contextMutex ) );

        if( ( mbedtlsError == MBEDTLS_ERR_SSL_WANT_WRITE ) ||
            ( mbedtlsError == MBEDTLS_ERR_SSL_WANT_READ ) ||
            ( mbedtlsError == MBEDTLS_ERR_SSL_TIMEOUT ) )
        {
            /* Call receive again with the same arguments. */
            continue;
        }
        else if( mbedtlsError < 0 )
        {
            /* Error receiving, exit. */
            _logConnectionError( mbedtlsError, pNetworkConnection, "Failed to receive." );
            break;
        }
        else
        {
            bytesReceived += ( size_t ) mbedtlsError;
        }
    }

    return bytesReceived;
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkMbedtls_Close( void * pConnection )
{
    int mbedtlsError = 0;

    /* Cast function parameter to correct type. */
    _networkConnection_t * const pNetworkConnection = pConnection;

    IotMutex_Lock( &( pNetworkConnection->contextMutex ) );

    /* Notify the server that the SSL connection is being closed. */
    if( ( pNetworkConnection->flags & FLAG_SECURED ) == FLAG_SECURED )
    {
        do
        {
            mbedtlsError = mbedtls_ssl_close_notify( &( pNetworkConnection->ssl.context ) );
        } while( ( mbedtlsError == MBEDTLS_ERR_SSL_WANT_READ ) ||
                 ( mbedtlsError == MBEDTLS_ERR_SSL_WANT_WRITE ) );

        if( mbedtlsError != 0 )
        {
            _logConnectionError( mbedtlsError, pNetworkConnection, "Failed to notify peer of SSL connection close." );
        }
        else
        {
            IotLogInfo( "(Network connection %p) TLS session terminated.",
                        pNetworkConnection );
        }
    }

    /* Shutdown and close the network connection. */
    mbedtls_net_free( &( pNetworkConnection->networkContext ) );

    IotMutex_Unlock( &( pNetworkConnection->contextMutex ) );

    IotLogInfo( "(Network connection %p) Connection closed.", pNetworkConnection );

    return IOT_NETWORK_SUCCESS;
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkMbedtls_Destroy( void * pConnection )
{
    /* Cast function parameter to correct type. */
    _networkConnection_t * const pNetworkConnection = pConnection;

    /* Shutdown and close the network connection. */
    IotMutex_Lock( &( pNetworkConnection->callbackMutex ) );
    mbedtls_net_free( &( pNetworkConnection->networkContext ) );
    pNetworkConnection->flags |= FLAG_CONNECTION_DESTROYED;
    IotMutex_Unlock( &( pNetworkConnection->callbackMutex ) );

    /* Check if this connection has a receive callback. If it does not, it can
     * be destroyed here. Otherwise, notify the receive callback that destroy
     * has been called and rely on the receive callback to clean up. */
    if( ( pNetworkConnection->flags & FLAG_HAS_RECEIVE_CALLBACK ) == 0 )
    {
        _destroyConnection( pNetworkConnection );
    }
    else
    {
        IotSemaphore_Post( &( pNetworkConnection->destroyNotification ) );
    }

    return IOT_NETWORK_SUCCESS;
}

/*-----------------------------------------------------------*/

void IotNetworkMbedtls_GetServerInfo( void * pConnection,
                                      IotMetricsTcpConnection_t * pServerInfo )
{
    int status = 0, portLength = 0;
    struct sockaddr_storage server = { 0 };
    socklen_t length = sizeof( struct sockaddr_storage );
    const void * pServerAddress = NULL;
    char * pAddressStart = NULL;
    const char * pPortFormat = NULL;
    uint16_t remotePort = 0;
    size_t addressLength = 0;
    const _networkConnection_t * pNetworkConnection = NULL;

    /* Cast function parameter to correct type. */
    if( ( pConnection != NULL ) && ( pServerInfo != NULL ) )
    {
        pNetworkConnection = pConnection;

        /* Get peer info. */
        status = getpeername( pNetworkConnection->networkContext.fd,
                              ( struct sockaddr * ) &server,
                              &length );
    }
    else
    {
        status = IOT_NETWORK_BAD_PARAMETER;
    }

    if( status == 0 )
    {
        /* Calculate the pointer to the IP address and get the remote port based
         * on protocol version. */
        if( server.ss_family == AF_INET )
        {
            /* IPv4. */
            pServerAddress = &( ( ( struct sockaddr_in * ) &server )->sin_addr );
            remotePort = ntohs( ( ( struct sockaddr_in * ) &server )->sin_port );

            /* Print the IPv4 address at the start of the address buffer. */
            pAddressStart = pServerInfo->pRemoteAddress;
            addressLength = IOT_METRICS_IP_ADDRESS_LENGTH;
            pPortFormat = ":%hu";
        }
        else
        {
            /* IPv6. */
            pServerAddress = &( ( ( struct sockaddr_in6 * ) &server )->sin6_addr );
            remotePort = ntohs( ( ( struct sockaddr_in6 * ) &server )->sin6_port );

            /* Enclose the IPv6 address with []. */
            pServerInfo->pRemoteAddress[ 0 ] = '[';
            pAddressStart = pServerInfo->pRemoteAddress + 1;
            addressLength = IOT_METRICS_IP_ADDRESS_LENGTH - 1;
            pPortFormat = "]:%hu";
        }

        /* Convert IP address to text. */
        if( inet_ntop( server.ss_family,
                       pServerAddress,
                       pAddressStart,
                       addressLength ) != NULL )
        {
            /* Add the port to the end of the address. */
            addressLength = strlen( pServerInfo->pRemoteAddress );

            portLength = snprintf( &( pServerInfo->pRemoteAddress[ addressLength ] ),
                                   7,
                                   pPortFormat,
                                   remotePort );

            if( portLength > 0 )
            {
                pServerInfo->addressLength = addressLength + ( size_t ) portLength;

                IotLogInfo( "(Socket %d) Collecting network metrics for %s.",
                            pNetworkConnection->networkContext.fd,
                            pServerInfo->pRemoteAddress );
            }
            else
            {
                IotLogError( "(Socket %d) Failed to add port to IP address buffer." );
            }
        }
        else
        {
            IotLogError( "(Socket %d) Failed to convert IP address to text format.",
                         pNetworkConnection->networkContext.fd );
        }
    }
    else
    {
        IotLogError( "(Socket %d) Failed to query peer name.",
                     pNetworkConnection->networkContext.fd );
    }
}

/*-----------------------------------------------------------*/

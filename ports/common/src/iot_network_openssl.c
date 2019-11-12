/*
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file iot_network_openssl.c
 * @brief Implementation of the network interface functions in iot_network.h
 * for systems with OpenSSL.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdbool.h>
#include <string.h>
#include <unistd.h>

/* POSIX includes. */
#include <errno.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <sys/ioctl.h>

/* Sockets includes. */
#include <arpa/inet.h>
#include <netdb.h>
#include <sys/socket.h>

/* OpenSSL includes. */
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/ssl.h>

/* OpenSSL network include. */
#include "iot_network_openssl.h"

/* Platform threads include. */
#include "platform/iot_threads.h"

/* Error handling include. */
#include "iot_error.h"

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
    int socket;                                  /**< @brief Socket associated with this connection. */
    SSL * pSslContext;                           /**< @brief SSL context for connection. */
    IotMutex_t sslMutex;                         /**< @brief Prevents concurrent use of the SSL context. */

    bool receiveThreadCreated;                   /**< @brief Whether a receive thread exists for this connection. */
    pthread_t receiveThread;                     /**< @brief Thread that handles receiving on this connection. */

    IotNetworkReceiveCallback_t receiveCallback; /**< @brief Network receive callback, if any. */
    void * pReceiveContext;                      /**< @brief The context for the receive callback. */
    IotNetworkCloseCallback_t closeCallback;     /**< @brief Network close callback, if any. */
    void * pCloseContext;                        /**< @brief The context for the close callback. */
} _networkConnection_t;

/*-----------------------------------------------------------*/

/**
 * @brief An #IotNetworkInterface_t that uses the functions in this file.
 */
static const IotNetworkInterface_t _networkOpenssl =
{
    .create             = IotNetworkOpenssl_Create,
    .setReceiveCallback = IotNetworkOpenssl_SetReceiveCallback,
    .setCloseCallback   = IotNetworkOpenssl_SetCloseCallback,
    .send               = IotNetworkOpenssl_Send,
    .receive            = IotNetworkOpenssl_Receive,
    .close              = IotNetworkOpenssl_Close,
    .destroy            = IotNetworkOpenssl_Destroy
};

/*-----------------------------------------------------------*/

/**
 * @brief Network receive thread.
 *
 * This thread polls the network socket and reads data when data is available.
 * It then invokes the receive callback, if any.
 *
 * @param[in] pArgument The connection associated with this receive thread.
 */
static void * _networkReceiveThread( void * pArgument )
{
    int pollStatus = 0;
    struct pollfd fileDescriptor =
    {
        .events  = POLLIN | POLLPRI,
        .revents = 0
    };

    /* Cast function parameter to correct type. */
    _networkConnection_t * pConnection = pArgument;

    /* Set the file descriptor for poll. */
    fileDescriptor.fd = pConnection->socket;

    /* Continuously poll the network socket for events. */
    while( true )
    {
        pollStatus = poll( &fileDescriptor, 1, -1 );

        if( pollStatus == -1 )
        {
            IotLogError( "Failed to poll socket %d. errno=%d.",
                         pConnection->socket,
                         errno );
            break;
        }

        /* If an error event is detected, terminate this thread. */
        if( ( fileDescriptor.revents & POLLERR ) ||
            ( fileDescriptor.revents & POLLHUP ) ||
            ( fileDescriptor.revents & POLLNVAL ) )
        {
            IotLogError( "Detected error on socket %d, receive thread exiting.",
                         pConnection->socket );
            break;
        }

        /* Invoke the callback function. */
        pConnection->receiveCallback( pConnection,
                                      pConnection->pReceiveContext );
    }

    /**
     * If a close callback has been defined, invoke it now; since we
     * don't know what caused the close, use "unknown" as the reason.
     */
    if( pConnection->closeCallback != NULL )
    {
        pConnection->closeCallback( pConnection,
                                    IOT_NETWORK_UNKNOWN_CLOSED,
                                    pConnection->pCloseContext );
    }

    IotLogDebug( "Network receive thread for socket %d terminating.",
                 pConnection->socket );

    return NULL;
}

/*-----------------------------------------------------------*/

/**
 * @brief Perform a DNS lookup of a host name and establish a TCP connection.
 *
 * @param[in] pServerInfo Server host name and port.
 *
 * @return A connected TCP socket number; `-1` if the DNS lookup failed.
 */
static int _dnsLookup( IotNetworkServerInfo_t pServerInfo )
{
    IOT_FUNCTION_ENTRY( int, 0 );
    int tcpSocket = -1;
    const uint16_t netPort = htons( pServerInfo->port );
    struct addrinfo * pListHead = NULL, * pAddressInfo = NULL;
    struct sockaddr * pServer = NULL;
    socklen_t serverLength = 0;

    /* Perform a DNS lookup of host name. */
    IotLogDebug( "Performing DNS lookup of %s", pServerInfo->pHostName );
    status = getaddrinfo( pServerInfo->pHostName, NULL, NULL, &pListHead );

    if( status != 0 )
    {
        IotLogError( "DNS lookup failed. %s.", gai_strerror( status ) );

        IOT_SET_AND_GOTO_CLEANUP( -1 );
    }

    IotLogDebug( "Successfully received DNS records." );

    /* Go through the list of DNS records until a successful connection is made. */
    for( pAddressInfo = pListHead; pAddressInfo != NULL; pAddressInfo = pAddressInfo->ai_next )
    {
        /* Open a socket using the information in the DNS record. */
        IotLogDebug( "Creating socket for domain: %d, type: %d, protocol: %d.",
                     pAddressInfo->ai_family, pAddressInfo->ai_socktype, pAddressInfo->ai_protocol );
        tcpSocket = socket( pAddressInfo->ai_family, pAddressInfo->ai_socktype, pAddressInfo->ai_protocol );

        /* Check if the socket was successfully opened. */
        if( tcpSocket == -1 )
        {
            IotLogDebug( "Could not open socket for record at %p. Trying next.",
                         pAddressInfo );
            continue;
        }

        IotLogDebug( "Socket creation successful. Attempting connection." );

        /* Set the port for the connection based on protocol. */
        pServer = pAddressInfo->ai_addr;

        if( pServer->sa_family == AF_INET )
        {
            /* IPv4. */
            ( ( struct sockaddr_in * ) pServer )->sin_port = netPort;
            serverLength = sizeof( struct sockaddr_in );
        }
        else
        {
            /* IPv6. */
            ( ( struct sockaddr_in6 * ) pServer )->sin6_port = netPort;
            serverLength = sizeof( struct sockaddr_in6 );
        }

        /* Attempt to connect. */
        if( connect( tcpSocket,
                     pServer,
                     serverLength ) == -1 )
        {
            /* Connect failed; close socket and try next record. */
            if( close( tcpSocket ) != 0 )
            {
                IotLogWarn( "Failed to close socket %d. errno=%d.",
                            tcpSocket,
                            errno );
            }

            IotLogDebug( "Socket connection failed. Trying next." );
        }
        else
        {
            /* Connection successful; stop searching the list. */
            IotLogDebug( "Socket connection successful." );
            break;
        }
    }

    /* If pAddressInfo is NULL, then the entire list of records was parsed but none
     * of them provided a successful connection. */
    if( pAddressInfo == NULL )
    {
        IotLogError( "Failed to connect to all retrieved DNS records." );

        IOT_SET_AND_GOTO_CLEANUP( -1 );
    }

    IOT_FUNCTION_CLEANUP_BEGIN();

    /* Free DNS records. */
    if( pListHead != NULL )
    {
        freeaddrinfo( pListHead );
    }

    /* Return the socket descriptor on success. */
    if( status == 0 )
    {
        status = tcpSocket;
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

/**
 * @brief Reads credentials from the filesystem.
 *
 * Uses OpenSSL to import the root CA certificate, client certificate, and
 * client certificate private key.
 * @param[in] pSslContext Destination for the imported credentials.
 * @param[in] pRootCaPath Path to the root CA certificate.
 * @param[in] pClientCertPath Path to the client certificate.
 * @param[in] pCertPrivateKeyPath Path to the client certificate private key.
 *
 * @return `true` if all credentials were successfully read; `false` otherwise.
 */
static bool _readCredentials( SSL_CTX * pSslContext,
                              const char * pRootCaPath,
                              const char * pClientCertPath,
                              const char * pCertPrivateKeyPath )
{
    IOT_FUNCTION_ENTRY( bool, true );
    X509 * pRootCa = NULL;

    /* OpenSSL does not provide a single function for reading and loading certificates
     * from files into stores, so the file API must be called. */
    IotLogDebug( "Opening root certificate %s", pRootCaPath );
    FILE * pRootCaFile = fopen( pRootCaPath, "r" );

    if( pRootCaFile == NULL )
    {
        IotLogError( "Failed to open %s", pRootCaPath );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    /* Read the root CA into an X509 object, then close its file handle. */
    pRootCa = PEM_read_X509( pRootCaFile, NULL, NULL, NULL );

    if( fclose( pRootCaFile ) != 0 )
    {
        IotLogWarn( "Failed to close file %s", pRootCaPath );
    }

    if( pRootCa == NULL )
    {
        IotLogError( "Failed to parse root CA." );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    /* Add the root CA to certificate store. */
    if( X509_STORE_add_cert( SSL_CTX_get_cert_store( pSslContext ),
                             pRootCa ) != 1 )
    {
        IotLogError( "Failed to add root CA to certificate store." );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    IotLogInfo( "Successfully imported root CA." );

    /* Import the client certificate. */
    if( SSL_CTX_use_certificate_chain_file( pSslContext,
                                            pClientCertPath ) != 1 )
    {
        IotLogError( "Failed to import client certificate at %s",
                     pClientCertPath );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    IotLogInfo( "Successfully imported client certificate." );

    /* Import the client certificate private key. */
    if( SSL_CTX_use_PrivateKey_file( pSslContext,
                                     pCertPrivateKeyPath,
                                     SSL_FILETYPE_PEM ) != 1 )
    {
        IotLogError( "Failed to import client certificate private key at %s",
                     pCertPrivateKeyPath );

        IOT_SET_AND_GOTO_CLEANUP( false );
    }

    IotLogInfo( "Successfully imported client certificate private key." );

    IOT_FUNCTION_CLEANUP_BEGIN();

    /* Free the root CA object. */
    if( pRootCa != NULL )
    {
        X509_free( pRootCa );
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

/**
 * @brief Set up TLS on a TCP connection.
 *
 * @param[in] pConnection An established TCP connection.
 * @param[in] pServerName Remote host name, used for server name indication.
 * @param[in] pOpensslCredentials TLS setup parameters.
 *
 * @return #IOT_NETWORK_SUCCESS, #IOT_NETWORK_FAILURE, or #IOT_NETWORK_SYSTEM_ERROR.
 */
static IotNetworkError_t _tlsSetup( _networkConnection_t * pConnection,
                                    const char * pServerName,
                                    const IotNetworkCredentials_t pOpensslCredentials )
{
    IOT_FUNCTION_ENTRY( IotNetworkError_t, IOT_NETWORK_SUCCESS );
    SSL_CTX * pSslContext = NULL;

    /* Create a new SSL context. */
    #if OPENSSL_VERSION_NUMBER < 0x10100000L
        pSslContext = SSL_CTX_new( TLSv1_2_client_method() );
    #else
        pSslContext = SSL_CTX_new( TLS_client_method() );
    #endif

    if( pSslContext == NULL )
    {
        IotLogError( "Failed to create new SSL context." );

        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
    }

    /* Set auto retry mode for the blocking calls to SSL_read and SSL_write. The
     * mask returned by SSL_CTX_set_mode does not need to be checked. */
    IotLogDebug( "New SSL context created. Setting SSL_MODE_AUTO_RETRY." );
    ( void ) SSL_CTX_set_mode( pSslContext, SSL_MODE_AUTO_RETRY );

    /* Import all credentials. */
    if( _readCredentials( pSslContext,
                          pOpensslCredentials->pRootCa,
                          pOpensslCredentials->pClientCert,
                          pOpensslCredentials->pPrivateKey ) == false )
    {
        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_FAILURE );
    }

    /* Create a new SSL connection context */
    pConnection->pSslContext = SSL_new( pSslContext );

    if( pConnection->pSslContext == NULL )
    {
        IotLogError( "Failed to create new SSL connection context." );

        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
    }

    /* Enable SSL peer verification. */
    IotLogDebug( "Setting SSL_VERIFY_PEER." );
    SSL_set_verify( pConnection->pSslContext, SSL_VERIFY_PEER, NULL );

    /* Set the socket for the SSL connection. */
    if( SSL_set_fd( pConnection->pSslContext,
                    pConnection->socket ) != 1 )
    {
        IotLogError( "Failed to set SSL socket %d.", pConnection->socket );

        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
    }

    /* Set up ALPN if requested. */
    if( pOpensslCredentials->pAlpnProtos != NULL )
    {
        IotLogDebug( "Setting ALPN protos." );

        if( ( SSL_set_alpn_protos( pConnection->pSslContext,
                                   ( const unsigned char * ) pOpensslCredentials->pAlpnProtos,
                                   ( unsigned int ) strlen( pOpensslCredentials->pAlpnProtos ) ) != 0 ) )
        {
            IotLogError( "Failed to set ALPN protos." );

            IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
        }
    }

    /* Set TLS MFLN if requested. */
    if( pOpensslCredentials->maxFragmentLength > 0 )
    {
        IotLogDebug( "Setting max send fragment length %lu.",
                     ( unsigned long ) pOpensslCredentials->maxFragmentLength );

        /* Set the maximum send fragment length. */
        if( SSL_set_max_send_fragment( pConnection->pSslContext,
                                       ( long ) pOpensslCredentials->maxFragmentLength ) != 1 )
        {
            IotLogError( "Failed to set max send fragment length %lu.",
                         ( unsigned long ) pOpensslCredentials->maxFragmentLength );

            IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
        }

        /* In supported versions of OpenSSL, change the size of the read buffer
         * to match the maximum fragment length + some extra bytes for overhead.
         * Note that OpenSSL ignores this setting if it's smaller than the default.
         */
        #if OPENSSL_VERSION_NUMBER > 0x10100000L
            SSL_set_default_read_buffer_len( pConnection->pSslContext,
                                             pOpensslCredentials->maxFragmentLength +
                                             SSL3_RT_MAX_ENCRYPTED_OVERHEAD );
        #endif
    }

    /* Enable SNI if requested. */
    if( pOpensslCredentials->disableSni == false )
    {
        IotLogDebug( "Setting server name %s for SNI.", pServerName );

        if( SSL_set_tlsext_host_name( pConnection->pSslContext,
                                      pServerName ) != 1 )
        {
            IotLogError( "Failed to set server name %s for SNI.", pServerName );

            IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
        }
    }

    /* Perform the TLS handshake. */
    if( SSL_connect( pConnection->pSslContext ) != 1 )
    {
        IotLogError( "TLS handshake failed." );

        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
    }

    IotLogInfo( "TLS handshake succeeded." );

    /* Verify the peer certificate. */
    if( SSL_get_verify_result( pConnection->pSslContext ) != X509_V_OK )
    {
        IotLogError( "Peer certificate verification failed." );

        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
    }

    IotLogInfo( "Peer certificate verified. TLS connection established." );

    IOT_FUNCTION_CLEANUP_BEGIN();

    /* Free the SSL context. */
    if( pSslContext != NULL )
    {
        SSL_CTX_free( pSslContext );
    }

    /* Clean up on error. */
    if( status != IOT_NETWORK_SUCCESS )
    {
        if( pConnection->pSslContext != NULL )
        {
            SSL_free( pConnection->pSslContext );
            pConnection->pSslContext = NULL;
        }
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

/**
 * @brief Close a TLS connection.
 *
 * @param[in] pConnection The TLS connection to close.
 */
static void _tlsClose( _networkConnection_t * pConnection )
{
    /* Shut down the TLS connection. */
    IotLogInfo( "Shutting down TLS connection." );

    /* Lock the SSL context mutex. */
    IotMutex_Lock( &( pConnection->sslMutex ) );

    /* SSL shutdown should be called twice: once to send "close notify" and once
     * more to receive the peer's "close notify". */
    if( SSL_shutdown( pConnection->pSslContext ) == 0 )
    {
        IotLogDebug( "\"Close notify\" sent. Awaiting peer response." );

        /* The previous call to SSL_shutdown marks the SSL connection as closed.
         * SSL_shutdown must be called again to read the peer response. */
        if( SSL_shutdown( pConnection->pSslContext ) != 1 )
        {
            IotLogWarn( "No response from peer." );
        }
        else
        {
            IotLogDebug( "Peer response to \"close notify\" received." );
        }
    }

    /* Unlock the SSL context mutex. */
    IotMutex_Unlock( &( pConnection->sslMutex ) );

    IotLogInfo( "TLS connection closed." );
}

/*-----------------------------------------------------------*/

const IotNetworkInterface_t * IotNetworkOpenssl_GetInterface( void )
{
    return &_networkOpenssl;
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkOpenssl_Init( void )
{
    IotNetworkError_t status = IOT_NETWORK_SUCCESS;

    /* Details on SIGPIPE handling. */
    struct sigaction sigpipeAction;

    ( void ) memset( &sigpipeAction, 0x00, sizeof( struct sigaction ) );

    /* Ignore SIGPIPE, which may be raised if the peer closes the connection. */
    sigpipeAction.sa_handler = SIG_IGN;

    if( sigaction( SIGPIPE, &sigpipeAction, NULL ) != 0 )
    {
        IotLogError( "Failed to set SIGPIPE handler. errno=%d.", errno );

        status = IOT_NETWORK_FAILURE;
    }

    if( status == IOT_NETWORK_SUCCESS )
    {
        /* Per the OpenSSL docs, the return value of this function is meaningless.
         * This function is also deprecated, but it's called to retain compatibility
         * with v1.0.2. */
        ( void ) SSL_library_init();

        IotLogInfo( "Network library initialized." );
    }

    return status;
}

/*-----------------------------------------------------------*/

void IotNetworkOpenssl_Cleanup( void )
{
    /* Call the necessary OpenSSL functions to prevent memory leaks. */
    #if OPENSSL_VERSION_NUMBER < 0x10100000L
        ERR_remove_thread_state( NULL );
    #endif
    CRYPTO_cleanup_all_ex_data();
    EVP_cleanup();
    SSL_COMP_free_compression_methods();

    IotLogInfo( "Network library cleanup done." );
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkOpenssl_Create( IotNetworkServerInfo_t pServerInfo,
                                            IotNetworkCredentials_t pCredentialInfo,
                                            IotNetworkConnection_t * pConnection )
{
    IOT_FUNCTION_ENTRY( IotNetworkError_t, IOT_NETWORK_SUCCESS );
    int tcpSocket = -1;
    bool sslMutexCreated = false;
    _networkConnection_t * pNewNetworkConnection = NULL;

    /* Allocate memory for a new connection. */
    pNewNetworkConnection = IotNetwork_Malloc( sizeof( _networkConnection_t ) );

    if( pNewNetworkConnection == NULL )
    {
        IotLogError( "Failed to allocate memory for new network connection." );

        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_NO_MEMORY );
    }

    /* Clear connection data. */
    ( void ) memset( pNewNetworkConnection, 0x00, sizeof( _networkConnection_t ) );

    /* Perform a DNS lookup of pHostName. This also establishes a TCP socket. */
    tcpSocket = _dnsLookup( pServerInfo );

    if( tcpSocket == -1 )
    {
        IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_FAILURE );
    }
    else
    {
        IotLogInfo( "TCP connection successful." );
    }

    /* Set the socket in the network connection. */
    pNewNetworkConnection->socket = tcpSocket;

    /* Set up TLS if credentials are provided. */
    if( pCredentialInfo != NULL )
    {
        IotLogInfo( "Setting up TLS." );

        /* Create the mutex that protects the SSL context. */
        sslMutexCreated = IotMutex_Create( &( pNewNetworkConnection->sslMutex ), true );

        if( sslMutexCreated == false )
        {
            IotLogError( "Failed to create network send mutex." );

            IOT_SET_AND_GOTO_CLEANUP( IOT_NETWORK_SYSTEM_ERROR );
        }

        status = _tlsSetup( pNewNetworkConnection,
                            pServerInfo->pHostName,
                            pCredentialInfo );
    }

    /* Clean up on error. */
    IOT_FUNCTION_CLEANUP_BEGIN();

    if( status != IOT_NETWORK_SUCCESS )
    {
        if( tcpSocket != -1 )
        {
            ( void ) close( tcpSocket );
        }

        if( sslMutexCreated == true )
        {
            IotMutex_Destroy( &( pNewNetworkConnection->sslMutex ) );
        }

        if( pNewNetworkConnection != NULL )
        {
            IotNetwork_Free( pNewNetworkConnection );
        }
    }
    else
    {
        /* Set the output parameter. */
        *pConnection = pNewNetworkConnection;
    }

    IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkOpenssl_SetReceiveCallback( IotNetworkConnection_t pConnection,
                                                        IotNetworkReceiveCallback_t receiveCallback,
                                                        void * pContext )
{
    IOT_FUNCTION_ENTRY( IotNetworkError_t, IOT_NETWORK_BAD_PARAMETER );
    int posixError = 0;

    /* The receive callback must be non-NULL) */
    if( receiveCallback != NULL )
    {
        /* Set the callback and parameter. */
        pConnection->receiveCallback = receiveCallback;
        pConnection->pReceiveContext = pContext;

        posixError = pthread_create( &pConnection->receiveThread,
                                     NULL,
                                     _networkReceiveThread,
                                     pConnection );

        if( posixError != 0 )
        {
            IotLogError( "Failed to create socket %d network receive thread. errno=%d.",
                         pConnection->socket,
                         posixError );
            status = IOT_NETWORK_SYSTEM_ERROR;
        }
        else
        {
            pConnection->receiveThreadCreated = true;
            status = IOT_NETWORK_SUCCESS;
        }
    }

    IOT_FUNCTION_EXIT_NO_CLEANUP();
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkOpenssl_SetCloseCallback( IotNetworkConnection_t pConnection,
                                                      IotNetworkCloseCallback_t closeCallback,
                                                      void * pContext )
{
    IotNetworkError_t status = IOT_NETWORK_BAD_PARAMETER;

    if( closeCallback != NULL )
    {
        /* Set the callback and parameter. */
        pConnection->closeCallback = closeCallback;
        pConnection->pCloseContext = pContext;

        status = IOT_NETWORK_SUCCESS;
    }

    return status;
}

/*-----------------------------------------------------------*/

size_t IotNetworkOpenssl_Send( IotNetworkConnection_t pConnection,
                               const uint8_t * pMessage,
                               size_t messageLength )
{
    int bytesSent = 0;
    struct pollfd fileDescriptor =
    {
        .events  = POLLOUT,
        .revents = 0
    };

    IotLogDebug( "Sending %lu bytes over socket %d.",
                 ( unsigned long ) messageLength,
                 pConnection->socket );

    /* Set the file descriptor for poll. */
    fileDescriptor.fd = pConnection->socket;

    /* The SSL mutex must be locked to protect an SSL context from concurrent
     * access. */
    if( pConnection->pSslContext != NULL )
    {
        IotMutex_Lock( &( pConnection->sslMutex ) );
    }

    /* Check that it's possible to send data right now. */
    if( poll( &fileDescriptor, 1, 0 ) == 1 )
    {
        /* Use OpenSSL's SSL_write() function or the POSIX send() function based on
         * whether the SSL connection context is set up. */
        if( pConnection->pSslContext != NULL )
        {
            bytesSent = SSL_write( pConnection->pSslContext,
                                   pMessage,
                                   ( int ) messageLength );
        }
        else
        {
            bytesSent = ( int ) send( pConnection->socket,
                                      pMessage,
                                      messageLength,
                                      0 );
        }
    }
    else
    {
        IotLogError( "Not possible to send on socket %d.", pConnection->socket );
    }

    /* Unlock the SSL context mutex. */
    if( pConnection->pSslContext != NULL )
    {
        IotMutex_Unlock( &( pConnection->sslMutex ) );
    }

    /* Log the number of bytes sent. */
    if( bytesSent <= 0 )
    {
        IotLogError( "Send failure." );

        bytesSent = 0;
    }
    else if( ( size_t ) bytesSent != messageLength )
    {
        IotLogWarn( "Failed to send %lu bytes, %d bytes sent instead.",
                    ( unsigned long ) messageLength,
                    bytesSent );
    }
    else
    {
        IotLogDebug( "Successfully sent %lu bytes.",
                     ( unsigned long ) messageLength );
    }

    return ( size_t ) bytesSent;
}

/*-----------------------------------------------------------*/

size_t IotNetworkOpenssl_Receive( IotNetworkConnection_t pConnection,
                                  uint8_t * pBuffer,
                                  size_t bytesRequested )
{
    int receiveStatus = 0;
    size_t bytesRead = 0, bytesRemaining = bytesRequested;

    IotLogDebug( "Blocking to wait for %lu bytes on socket %d.",
                 ( unsigned long ) bytesRequested,
                 pConnection->socket );

    /* The SSL mutex must be locked to protect an SSL context from concurrent
     * access. */
    if( pConnection->pSslContext != NULL )
    {
        IotMutex_Lock( &( pConnection->sslMutex ) );
    }

    /* Loop until all bytes are received. */
    while( bytesRemaining > 0 )
    {
        /* Use OpenSSL's SSL_read() function or the POSIX recv() function based on
         * whether the SSL connection context is set up. */
        if( pConnection->pSslContext != NULL )
        {
            receiveStatus = SSL_read( pConnection->pSslContext,
                                      pBuffer + bytesRead,
                                      ( int ) bytesRemaining );
        }
        else
        {
            receiveStatus = ( int ) recv( pConnection->socket,
                                          pBuffer + bytesRead,
                                          bytesRemaining,
                                          0 );
        }

        /* Check receive status. */
        if( receiveStatus <= 0 )
        {
            IotLogError( "Error receiving from socket %d.",
                         pConnection->socket );

            break;
        }
        else
        {
            bytesRead += ( size_t ) receiveStatus;
            bytesRemaining -= ( size_t ) receiveStatus;
        }
    }

    /* Unlock the SSL context mutex. */
    if( pConnection->pSslContext != NULL )
    {
        IotMutex_Unlock( &( pConnection->sslMutex ) );
    }

    /* Check how many bytes were read. */
    if( bytesRead < bytesRequested )
    {
        IotLogWarn( "Receive requested %lu bytes, but only %lu bytes received.",
                    ( unsigned long ) bytesRequested,
                    ( unsigned long ) bytesRead );
    }
    else
    {
        IotLogDebug( "Successfully received %lu bytes.",
                     ( unsigned long ) bytesRequested );
    }

    return bytesRead;
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkOpenssl_Close( IotNetworkConnection_t pConnection )
{
    /* If TLS was set up for this connection, clean it up. */
    if( pConnection->pSslContext != NULL )
    {
        _tlsClose( pConnection );
    }

    /* Shut down the connection. */
    if( shutdown( pConnection->socket, SHUT_RDWR ) != 0 )
    {
        IotLogWarn( "Could not shut down socket %d. errno=%d.",
                    pConnection->socket,
                    errno );
    }
    else
    {
        IotLogInfo( "Connection (socket %d) shut down.",
                    pConnection->socket );
    }

    return IOT_NETWORK_SUCCESS;
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkOpenssl_Destroy( IotNetworkConnection_t pConnection )
{
    int posixError = 0;

    /* Check if a receive thread needs to be cleaned up. */
    if( pConnection->receiveThreadCreated == true )
    {
        if( pthread_self() == pConnection->receiveThread )
        {
            /* If this function is being called from the receive thread, detach
             * it so no other thread needs to clean it up. */
            posixError = pthread_detach( pConnection->receiveThread );

            if( posixError != 0 )
            {
                IotLogWarn( "Failed to detach receive thread for socket %d. errno=%d.",
                            pConnection->socket,
                            posixError );
            }
        }
        else
        {
            /* Wait for the receive thread to exit. */
            posixError = pthread_join( pConnection->receiveThread, NULL );

            if( posixError != 0 )
            {
                IotLogWarn( "Failed to join receive thread for socket %d. errno=%d.",
                            pConnection->socket,
                            posixError );
            }
        }
    }

    /* Free the memory used by the TLS connection, if any. */
    if( pConnection->pSslContext != NULL )
    {
        SSL_free( pConnection->pSslContext );

        /* Destroy the SSL context mutex. */
        IotMutex_Destroy( &( pConnection->sslMutex ) );
    }

    /* Close the socket file descriptor. */
    if( close( pConnection->socket ) != 0 )
    {
        IotLogWarn( "Could not close socket %d. errno=%d.",
                    pConnection->socket,
                    errno );
    }
    else
    {
        IotLogInfo( "(Socket %d) Socket closed.",
                    pConnection->socket );
    }

    /* Free the connection. */
    IotNetwork_Free( pConnection );

    return IOT_NETWORK_SUCCESS;
}

/*-----------------------------------------------------------*/

int IotNetworkOpenssl_GetSocket( IotNetworkConnection_t pConnection )
{
    return pConnection->socket;
}

/*-----------------------------------------------------------*/

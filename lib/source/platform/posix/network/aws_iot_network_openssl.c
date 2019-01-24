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
 * @file aws_iot_network_openssl.c
 * @brief Implementation of the network-related functions from aws_iot_network.h
 * for systems with OpenSSL on POSIX systems.
 */

/* Build using a config header, if provided. */
#ifdef IOT_CONFIG_FILE
    #include IOT_CONFIG_FILE
#endif

/* Standard includes. */
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

/* POSIX includes. */
#include <errno.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <sys/ioctl.h>

/* Sockets includes. */
#include <netdb.h>
#include <sys/socket.h>

/* OpenSSL includes. */
#include <openssl/err.h>
#include <openssl/evp.h>
#include <openssl/ssl.h>

/* Network header include. */
#include "platform/aws_iot_network.h"

/* Platform threads include. */
#include "platform/iot_threads.h"

/* Configure logs for the functions in this file. */
#ifdef AWS_IOT_LOG_LEVEL_NETWORK
    #define _LIBRARY_LOG_LEVEL        AWS_IOT_LOG_LEVEL_NETWORK
#else
    #ifdef AWS_IOT_LOG_LEVEL_GLOBAL
        #define _LIBRARY_LOG_LEVEL    AWS_IOT_LOG_LEVEL_GLOBAL
    #else
        #define _LIBRARY_LOG_LEVEL    AWS_IOT_LOG_NONE
    #endif
#endif

#define _LIBRARY_LOG_NAME    ( "NET" )
#include "aws_iot_logging_setup.h"

/*
 * Provide default values for undefined memory allocation functions based on
 * the usage of dynamic memory allocation.
 */
#ifndef AwsIotNetwork_Malloc
    #include <stdlib.h>

/**
 * @brief Memory allocation. This function should have the same signature as
 * [malloc.](http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html)
 */
    #define AwsIotNetwork_Malloc    malloc
#endif
#ifndef AwsIotNetwork_Free
    #include <stdlib.h>

/**
 * @brief Free memory. This function should have the same signature as
 * [free.](http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html)
 */
    #define AwsIotNetwork_Free    free
#endif

/*-----------------------------------------------------------*/

/**
 * @brief Statuses for receive threads.
 */
typedef enum _threadStatus
{
    _NONE = 0,  /**< Any previously created thread is fully cleaned up. */
    _ACTIVE,    /**< A receive thread is currently running. */
    _TERMINATED /**< A receive thread is terminated and needs to be joined. */
} _threadStatus_t;

/**
 * @brief Connection info, which is pointed to by the connection handle.
 *
 * Holds data on a single connection.
 */
typedef struct _connectionInfo
{
    int tcpSocket;                                   /**< @brief Socket associated with connection. */
    SSL * pSSLConnectionContext;                     /**< @brief SSL context for connection. */
    IotMutex_t mutex;                                /**< @brief Synchronizes the various network threads. */
    _threadStatus_t receiveThreadStatus;             /**< @brief Status of the receive thread for this connection. */
    pthread_t receiveThread;                         /**< @brief Thread that handles receiving on this connection. */

    AwsIotMqttReceiveCallback_t mqttReceiveCallback; /**< @brief Function to call when MQTT data is received, if any. */
    AwsIotMqttConnection_t * pMqttConnection;        /**< @brief The first parameter passed to #_connectionInfo_t.mqttReceiveCallback. */
} _connectionInfo_t;

/*-----------------------------------------------------------*/

/**
 * @brief Signal handler for SIGPIPE.
 *
 * Currently, this function just prevents SIGPIPE from terminating the program.
 *
 * @param[in] signal Should always be SIGPIPE.
 */
static void _sigpipeHandler( int signal )
{
    ( void ) signal;

    /* This signal handler doesn't do anything, it just prevents SIGPIPE from
     * terminating this process. SIGPIPE will cause any receive threads to
     * terminate, and any further calls to AwsIotNetwork_Send will fail. */
}

/*-----------------------------------------------------------*/

/**
 * @brief Network receive thread.
 *
 * This thread polls the network socket and reads data when data is available.
 * It then invokes the MQTT receive callback, if any.
 *
 * @param[in] pArgument The connection associated with this receive thread.
 */
static void * _networkReceiveThread( void * pArgument )
{
    int bytesAvailable = 0, bytesRead = 0;
    int32_t bytesProcessed = 0;
    _connectionInfo_t * pConnectionInfo = ( _connectionInfo_t * ) pArgument;
    void * pReceiveBuffer = NULL;
    struct pollfd fileDescriptors =
    {
        .fd      = pConnectionInfo->tcpSocket,
        .events  = POLLIN,
        .revents = 0
    };

    /* Continuously poll the network socket for events. */
    while( poll( &fileDescriptors, 1, -1 ) == 1 )
    {
        /* Prevent this thread from being cancelled while running. But if the
         * connection mutex is locked, wait until it is available. */
        if( IotMutex_TryLock( &( pConnectionInfo->mutex ) ) == false )
        {
            continue;
        }

        /* If an error event is detected, terminate this thread. */
        if( ( fileDescriptors.revents & POLLERR ) ||
            ( fileDescriptors.revents & POLLHUP ) ||
            ( fileDescriptors.revents & POLLNVAL ) )
        {
            AwsIotLogError( "Detected error on socket %d, receive thread exiting.",
                            pConnectionInfo->tcpSocket );
            break;
        }

        /* Query how many bytes are available to read. The value returned by this
         * function may include more than just the data. */
        if( ioctl( pConnectionInfo->tcpSocket, FIONREAD, &bytesAvailable ) != 0 )
        {
            AwsIotLogError( "Failed to query bytes available on socket. errno=%d.",
                            errno );

            /* Unlock the connection mutex before polling again. */
            IotMutex_Unlock( &( pConnectionInfo->mutex ) );

            continue;
        }

        AwsIotLogDebug( "%d bytes available on socket %d.",
                        bytesAvailable,
                        pConnectionInfo->tcpSocket );

        /* If no bytes can be read, the socket is likely closed. Terminate this thread. */
        if( bytesAvailable == 0 )
        {
            AwsIotLogInfo( "No data available, terminating receive thread for socket %d.",
                           pConnectionInfo->tcpSocket );
            break;
        }

        /* Allocate memory to hold the received message. */
        pReceiveBuffer = AwsIotNetwork_Malloc( ( size_t ) bytesAvailable );

        if( pReceiveBuffer == NULL )
        {
            AwsIotLogError( "Failed to allocate %d bytes for socket read on %d.",
                            bytesAvailable,
                            pConnectionInfo->tcpSocket );

            /* Unlock the connection mutex before polling again. */
            IotMutex_Unlock( &( pConnectionInfo->mutex ) );

            continue;
        }

        /* Use OpenSSL's SSL_read() function or the POSIX recv() function based on
         * whether the SSL connection context is set up. */
        if( pConnectionInfo->pSSLConnectionContext != NULL )
        {
            bytesRead = SSL_read( pConnectionInfo->pSSLConnectionContext,
                                  pReceiveBuffer,
                                  bytesAvailable );
        }
        else
        {
            bytesRead = ( int ) recv( pConnectionInfo->tcpSocket,
                                      pReceiveBuffer,
                                      ( size_t ) bytesAvailable,
                                      0 );
        }

        /* Check how many bytes were read. */
        if( bytesRead <= 0 )
        {
            AwsIotLogError( "Error reading from socket %d.",
                            pConnectionInfo->tcpSocket );

            AwsIotNetwork_Free( pReceiveBuffer );
            break;
        }

        AwsIotLogDebug( "Received %d bytes from socket %d.",
                        bytesRead,
                        pConnectionInfo->tcpSocket );

        /* Invoke the callback function. But if there's no callback to invoke,
         * terminate this thread. */
        if( pConnectionInfo->mqttReceiveCallback != NULL )
        {
            bytesProcessed = pConnectionInfo->mqttReceiveCallback( pConnectionInfo->pMqttConnection,
                                                                   pReceiveBuffer,
                                                                   0,
                                                                   ( size_t ) bytesRead,
                                                                   AwsIotNetwork_Free );
        }
        else
        {
            /* Free resources and terminate thread. */
            AwsIotNetwork_Free( pReceiveBuffer );

            break;
        }

        /* Check the return value of the MQTT callback. */
        if( bytesProcessed < 0 )
        {
            AwsIotLogError( "Detected MQTT protocol violation. Receive thread for "
                            "socket %d terminating.", pConnectionInfo->tcpSocket );
            break;
        }

        /* Unlock the connection mutex before polling again. */
        IotMutex_Unlock( &( pConnectionInfo->mutex ) );
    }

    AwsIotLogDebug( "Network receive thread for socket %d terminating.",
                    pConnectionInfo->tcpSocket );

    /* Clear data about the callback. */
    pConnectionInfo->receiveThreadStatus = _TERMINATED;
    pConnectionInfo->mqttReceiveCallback = NULL;
    pConnectionInfo->pMqttConnection = NULL;

    /* Unlock the connection mutex before exiting. */
    IotMutex_Unlock( &( pConnectionInfo->mutex ) );

    return NULL;
}

/*-----------------------------------------------------------*/

/**
 * @brief Perform a DNS lookup of a host name and establish a TCP connection.
 *
 * @param[in] pHostName The host name to look up.
 * @param[in] port Remote server port (in host byte order) for the TCP connection.
 *
 * @return A connected TCP socket number; -1 if the DNS lookup failed.
 */
static inline int _dnsLookup( const char * const pHostName,
                              uint16_t port )
{
    int status = 0, tcpSocket = -1;
    const uint16_t netPort = htons( port );
    struct addrinfo * pListHead = NULL, * pAddressInfo = NULL;
    struct sockaddr_in * pServer = NULL;

    /* Perform a DNS lookup of pHostName. */
    AwsIotLogDebug( "Performing DNS lookup of %s", pHostName );
    status = getaddrinfo( pHostName, NULL, NULL, &pListHead );

    if( status != 0 )
    {
        AwsIotLogError( "DNS lookup failed. %s.", gai_strerror( status ) );

        return -1;
    }

    AwsIotLogDebug( "Successfully received DNS records." );

    /* Go through the list of DNS records until a successful connection is made. */
    for( pAddressInfo = pListHead; pAddressInfo != NULL; pAddressInfo = pAddressInfo->ai_next )
    {
        /* Open a socket using the information in the DNS record. */
        AwsIotLogDebug( "Creating socket for domain: %d, type: %d, protocol: %d.",
                        pAddressInfo->ai_family, pAddressInfo->ai_socktype, pAddressInfo->ai_protocol );
        tcpSocket = socket( pAddressInfo->ai_family, pAddressInfo->ai_socktype, pAddressInfo->ai_protocol );

        /* Check if the socket was successfully opened. */
        if( tcpSocket == -1 )
        {
            AwsIotLogDebug( "Could not open socket for record at %p. Trying next.",
                            pAddressInfo );
            continue;
        }

        /* Set the port for the connection. */
        AwsIotLogDebug( "Socket creation successful. Attempting connection." );
        pServer = ( struct sockaddr_in * ) ( pAddressInfo->ai_addr );
        pServer->sin_port = netPort;

        /* Attempt to connect. */
        if( connect( tcpSocket,
                     ( struct sockaddr * ) pServer,
                     sizeof( struct sockaddr ) ) == -1 )
        {
            /* Connect failed; close socket and try next record. */
            if( close( tcpSocket ) != 0 )
            {
                AwsIotLogWarn( "Failed to close socket %d. errno=%d.",
                               tcpSocket,
                               errno );
            }

            AwsIotLogDebug( "Socket connection failed. Trying next." );
        }
        else
        {
            /* Connection successful; stop searching the list. */
            AwsIotLogDebug( "Socket connection successful." );
            break;
        }
    }

    freeaddrinfo( pListHead );

    /* If pAddressInfo is NULL, then the entire list of records was parsed but none
     * of them provided a successful connection. */
    if( pAddressInfo == NULL )
    {
        AwsIotLogError( "Failed to connect to all retrieved DNS records." );

        return -1;
    }

    return tcpSocket;
}

/*-----------------------------------------------------------*/

/**
 * @brief Reads credentials from the filesystem.
 *
 * Uses OpenSSL to import the root CA certificate, client certificate, and
 * client certificate private key.
 * @param[in] pSSLContext Destination for the imported credentials.
 * @param[in] pRootCAPath Path to the root CA certificate.
 * @param[in] pClientCertPath Path to the client certificate.
 * @param[in] pCertPrivateKeyPath Path to the client certificate private key.
 */
static inline bool _readCredentials( SSL_CTX * pSSLContext,
                                     const char * const pRootCAPath,
                                     const char * const pClientCertPath,
                                     const char * const pCertPrivateKeyPath )
{
    X509 * pRootCA = NULL;

    /* OpenSSL does not provide a single function for reading and loading certificates
     * from files into stores, so the file API must be called. */
    AwsIotLogDebug( "Opening root certificate %s", pRootCAPath );
    FILE * pRootCAFile = fopen( pRootCAPath, "r" );

    if( pRootCAFile == NULL )
    {
        AwsIotLogError( "Failed to open %s", pRootCAPath );

        return false;
    }

    /* Read the root CA into an X509 object, then close its file handle. */
    pRootCA = PEM_read_X509( pRootCAFile, NULL, NULL, NULL );

    if( fclose( pRootCAFile ) != 0 )
    {
        AwsIotLogWarn( "Failed to close file %s", pRootCAPath );
    }

    if( pRootCA == NULL )
    {
        AwsIotLogError( "Failed to parse root CA." );

        return false;
    }

    /* Add the root CA to certificate store. */
    if( X509_STORE_add_cert( SSL_CTX_get_cert_store( pSSLContext ),
                             pRootCA ) != 1 )
    {
        AwsIotLogError( "Failed to add root CA to certificate store." );

        return false;
    }

    /* Free the root CA object. */
    X509_free( pRootCA );
    AwsIotLogInfo( "Successfully imported root CA." );

    /* Import the client certificate. */
    if( SSL_CTX_use_certificate_file( pSSLContext,
                                      pClientCertPath,
                                      SSL_FILETYPE_PEM ) != 1 )
    {
        AwsIotLogError( "Failed to import client certificate at %s",
                        pClientCertPath );

        return false;
    }

    AwsIotLogInfo( "Successfully imported client certificate." );

    /* Import the client certificate private key. */
    if( SSL_CTX_use_PrivateKey_file( pSSLContext,
                                     pCertPrivateKeyPath,
                                     SSL_FILETYPE_PEM ) != 1 )
    {
        AwsIotLogError( "Failed to import client certificate private key at %s",
                        pCertPrivateKeyPath );

        return false;
    }

    AwsIotLogInfo( "Successfully imported client certificate private key." );

    return true;
}

/*-----------------------------------------------------------*/

/**
 * @brief Set up TLS on a TCP connection.
 *
 * @param[in] pConnectionInfo An established TCP connection.
 * @param[in] pServerName Remote host name, used for server name indication.
 * @param[in] pTlsInfo TLS setup parameters.
 *
 * @return #AWS_IOT_NETWORK_SUCCESS, #AWS_IOT_NETWORK_BAD_PARAMETER,
 * #AWS_IOT_NETWORK_TLS_LIBRARY_ERROR, or #AWS_IOT_NETWORK_CREDENTIAL_READ_ERROR
 */
static inline AwsIotNetworkError_t _tlsSetup( _connectionInfo_t * const pConnectionInfo,
                                              const char * const pServerName,
                                              const AwsIotNetworkTlsInfo_t * const pTlsInfo )
{
    SSL_CTX * pSSLContext = NULL;
    AwsIotNetworkError_t status = AWS_IOT_NETWORK_SUCCESS;

    /* Check credentials. The sizes of credentials are ignored, as the credential
     * parameters represent filesystem paths and the OpenSSL APIs for reading
     * credential paths do not take a size (NULL-terminated strings expected). */
    if( ( pTlsInfo->pRootCa == NULL ) ||
        ( pTlsInfo->pClientCert == NULL ) ||
        ( pTlsInfo->pPrivateKey == NULL ) )
    {
        AwsIotLogError( "Bad parameter in TLS setup parameters." );

        return AWS_IOT_NETWORK_BAD_PARAMETER;
    }

    /* Create a new SSL context. */
    #if OPENSSL_VERSION_NUMBER < 0x10100000L
        pSSLContext = SSL_CTX_new( TLSv1_2_client_method() );
    #else
        pSSLContext = SSL_CTX_new( TLS_client_method() );
    #endif

    if( pSSLContext == NULL )
    {
        AwsIotLogError( "Failed to create new SSL context." );

        return AWS_IOT_NETWORK_TLS_LIBRARY_ERROR;
    }

    /* Set auto retry mode for the blocking calls to SSL_read and SSL_write. The
     * mask returned by SSL_CTX_set_mode does not need to be checked. */
    AwsIotLogDebug( "New SSL context created. Setting SSL_MODE_AUTO_RETRY." );
    ( void ) SSL_CTX_set_mode( pSSLContext, SSL_MODE_AUTO_RETRY );

    /* Import all credentials. */
    if( _readCredentials( pSSLContext,
                          pTlsInfo->pRootCa,
                          pTlsInfo->pClientCert,
                          pTlsInfo->pPrivateKey ) == false )
    {
        SSL_CTX_free( pSSLContext );

        return AWS_IOT_NETWORK_CREDENTIAL_READ_ERROR;
    }

    /* Create a new SSL connection context, then free the SSL context as it's no
     * longer needed. */
    pConnectionInfo->pSSLConnectionContext = SSL_new( pSSLContext );
    SSL_CTX_free( pSSLContext );

    if( pConnectionInfo->pSSLConnectionContext == NULL )
    {
        AwsIotLogError( "Failed to create new SSL connection context." );

        return AWS_IOT_NETWORK_TLS_LIBRARY_ERROR;
    }

    /* Enable SSL peer verification. */
    AwsIotLogDebug( "Setting SSL_VERIFY_PEER." );
    SSL_set_verify( pConnectionInfo->pSSLConnectionContext, SSL_VERIFY_PEER, NULL );

    /* Set the socket for the SSL connection. */
    if( SSL_set_fd( pConnectionInfo->pSSLConnectionContext,
                    pConnectionInfo->tcpSocket ) != 1 )
    {
        AwsIotLogError( "Failed to set SSL socket %d.", pConnectionInfo->tcpSocket );
        status = AWS_IOT_NETWORK_TLS_LIBRARY_ERROR;
    }

    /* Set up ALPN. */
    if( ( status == AWS_IOT_NETWORK_SUCCESS ) && ( pTlsInfo->pAlpnProtos != NULL ) )
    {
        AwsIotLogDebug( "Setting ALPN protos." );

        if( ( SSL_set_alpn_protos( pConnectionInfo->pSSLConnectionContext,
                                   ( const unsigned char * ) pTlsInfo->pAlpnProtos,
                                   ( unsigned int ) strlen( pTlsInfo->pAlpnProtos ) ) != 0 ) )
        {
            AwsIotLogError( "Failed to set ALPN protos." );
            status = AWS_IOT_NETWORK_TLS_LIBRARY_ERROR;
        }
    }

    /* Set TLS MFLN. */
    if( ( status == AWS_IOT_NETWORK_SUCCESS ) && ( pTlsInfo->maxFragmentLength > 0 ) )
    {
        AwsIotLogDebug( "Setting max send fragment length %lu.",
                        ( unsigned long ) pTlsInfo->maxFragmentLength );

        /* Set the maximum send fragment length. */
        if( SSL_set_max_send_fragment( pConnectionInfo->pSSLConnectionContext,
                                       ( long ) pTlsInfo->maxFragmentLength ) != 1 )
        {
            AwsIotLogError( "Failed to set max send fragment length %lu.",
                            ( unsigned long ) pTlsInfo->maxFragmentLength );
            status = AWS_IOT_NETWORK_TLS_LIBRARY_ERROR;
        }
        else
        {
            /* In supported versions of OpenSSL, change the size of the read buffer
             * to match the maximum fragment length + some extra bytes for overhead.
             * Note that OpenSSL ignores this setting if it's smaller than the default.
             */
            #if OPENSSL_VERSION_NUMBER > 0x10100000L
                SSL_set_default_read_buffer_len( pConnectionInfo->pSSLConnectionContext,
                                                 pTlsInfo->maxFragmentLength +
                                                 SSL3_RT_MAX_ENCRYPTED_OVERHEAD );
            #endif
        }
    }

    /* Set server name for SNI. */
    if( ( status == AWS_IOT_NETWORK_SUCCESS ) && ( pTlsInfo->disableSni == false ) )
    {
        AwsIotLogDebug( "Setting server name %s for SNI.", pServerName );

        if( SSL_set_tlsext_host_name( pConnectionInfo->pSSLConnectionContext,
                                      pServerName ) != 1 )
        {
            AwsIotLogError( "Failed to set server name %s for SNI.", pServerName );
            status = AWS_IOT_NETWORK_TLS_LIBRARY_ERROR;
        }
    }

    /* Perform the TLS handshake. */
    if( status == AWS_IOT_NETWORK_SUCCESS )
    {
        if( SSL_connect( pConnectionInfo->pSSLConnectionContext ) != 1 )
        {
            AwsIotLogError( "TLS handshake failed." );
            status = AWS_IOT_NETWORK_TLS_LIBRARY_ERROR;
        }
        else
        {
            AwsIotLogInfo( "TLS handshake succeeded." );
        }
    }

    /* Verify the peer certificate. */
    if( status == AWS_IOT_NETWORK_SUCCESS )
    {
        if( SSL_get_verify_result( pConnectionInfo->pSSLConnectionContext ) != X509_V_OK )
        {
            AwsIotLogError( "Peer certificate verification failed." );
            status = AWS_IOT_NETWORK_TLS_LIBRARY_ERROR;
        }
        else
        {
            AwsIotLogInfo( "Peer certificate verified. TLS connection established." );
        }
    }

    /* Clean up on error. */
    if( status != AWS_IOT_NETWORK_SUCCESS )
    {
        SSL_free( pConnectionInfo->pSSLConnectionContext );
        pConnectionInfo->pSSLConnectionContext = NULL;
    }

    return status;
}

/*-----------------------------------------------------------*/

/**
 * @brief Cleans up TLS for a connection.
 *
 * @param[in] pConnectionInfo The TLS connection to clean up.
 */
static inline void _tlsCleanup( _connectionInfo_t * const pConnectionInfo )
{
    /* Shut down the TLS connection. */
    AwsIotLogInfo( "Shutting down TLS connection." );

    /* SSL shutdown should be called twice: once to send "close notify" and once
     * more to receive the peer's "close notify". */
    if( SSL_shutdown( pConnectionInfo->pSSLConnectionContext ) == 0 )
    {
        AwsIotLogDebug( "\"Close notify\" sent. Awaiting peer response." );

        /* The previous call to SSL_shutdown marks the SSL connection as closed.
         * SSL_shutdown must be called again to read the peer response. */
        if( SSL_shutdown( pConnectionInfo->pSSLConnectionContext ) != 1 )
        {
            AwsIotLogWarn( "No response from peer." );
        }
        else
        {
            AwsIotLogDebug( "Peer response to \"close notify\" received." );
        }
    }

    AwsIotLogInfo( "TLS connection terminated." );

    /* Free the memory used by the TLS connection. */
    SSL_free( pConnectionInfo->pSSLConnectionContext );
    pConnectionInfo->pSSLConnectionContext = NULL;
}

/*-----------------------------------------------------------*/

AwsIotNetworkError_t AwsIotNetwork_Init( void )
{
    /* Details on SIGPIPE handling. */
    struct sigaction sigpipeAction;

    ( void ) memset( &sigpipeAction, 0x00, sizeof( struct sigaction ) );

    /* Set a signal handler for SIGPIPE, which may be raised if the peer closes
     * the connection. */
    sigpipeAction.sa_handler = _sigpipeHandler;

    if( sigaction( SIGPIPE, &sigpipeAction, NULL ) != 0 )
    {
        AwsIotLogError( "Failed to set SIGPIPE handler. errno=%d.", errno );

        return AWS_IOT_NETWORK_INIT_FAILED;
    }

    /* Per the OpenSSL 1.0.2 docs, the return value of this function is meaningless.
     * This function is also deprecated, but it's called to retain compatibility
     * with v1.0.2. */
    ( void ) SSL_library_init();

    AwsIotLogInfo( "Network library initialized." );

    return AWS_IOT_NETWORK_SUCCESS;
}

/*-----------------------------------------------------------*/

void AwsIotNetwork_Cleanup( void )
{
    /* Call the necessary OpenSSL functions to prevent memory leaks. */
    #if OPENSSL_VERSION_NUMBER < 0x10100000L
        ERR_remove_thread_state( NULL );
    #endif
    CRYPTO_cleanup_all_ex_data();
    EVP_cleanup();
    SSL_COMP_free_compression_methods();

    AwsIotLogInfo( "Network library cleanup done." );
}

/*-----------------------------------------------------------*/

AwsIotNetworkError_t AwsIotNetwork_CreateConnection( AwsIotNetworkConnection_t * const pNetworkConnection,
                                                     const char * const pHostName,
                                                     uint16_t port,
                                                     const AwsIotNetworkTlsInfo_t * const pTlsInfo )
{
    int tcpSocket = -1;
    AwsIotNetworkError_t status = AWS_IOT_NETWORK_SUCCESS;
    _connectionInfo_t * pConnectionInfo = NULL;

    /* Check parameters. */
    if( ( pNetworkConnection == NULL ) || ( pHostName == NULL ) || ( port == 0 ) )
    {
        AwsIotLogError( "Bad parameter to AwsIotNetwork_TcpConnect." );

        return AWS_IOT_NETWORK_BAD_PARAMETER;
    }

    /* Allocate memory for the connection context. This will hold information
     * about the connection. */
    pConnectionInfo = ( _connectionInfo_t * ) AwsIotNetwork_Malloc( sizeof( _connectionInfo_t ) );

    if( pConnectionInfo == NULL )
    {
        AwsIotLogError( "Failed to allocate memory for connection information." );

        return AWS_IOT_NETWORK_NO_MEMORY;
    }

    /* Create the network connection mutex. */
    if( IotMutex_Create( &( pConnectionInfo->mutex ) ) == false )
    {
        AwsIotLogError( "Failed to create connection mutex." );
        AwsIotNetwork_Free( pConnectionInfo );

        return AWS_IOT_NETWORK_NO_MEMORY;
    }

    /* Perform a DNS lookup of pHostName. This also establishes a TCP socket. */
    tcpSocket = _dnsLookup( pHostName, port );

    if( tcpSocket == -1 )
    {
        status = AWS_IOT_NETWORK_DNS_LOOKUP_ERROR;
    }

    if( status == AWS_IOT_NETWORK_SUCCESS )
    {
        /* Initialize the other members of the connection struct. */
        pConnectionInfo->tcpSocket = tcpSocket;
        pConnectionInfo->pSSLConnectionContext = NULL;
        pConnectionInfo->receiveThreadStatus = _NONE;
        pConnectionInfo->mqttReceiveCallback = NULL;
        pConnectionInfo->pMqttConnection = NULL;
        ( void ) memset( &( pConnectionInfo->receiveThread ), 0x00, sizeof( pthread_t ) );

        /* Set the output parameter. */
        *pNetworkConnection = pConnectionInfo;

        AwsIotLogInfo( "TCP connection successful." );

        if( pTlsInfo != NULL )
        {
            AwsIotLogInfo( "Setting up TLS." );

            status = _tlsSetup( pConnectionInfo, pHostName, pTlsInfo );
        }
    }

    /* Clean up on error. */
    if( status != AWS_IOT_NETWORK_SUCCESS )
    {
        if( tcpSocket != -1 )
        {
            ( void ) close( tcpSocket );
        }

        AwsIotNetwork_DestroyConnection( pConnectionInfo );
    }

    return status;
}

/*-----------------------------------------------------------*/

void AwsIotNetwork_CloseConnection( AwsIotNetworkConnection_t networkConnection )
{
    int posixError = 0;
    _connectionInfo_t * pConnectionInfo = ( _connectionInfo_t * ) networkConnection;

    /* Check parameters. */
    if( pConnectionInfo == NULL )
    {
        AwsIotLogError( "Bad parameter to AwsIotNetwork_CloseConnection." );

        return;
    }

    /* Lock the connection mutex to block the receive thread. */
    IotMutex_Lock( &( pConnectionInfo->mutex ) );

    /* Check if a network receive thread was created. */
    if( pConnectionInfo->receiveThreadStatus != _NONE )
    {
        /* Send a cancellation request to the receive thread if active. */
        if( pConnectionInfo->receiveThreadStatus == _ACTIVE )
        {
            posixError = pthread_cancel( pConnectionInfo->receiveThread );

            if( ( posixError != 0 ) && ( posixError != ESRCH ) )
            {
                AwsIotLogWarn( "Failed to send cancellation request to socket %d receive "
                               "thread during TLS cleanup. errno=%d.",
                               pConnectionInfo->tcpSocket,
                               posixError );
            }
        }

        /* Join the receive thread. */
        posixError = pthread_join( pConnectionInfo->receiveThread, NULL );

        if( posixError != 0 )
        {
            AwsIotLogWarn( "Failed to join network receive thread for socket %d. errno=%d",
                           pConnectionInfo->tcpSocket,
                           posixError );
        }

        /* Clear data about the receive thread. */
        pConnectionInfo->receiveThreadStatus = _NONE;
        ( void ) memset( &( pConnectionInfo->receiveThread ), 0x00, sizeof( pthread_t ) );
    }

    /* If TLS was set up for this connection, clean it up. */
    if( pConnectionInfo->pSSLConnectionContext != NULL )
    {
        _tlsCleanup( pConnectionInfo );
    }

    /* Close the connection. */
    if( close( pConnectionInfo->tcpSocket ) != 0 )
    {
        AwsIotLogWarn( "Could not close socket %d. errno=%d.",
                       pConnectionInfo->tcpSocket,
                       errno );
    }
    else
    {
        AwsIotLogInfo( "Connection (socket %d) closed.",
                       pConnectionInfo->tcpSocket );
    }

    /* Unlock the connection mutex. */
    IotMutex_Unlock( &( pConnectionInfo->mutex ) );
}

/*-----------------------------------------------------------*/

void AwsIotNetwork_DestroyConnection( AwsIotNetworkConnection_t networkConnection )
{
    _connectionInfo_t * pConnectionInfo = ( _connectionInfo_t * ) networkConnection;

    if( pConnectionInfo == NULL )
    {
        AwsIotLogError( "Bad parameter to AwsIotNetwork_DestroyConnection." );

        return;
    }

    /* Destroy the connection data mutex. */
    IotMutex_Destroy( &( pConnectionInfo->mutex ) );

    /* Free memory in use by the connection. */
    AwsIotNetwork_Free( pConnectionInfo );
}

/*-----------------------------------------------------------*/

AwsIotNetworkError_t AwsIotNetwork_SetMqttReceiveCallback( AwsIotNetworkConnection_t networkConnection,
                                                           AwsIotMqttConnection_t * pMqttConnection,
                                                           AwsIotMqttReceiveCallback_t receiveCallback )
{
    int posixError = 0;
    AwsIotNetworkError_t status = AWS_IOT_NETWORK_SUCCESS;
    _connectionInfo_t * pConnectionInfo = ( _connectionInfo_t * ) networkConnection;

    /* Lock the connection mutex before changing the callback and its parameter. */
    IotMutex_Lock( &( pConnectionInfo->mutex ) );

    /* Clean up any previously terminated receive thread. */
    if( pConnectionInfo->receiveThreadStatus == _TERMINATED )
    {
        posixError = pthread_join( pConnectionInfo->receiveThread, NULL );

        if( posixError != 0 )
        {
            AwsIotLogWarn( "Failed to join socket %d network receive thread. errno=%d.",
                           pConnectionInfo->tcpSocket,
                           posixError );

            status = AWS_IOT_NETWORK_SYSTEM_ERROR;
        }
        else
        {
            pConnectionInfo->receiveThreadStatus = _NONE;
        }
    }

    /* If the receive thread for this connection hasn't been created, create it now. */
    if( ( pConnectionInfo->receiveThreadStatus == _NONE ) && ( status == AWS_IOT_NETWORK_SUCCESS ) )
    {
        /* Update the callback and parameter. */
        pConnectionInfo->mqttReceiveCallback = receiveCallback;
        pConnectionInfo->pMqttConnection = pMqttConnection;

        posixError = pthread_create( &pConnectionInfo->receiveThread,
                                     NULL,
                                     _networkReceiveThread,
                                     pConnectionInfo );

        if( posixError != 0 )
        {
            AwsIotLogError( "Failed to create socket %d network receive thread. errno=%d.",
                            pConnectionInfo->tcpSocket,
                            posixError );
            status = AWS_IOT_NETWORK_SYSTEM_ERROR;
        }
        else
        {
            pConnectionInfo->receiveThreadStatus = _ACTIVE;
        }
    }

    /* Unlock the connection mutex. */
    IotMutex_Unlock( &( pConnectionInfo->mutex ) );

    return status;
}

/*-----------------------------------------------------------*/

size_t AwsIotNetwork_Send( void * networkConnection,
                           const void * const pMessage,
                           size_t messageLength )
{
    int bytesSent = 0;
    _connectionInfo_t * pConnectionInfo = ( _connectionInfo_t * ) networkConnection;
    struct pollfd fileDescriptors =
    {
        .events  = POLLOUT,
        .revents = 0
    };

    /* Check parameters. */
    if( ( pConnectionInfo == NULL ) || ( pMessage == NULL ) || ( messageLength == 0 ) )
    {
        AwsIotLogError( "Bad parameter to AwsIotNetwork_Send." );

        return 0;
    }

    /* Send message. */
    AwsIotLogDebug( "Sending %lu bytes over network.",
                    ( unsigned long ) messageLength );

    /* Lock the connection mutex to prevent the connection from being closed
     * while sending. */
    IotMutex_Lock( &( pConnectionInfo->mutex ) );

    /* Set the file descriptor for poll. */
    fileDescriptors.fd = pConnectionInfo->tcpSocket;

    /* Check that it's possible to send data right now. */
    if( poll( &fileDescriptors, 1, 0 ) == 1 )
    {
        /* Use OpenSSL's SSL_write() function or the POSIX send() function based on
         * whether the SSL connection context is set up. */
        if( pConnectionInfo->pSSLConnectionContext != NULL )
        {
            bytesSent = SSL_write( pConnectionInfo->pSSLConnectionContext,
                                   pMessage,
                                   ( int ) messageLength );
        }
        else
        {
            bytesSent = ( int ) send( pConnectionInfo->tcpSocket,
                                      pMessage,
                                      messageLength,
                                      0 );
        }
    }

    /* Unlock the connection mutex. */
    IotMutex_Unlock( &( pConnectionInfo->mutex ) );

    /* Check for errors. */
    if( bytesSent <= 0 )
    {
        AwsIotLogError( "Send failure." );

        return 0;
    }

    if( ( size_t ) bytesSent != messageLength )
    {
        AwsIotLogWarn( "Failed to send %lu bytes, %d bytes sent instead.",
                       ( unsigned long ) messageLength,
                       bytesSent );
    }
    else
    {
        AwsIotLogDebug( "Successfully sent %lu bytes.",
                        ( unsigned long ) messageLength );
    }

    return ( size_t ) bytesSent;
}

/*-----------------------------------------------------------*/

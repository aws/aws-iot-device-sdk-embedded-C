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
 * for POSIX systems with OpenSSL.
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

/* POSIX+OpenSSL network include. */
#include "posix/iot_network_openssl.h"

/* Platform threads include. */
#include "platform/iot_threads.h"

/* Metrics include. */
#include "iot_metrics.h"

/* Configure logs for the functions in this file. */
#ifdef IOT_LOG_LEVEL_NETWORK
    #define _LIBRARY_LOG_LEVEL        IOT_LOG_LEVEL_NETWORK
#else
    #ifdef IOT_LOG_LEVEL_GLOBAL
        #define _LIBRARY_LOG_LEVEL    IOT_LOG_LEVEL_GLOBAL
    #else
        #define _LIBRARY_LOG_LEVEL    IOT_LOG_NONE
    #endif
#endif

#define _LIBRARY_LOG_NAME    ( "NET" )
#include "iot_logging_setup.h"

/*
 * Provide default values for undefined memory allocation functions based on
 * the usage of dynamic memory allocation.
 */
#ifndef IotNetwork_Malloc
    #include <stdlib.h>

/**
 * @brief Memory allocation. This function should have the same signature as
 * [malloc.](http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html)
 */
    #define IotNetwork_Malloc    malloc
#endif
#ifndef IotNetwork_Free
    #include <stdlib.h>

/**
 * @brief Free memory. This function should have the same signature as
 * [free.](http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html)
 */
    #define IotNetwork_Free    free
#endif

/*-----------------------------------------------------------*/

/**
 * @brief An #IotNetworkInterface_t that uses the functions in this file.
 */
const IotNetworkInterface_t _IotNetworkOpenssl =
{
    .create             = IotNetworkOpenssl_Create,
    .setReceiveCallback = IotNetworkOpenssl_SetReceiveCallback,
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
    int bytesAvailable = 0, bytesRead = 0;
    int32_t bytesProcessed = 0;
    uint8_t * pReceiveBuffer = NULL;
    struct pollfd fileDescriptor =
    {
        .events  = POLLIN,
        .revents = 0
    };

    /* Cast function parameter to correct type. */
    IotNetworkConnectionOpenssl_t * const pNetworkConnection = pArgument;

    /* Set the file descriptor for poll. */
    fileDescriptor.fd = pNetworkConnection->socket;

    /* Continuously poll the network socket for events. */
    while( poll( &fileDescriptor, 1, -1 ) == 1 )
    {
        /* Prevent this thread from being cancelled while running. But if the
         * connection mutex is locked, wait until it is available. */
        if( IotMutex_TryLock( &( pNetworkConnection->mutex ) ) == false )
        {
            continue;
        }

        /* If an error event is detected, terminate this thread. */
        if( ( fileDescriptor.revents & POLLERR ) ||
            ( fileDescriptor.revents & POLLHUP ) ||
            ( fileDescriptor.revents & POLLNVAL ) )
        {
            IotLogError( "Detected error on socket %d, receive thread exiting.",
                         pNetworkConnection->socket );
            break;
        }

        /* Query how many bytes are available to read. The value returned by this
         * function may include more than just the data. */
        if( ioctl( pNetworkConnection->socket, FIONREAD, &bytesAvailable ) != 0 )
        {
            IotLogError( "Failed to query bytes available on socket. errno=%d.",
                         errno );

            /* Unlock the connection mutex before polling again. */
            IotMutex_Unlock( &( pNetworkConnection->mutex ) );

            continue;
        }

        IotLogDebug( "%d bytes available on socket %d.",
                     bytesAvailable,
                     pNetworkConnection->socket );

        /* If no bytes can be read, the socket is likely closed. Terminate this thread. */
        if( bytesAvailable == 0 )
        {
            IotLogInfo( "No data available, terminating receive thread for socket %d.",
                        pNetworkConnection->socket );
            break;
        }

        /* Allocate memory to hold the received message. */
        pReceiveBuffer = IotNetwork_Malloc( ( size_t ) bytesAvailable );

        if( pReceiveBuffer == NULL )
        {
            IotLogError( "Failed to allocate %d bytes for socket read on %d.",
                         bytesAvailable,
                         pNetworkConnection->socket );

            /* Terminate on memory allocation failure to prevent unread incoming
             * data from accumulating. */
            break;
        }

        /* Use OpenSSL's SSL_read() function or the POSIX recv() function based on
         * whether the SSL connection context is set up. */
        if( pNetworkConnection->pSslContext != NULL )
        {
            bytesRead = SSL_read( pNetworkConnection->pSslContext,
                                  pReceiveBuffer,
                                  bytesAvailable );
        }
        else
        {
            bytesRead = ( int ) recv( pNetworkConnection->socket,
                                      pReceiveBuffer,
                                      ( size_t ) bytesAvailable,
                                      0 );
        }

        /* Check how many bytes were read. */
        if( bytesRead <= 0 )
        {
            IotLogError( "Error reading from socket %d.",
                         pNetworkConnection->socket );

            IotNetwork_Free( pReceiveBuffer );
            break;
        }

        IotLogDebug( "Received %d bytes from socket %d.",
                     bytesRead,
                     pNetworkConnection->socket );

        /* Invoke the callback function. But if there's no callback to invoke,
         * terminate this thread. */
        if( pNetworkConnection->receiveCallback != NULL )
        {
            bytesProcessed = pNetworkConnection->receiveCallback( pNetworkConnection->pReceiveContext,
                                                                  pNetworkConnection,
                                                                  pReceiveBuffer,
                                                                  ( size_t ) bytesRead,
                                                                  0,
                                                                  IotNetwork_Free );
        }
        else
        {
            /* Free resources and terminate thread. */
            IotNetwork_Free( pReceiveBuffer );

            break;
        }

        /* Free resources and terminate thread if some data was unprocessed. */
        if( bytesProcessed != ( int32_t ) bytesRead )
        {
            if( bytesProcessed < 0 )
            {
                IotLogError( "Receive callback for socket %d returned error."
                             "Receive thread terminating.", pNetworkConnection->socket );
            }
            else
            {
                /* This implementation should never read incomplete packets
                 * because it is able to allocate buffers large enough for
                 * entire streams. */
                IotLogError( "Incomplete data received from network on socket %d.",
                             pNetworkConnection->socket );
            }

            IotNetwork_Free( pReceiveBuffer );
            break;
        }

        /* Unlock the connection mutex before polling again. */
        IotMutex_Unlock( &( pNetworkConnection->mutex ) );
    }

    IotLogDebug( "Network receive thread for socket %d terminating.",
                 pNetworkConnection->socket );

    /* Clear data about the callback. */
    pNetworkConnection->receiveThreadStatus = _TERMINATED;
    pNetworkConnection->receiveCallback = NULL;
    pNetworkConnection->pReceiveContext = NULL;

    /* Unlock the connection mutex before exiting. */
    IotMutex_Unlock( &( pNetworkConnection->mutex ) );

    return NULL;
}

/*-----------------------------------------------------------*/

/**
 * @brief Perform a DNS lookup of a host name and establish a TCP connection.
 *
 * @param[in] pServerInfo Server host name and port.
 * @param[out] pIpAddress Ip address number in network byte order.
 *
 * @return A connected TCP socket number; `-1` if the DNS lookup failed.
 */
static inline int _dnsLookup( const IotNetworkServerInfoOpenssl_t * const pServerInfo, uint32_t * pIpAddress )
{
    int status = 0, tcpSocket = -1;
    const uint16_t netPort = htons( pServerInfo->port );
    struct addrinfo * pListHead = NULL, * pAddressInfo = NULL;
    struct sockaddr_in * pServer = NULL;

    /* Perform a DNS lookup of host name. */
    IotLogDebug( "Performing DNS lookup of %s", pServerInfo->pHostName );
    status = getaddrinfo( pServerInfo->pHostName, NULL, NULL, &pListHead );

    if( status != 0 )
    {
        IotLogError( "DNS lookup failed. %s.", gai_strerror( status ) );

        return -1;
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

        /* Set the port for the connection. */
        IotLogDebug( "Socket creation successful. Attempting connection." );
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
                IotLogWarn( "Failed to close socket %d. errno=%d.",
                            tcpSocket,
                            errno );
            }

            IotLogDebug( "Socket connection failed. Trying next." );
        }
        else
        {
            /* Copy IP address to the output parameter. */
            *pIpAddress = pServer->sin_addr.s_addr;

            /* Connection successful; stop searching the list. */
            IotLogDebug( "Socket connection successful." );
            break;
        }
    }

    freeaddrinfo( pListHead );

    /* If pAddressInfo is NULL, then the entire list of records was parsed but none
     * of them provided a successful connection. */
    if( pAddressInfo == NULL )
    {
        IotLogError( "Failed to connect to all retrieved DNS records." );

        tcpSocket = -1;
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
 *
 * @return `true` if all credentials were successfully read; `false` otherwise.
 */
static inline bool _readCredentials( SSL_CTX * pSSLContext,
                                     const char * const pRootCAPath,
                                     const char * const pClientCertPath,
                                     const char * const pCertPrivateKeyPath )
{
    bool status = true;
    X509 * pRootCa = NULL;

    /* OpenSSL does not provide a single function for reading and loading certificates
     * from files into stores, so the file API must be called. */
    IotLogDebug( "Opening root certificate %s", pRootCAPath );
    FILE * pRootCaFile = fopen( pRootCAPath, "r" );

    if( pRootCaFile == NULL )
    {
        IotLogError( "Failed to open %s", pRootCAPath );

        status = false;
    }

    /* Read the root CA into an X509 object, then close its file handle. */
    if( status == true )
    {
        pRootCa = PEM_read_X509( pRootCaFile, NULL, NULL, NULL );

        if( fclose( pRootCaFile ) != 0 )
        {
            IotLogWarn( "Failed to close file %s", pRootCAPath );
        }

        if( pRootCa == NULL )
        {
            IotLogError( "Failed to parse root CA." );

            status = false;
        }
        else
        {
            /* Add the root CA to certificate store. */
            if( X509_STORE_add_cert( SSL_CTX_get_cert_store( pSSLContext ),
                                     pRootCa ) != 1 )
            {
                IotLogError( "Failed to add root CA to certificate store." );

                status = false;
            }
            else
            {
                IotLogInfo( "Successfully imported root CA." );
            }

            /* Free the root CA object. */
            X509_free( pRootCa );
        }
    }

    /* Import the client certificate. */
    if( status == true )
    {
        if( SSL_CTX_use_certificate_file( pSSLContext,
                                          pClientCertPath,
                                          SSL_FILETYPE_PEM ) != 1 )
        {
            IotLogError( "Failed to import client certificate at %s",
                         pClientCertPath );

            status = false;
        }
        else
        {
            IotLogInfo( "Successfully imported client certificate." );
        }
    }

    /* Import the client certificate private key. */
    if( status == true )
    {
        if( SSL_CTX_use_PrivateKey_file( pSSLContext,
                                         pCertPrivateKeyPath,
                                         SSL_FILETYPE_PEM ) != 1 )
        {
            IotLogError( "Failed to import client certificate private key at %s",
                         pCertPrivateKeyPath );

            status = false;
        }
        else
        {
            IotLogInfo( "Successfully imported client certificate private key." );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

/**
 * @brief Set up TLS on a TCP connection.
 *
 * @param[in] pNetworkConnection An established TCP connection.
 * @param[in] pServerName Remote host name, used for server name indication.
 * @param[in] pCredentials TLS setup parameters.
 *
 * @return #IOT_NETWORK_SUCCESS, #IOT_NETWORK_FAILURE, or #IOT_NETWORK_SYSTEM_ERROR.
 */
static inline IotNetworkError_t _tlsSetup( IotNetworkConnectionOpenssl_t * const pNetworkConnection,
                                           const char * const pServerName,
                                           const IotNetworkCredentialsOpenssl_t * const pOpensslCredentials )
{
    SSL_CTX * pSSLContext = NULL;
    IotNetworkError_t status = IOT_NETWORK_SUCCESS;

    /* Create a new SSL context. */
    #if OPENSSL_VERSION_NUMBER < 0x10100000L
        pSSLContext = SSL_CTX_new( TLSv1_2_client_method() );
    #else
        pSSLContext = SSL_CTX_new( TLS_client_method() );
    #endif

    if( pSSLContext == NULL )
    {
        IotLogError( "Failed to create new SSL context." );

        status = IOT_NETWORK_SYSTEM_ERROR;
    }
    else
    {
        /* Set auto retry mode for the blocking calls to SSL_read and SSL_write. The
         * mask returned by SSL_CTX_set_mode does not need to be checked. */
        IotLogDebug( "New SSL context created. Setting SSL_MODE_AUTO_RETRY." );
        ( void ) SSL_CTX_set_mode( pSSLContext, SSL_MODE_AUTO_RETRY );

        /* Import all credentials. */
        if( _readCredentials( pSSLContext,
                              pOpensslCredentials->pRootCaPath,
                              pOpensslCredentials->pClientCertPath,
                              pOpensslCredentials->pPrivateKeyPath ) == false )
        {
            status = IOT_NETWORK_FAILURE;
        }
        else
        {
            /* Create a new SSL connection context */
            pNetworkConnection->pSslContext = SSL_new( pSSLContext );

            if( pNetworkConnection->pSslContext == NULL )
            {
                IotLogError( "Failed to create new SSL connection context." );

                status = IOT_NETWORK_SYSTEM_ERROR;
            }
        }

        SSL_CTX_free( pSSLContext );
    }

    if( status == IOT_NETWORK_SUCCESS )
    {
        /* Enable SSL peer verification. */
        IotLogDebug( "Setting SSL_VERIFY_PEER." );
        SSL_set_verify( pNetworkConnection->pSslContext, SSL_VERIFY_PEER, NULL );

        /* Set the socket for the SSL connection. */
        if( SSL_set_fd( pNetworkConnection->pSslContext,
                        pNetworkConnection->socket ) != 1 )
        {
            IotLogError( "Failed to set SSL socket %d.", pNetworkConnection->socket );
            status = IOT_NETWORK_SYSTEM_ERROR;
        }

        /* Set up ALPN if requested. */
        if( status == IOT_NETWORK_SUCCESS )
        {
            if( pOpensslCredentials->pAlpnProtos != NULL )
            {
                IotLogDebug( "Setting ALPN protos." );

                if( ( SSL_set_alpn_protos( pNetworkConnection->pSslContext,
                                           ( const unsigned char * ) pOpensslCredentials->pAlpnProtos,
                                           ( unsigned int ) strlen( pOpensslCredentials->pAlpnProtos ) ) != 0 ) )
                {
                    IotLogError( "Failed to set ALPN protos." );
                    status = IOT_NETWORK_SYSTEM_ERROR;
                }
            }
        }

        /* Set TLS MFLN if requested. */
        if( status == IOT_NETWORK_SUCCESS )
        {
            if( pOpensslCredentials->maxFragmentLength > 0 )
            {
                IotLogDebug( "Setting max send fragment length %lu.",
                             ( unsigned long ) pOpensslCredentials->maxFragmentLength );

                /* Set the maximum send fragment length. */
                if( SSL_set_max_send_fragment( pNetworkConnection->pSslContext,
                                               ( long ) pOpensslCredentials->maxFragmentLength ) != 1 )
                {
                    IotLogError( "Failed to set max send fragment length %lu.",
                                 ( unsigned long ) pOpensslCredentials->maxFragmentLength );
                    status = IOT_NETWORK_SYSTEM_ERROR;
                }
                else
                {
                    /* In supported versions of OpenSSL, change the size of the read buffer
                     * to match the maximum fragment length + some extra bytes for overhead.
                     * Note that OpenSSL ignores this setting if it's smaller than the default.
                     */
                    #if OPENSSL_VERSION_NUMBER > 0x10100000L
                        SSL_set_default_read_buffer_len( pNetworkConnection->pSslContext,
                                                         pOpensslCredentials->maxFragmentLength +
                                                         SSL3_RT_MAX_ENCRYPTED_OVERHEAD );
                    #endif
                }
            }
        }

        if( status == IOT_NETWORK_SUCCESS )
        {
            if( pOpensslCredentials->disableSni == false )
            {
                IotLogDebug( "Setting server name %s for SNI.", pServerName );

                if( SSL_set_tlsext_host_name( pNetworkConnection->pSslContext,
                                              pServerName ) != 1 )
                {
                    IotLogError( "Failed to set server name %s for SNI.", pServerName );
                    status = IOT_NETWORK_SYSTEM_ERROR;
                }
            }
        }

        /* Perform the TLS handshake. */
        if( status == IOT_NETWORK_SUCCESS )
        {
            if( SSL_connect( pNetworkConnection->pSslContext ) != 1 )
            {
                IotLogError( "TLS handshake failed." );
                status = IOT_NETWORK_FAILURE;
            }
            else
            {
                IotLogInfo( "TLS handshake succeeded." );
            }
        }

        /* Verify the peer certificate. */
        if( status == IOT_NETWORK_SUCCESS )
        {
            if( SSL_get_verify_result( pNetworkConnection->pSslContext ) != X509_V_OK )
            {
                IotLogError( "Peer certificate verification failed." );
                status = IOT_NETWORK_FAILURE;
            }
            else
            {
                IotLogInfo( "Peer certificate verified. TLS connection established." );
            }
        }

        /* Clean up on error. */
        if( status != IOT_NETWORK_SUCCESS )
        {
            SSL_free( pNetworkConnection->pSslContext );
            pNetworkConnection->pSslContext = NULL;
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

/**
 * @brief Cleans up TLS for a connection.
 *
 * @param[in] pNetworkConnection The TLS connection to clean up.
 */
static inline void _tlsCleanup( IotNetworkConnectionOpenssl_t * const pNetworkConnection )
{
    /* Shut down the TLS connection. */
    IotLogInfo( "Shutting down TLS connection." );

    /* SSL shutdown should be called twice: once to send "close notify" and once
     * more to receive the peer's "close notify". */
    if( SSL_shutdown( pNetworkConnection->pSslContext ) == 0 )
    {
        IotLogDebug( "\"Close notify\" sent. Awaiting peer response." );

        /* The previous call to SSL_shutdown marks the SSL connection as closed.
         * SSL_shutdown must be called again to read the peer response. */
        if( SSL_shutdown( pNetworkConnection->pSslContext ) != 1 )
        {
            IotLogWarn( "No response from peer." );
        }
        else
        {
            IotLogDebug( "Peer response to \"close notify\" received." );
        }
    }

    IotLogInfo( "TLS connection terminated." );

    /* Free the memory used by the TLS connection. */
    SSL_free( pNetworkConnection->pSslContext );
    pNetworkConnection->pSslContext = NULL;
}

/*-----------------------------------------------------------*/

/**
 * @brief Cleans up the receive thread for a connection.
 *
 * @param[in] pNetworkConnection The network connection with the receive thread
 * to clean up.
 *
 * This function must be called with the network connection mutex locked.
 *
 * @return #IOT_NETWORK_SUCCESS or #IOT_NETWORK_SYSTEM_ERROR.
 */
static IotNetworkError_t _cancelReceiveThread( IotNetworkConnectionOpenssl_t * const pNetworkConnection )
{
    int posixError = 0;
    IotNetworkError_t status = IOT_NETWORK_SUCCESS;

    /* Do nothing if this thread is attempting to cancel itself. */
    if( pNetworkConnection->receiveThreadStatus == _ACTIVE )
    {
        if( pNetworkConnection->receiveThread == pthread_self() )
        {
            status = IOT_NETWORK_FAILURE;
        }
    }

    if( status == IOT_NETWORK_SUCCESS )
    {
        if( pNetworkConnection->receiveThreadStatus != _NONE )
        {
            /* Send a cancellation request to the receive thread if active. */
            if( pNetworkConnection->receiveThreadStatus == _ACTIVE )
            {
                posixError = pthread_cancel( pNetworkConnection->receiveThread );

                if( ( posixError != 0 ) && ( posixError != ESRCH ) )
                {
                    IotLogWarn( "Failed to send cancellation request to socket %d receive "
                                "thread. errno=%d.",
                                pNetworkConnection->socket,
                                posixError );

                    status = IOT_NETWORK_SYSTEM_ERROR;
                }
                else
                {
                    pNetworkConnection->receiveThreadStatus = _TERMINATED;
                }
            }

            if( pNetworkConnection->receiveThreadStatus == _TERMINATED )
            {
                /* Join the receive thread. */
                posixError = pthread_join( pNetworkConnection->receiveThread, NULL );

                if( posixError != 0 )
                {
                    IotLogWarn( "Failed to join network receive thread for socket %d. errno=%d.",
                                pNetworkConnection->socket,
                                posixError );
                }

                /* Clear data about the receive thread and callback. */
                pNetworkConnection->receiveThreadStatus = _NONE;
                ( void ) memset( &( pNetworkConnection->receiveThread ), 0x00, sizeof( pthread_t ) );
                pNetworkConnection->receiveCallback = NULL;
                pNetworkConnection->pReceiveContext = NULL;
            }
        }
    }

    return status;
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

IotNetworkError_t IotNetworkOpenssl_Create( void * pConnectionInfo,
                                            void * pCredentialInfo,
                                            void * const pConnection )
{
    int tcpSocket = -1;
    IotNetworkError_t status = IOT_NETWORK_SUCCESS;

    /* Cast function parameters to correct types. */
    const IotNetworkServerInfoOpenssl_t * const pServerInfo = pConnectionInfo;
    const IotNetworkCredentialsOpenssl_t * const pOpensslCredentials = pCredentialInfo;
    IotNetworkConnectionOpenssl_t * const pNetworkConnection = pConnection;

    IotMetricsTcpConnection_t connection = { .remotePort = pServerInfo->port };

    /* Check output parameter. */
    if( pNetworkConnection == NULL )
    {
        IotLogError( "Output parameter for connection create cannot be NULL." );

        return IOT_NETWORK_BAD_PARAMETER;
    }

    /* Check server info. */
    if( ( pServerInfo == NULL ) ||
        ( pServerInfo->pHostName == NULL ) ||
        ( pServerInfo->port == 0 ) )
    {
        IotLogError( "Missing server information." );

        return IOT_NETWORK_BAD_PARAMETER;
    }

    /* Check credentials parameter if given. */
    if( pOpensslCredentials != NULL )
    {
        if( ( pOpensslCredentials->pRootCaPath == NULL ) ||
            ( pOpensslCredentials->pClientCertPath == NULL ) ||
            ( pOpensslCredentials->pPrivateKeyPath == NULL ) )
        {
            IotLogError( "Missing credential information." );

            return IOT_NETWORK_BAD_PARAMETER;
        }
    }

    /* Clear connection data. */
    ( void ) memset( pNetworkConnection, 0x00, sizeof( IotNetworkConnectionOpenssl_t ) );

    /* Create the network connection mutex. */
    if( IotMutex_Create( &( pNetworkConnection->mutex ), true ) == false )
    {
        IotLogError( "Failed to create network connection mutex." );

        return IOT_NETWORK_NO_MEMORY;
    }

    /* Perform a DNS lookup of pHostName. This also establishes a TCP socket. */
    tcpSocket = _dnsLookup( pServerInfo, &connection.remoteIP );

    if( tcpSocket == -1 )
    {
        status = IOT_NETWORK_FAILURE;
    }
    else
    {
        IotLogInfo( "TCP connection successful." );

        /* Set the socket in the network connection. */
        pNetworkConnection->socket = tcpSocket;

        /* Set up TLS if credentials are provided. */
        if( pOpensslCredentials != NULL )
        {
            IotLogInfo( "Setting up TLS." );

            status = _tlsSetup( pNetworkConnection, pServerInfo->pHostName, pOpensslCredentials );
        }
    }

    /* Clean up on error. */
    if( status != IOT_NETWORK_SUCCESS )
    {
        if( tcpSocket != -1 )
        {
            ( void ) close( tcpSocket );
        }

        IotNetworkOpenssl_Destroy( pNetworkConnection );
    }
    else
    {
        connection.id = tcpSocket;
        IotMetrics_AddTcpConnection( &connection );
    }
    return status;
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkOpenssl_SetReceiveCallback( void * pConnection,
                                                        IotNetworkReceiveCallback_t receiveCallback,
                                                        void * pContext )
{
    int posixError = 0;
    IotNetworkError_t status = IOT_NETWORK_SUCCESS;

    /* Cast function parameter to correct type. */
    IotNetworkConnectionOpenssl_t * const pNetworkConnection = pConnection;

    /* Lock the connection mutex before changing the callback and its parameter. */
    IotMutex_Lock( &( pNetworkConnection->mutex ) );

    /* Cancel any active receive thread for this connection. */
    status = _cancelReceiveThread( pNetworkConnection );

    if( status == IOT_NETWORK_SUCCESS )
    {
        /* Create a new receive thread if a callback is given. */
        if( receiveCallback != NULL )
        {
            /* Update the callback and parameter. */
            pNetworkConnection->receiveCallback = receiveCallback;
            pNetworkConnection->pReceiveContext = pContext;

            posixError = pthread_create( &pNetworkConnection->receiveThread,
                                         NULL,
                                         _networkReceiveThread,
                                         pNetworkConnection );

            if( posixError != 0 )
            {
                IotLogError( "Failed to create socket %d network receive thread. errno=%d.",
                             pNetworkConnection->socket,
                             posixError );
                status = IOT_NETWORK_SYSTEM_ERROR;
            }
            else
            {
                pNetworkConnection->receiveThreadStatus = _ACTIVE;
            }
        }
    }

    /* Unlock the connection mutex. */
    IotMutex_Unlock( &( pNetworkConnection->mutex ) );

    return status;
}

/*-----------------------------------------------------------*/

size_t IotNetworkOpenssl_Send( void * pConnection,
                               const uint8_t * pMessage,
                               size_t messageLength )
{
    int bytesSent = 0;
    struct pollfd fileDescriptor =
    {
        .events  = POLLOUT,
        .revents = 0
    };

    /* Cast function parameter to correct type. */
    IotNetworkConnectionOpenssl_t * const pNetworkConnection = pConnection;

    /* Check parameters. */
    if( ( pNetworkConnection == NULL ) || ( pMessage == NULL ) || ( messageLength == 0 ) )
    {
        IotLogError( "Bad parameter to network connection send." );

        return 0;
    }

    IotLogDebug( "Sending %lu bytes over socket %d.",
                 ( unsigned long ) messageLength,
                 pNetworkConnection->socket );

    /* Set the file descriptor for poll. */
    fileDescriptor.fd = pNetworkConnection->socket;

    /* Lock the connection mutex to prevent the connection from being closed
     * while sending. */
    IotMutex_Lock( &( pNetworkConnection->mutex ) );

    /* Check that it's possible to send data right now. */
    if( poll( &fileDescriptor, 1, 0 ) == 1 )
    {
        /* Use OpenSSL's SSL_write() function or the POSIX send() function based on
         * whether the SSL connection context is set up. */
        if( pNetworkConnection->pSslContext != NULL )
        {
            bytesSent = SSL_write( pNetworkConnection->pSslContext,
                                   pMessage,
                                   ( int ) messageLength );
        }
        else
        {
            bytesSent = ( int ) send( pNetworkConnection->socket,
                                      pMessage,
                                      messageLength,
                                      0 );
        }
    }
    else
    {
        IotLogError( "Not possible to send on socket %d.", pNetworkConnection->socket );
    }

    /* Unlock the connection mutex. */
    IotMutex_Unlock( &( pNetworkConnection->mutex ) );

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

size_t IotNetworkOpenssl_Receive( void * pConnection,
                                  uint8_t * const pBuffer,
                                  size_t bytesRequested )
{
    int bytesRead = 0;
    size_t totalBytesRead = 0;
    struct pollfd fileDescriptor =
    {
        .events  = POLLIN | POLLPRI,
        .revents = 0
    };

    /* Cast function parameter to correct type. */
    IotNetworkConnectionOpenssl_t * const pNetworkConnection = pConnection;

    /* Check parameters. */
    if( ( pNetworkConnection == NULL ) || ( pBuffer == NULL ) || ( bytesRequested == 0 ) )
    {
        IotLogError( "Bad parameter to network connection receive." );

        return 0;
    }

    IotLogDebug( "Blocking to wait for %lu bytes on socket %d.",
                 ( unsigned long ) bytesRequested,
                 pNetworkConnection->socket );

    /* Set the file descriptor for poll. */
    fileDescriptor.fd = pNetworkConnection->socket;

    /* Lock the connection mutex to prevent the connection from being closed
     * while receiving. */
    IotMutex_Lock( &( pNetworkConnection->mutex ) );

    /* Continuously block on the socket for available data. */
    while( poll( &fileDescriptor, 1, -1 ) == 1 )
    {
        /* If an error event is detected, stop receiving. */
        if( ( fileDescriptor.revents & POLLERR ) ||
            ( fileDescriptor.revents & POLLHUP ) ||
            ( fileDescriptor.revents & POLLNVAL ) )
        {
            IotLogError( "Error receiving on socket %d after %lu bytes;"
                         " stopping blocking receive.",
                         ( unsigned long ) totalBytesRead,
                         pNetworkConnection->socket );
            break;
        }

        /* Use OpenSSL's SSL_read() function or the POSIX recv() function based on
         * whether the SSL connection context is set up. */
        if( pNetworkConnection->pSslContext != NULL )
        {
            bytesRead = SSL_read( pNetworkConnection->pSslContext,
                                  pBuffer + totalBytesRead,
                                  ( int ) ( bytesRequested - totalBytesRead ) );
        }
        else
        {
            bytesRead = ( int ) recv( pNetworkConnection->socket,
                                      pBuffer + totalBytesRead,
                                      bytesRequested - totalBytesRead,
                                      0 );
        }

        /* Check for an error during receive. */
        if( bytesRead <= 0 )
        {
            IotLogError( "Error receiving from socket %d after receiving %lu bytes",
                         pNetworkConnection->socket,
                         ( unsigned long ) totalBytesRead );
            break;
        }

        totalBytesRead += ( size_t ) bytesRead;

        /* Check if any more data needs to be read. */
        if( totalBytesRead == bytesRequested )
        {
            IotLogDebug( "Successfully received %lu bytes.",
                         ( unsigned long ) bytesRequested );

            break;
        }
    }

    /* Unlock the connection mutex. */
    IotMutex_Unlock( &( pNetworkConnection->mutex ) );

    return totalBytesRead;
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkOpenssl_Close( void * pConnection )
{
    /* Cast function parameter to correct type. */
    IotNetworkConnectionOpenssl_t * const pNetworkConnection = pConnection;

    /* Check parameter. */
    if( pNetworkConnection == NULL )
    {
        IotLogError( "NULL parameter to network connection close." );

        return IOT_NETWORK_BAD_PARAMETER;
    }

    /* Lock the connection mutex to block the receive thread. */
    IotMutex_Lock( &( pNetworkConnection->mutex ) );

    /* Cancel any receive thread for this connection. The return value is not
     * checked because the socket will be closed anyways. */
    ( void ) _cancelReceiveThread( pNetworkConnection );

    /* If TLS was set up for this connection, clean it up. */
    if( pNetworkConnection->pSslContext != NULL )
    {
        _tlsCleanup( pNetworkConnection );
    }

    /* Close the connection. */
    if( close( pNetworkConnection->socket ) != 0 )
    {
        IotLogWarn( "Could not close socket %d. errno=%d.",
                    pNetworkConnection->socket,
                    errno );
    }
    else
    {
        IotLogInfo( "Connection (socket %d) closed.",
                    pNetworkConnection->socket );
    }

    /* Unlock the connection mutex. */
    IotMutex_Unlock( &( pNetworkConnection->mutex ) );

    /* Remove the socket from metrics. */
    IotMetrics_RemoveTcpConnection( pNetworkConnection->socket );

    return IOT_NETWORK_SUCCESS;
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkOpenssl_Destroy( void * pConnection )
{
    IotNetworkError_t status = IOT_NETWORK_SUCCESS;

    /* Cast function parameter to correct type. */
    IotNetworkConnectionOpenssl_t * const pNetworkConnection = pConnection;

    if( pNetworkConnection == NULL )
    {
        IotLogError( "NULL parameter to network connection destroy." );

        status = IOT_NETWORK_BAD_PARAMETER;
    }
    else
    {
        /* Clean up the connection by destroying its mutex. */
        IotMutex_Destroy( &( pNetworkConnection->mutex ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

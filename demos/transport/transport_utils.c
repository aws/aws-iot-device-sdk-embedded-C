/*
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

/**
 * @file transport_utils.c
 * @brief Implementation of wrapper utilities for using OpenSSL as the TLS stack
 * on POSIX platform.
 */

/* POSIX socket includes. */
#include <netdb.h>
#include <poll.h>
#include <time.h>
#include <unistd.h>

#include <sys/socket.h>
#include <sys/types.h>

/* Standard includes. */
#include <string.h>
#include <stdlib.h>
#include <assert.h>

/* Include config file before non-system headers. */
#include "transport_config.h"

/* Header file for the library. */
#include "transport_utils.h"

/*-----------------------------------------------------------*/

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS    ( 20 )

/*-----------------------------------------------------------*/

int tcpConnectToServer( const char * pServer,
                        uint16_t port,
                        int * pTcpSocket )
{
    int status = EXIT_SUCCESS;
    struct addrinfo hints, * pIndex, * pListHead = NULL;
    struct sockaddr * pServerInfo;
    uint16_t netPort = htons( port );
    socklen_t serverInfoLength;

    /* Add hints to retrieve only TCP sockets in getaddrinfo. */
    ( void ) memset( &hints, 0x00, sizeof( hints ) );
    /* Address family of either IPv4 or IPv6. */
    hints.ai_family = AF_UNSPEC;
    /* TCP Socket. */
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_protocol = IPPROTO_TCP;

    LogInfo( ( "Looking up DNS for endpoint: %s", pServer ) );

    /* Perform a DNS lookup on the given host name. */
    status = getaddrinfo( pServer, NULL, &hints, &pListHead );

    LogInfo( ( "Resolved DNS for endpoint: %s", pServer ) );

    if( status != -1 )
    {
        /* Attempt to connect to one of the retrieved DNS records. */
        for( pIndex = pListHead; pIndex != NULL; pIndex = pIndex->ai_next )
        {
            LogInfo( ( "Attempting to create TCP client socket" ) );

            *pTcpSocket = socket( pIndex->ai_family, pIndex->ai_socktype, pIndex->ai_protocol );

            if( *pTcpSocket == -1 )
            {
                continue;
            }

            pServerInfo = pIndex->ai_addr;

            if( pServerInfo->sa_family == AF_INET )
            {
                /* IPv4 */
                ( ( struct sockaddr_in * ) pServerInfo )->sin_port = netPort;
                serverInfoLength = sizeof( struct sockaddr_in );
            }
            else
            {
                /* IPv6 */
                ( ( struct sockaddr_in6 * ) pServerInfo )->sin6_port = netPort;
                serverInfoLength = sizeof( struct sockaddr_in6 );
            }

            LogInfo( ( "Attempting to connect with socket: Fd=%d", *pTcpSocket ) );

            status = connect( *pTcpSocket, pServerInfo, serverInfoLength );

            if( status == -1 )
            {
                LogError( ( "Connection with socket failed: Fd=%d", *pTcpSocket ) );
                close( *pTcpSocket );
            }
            else
            {
                break;
            }
        }

        if( pIndex == NULL )
        {
            /* Fail if no connection could be established. */
            status = EXIT_FAILURE;
            LogError( ( "Located but could not connect to MQTT broker %.*s.",
                        ( int ) strlen( pServer ),
                        pServer ) );
        }
        else
        {
            status = EXIT_SUCCESS;
            LogInfo( ( "TCP connection established with %.*s.\n\n",
                       ( int ) strlen( pServer ),
                       pServer ) );
        }
    }
    else
    {
        LogError( ( "Could not locate MQTT broker %.*s.",
                    ( int ) strlen( pServer ),
                    pServer ) );
        status = EXIT_FAILURE;
    }

    if( pListHead != NULL )
    {
        freeaddrinfo( pListHead );
    }

    return status;
}

/*-----------------------------------------------------------*/

int tlsSetup( int tcpSocket,
              const char * pServerCertPath,
              SSL ** pSslContext )
{
    int status = EXIT_FAILURE, sslStatus = 0;
    FILE * pRootCaFile = NULL;
    X509 * pRootCa = NULL;

    assert( tcpSocket >= 0 );

    /* Setup for creating a TLS client. */
    SSL_CTX * pSslSetup = SSL_CTX_new( TLS_client_method() );

    if( pSslSetup != NULL )
    {
        /* Set auto retry mode for the blocking calls to SSL_read and SSL_write.
         * The mask returned by SSL_CTX_set_mode does not need to be checked. */
        ( void ) SSL_CTX_set_mode( pSslSetup, SSL_MODE_AUTO_RETRY );

        /* OpenSSL does not provide a single function for reading and loading certificates
         * from files into stores, so the file API must be called. */
        pRootCaFile = fopen( pServerCertPath, "r" );

        if( pRootCaFile != NULL )
        {
            pRootCa = PEM_read_X509( pRootCaFile, NULL, NULL, NULL );
        }
        else
        {
            LogError( ( "Unable to find the certificate file in the path"
                        " provided by SERVER_CERT_PATH(%s).",
                        pServerCertPath ) );
        }

        if( pRootCa != NULL )
        {
            sslStatus = X509_STORE_add_cert( SSL_CTX_get_cert_store( pSslSetup ),
                                             pRootCa );
        }
        else
        {
            LogError( ( "Failed to parse the server certificate from"
                        " file %s. Please validate the certificate.",
                        pServerCertPath ) );
        }
    }

    /* Set up the TLS connection. */
    if( sslStatus == 1 )
    {
        /* Create a new SSL context. */
        *pSslContext = SSL_new( pSslSetup );

        if( *pSslContext != NULL )
        {
            /* Enable SSL peer verification. */
            SSL_set_verify( *pSslContext, SSL_VERIFY_PEER, NULL );

            sslStatus = SSL_set_fd( *pSslContext, tcpSocket );
        }
        else
        {
            LogError( ( "Failed to create a new SSL context." ) );
            sslStatus = 0;
        }

        /* Perform the TLS handshake. */
        if( sslStatus == 1 )
        {
            sslStatus = SSL_connect( *pSslContext );
        }
        else
        {
            LogError( ( "Failed to set the socket fd to SSL context." ) );
        }

        if( sslStatus == 1 )
        {
            if( SSL_get_verify_result( *pSslContext ) != X509_V_OK )
            {
                sslStatus = 0;
            }
        }
        else
        {
            LogError( ( "Failed to perform TLS handshake." ) );
        }

        /* Clean up on error. */
        if( sslStatus == 0 )
        {
            SSL_free( *pSslContext );
            *pSslContext = NULL;
        }
    }
    else
    {
        LogError( ( "Failed to add certificate to store." ) );
    }

    if( pRootCaFile != NULL )
    {
        ( void ) fclose( pRootCaFile );
    }

    if( pRootCa != NULL )
    {
        X509_free( pRootCa );
    }

    if( pSslSetup != NULL )
    {
        SSL_CTX_free( pSslSetup );
    }

    /* Log failure or success and update the correct exit status to return. */
    if( sslStatus == 0 )
    {
        LogError( ( "Failed to establish a TLS connection." ) );
        status = EXIT_FAILURE;
    }
    else
    {
        LogInfo( ( "Established a TLS connection." ) );
        status = EXIT_SUCCESS;
    }

    return status;
}

/*-----------------------------------------------------------*/

void closeTlsSession( SSL * pSslContext )
{
    /* Need to call SSL shutdown twice: once to send "close notify" and
     * once more to receive the peer's "close notify". */
    if( SSL_shutdown( pSslContext ) == 0 )
    {
        ( void ) SSL_shutdown( pSslContext );
    }

    SSL_free( pSslContext );
}

/*-----------------------------------------------------------*/

void closeTcpConnection( int tcpSocket )
{
/* Close TCP connection if established. */
    if( tcpSocket != -1 )
    {
        shutdown( tcpSocket, SHUT_RDWR );
        close( tcpSocket );
    }
}

/*-----------------------------------------------------------*/

int32_t transportSend( SSL * pSslContext,
                       const void * pMessage,
                       size_t bytesToSend )
{
    int32_t bytesSent = 0;
    int pollStatus = 0;
    struct pollfd fileDescriptor =
    {
        .events  = POLLOUT,
        .revents = 0
    };

    /* Set the file descriptor for poll. */
    fileDescriptor.fd = SSL_get_fd( pSslContext );

    /* Poll the file descriptor to check if SSL_Write can be done now. */
    pollStatus = poll( &fileDescriptor, 1, TRANSPORT_SEND_RECV_TIMEOUT_MS );

    if( pollStatus > 0 )
    {
        bytesSent = ( int32_t ) SSL_write( pSslContext, pMessage, bytesToSend );
        LogInfo( ( "Bytes sent over SSL: %d", bytesSent ) );
    }
    else if( pollStatus == 0 )
    {
        LogDebug( ( "Timed out while polling SSL socket for write buffer availability." ) );
    }
    else
    {
        LogError( ( "Polling of the SSL socket for write buffer availability failed"
                    " with status %d.",
                    pollStatus ) );
        bytesSent = -1;
    }

    return bytesSent;
}

/*-----------------------------------------------------------*/

int32_t transportRecv( SSL * pSslContext,
                       void * pBuffer,
                       size_t bytesToRecv )
{
    int32_t bytesReceived = 0;
    int pollStatus = -1, bytesAvailableToRead = 0;
    struct pollfd fileDescriptor =
    {
        .events  = POLLIN | POLLPRI,
        .revents = 0
    };

    /* Set the file descriptor for poll. */
    fileDescriptor.fd = SSL_get_fd( pSslContext );

    /* Check if there are any pending data available for read. */
    bytesAvailableToRead = SSL_pending( pSslContext );

    /* Poll only if there is no data available yet to read. */
    if( bytesAvailableToRead <= 0 )
    {
        pollStatus = poll( &fileDescriptor, 1, TRANSPORT_SEND_RECV_TIMEOUT_MS );
    }

    /* SSL read of data. */
    if( ( pollStatus > 0 ) || ( bytesAvailableToRead > 0 ) )
    {
        bytesReceived = ( int32_t ) SSL_read( pSslContext, pBuffer, bytesToRecv );
    }
    /* Poll timed out. */
    else if( pollStatus == 0 )
    {
        LogDebug( ( "Poll timed out and there is no data to read from the buffer." ) );
    }
    else
    {
        LogError( ( "Poll returned with status = %d.", pollStatus ) );
        bytesReceived = -1;
    }

    return bytesReceived;
}

/*-----------------------------------------------------------*/

uint32_t getTimeMs( void )
{
    uint32_t timeMs;
    struct timespec timeSpec;

    /* Get the MONOTONIC time. */
    clock_gettime( CLOCK_MONOTONIC, &timeSpec );

    /* Calculate the milliseconds from timespec. */
    timeMs = ( uint32_t ) ( timeSpec.tv_sec * 1000 )
             + ( uint32_t ) ( timeSpec.tv_nsec / ( 1000 * 1000 ) );

    return timeMs;
}

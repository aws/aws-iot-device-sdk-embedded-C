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

/* Standard includes. */
#include <assert.h>
#include <stdlib.h>
#include <string.h>

/* POSIX socket includes. */
#include <errno.h>
#include <netdb.h>
#include <time.h>
#include <poll.h>
#include <unistd.h>
#include <arpa/inet.h>

#include <sys/socket.h>
#include <sys/types.h>

#include "tcp_posix.h"

/*-----------------------------------------------------------*/

/**
 * @brief Number of DNS records to attempt a connection.
 *
 * @note Negative value implies attempting to connect to all DNS records
 * until successful.
 */
#define NUM_DNS_RECORDS_TO_TRY    ( -1 )

/**
 * @brief Number of milliseconds in one second.
 */
#define ONE_SEC_TO_MS             ( 1000 )

/**
 * @brief Number of microseconds in one millisecond.
 */
#define ONE_MS_TO_US              ( 1000 )

/*-----------------------------------------------------------*/

/**
 * @brief Defined by transport layer to check send or receive error.
 */
extern int errno;

/**
 * @brief Definition of the network context.
 *
 * @note An integer is used to store the descriptor of the socket.
 */
struct NetworkContext
{
    int tcpSocket;
};

/*-----------------------------------------------------------*/

/**
 * @brief Resolve a host name.
 *
 * @brief param[in] pHostName Server host name.
 * @brief param[in] hostNameLength Length associated with host name.
 * @brief param[out] pListHead List containing resolved DNS records.
 *
 * @return #TCP_SUCCESS if successful; #TCP_DNS_FAILURE, #TCP_CONNECT_FAILURE on error.
 */
static TCPStatus_t resolveHostName( const char * pHostName,
                                    size_t hostNameLength,
                                    struct addrinfo ** pListHead );

/**
 * @brief Traverse list of DNS records and return successfully if able to connect to one.
 *
 * @brief param[in] pListHead List containing resolved DNS records.
 * @brief param[in] pHostName Server host name.
 * @brief param[in] hostNameLength Length associated with host name.
 * @brief param[in] port Server port in host-order.
 * @brief param[in] pTcpSocket Pointer to the socket descriptor.
 * @brief param[in] maxAttempts Number of DNS records to attempt connection.
 *
 * @note If maxAttempts is negative, attempt to connect to all DNS records
 * until successful.
 *
 * @return #TCP_SUCCESS if successful; #TCP_CONNECT_FAILURE on error.
 */
static TCPStatus_t attemptConnection( struct addrinfo * pListHead,
                                      const char * pHostName,
                                      size_t hostNameLength,
                                      uint16_t port,
                                      int * pTcpSocket,
                                      int32_t maxAttempts );

/**
 * @brief Log possible error from setsockopt and return appropriate status.
 *
 * @return #TCP_API_ERROR, #TCP_INSUFFICIENT_MEMORY, #TCP_INVALID_PARAMETER on error.
 */
static TCPStatus_t retreiveError( void );

/*-----------------------------------------------------------*/

static TCPStatus_t resolveHostName( const char * pHostName,
                                    size_t hostNameLength,
                                    struct addrinfo ** pListHead )
{
    TCPStatus_t returnStatus = TCP_SUCCESS;
    int dnsStatus = -1;
    struct addrinfo hints;

    assert( pHostName != NULL );
    assert( hostNameLength > 0 );

    /* Add hints to retrieve only TCP sockets in getaddrinfo. */
    ( void ) memset( &hints, 0, sizeof( hints ) );

    /* Address family of either IPv4 or IPv6. */
    hints.ai_family = AF_UNSPEC;
    /* TCP Socket. */
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_protocol = IPPROTO_TCP;

    /* Perform a DNS lookup on the given host name. */
    dnsStatus = getaddrinfo( pHostName, NULL, &hints, pListHead );

    if( dnsStatus == -1 )
    {
        LogError( ( "Could not resolve host %.*s.\n",
                    ( int32_t ) hostNameLength,
                    pHostName ) );
        returnStatus = TCP_DNS_FAILURE;
    }

    return returnStatus;
}

static TCPStatus_t attemptConnection( struct addrinfo * pListHead,
                                      const char * pHostName,
                                      size_t hostNameLength,
                                      uint16_t port,
                                      int * pTcpSocket,
                                      int32_t maxAttempts )
{
    TCPStatus_t returnStatus = TCP_SUCCESS;
    struct addrinfo * pIndex = NULL;
    struct sockaddr * pAddrInfo;
    socklen_t addrInfoLength;
    uint16_t netPort = -1;
    int curAttempts = 0, connectStatus = 0;
    char resolvedIpAddr[ INET6_ADDRSTRLEN ];

    assert( pListHead != NULL );
    assert( pHostName != NULL );
    assert( hostNameLength > 0 );
    assert( pTcpSocket != NULL );

    netPort = htons( port );

    LogDebug( ( "Performing DNS lookup: Host=%.*s.",
                ( int32_t ) hostNameLength,
                pHostName ) );

    /* Attempt to connect to one of the retrieved DNS records. */
    for( pIndex = pListHead; pIndex != NULL; pIndex = pIndex->ai_next )
    {
        *pTcpSocket = socket( pIndex->ai_family,
                              pIndex->ai_socktype,
                              pIndex->ai_protocol );

        if( *pTcpSocket == -1 )
        {
            continue;
        }

        pAddrInfo = pIndex->ai_addr;

        if( pAddrInfo->sa_family == AF_INET )
        {
            /* Store IPv4 in string to log. */
            ( ( struct sockaddr_in * ) pAddrInfo )->sin_port = netPort;
            addrInfoLength = sizeof( struct sockaddr_in );
            ( void ) inet_ntop( pAddrInfo->sa_family,
                                &( ( struct sockaddr_in * ) pAddrInfo )->sin_addr,
                                resolvedIpAddr,
                                sizeof( resolvedIpAddr ) );
        }
        else
        {
            /* Store IPv6 in string to log. */
            ( ( struct sockaddr_in6 * ) pAddrInfo )->sin6_port = netPort;
            addrInfoLength = sizeof( struct sockaddr_in6 );
            ( void ) inet_ntop( pAddrInfo->sa_family,
                                &( ( struct sockaddr_in6 * ) pAddrInfo )->sin6_addr,
                                resolvedIpAddr,
                                sizeof( resolvedIpAddr ) );
        }

        LogDebug( ( "Attempting to connect to server: Host=%.*s, IP address=%s.",
                    ( int32_t ) hostNameLength,
                    pHostName,
                    resolvedIpAddr ) );

        connectStatus = connect( *pTcpSocket, pAddrInfo, addrInfoLength );

        if( connectStatus == -1 )
        {
            LogError( ( "Failed to connect to server: Host=%.*s, IP address=%s.",
                        ( int32_t ) hostNameLength,
                        pHostName,
                        resolvedIpAddr ) );
            close( *pTcpSocket );
        }
        else
        {
            LogDebug( ( "Connected to IP address: %s.",
                        resolvedIpAddr ) );
            break;
        }

        curAttempts += 1;

        if( ( maxAttempts >= 0 ) && ( curAttempts >= maxAttempts ) )
        {
            /* Fail if no connection could be established. */
            LogError( ( "Could not connect to any resolved IP address from %.*s "
                        "after %d attempts.",
                        ( int32_t ) hostNameLength,
                        pHostName,
                        curAttempts ) );
            returnStatus = TCP_CONNECT_FAILURE;
            break;
        }
    }

    if( pIndex == NULL )
    {
        /* Fail if no connection could be established. */
        LogError( ( "Could not connect to any resolved IP address from %.*s.",
                    ( int32_t ) hostNameLength,
                    pHostName ) );
        returnStatus = TCP_CONNECT_FAILURE;
    }
    else
    {
        LogDebug( ( "Established TCP connection: Server=%.*s.\n",
                    ( int32_t ) hostNameLength,
                    pHostName ) );
        returnStatus = TCP_SUCCESS;
    }

    freeaddrinfo( pListHead );

    return returnStatus;
}

static TCPStatus_t retreiveError( void )
{
    TCPStatus_t returnStatus = TCP_API_ERROR;

    switch( errno )
    {
        case EBADF:
            LogError( ( "The socket argument is not a valid file descriptor." ) );
            break;

        case ECONNRESET:
            LogError( ( "A connection was forcibly closed by a peer." ) );
            break;

        case EDESTADDRREQ:
            LogError( ( "The socket is not connection-mode and no peer address is set." ) );
            break;

        case EINTR:
            LogError( ( "A signal interrupted send/recv." ) );
            break;

        case EMSGSIZE:
            LogError( ( "The message is too large to be sent all at once, as the socket requires." ) );
            break;

        case ENOTCONN:
            LogError( ( "The socket is not connected." ) );
            break;

        case EOPNOTSUPP:
            LogError( ( "The socket argument is associated with a socket that does not support one or more of the values set in flags." ) );
            break;

        case EPIPE:
            LogError( ( "The socket is shut down for writing, or the socket is connection-mode and is no longer connected. In the latter case, and if the socket is of type SOCK_STREAM or SOCK_SEQPACKET and the MSG_NOSIGNAL flag is not set, the SIGPIPE signal is generated to the calling thread." ) );
            break;

        case EDOM:
            LogError( ( "The send and receive timeout values are too big to fit "
                        "into the timeout fields in the socket structure." ) );
            break;

        case EINVAL:
            LogError( ( "The specified option is invalid at the specified "
                        "socket level or the socket has been shut down." ) );
            break;

        case EISCONN:
            LogError( ( "The socket is already connected, and a specified option "
                        "cannot be set while the socket is connected." ) );
            break;

        case ENOPROTOOPT:
            LogError( ( "The option is not supported by the protocol." ) );
            break;

        case ENOTSOCK:
            LogError( ( "The socket argument does not refer to a socket." ) );
            break;

        case ENOMEM:
            LogError( ( "There was insufficient memory available for the "
                        "operation to complete." ) );
            break;

        case ENOBUFS:
            LogError( ( "Insufficient resources are available in the system to "
                        "complete the call." ) );
            break;
    }

    if( ( errno == ENOMEM ) || ( errno == ENOBUFS ) )
    {
        returnStatus = TCP_INSUFFICIENT_MEMORY;
    }
    else if( ( errno == ENOTSOCK ) || ( errno == EDOM ) || ( errno == EBADF ) )
    {
        returnStatus = TCP_INVALID_PARAMETER;
    }
    else
    {
        /* Empty else. */
    }

    return returnStatus;
}

TCPStatus_t TCP_Connect( const char * pHostName,
                         size_t hostNameLength,
                         uint16_t port,
                         int * pTcpSocket,
                         uint32_t sendTimeoutMs,
                         uint32_t recvTimeoutMs )
{
    TCPStatus_t returnStatus = TCP_SUCCESS;
    struct addrinfo * pListHead = NULL;
    struct timeval transportTimeout;
    int setTimeoutStatus = -1;

    if( pHostName == NULL )
    {
        LogError( ( "Parameter check failed: pHostName is NULL." ) );
        returnStatus = TCP_INVALID_PARAMETER;
    }
    else if( pTcpSocket == NULL )
    {
        LogError( ( "Parameter check failed: pOpensslCredentials is NULL." ) );
        returnStatus = TCP_INVALID_PARAMETER;
    }
    else if( hostNameLength == 0 )
    {
        LogError( ( "Parameter check failed: hostNameLength must be greater than 0." ) );
        returnStatus = TCP_INVALID_PARAMETER;
    }
    else
    {
        /* Empty else. */
    }

    if( returnStatus == TCP_SUCCESS )
    {
        returnStatus = resolveHostName( pHostName, hostNameLength, &pListHead );
    }

    if( returnStatus == TCP_SUCCESS )
    {
        returnStatus = attemptConnection( pListHead,
                                          pHostName, hostNameLength,
                                          port,
                                          pTcpSocket,
                                          NUM_DNS_RECORDS_TO_TRY );
    }

    /* Set the send timeout. */
    if( returnStatus == TCP_SUCCESS )
    {
        transportTimeout.tv_sec = ( sendTimeoutMs / ONE_SEC_TO_MS );
        transportTimeout.tv_usec = ( ONE_MS_TO_US * ( sendTimeoutMs % ONE_SEC_TO_MS ) );

        setTimeoutStatus = setsockopt( *pTcpSocket,
                                       SOL_SOCKET,
                                       SO_SNDTIMEO,
                                       &transportTimeout,
                                       sizeof( transportTimeout ) );

        if( setTimeoutStatus < 0 )
        {
            LogError( ( "Setting socket send timeout failed." ) );
            returnStatus = retreiveError();
        }
        else
        {
            returnStatus = TCP_SUCCESS;
        }
    }

    /* Set the receive timeout. */
    if( returnStatus == TCP_SUCCESS )
    {
        transportTimeout.tv_sec = ( recvTimeoutMs / ONE_SEC_TO_MS );
        transportTimeout.tv_usec = ( ONE_MS_TO_US * ( recvTimeoutMs % ONE_SEC_TO_MS ) );

        setTimeoutStatus = setsockopt( *pTcpSocket,
                                       SOL_SOCKET,
                                       SO_RCVTIMEO,
                                       &transportTimeout,
                                       sizeof( transportTimeout ) );

        if( setTimeoutStatus < 0 )
        {
            LogError( ( "Setting socket receive timeout failed." ) );
            returnStatus = retreiveError();
        }
        else
        {
            returnStatus = TCP_SUCCESS;
        }
    }

    return returnStatus;
}

TCPStatus_t TCP_Disconnect( int tcpSocket )
{
    TCPStatus_t returnStatus = TCP_SUCCESS;

    if( tcpSocket > 0 )
    {
        ( void ) shutdown( tcpSocket, SHUT_RDWR );
        ( void ) close( tcpSocket );
    }
    else
    {
        LogError( ( "Parameter check failed: tcpSocket was negative." ) );
        returnStatus = TCP_INVALID_PARAMETER;
    }

    return returnStatus;
}

int32_t TCP_Recv( NetworkContext_t pContext,
                  void * pBuffer,
                  size_t bytesToRecv )
{
    int32_t bytesReceived = 0;

    bytesReceived = recv( pContext->tcpSocket, pBuffer, bytesToRecv, 0 );

    if( bytesReceived == 0 )
    {
        /* Server closed the connection, treat it as an error. */
        bytesReceived = -1;
    }
    else if( bytesReceived < 0 )
    {
        ( void ) retreiveError();

        /* Check if it was time out. */
        if( ( errno == EAGAIN ) || ( errno == EWOULDBLOCK ) )
        {
            /* Set return value to 0 to indicate nothing to receive. */
            bytesReceived = 0;
        }
    }
    else
    {
        /* Empty else. */
    }

    return bytesReceived;
}

int32_t TCP_Send( NetworkContext_t pContext,
                  const void * pBuffer,
                  size_t bytesToSend )
{
    int32_t bytesSent = 0;

    bytesSent = send( pContext->tcpSocket, pBuffer, bytesToSend, 0 );

    if( bytesSent < 0 )
    {
        ( void ) retreiveError();

        /* Check if it was time out */
        if( ( errno == EAGAIN ) || ( errno == EWOULDBLOCK ) )
        {
            /* Set return value to 0 to indicate that send had timed out. */
            bytesSent = 0;
        }
    }

    return bytesSent;
}

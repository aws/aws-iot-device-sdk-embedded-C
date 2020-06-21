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

/*-----------------------------------------------------------*/

/**
 * @brief Defined by transport layer to check send or receive error.
 */
extern int errno;

/**
 * @brief Timeout for transport send.
 *
 * @note Setting to a negative value implies an infinite timeout.
 */
static int tcpSendTimeout = -1;

/**
 * @brief Timeout for transport recv.
 *
 * @note Setting to a negative value implies an infinite timeout.
 */
static int tcpRecvTimeout = -1;

/**
 * @brief String for storing the resolved IP address to log.
 */
static char resolvedIpAddr[ INET6_ADDRSTRLEN ];

/**
 * @brief Defined by transport layer to check error from setsockopt.
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
TCPStatus_t resolveHostName( const char * pHostName,
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
TCPStatus_t attemptConnection( struct addrinfo * pListHead,
                               const char * pHostName,
                               size_t hostNameLength,
                               uint16_t port,
                               int * pTcpSocket,
                               int32_t maxAttempts );

/**
 * @brief Log possible error from setsockopt and return appropriate status.
 *
 * @brief param[in] pHostName Server host name.
 * @brief param[in] hostNameLength Length associated with host name.
 * @brief param[out] pListHead List containing resolved DNS records.
 *
 * @return #TCP_SUCCESS if successful; #TCP_DNS_FAILURE, #TCP_CONNECT_FAILURE on error.
 */
TCPStatus_t retreiveError();

/*-----------------------------------------------------------*/

TCPStatus_t resolveHostName( const char * pHostName,
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

TCPStatus_t attemptConnection( struct addrinfo * pListHead,
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

TCPStatus_t retreiveError()
{
    TCPStatus_t returnStatus = TCP_API_ERROR;

    switch( errno )
    {
        case EBADF:
            LogError( ( "The socket argument is not a valid file descriptor." ) );
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
                         int sendTimeout,
                         int recvTimeout )
{
    TCPStatus_t returnStatus = TCP_SUCCESS;
    struct addrinfo * pListHead = NULL;
    struct timeval transportTimeout;

    transportTimeout.tv_sec = 0;

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
        transportTimeout.tv_usec = ( sendTimeout * 1000 );

        setTimeoutStatus = setsockopt( *pTcpSocket,
                                       SOL_SOCKET,
                                       SO_SENDTIMEO,
                                       ( char * ) &transportTimeout,
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
        transportTimeout.tv_usec = ( recvTimeout * 1000 );

        setTimeoutStatus = setsockopt( *pTcpSocket,
                                       SOL_SOCKET,
                                       SO_RCVTIMEO,
                                       ( char * ) &transportTimeout,
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
    int pollStatus = -1;
    struct pollfd fileDescriptor;

    /* Initialize the file descriptor for polling. */
    fileDescriptor.events = POLLIN | POLLPRI;
    fileDescriptor.revents = 0;
    fileDescriptor.fd = pContext->tcpSocket;

    /* Check if there are any pending data available for read. */
    pollStatus = poll( &fileDescriptor, 1, tcpRecvTimeout );

    /* SSL read of data. */
    if( pollStatus > 0 )
    {
        bytesReceived = ( int32_t ) recv( pContext->tcpSocket, pBuffer, bytesToRecv, 0 );
    }
    /* Poll timed out. */
    else if( pollStatus == 0 )
    {
        LogDebug( ( "Poll timed out while waiting for data to read from the buffer." ) );
    }
    else
    {
        if( ( errno == EAGAIN ) || ( errno == EWOULDBLOCK ) )
        {
            LogError( ( "Server closed the connection." ) );
            /* Set return value to 0 to indicate connection was dropped by server. */
            bytesReceived = 0;
        }
        else
        {
            LogError( ( "Poll returned with status = %d.", pollStatus ) );
            bytesReceived = -1;
        }
    }

    return bytesReceived;
}

int32_t TCP_Send( NetworkContext_t pContext,
                  const void * pBuffer,
                  size_t bytesToSend )
{
    int32_t bytesSent = 0;
    int pollStatus = 0;
    struct pollfd fileDescriptor;

    /* Initialize the file descriptor for polling. */
    fileDescriptor.events = POLLOUT;
    fileDescriptor.revents = 0;
    fileDescriptor.fd = pContext->tcpSocket;

    /* Poll the file descriptor to check if send is ready. */
    pollStatus = poll( &fileDescriptor, 1, tcpSendTimeout );

    /* TCP read of data. */
    if( pollStatus > 0 )
    {
        bytesSent = ( int32_t ) send( pContext->tcpSocket, pBuffer, bytesToSend, 0 );
    }
    /* Poll timed out. */
    else if( pollStatus == 0 )
    {
        LogDebug( ( "Poll timed out while polling the socket for write buffer availability." ) );
    }
    else
    {
        if( ( errno == EAGAIN ) || ( errno == EWOULDBLOCK ) )
        {
            LogError( ( "Server closed the connection." ) );
            /* Set return value to 0 to indicate connection was dropped by server. */
            bytesSent = 0;
        }
        else
        {
            LogError( ( "Poll returned with status = %d.", pollStatus ) );
            bytesSent = -1;
        }
    }

    return bytesSent;
}

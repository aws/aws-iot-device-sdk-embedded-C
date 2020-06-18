#include "TCP_transport.h"

/* POSIX socket includes. */
#include <errno.h>
#include <netdb.h>
#include <poll.h>
#include <arpa/inet.h>

#include <sys/socket.h>
#include <sys/types.h>

/* Transport interface include. */
#include "transport_interface.h"

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
static int sendTimeout = -1;

/**
 * @brief Timeout for transport recv.
 *
 * @note Setting to a negative value implies an infinite timeout.
 */
static int recvTimeout = -1;

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
 * @brief Length of an IPv6 address when converted to hex digits.
 */
#define IPV6_ADDRESS_STRING_LENGTH    ( 40 )

/*-----------------------------------------------------------*/

int resolveHost( const char * pHostName,
                 size_t hostNameLength );

/*-----------------------------------------------------------*/

int resolveHost( const char * pHostName,
                 size_t hostNameLength )
{
}

NetworkStatus_t TCP_Connect( const char * pHostName,
                             size_t hostNameLength,
                             uint16_t port,
                             int * pTcpSocket )
{
    int networkStatus = NETWORK_INTERNAL_ERROR;
    struct addrinfo hints, * pIndex, * pListHead = NULL;
    struct sockaddr * pAddrInfo;
    uint16_t netPort = -1;
    socklen_t addrInfoLength;
    char resolvedIpAddr[ IPV6_ADDRESS_STRING_LENGTH ];

    assert( pServerInfo != NULL );

    /* Initialize string to store the resolved IP address from the host name. */
    ( void ) memset( resolvedIpAddr, 0, IPV6_ADDRESS_STRING_LENGTH );
    /* Add hints to retrieve only TCP sockets in getaddrinfo. */
    ( void ) memset( &hints, 0, sizeof( hints ) );
    /* Address family of either IPv4 or IPv6. */
    hints.ai_family = AF_UNSPEC;
    /* TCP Socket. */
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_protocol = IPPROTO_TCP;
    netPort = htons( pServerInfo->port );

    /* Perform a DNS lookup on the given host name. */
    networkStatus = getaddrinfo( pServerInfo->pHostName, NULL, &hints, &pListHead );

    if( networkStatus == -1 )
    {
        LogError( ( "Could not resolve host %.*s.\n",
                    ( int32_t ) pServerInfo->hostNameLength,
                    pServerInfo->pHostName ) );
        networkStatus = NETWORK_DNS_FAILURE;
    }
    else
    {
        LogInfo( ( "Performing DNS lookup: Host=%.*s.",
                   ( int32_t ) pServerInfo->hostNameLength,
                   pServerInfo->pHostName ) );

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
                /* IPv4 */
                ( ( struct sockaddr_in * ) pAddrInfo )->sin_port = netPort;
                addrInfoLength = sizeof( struct sockaddr_in );
                inet_ntop( pAddrInfo->sa_family,
                           &( ( struct sockaddr_in * ) pAddrInfo )->sin_addr,
                           resolvedIpAddr,
                           sizeof( resolvedIpAddr ) );
            }
            else
            {
                /* IPv6 */
                ( ( struct sockaddr_in6 * ) pAddrInfo )->sin6_port = netPort;
                addrInfoLength = sizeof( struct sockaddr_in6 );
                inet_ntop( pAddrInfo->sa_family,
                           &( ( struct sockaddr_in6 * ) pAddrInfo )->sin6_addr,
                           resolvedIpAddr,
                           sizeof( resolvedIpAddr ) );
            }

            LogInfo( ( "Attempting to connect to server: Host=%.*s, IP address=%s.",
                       ( int32_t ) pServerInfo->hostNameLength,
                       pServerInfo->pHostName,
                       resolvedIpAddr ) );

            networkStatus = connect( *pTcpSocket, pAddrInfo, addrInfoLength );

            if( networkStatus == -1 )
            {
                LogError( ( "Failed to connect to server: Host=%.*s, IP address=%s.",
                            ( int32_t ) pServerInfo->hostNameLength,
                            pServerInfo->pHostName,
                            resolvedIpAddr ) );
                close( *pTcpSocket );
            }
            else
            {
                LogInfo( ( "Connected to IP address: %s.",
                           resolvedIpAddr ) );
                break;
            }
        }

        if( pIndex == NULL )
        {
            /* Fail if no connection could be established. */
            LogError( ( "Could not connect to any resolved IP address from %.*s.",
                        ( int32_t ) pServerInfo->hostNameLength,
                        pServerInfo->pHostName ) );
            networkStatus = NETWORK_CONNECT_FAILURE;
        }
        else
        {
            LogInfo( ( "Established TCP connection: Server=%.*s.\n",
                       ( int32_t ) pServerInfo->hostNameLength,
                       pServerInfo->pHostName ) );
            networkStatus = NETWORK_SUCCESS;
        }
    }

    if( pListHead != NULL )
    {
        freeaddrinfo( pListHead );
    }

    return networkStatus;
}

void TCP_Disconnect( int tcpSocket )
{
    if( tcpSocket != -1 )
    {
        ( void ) shutdown( tcpSocket, SHUT_RDWR );
        ( void ) close( tcpSocket );
    }
}

void TCP_SetSendTimeout( int timeout )
{
    sendTimeout = timeout;
}

void TCP_SetRecvTimeout( int timeout )
{
    recvTimeout = timeout;
}

int32_t TCP_Send( NetworkContext_t pContext,
                  const void * pBuffer,
                  size_t bytesToSend )
{
    int32_t bytesSent = 0;
    int pollStatus = 0;
    struct pollfd fileDescriptor;

    fileDescriptor.events = POLLOUT;
    fileDescriptor.revents = 0;

    /* Set the file descriptor for poll. */
    fileDescriptor.fd = pContext->tcpSocket;

    /* Poll the file descriptor to check if send is ready. */
    pollStatus = poll( &fileDescriptor, 1, sendTimeout );

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

int32_t TCP_Recv( NetworkContext_t pContext,
                  void * pBuffer,
                  size_t bytesToRecv )
{
    int32_t bytesReceived = 0;
    int pollStatus = -1, bytesAvailableToRead = 0;
    struct pollfd fileDescriptor;

    fileDescriptor.events = POLLIN | POLLPRI;
    fileDescriptor.revents = 0;

    /* Set the file descriptor for poll. */
    fileDescriptor.fd = pContext->tcpSocket;

    /* Check if there are any pending data available for read. */
    pollStatus = poll( &fileDescriptor, 1, recvTimeout );

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

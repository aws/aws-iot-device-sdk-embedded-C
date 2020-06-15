/* Standard includes. */
#include <assert.h>
#include <stdlib.h>

/* POSIX socket includes. */
#include <errno.h>
#include <netdb.h>
#include <time.h>
#include <poll.h>
#include <unistd.h>
#include <arpa/inet.h>

#include <sys/socket.h>
#include <sys/types.h>

#include "connect.h"

/**
 * @brief Length of an IPv6 address when converted to hex digits.
 */
#define IPV6_ADDRESS_STRING_LENGTH    ( 40 )

NetworkStatus_t TCP_Connect( const NetworkServerInfo_t * pServerInfo,
                             int * pTcpSocket )
{
    int networkStatus = NETWORK_INTERNAL_ERROR;
    struct addrinfo hints, * pIndex, * pListHead = NULL;
    struct sockaddr * pAddrInfo;
    uint16_t netPort = -1;
    socklen_t addrInfoLength;
    char resolvedIpAddr[ IPV6_ADDRESS_STRING_LENGTH ];

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
                       ( int32_t ) pServerInfo->hostNameLength, pServerInfo->pHostName, resolvedIpAddr ) );

            networkStatus = connect( *pTcpSocket, pAddrInfo, addrInfoLength );

            if( networkStatus == -1 )
            {
                LogError( ( "Failed to connect to server: Host=%.*s, IP address=%s.",
                            ( int32_t ) pServerInfo->hostNameLength, pServerInfo->pHostName, resolvedIpAddr ) );
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

NetworkStatus_t TCP_Disconnect( int tcpSocket )
{
    if( tcpSocket != -1 )
    {
        ( void ) shutdown( tcpSocket, SHUT_RDWR );
        ( void ) close( tcpSocket );
    }
}

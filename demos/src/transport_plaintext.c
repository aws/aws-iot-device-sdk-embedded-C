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

#include "transport_plaintext.h"

#include <netdb.h>
#include <unistd.h>

#include <sys/socket.h>
#include <sys/types.h>

int Transport_ConnectToServer( const char * pServer, uint16_t port )
{
    int status, tcpSocket = -1;
    struct addrinfo * pListHead = NULL, * pIndex;
    struct sockaddr * pServerInfo;
    uint16_t netPort = htons( port );
    socklen_t serverInfoLength;

    status = getaddrinfo( pServer, NULL, NULL, &pListHead );

    if( status != -1 )
    {
        for( pIndex = pListHead; pIndex != NULL; pIndex = pIndex->ai_next )
        {
            tcpSocket = socket( pIndex->ai_family, pIndex->ai_socktype, pIndex->ai_protocol );

            if( tcpSocket == -1 )
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

            status = connect( tcpSocket, pServerInfo, serverInfoLength );

            if( status == -1 )
            {
                close( tcpSocket );
            }
            else
            {
                break;
            }
        }

        if( pIndex == NULL )
        {
            status = -1;
        }
        else
        {
            status = tcpSocket;
        }
    }

    if( pListHead != NULL )
    {
        freeaddrinfo( pListHead );
    }

    return status;
}

int32_t Transport_SendExact( int tcpSocket, const void * pMessage, size_t bytesToSend )
{
    const uint8_t * pIndex = pMessage;
    size_t bytesRemaining = bytesToSend;
    int32_t totalBytesSent = 0;
    ssize_t bytesSent;

    while( bytesRemaining > 0 )
    {
        bytesSent = send( tcpSocket, pIndex, bytesRemaining, 0 );

        if( bytesSent > 0 )
        {
            bytesRemaining -= ( size_t ) bytesSent;
            totalBytesSent += ( int32_t ) bytesSent;
            pIndex += bytesSent;
        }
        else
        {
            totalBytesSent = -1;
            break;
        }
    }

    return totalBytesSent;
}

int32_t Transport_RecvExact( int tcpSocket, void * pBuffer, size_t bytesToRecv )
{
    uint32_t * pIndex = pBuffer;
    size_t bytesRemaining = bytesToRecv;
    int32_t bytesRecvd, totalBytesRecvd = 0;

    while( bytesRemaining > 0 )
    {
        bytesRecvd = Transport_RecvUpTo( tcpSocket, pIndex, bytesRemaining );

        if( bytesRecvd > 0 )
        {
            bytesRemaining -= ( size_t ) bytesRecvd;
            totalBytesRecvd += bytesRecvd;
            pIndex += bytesRecvd;
        }
        else
        {
            totalBytesRecvd = -1;
            break;
        }
    }

    return totalBytesRecvd;
}

int32_t Transport_RecvUpTo( int tcpSocket, void * pBuffer, size_t bytesToRecv )
{
    return ( int32_t ) recv( tcpSocket, pBuffer, bytesToRecv, 0 );
}

void Transport_Close( int tcpSocket )
{
    shutdown( tcpSocket, SHUT_RDWR );
    close( tcpSocket );
}

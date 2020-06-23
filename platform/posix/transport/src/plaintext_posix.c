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

#include "plaintext_posix.h"

/*-----------------------------------------------------------*/

/**
 * @brief Defined by transport layer to check send or receive error.
 */
extern int errno;

/*-----------------------------------------------------------*/

/**
 * @brief Log possible error from send/recv.
 */
static void logTransportError( void );

/*-----------------------------------------------------------*/

static void logTransportError( void )
{
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

        case EINVAL:
            LogError( ( "The MSG_OOB flag is set and no out-of-band data is available." ) );
            break;

        case ENOTCONN:
            LogError( ( "A send/receive is attempted on a connection-mode socket that is not connected." ) );
            break;

        case ENOTSOCK:
            LogError( ( "The socket argument does not refer to a socket." ) );
            break;

        case EOPNOTSUPP:
            LogError( ( "The specified flags are not supported for this socket type or protocol." ) );
            break;

        case ETIMEDOUT:
            LogError( ( "The connection timed out during connection establishment, or due to a transmission timeout on active connection." ) );
            break;

        case EMSGSIZE:
            LogError( ( "The message is too large to be sent all at once, as the socket requires." ) );
            break;

        case EPIPE:
            LogError( ( "The socket is shut down for writing, or the socket is connection-mode and is no longer connected. In the latter case, and if the socket is of type SOCK_STREAM or SOCK_SEQPACKET and the MSG_NOSIGNAL flag is not set, the SIGPIPE signal is generated to the calling thread." ) );
            break;
    }
}

SocketStatus_t Plaintext_Connect( NetworkContext_t pNetworkContext,
                                  const ServerInfo_t * pServerInfo,
                                  uint32_t sendTimeoutMs,
                                  uint32_t recvTimeoutMs )
{
    return Sockets_Connect( &pNetworkContext->socketDescriptor,
                            pServerInfo,
                            sendTimeoutMs,
                            recvTimeoutMs );
}

SocketStatus_t Plaintext_Disconnect( const NetworkContext_t pNetworkContext )
{
    return Sockets_Disconnect( pNetworkContext->socketDescriptor );
}

int32_t Plaintext_Recv( NetworkContext_t pNetworkContext,
                        void * pBuffer,
                        size_t bytesToRecv )
{
    int32_t bytesReceived = 0;

    bytesReceived = recv( pNetworkContext->socketDescriptor, pBuffer, bytesToRecv, 0 );

    if( bytesReceived == 0 )
    {
        /* Server closed the connection, treat it as an error. */
        bytesReceived = -1;
    }
    else if( bytesReceived < 0 )
    {
        logTransportError();

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

int32_t Plaintext_Send( NetworkContext_t pNetworkContext,
                        const void * pBuffer,
                        size_t bytesToSend )
{
    int32_t bytesSent = 0;

    bytesSent = send( pNetworkContext->socketDescriptor, pBuffer, bytesToSend, 0 );

    if( bytesSent < 0 )
    {
        logTransportError();

        /* Check if it was time out */
        if( ( errno == EAGAIN ) || ( errno == EWOULDBLOCK ) )
        {
            /* Set return value to 0 to indicate that send had timed out. */
            bytesSent = 0;
        }
    }

    return bytesSent;
}

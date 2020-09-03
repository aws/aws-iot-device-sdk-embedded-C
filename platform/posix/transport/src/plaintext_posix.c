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
#include <string.h>

/* POSIX socket includes. */
#include <errno.h>
#include <sys/socket.h>
#include <sys/select.h>

#include "plaintext_posix.h"

/*-----------------------------------------------------------*/

/**
 * @brief Log possible error from send/recv.
 *
 * @param[in] errorNumber Error number to be logged.
 */
static void logTransportError( int32_t errorNumber );

/*-----------------------------------------------------------*/

static void logTransportError( int32_t errorNumber )
{
    LogError( ( "A transport error occurred: %s.", strerror( errorNumber ) ) );
}
/*-----------------------------------------------------------*/

SocketStatus_t Plaintext_Connect( NetworkContext_t * pNetworkContext,
                                  const ServerInfo_t * pServerInfo,
                                  uint32_t sendTimeoutMs,
                                  uint32_t recvTimeoutMs )
{
    return Sockets_Connect( &pNetworkContext->socketDescriptor,
                            pServerInfo,
                            sendTimeoutMs,
                            recvTimeoutMs );
}
/*-----------------------------------------------------------*/

SocketStatus_t Plaintext_Disconnect( const NetworkContext_t * pNetworkContext )
{
    return Sockets_Disconnect( pNetworkContext->socketDescriptor );
}
/*-----------------------------------------------------------*/

int32_t Plaintext_Recv( const NetworkContext_t * pNetworkContext,
                        void * pBuffer,
                        size_t bytesToRecv )
{
    int32_t bytesReceived = -1, selectStatus = -1, getTimeoutStatus = -1;
    struct timeval transportTimeout, selectTimeout;
    socklen_t transportTimeoutLen;
    fd_set readfds;

    assert( pNetworkContext != NULL );
    assert( pBuffer != NULL );
    assert( bytesToRecv > 0 );

    FD_ZERO( &readfds );
    FD_SET( pNetworkContext->socketDescriptor, &readfds );

    getTimeoutStatus = getsockopt( pNetworkContext->socketDescriptor,
                                   SOL_SOCKET,
                                   SO_RCVTIMEO,
                                   &transportTimeout,
                                   &transportTimeoutLen );

    if( getTimeoutStatus < 0 )
    {
        /* Make #select return immediately if getting the timeout failed. */
        selectTimeout.tv_sec = 0;
        selectTimeout.tv_usec = 0;
    }
    else
    {
        selectTimeout.tv_sec = transportTimeout.tv_sec;
        selectTimeout.tv_usec = transportTimeout.tv_usec;
    }

    /* Check if there is data to read from the socket. */
    selectStatus = select( pNetworkContext->socketDescriptor + 1,
                           &readfds,
                           NULL,
                           &readfds,
                           &selectTimeout );

    if( selectStatus > 0 )
    {
        bytesReceived = ( int32_t ) recv( pNetworkContext->socketDescriptor,
                                          pBuffer,
                                          bytesToRecv,
                                          0 );
    }
    else if( selectStatus < 0 )
    {
        /* An error occurred while polling. */
        bytesReceived = -1;
    }
    else
    {
        /* No data to receive at this time. */
        bytesReceived = 0;
    }

    if( ( selectStatus > 0 ) && ( bytesReceived == 0 ) )
    {
        /* Peer has closed the connection. Treat as an error. */
        bytesReceived = -1;
    }
    else if( bytesReceived < 0 )
    {
        logTransportError( errno );
    }
    else
    {
        /* Empty else MISRA 15.7 */
    }

    return bytesReceived;
}
/*-----------------------------------------------------------*/

int32_t Plaintext_Send( const NetworkContext_t * pNetworkContext,
                        const void * pBuffer,
                        size_t bytesToSend )
{
    int32_t bytesSent = -1, selectStatus = -1, getTimeoutStatus = -1;
    struct timeval transportTimeout, selectTimeout;
    socklen_t transportTimeoutLen;
    fd_set writefds;

    assert( pNetworkContext != NULL );
    assert( pBuffer != NULL );
    assert( bytesToSend > 0 );

    FD_ZERO( &writefds );
    FD_SET( pNetworkContext->socketDescriptor, &writefds );

    getTimeoutStatus = getsockopt( pNetworkContext->socketDescriptor,
                                   SOL_SOCKET,
                                   SO_SNDTIMEO,
                                   &transportTimeout,
                                   &transportTimeoutLen );

    if( getTimeoutStatus < 0 )
    {
        /* Make #select return immediately if getting the timeout failed. */
        selectTimeout.tv_sec = 0;
        selectTimeout.tv_usec = 0;
    }
    else
    {
        selectTimeout.tv_sec = transportTimeout.tv_sec;
        selectTimeout.tv_usec = transportTimeout.tv_usec;
    }

    /* Check if data can be written to the socket. */
    selectStatus = select( pNetworkContext->socketDescriptor + 1,
                           NULL,
                           &writefds,
                           &writefds,
                           &selectTimeout );

    if( selectStatus > 0 )
    {
        bytesSent = ( int32_t ) send( pNetworkContext->socketDescriptor,
                                      pBuffer,
                                      bytesToSend,
                                      0 );
    }
    else if( selectStatus < 0 )
    {
        /* An error occurred while polling. */
        bytesSent = -1;
    }
    else
    {
        /* Not able to send data at this time. */
        bytesSent = 0;
    }

    if( ( selectStatus > 0 ) && ( bytesSent == 0 ) )
    {
        /* Peer has closed the connection. Treat as an error. */
        bytesSent = -1;
    }
    else if( bytesSent < 0 )
    {
        logTransportError( errno );
    }
    else
    {
        /* Empty else MISRA 15.7 */
    }

    return bytesSent;
}
/*-----------------------------------------------------------*/

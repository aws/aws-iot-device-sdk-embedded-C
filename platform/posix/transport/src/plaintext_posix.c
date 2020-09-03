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
#include <string.h>

/* POSIX socket includes. */
#include <stdlib.h>
#include <assert.h>
#include <errno.h>
#include <sys/socket.h>
#include <poll.h>

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
    int32_t bytesReceived = -1, pollStatus = 0;
    struct pollfd fileDescriptor;
    nfds_t nfds = 1U;

    assert( pNetworkContext != NULL );
    assert( pBuffer != NULL );

    fileDescriptor.fd = pNetworkContext->socketDescriptor;
    fileDescriptor.events = POLLIN | POLLPRI | POLLHUP;
    fileDescriptor.revents = 0;

    /* Poll the socket for read availability. */
    pollStatus = poll( &fileDescriptor, nfds, 0 );

    if( pollStatus > 0 )
    {
        bytesReceived = ( int32_t ) recv( pNetworkContext->socketDescriptor,
                                          pBuffer,
                                          bytesToRecv,
                                          0 );
    }
    else if( pollStatus < 0 )
    {
        /* An error occurred while polling. */
        bytesReceived = -1;
    }
    else
    {
        /* No data to receive at this time. */
        bytesReceived = 0;
    }

    if( ( pollStatus > 0 ) && ( bytesReceived == 0 ) )
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
    int32_t bytesSent = -1, pollStatus = 0;
    struct pollfd fileDescriptor;
    nfds_t nfds = 1U;

    assert( pNetworkContext != NULL );
    assert( pBuffer != NULL );

    fileDescriptor.fd = pNetworkContext->socketDescriptor;
    fileDescriptor.events = POLLOUT | POLLHUP;
    fileDescriptor.revents = 0;

    /* Poll the socket for write availability. */
    pollStatus = poll( &fileDescriptor, nfds, 0 );

    if( pollStatus > 0 )
    {
        bytesSent = ( int32_t ) send( pNetworkContext->socketDescriptor,
                                      pBuffer,
                                      bytesToSend,
                                      0 );
    }
    else if( pollStatus < 0 )
    {
        /* An error occurred while polling. */
        bytesSent = -1;
    }
    else
    {
        /* Not able to send data at this time. */
        bytesSent = 0;
    }

    if( ( pollStatus > 0 ) && ( bytesSent == 0 ) )
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

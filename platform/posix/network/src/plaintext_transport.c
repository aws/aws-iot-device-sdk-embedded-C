#include "plaintext_transport.h"

/* POSIX socket includes. */
#include <errno.h>
#include <netdb.h>
#include <arpa/inet.h>

#include <sys/socket.h>
#include <sys/types.h>

/**
 * @brief Defined by transport layer to check send or receive error.
 */
extern int errno;

int32_t plaintextSend( NetworkContext_t pContext,
                       const void * pBuffer,
                       size_t bytesToSend )
{
    int32_t bytesSent = 0;

    bytesSent = send( pContext->tcpSocket, pBuffer, bytesToSend, 0 );

    if( bytesSent < 0 )
    {
        /* Check if it was time out */
        if( ( errno == EAGAIN ) || ( errno == EWOULDBLOCK ) )
        {
            /* Set return value to 0 to indicate that send had timed out. */
            bytesSent = 0;
        }
    }

    return bytesSent;
}

int32_t plaintextRecv( NetworkContext_t pContext,
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
        /* Check if it was time out. */
        if( ( errno == EAGAIN ) || ( errno == EWOULDBLOCK ) )
        {
            /* Set return value to 0 to indicate nothing to receive. */
            bytesReceived = 0;
        }
    }
    else
    {
        /* EMPTY else */
    }

    return bytesReceived;
}

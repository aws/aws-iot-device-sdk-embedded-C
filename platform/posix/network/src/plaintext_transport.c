#include "plaintext_transport.h"

/* POSIX socket includes. */
#include <errno.h>
#include <netdb.h>
#include <poll.h>
#include <arpa/inet.h>

#include <sys/socket.h>
#include <sys/types.h>

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

/*-----------------------------------------------------------*/

void Plaintext_SetSendTimeout( int timeout )
{
    sendTimeout = timeout;
}

void Plaintext_SetRecvTimeout( int timeout )
{
    recvTimeout = timeout;
}

int32_t Plaintext_Send( NetworkContext_t pContext,
                        const void * pBuffer,
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
    fileDescriptor.fd = pContext->tcpSocket;

    /* Poll the file descriptor to check if SSL_Write can be done now. */
    pollStatus = poll( &fileDescriptor, 1, sendTimeout );

    /* SSL read of data. */
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

int32_t Plaintext_Recv( NetworkContext_t pContext,
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

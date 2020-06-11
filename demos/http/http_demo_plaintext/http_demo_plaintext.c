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
#include <stdlib.h>
#include <string.h>

/* POSIX socket includes. */
#include <errno.h>
#include <netdb.h>
#include <time.h>
#include <unistd.h>
#include <arpa/inet.h>

#include <sys/socket.h>
#include <sys/types.h>

/* Include Demo Config as the first non-system header. */
#include "demo_config.h"

/* HTTP API header. */
#include "http_client.h"

/**
 * @brief Length of an IPv6 address when converted to hex digits.
 */
#define IPV6_ADDRESS_STRING_LEN    ( 40 )

/**
 * @brief Defined by transport layer to check send or receive error.
 */
extern int errno;

/**
 * @brief A string to store the resolved IP address from the host name.
 */
static char resolvedIpAddr[ IPV6_ADDRESS_STRING_LEN ];

/**
 * @brief A buffer used in the demo for storing HTTP request headers and
 * HTTP response headers and body.
 *
 * @note This demo shows how the same buffer can be re-used for storing the HTTP
 * response after the HTTP request is sent out. However, the user can also
 * decide to use separate buffers for storing the HTTP request and response.
 */
static uint8_t userBuffer[ USER_BUFFER_LENGTH ];

/**
 * @brief Definition of the HTTP network context.
 *
 * @note An integer is used to store the descriptor of the socket.
 */
struct NetworkContext
{
    int tcpSocket;
};

/**
 * @brief Structure based on the definition of the HTTP network context.
 */
static struct NetworkContext socketContext;

/**
 * @brief The HTTP Client library transport layer interface.
 */
static HTTPTransportInterface_t transportInterface;

/**
 * @brief Represents header data that will be sent in an HTTP request.
 */
static HTTPRequestHeaders_t requestHeaders;

/**
 * @brief Configurations of the initial request headers that are passed to
 * #HTTPClient_InitializeRequestHeaders.
 */
static HTTPRequestInfo_t requestInfo;

/**
 * @brief Represents a response returned from an HTTP server.
 */
static HTTPResponse_t response;

/*-----------------------------------------------------------*/

/**
 * @brief Performs a DNS lookup on the given host name, then establishes a TCP
 * connection to the server.
 *
 * @param[in] pServer Host name of server.
 * @param[in] port Server port.
 * @param[out] pTcpSocket Pointer to TCP socket file descriptor.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on success.
 */
static int connectToServer( const char * pServer,
                            uint16_t port,
                            int * pTcpSocket );

/**
 * @brief The transport send function that defines the transport interface.
 *
 * This is passed as the #HTTPTransportInterface.send function and used to
 * send data over the network.
 *
 * @param[in] pContext User defined context (TCP socket for this demo).
 * @param[in] pBuffer Buffer containing the bytes to send over the network stack.
 * @param[in] bytesToSend Number of bytes to write to the network.
 *
 * @return Number of bytes sent if successful; otherwise negative value on error.
 */
static int32_t transportSend( NetworkContext_t pContext,
                              const void * pBuffer,
                              size_t bytesToSend );

/**
 * @brief The transport receive function that defines the transport interface.
 *
 * This is passed as the #HTTPTransportInterface.recv function used for reading
 * data received from the network.
 *
 * @param[in] pContext User defined context (TCP socket for this demo).
 * @param[out] pBuffer Buffer to read network data into.
 * @param[in] bytesToRead Number of bytes requested from the network.
 *
 * @return Number of bytes received if successful; otherwise negative value on error.
 */
static int32_t transportRecv( NetworkContext_t pContext,
                              void * pBuffer,
                              size_t bytesToRecv );

/**
 * @brief Send an HTTP request based on a specified method and path, then
 * print the response received from the server.
 *
 * @param[in] pTransportInterface The transport interface for making network calls.
 * @param[in] pHost The host name of the server.
 * @param[in] pMethod The HTTP request method.
 * @param[in] pPath The Request-URI to the objects of interest.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on success.
 */
static int sendHttpRequest( const HTTPTransportInterface_t * pTransportInterface,
                            const char * pHost,
                            const char * pMethod,
                            const char * pPath );

/*-----------------------------------------------------------*/

static int connectToServer( const char * pServer,
                            uint16_t port,
                            int * pTcpSocket )
{
    int returnStatus = EXIT_SUCCESS;
    struct addrinfo hints, * pIndex, * pListHead = NULL;
    struct sockaddr * pServerInfo;
    uint16_t netPort = htons( port );
    socklen_t serverInfoLength;
    struct timeval transportTimeout;

    /* Add hints to retrieve only TCP sockets in getaddrinfo. */
    ( void ) memset( &hints, 0, sizeof( hints ) );
    /* Address family of either IPv4 or IPv6. */
    hints.ai_family = AF_UNSPEC;
    /* TCP Socket. */
    hints.ai_socktype = SOCK_STREAM;
    hints.ai_protocol = IPPROTO_TCP;

    /* Perform a DNS lookup on the given host name. */
    returnStatus = getaddrinfo( pServer, NULL, &hints, &pListHead );

    if( returnStatus != -1 )
    {
        LogInfo( ( "Performing DNS lookup: Host=%s.",
                   SERVER_HOST ) );

        /* Attempt to connect to one of the retrieved DNS records. */
        for( pIndex = pListHead; pIndex != NULL; pIndex = pIndex->ai_next )
        {
            *pTcpSocket = socket( pIndex->ai_family, pIndex->ai_socktype, pIndex->ai_protocol );

            if( *pTcpSocket == -1 )
            {
                continue;
            }

            pServerInfo = pIndex->ai_addr;

            if( pServerInfo->sa_family == AF_INET )
            {
                /* IPv4 */
                ( ( struct sockaddr_in * ) pServerInfo )->sin_port = netPort;
                serverInfoLength = sizeof( struct sockaddr_in );
                inet_ntop( pServerInfo->sa_family,
                           &( ( struct sockaddr_in * ) pServerInfo )->sin_addr,
                           resolvedIpAddr,
                           sizeof( resolvedIpAddr ) );
            }
            else
            {
                /* IPv6 */
                ( ( struct sockaddr_in6 * ) pServerInfo )->sin6_port = netPort;
                serverInfoLength = sizeof( struct sockaddr_in6 );
                inet_ntop( pServerInfo->sa_family,
                           &( ( struct sockaddr_in6 * ) pServerInfo )->sin6_addr,
                           resolvedIpAddr,
                           sizeof( resolvedIpAddr ) );
            }

            LogInfo( ( "Attempting to connect to server: Host=%s, IP address=%s.",
                       SERVER_HOST, resolvedIpAddr ) );

            returnStatus = connect( *pTcpSocket, pServerInfo, serverInfoLength );

            if( returnStatus == -1 )
            {
                LogError( ( "Failed to connect to server: Host=%s, IP address=%s.",
                            SERVER_HOST, resolvedIpAddr ) );
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
            returnStatus = EXIT_FAILURE;
            LogError( ( "Could not connect to any resolved IP address from %.*s.\n",
                        ( int ) strlen( pServer ),
                        pServer ) );
        }
        else
        {
            returnStatus = EXIT_SUCCESS;
            LogInfo( ( "Established TCP connection: Server=%.*s.\n",
                       ( int ) strlen( pServer ),
                       pServer ) );
        }
    }
    else
    {
        LogError( ( "Could not resolve host %.*s.\n",
                    ( int ) strlen( pServer ),
                    pServer ) );
        returnStatus = EXIT_FAILURE;
    }

    /* Set the socket option for send and receive timeouts. */
    if( returnStatus == EXIT_SUCCESS )
    {
        transportTimeout.tv_sec = 0;
        transportTimeout.tv_usec = ( TRANSPORT_SEND_RECV_TIMEOUT_MS * 1000 );

        /* Set the receive timeout. */
        if( setsockopt( *pTcpSocket,
                        SOL_SOCKET,
                        SO_RCVTIMEO,
                        ( char * ) &transportTimeout,
                        sizeof( transportTimeout ) ) < 0 )
        {
            LogError( ( "Setting socket receive timeout failed." ) );
            returnStatus = EXIT_FAILURE;
        }

        /* Set the send timeout. */
        if( setsockopt( *pTcpSocket,
                        SOL_SOCKET,
                        SO_SNDTIMEO,
                        ( char * ) &transportTimeout,
                        sizeof( transportTimeout ) ) < 0 )
        {
            LogError( ( "Setting socket send timeout failed." ) );
            returnStatus = EXIT_FAILURE;
        }
    }

    if( pListHead != NULL )
    {
        freeaddrinfo( pListHead );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int32_t transportSend( NetworkContext_t pContext,
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

/*-----------------------------------------------------------*/

static int32_t transportRecv( NetworkContext_t pContext,
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

/*-----------------------------------------------------------*/

static int sendHttpRequest( const HTTPTransportInterface_t * pTransportInterface,
                            const char * pHost,
                            const char * pMethod,
                            const char * pPath )
{
    int returnStatus = EXIT_SUCCESS;
    HTTPStatus_t httpStatus = HTTP_SUCCESS;

    /* Initialize the request object. */
    requestInfo.pHost = pHost;
    requestInfo.hostLen = strlen( pHost );
    requestInfo.method = pMethod;
    requestInfo.methodLen = strlen( pMethod );
    requestInfo.pPath = pPath;
    requestInfo.pathLen = strlen( pPath );

    /* Set "Connection" HTTP header to "keep-alive" so that multiple requests
     * can be sent over the same established TCP connection. */
    requestInfo.reqFlags = HTTP_REQUEST_KEEP_ALIVE_FLAG;

    /* Set the buffer used for storing request headers. */
    requestHeaders.pBuffer = userBuffer;
    requestHeaders.bufferLen = USER_BUFFER_LENGTH;

    httpStatus = HTTPClient_InitializeRequestHeaders( &requestHeaders,
                                                      &requestInfo );

    if( httpStatus == HTTP_SUCCESS )
    {
        /* Initialize the response object. The same buffer used for storing
         * request headers is reused here. */
        response.pBuffer = userBuffer;
        response.bufferLen = USER_BUFFER_LENGTH;

        LogInfo( ( "Sending HTTP %s request to %s%s...",
                   pMethod, SERVER_HOST, pPath ) );
        LogInfo( ( "Request Headers:\n%.*s",
                   ( int32_t ) requestHeaders.headersLen,
                   ( char * ) requestHeaders.pBuffer ) );
        LogInfo( ( "Request Body:\n%.*s\n",
                   ( int32_t ) REQUEST_BODY_LENGTH,
                   REQUEST_BODY ) );
        /* Send the request and receive the response. */
        httpStatus = HTTPClient_Send( pTransportInterface,
                                      &requestHeaders,
                                      ( uint8_t * ) REQUEST_BODY,
                                      REQUEST_BODY_LENGTH,
                                      &response,
                                      0 );
    }
    else
    {
        LogError( ( "Failed to initialize HTTP request headers: Error=%s.",
                    HTTPClient_strerror( httpStatus ) ) );
    }

    if( httpStatus == HTTP_SUCCESS )
    {
        LogInfo( ( "Received HTTP response from %s%s...",
                   SERVER_HOST, pPath ) );
        LogInfo( ( "Response Headers:\n%.*s",
                   ( int32_t ) response.headersLen,
                   response.pHeaders ) );
        LogInfo( ( "Response Status:\n%u",
                   response.statusCode ) );
        LogInfo( ( "Response Body:\n%.*s\n",
                   ( int32_t ) response.bodyLen,
                   response.pBody ) );
    }
    else
    {
        LogError( ( "Failed to send HTTP %s request to %s%s: Error=%s.",
                    pMethod, SERVER_HOST, pPath, HTTPClient_strerror( httpStatus ) ) );
    }

    if( httpStatus != HTTP_SUCCESS )
    {
        returnStatus = EXIT_FAILURE;
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

/**
 * @brief Entry point of demo.
 *
 * This example resolves a domain, then establishes a TCP connection with an
 * HTTP server to demonstrate HTTP request/response communication without using
 * an encrypted channel (i.e. without TLS). After which, HTTP Client library API
 * is used to send a GET, HEAD, PUT, and POST request in that order. For each
 * request, the HTTP response from the server (or an error code) is logged.
 *
 * @note This example is single-threaded and uses statically allocated memory.
 *
 */
int main( int argc,
          char ** argv )
{
    int returnStatus = EXIT_SUCCESS;
    NetworkContext_t pSocketContext = &socketContext;

    ( void ) argc;
    ( void ) argv;

    /**************************** Connect. ******************************/

    /* Establish TCP connection. */
    returnStatus = connectToServer( SERVER_HOST, SERVER_PORT, &pSocketContext->tcpSocket );

    /* Define the transport interface. */
    if( returnStatus == EXIT_SUCCESS )
    {
        transportInterface.recv = transportRecv;
        transportInterface.send = transportSend;
        transportInterface.pContext = pSocketContext;
    }

    /*********************** Send HTTPS request. ************************/

    /* Send GET Request. */
    if( returnStatus == EXIT_SUCCESS )
    {
        returnStatus = sendHttpRequest( &transportInterface,
                                        SERVER_HOST,
                                        HTTP_METHOD_GET,
                                        GET_PATH );
    }

    /* Send HEAD Request. */
    if( returnStatus == EXIT_SUCCESS )
    {
        returnStatus = sendHttpRequest( &transportInterface,
                                        SERVER_HOST,
                                        HTTP_METHOD_HEAD,
                                        HEAD_PATH );
    }

    /* Send PUT Request. */
    if( returnStatus == EXIT_SUCCESS )
    {
        returnStatus = sendHttpRequest( &transportInterface,
                                        SERVER_HOST,
                                        HTTP_METHOD_PUT,
                                        PUT_PATH );
    }

    /* Send POST Request. */
    if( returnStatus != EXIT_SUCCESS )
    {
        returnStatus = sendHttpRequest( &transportInterface,
                                        SERVER_HOST,
                                        HTTP_METHOD_POST,
                                        POST_PATH );
    }

    /************************** Disconnect. *****************************/

    if( pSocketContext->tcpSocket != -1 )
    {
        ( void ) shutdown( pSocketContext->tcpSocket, SHUT_RDWR );
        ( void ) close( pSocketContext->tcpSocket );
    }

    return returnStatus;
}

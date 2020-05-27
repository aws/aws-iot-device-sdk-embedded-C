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
#include <unistd.h>
#include <arpa/inet.h>

#include <sys/socket.h>
#include <sys/types.h>

/* HTTP API header. */
#include "http_client.h"

/* Demo Config header. */
#include "http_config.h"

/**
 * @brief HTTP server host name.
 *
 * This demo uses httpbin.org: A simple HTTP Request & Response Service.
 */
#define SERVER_HOST    "httpbin.org"

/**
 * @brief HTTP server port number.
 *
 * In general, port 80 is for plaintext HTTP connections.
 */
#define SERVER_PORT    80

/**
 * @brief Paths for different HTTP methods for specified host.
 *
 * For httpbin.org, see http://httpbin.org/#/HTTP_Methods for details on
 * supported REST API.
 */
#ifndef GET_PATH
    #define GET_PATH    "/get"
#endif

#ifndef HEAD_PATH
    #define HEAD_PATH    "/get"
#endif

#ifndef PUT_PATH
    #define PUT_PATH    "/put"
#endif

#ifndef POST_PATH
    #define POST_PATH    "/post"
#endif

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define TRANSSERVER_PORT_SEND_RECV_TIMEOUT_MS    ( 1000 )

/**
 * @brief The length in bytes of the user buffer.
 */
#define USER_BUFFER_LENGTH                       ( 1024 )

/**
 * @brief Length of an IPv6 address when converted to hex digits.
 */
#define IPV6_LENGTH                              ( 40 )


/**
 * @brief Some text to send as the request body for PUT and POST requests in
 * this demo.
 */
#define REQUEST_BODY_TEXT           "Hello, world!"
#define REQUEST_BODY_TEXT_LENGTH    ( sizeof( REQUEST_BODY_TEXT ) - 1 )

/**
 * @brief A string to store the resolved IP address from the host name.
 */
static uint8_t resolvedIpAddr[ IPV6_LENGTH ] = { 0 };

/**
 * @brief A buffer used to store request headers and reused after sending
 * the request to store the response headers and body.
 *
 * User can also decide to have two separate buffers for request and response.
 */
static uint8_t userBuffer[ USER_BUFFER_LENGTH ] = { 0 };

/**
 * @brief The request body.
 */
static uint8_t requestBodyBuffer[ REQUEST_BODY_TEXT_LENGTH ] = { 0 };

/**
 * @brief Definition of the HTTP network context.
 */
struct HTTPNetworkContext
{
    int tcpSocket;
};

/*-----------------------------------------------------------*/

/**
 * @brief Performs a DNS lookup on the given host name then establishes a TCP
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
 * @param[in] pContext User defined context (TCP socket for this demo).
 * @param[in] pBuffer Buffer containing the bytes to send over the network stack.
 * @param[in] bytesToWrite Number of bytes to write to the network.
 *
 * @return Number of bytes sent; negative value on error.
 */
static int32_t transportSend( HTTPNetworkContext_t * pContext,
                              const void * pBuffer,
                              size_t bytesToSend );

/**
 * @brief The transport receive function that defines the transport interface.
 *
 * @param[in] pContext User defined context (TCP socket for this demo).
 * @param[out] pBuffer Buffer to read network data into.
 * @param[in] bytesToRead Number of bytes requested from the network.
 *
 * @return Number of bytes received; negative value on error.
 */
static int32_t transportRecv( HTTPNetworkContext_t * pContext,
                              void * pBuffer,
                              size_t bytesToRecv );

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
        LogInfo( ( "Performing DNS lookup on %s.",
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
                           &( ( struct sockaddr_in * ) pServerInfo )->sin_addr,
                           resolvedIpAddr,
                           sizeof( resolvedIpAddr ) );
            }

            LogInfo( ( "Attempting to connect to resolved IP Address: %s.",
                       resolvedIpAddr ) );

            returnStatus = connect( *pTcpSocket, pServerInfo, serverInfoLength );

            if( returnStatus == -1 )
            {
                close( *pTcpSocket );
            }
            else
            {
                LogInfo( ( "Connected to IP Address: %s.",
                           resolvedIpAddr ) );
                break;
            }
        }

        if( pIndex == NULL )
        {
            /* Fail if no connection could be established. */
            returnStatus = EXIT_FAILURE;
            LogError( ( "Resolved but could not connect to any resolved IP from %.*s.\n",
                        ( int ) strlen( pServer ),
                        pServer ) );
        }
        else
        {
            returnStatus = EXIT_SUCCESS;
            LogInfo( ( "TCP connection established with %.*s.\n",
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
        transportTimeout.tv_usec = ( TRANSSERVER_PORT_SEND_RECV_TIMEOUT_MS * 1000 );

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

static int32_t transportSend( HTTPNetworkContext_t * pContext,
                              const void * pBuffer,
                              size_t bytesToSend )
{
    int32_t bytesSend = 0;

    bytesSend = send( ( int ) pContext->tcpSocket, pBuffer, bytesToSend, 0 );

    if( bytesSend < 0 )
    {
        /* Check if it was time out */
        if( ( errno == EAGAIN ) || ( errno == EWOULDBLOCK ) )
        {
            /* Set return value to 0 to indicate that send was timed out. */
            bytesSend = 0;
        }
    }

    return bytesSend;
}

/*-----------------------------------------------------------*/

static int32_t transportRecv( HTTPNetworkContext_t * pContext,
                              void * pBuffer,
                              size_t bytesToRecv )
{
    int32_t bytesReceived = 0;

    bytesReceived = ( int32_t ) recv( ( int ) pContext->tcpSocket, pBuffer, bytesToRecv, 0 );

    if( bytesReceived == 0 )
    {
        /* Server closed the connection, treat it as an error. */
        bytesReceived = -1;
    }
    else if( bytesReceived < 0 )
    {
        /* Check if it was time out */
        if( ( errno == EAGAIN ) || ( errno == EWOULDBLOCK ) )
        {
            /* Set return value to 0 to indicate nothing to receive */
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

/**
 * @brief Send an HTTP request based on a specified method and path.
 *
 * @param[in] pTransport The transport interface for network send and receive.
 * @param[in] pHost The host name of the server.
 * @param[in] pMethod The HTTP request method.
 * @param[in] pPath The Request-URI to the objects of interest.
 *
 * @return #HTTP_SUCCESS if successful;
 * otherwise, the error status returned by the HTTP library
 */
static int sendHttpRequest( HTTPTransportInterface_t * pTransport,
                            const char * pHost,
                            const char * pMethod,
                            const char * pPath )
{
    HTTPStatus_t httpStatus = HTTP_SUCCESS;
    HTTPRequestHeaders_t requestHeaders = { 0 };
    HTTPRequestInfo_t requestInfo = { 0 };
    HTTPResponse_t response = { 0 };

    assert( pTransport != NULL );
    assert( pMethod != NULL );

    /* Initialize the request object. */
    requestInfo.pHost = pHost;
    requestInfo.hostLen = strlen( pHost );
    requestInfo.method = pMethod;
    requestInfo.methodLen = strlen( pMethod );
    requestInfo.pPath = pPath;
    requestInfo.pathLen = strlen( pPath );

    /* Set "Connection" HTTP header to "keep-alive" so that multiple requests
     * can be sent over the same established TCP connection. */
    requestInfo.flags = HTTP_REQUEST_KEEP_ALIVE_FLAG;

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
                   ( int32_t ) REQUEST_BODY_TEXT_LENGTH,
                   ( char * ) requestBodyBuffer ) );
        /* Send the request and receive the response. */
        httpStatus = HTTPClient_Send( pTransport,
                                      &requestHeaders,
                                      requestBodyBuffer,
                                      REQUEST_BODY_TEXT_LENGTH,
                                      &response,
                                      0 );
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
        LogError( ( "Sending HTTP %s request to %s%s failed with status = %u.",
                    pMethod, SERVER_HOST, pPath, httpStatus ) );
    }

    if( httpStatus == HTTP_SUCCESS )
    {
        return EXIT_SUCCESS;
    }
    else
    {
        return EXIT_FAILURE;
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Entry point of demo.
 */
int main()
{
    int returnStatus = EXIT_SUCCESS;
    HTTPStatus_t httpStatus = HTTP_SUCCESS;
    HTTPNetworkContext_t socketContext = { 0 };
    HTTPTransportInterface_t transport = { 0 };

    /* Set the request body. */
    strncpy( ( char * ) requestBodyBuffer,
             REQUEST_BODY_TEXT, REQUEST_BODY_TEXT_LENGTH );

    /**************************** Connect. ******************************/

    /* Establish TCP connection. */
    returnStatus = connectToServer( SERVER_HOST, SERVER_PORT, &socketContext.tcpSocket );

    /* Define the transport interface. */
    transport.recv = transportRecv;
    transport.send = transportSend;
    transport.pContext = &socketContext;

    /*********************** Send HTTPS request. ************************/

    /* The client is now connected to the server. This example will send a
     * GET, HEAD, PUT, and POST request in that order. If any request fails,
     * an error code is returned. */

    /* Send GET Request. */
    if( returnStatus == EXIT_SUCCESS )
    {
        returnStatus = sendHttpRequest( &transport,
                                        SERVER_HOST,
                                        HTTP_METHOD_GET,
                                        GET_PATH );
    }

    /* Send HEAD Request. */
    if( returnStatus == EXIT_SUCCESS )
    {
        returnStatus = sendHttpRequest( &transport,
                                        SERVER_HOST,
                                        HTTP_METHOD_HEAD,
                                        HEAD_PATH );
    }

    /* Send PUT Request. */
    if( returnStatus == EXIT_SUCCESS )
    {
        returnStatus = sendHttpRequest( &transport,
                                        SERVER_HOST,
                                        HTTP_METHOD_PUT,
                                        PUT_PATH );
    }

    /* Send POST Request. */
    if( returnStatus != EXIT_SUCCESS )
    {
        returnStatus = sendHttpRequest( &transport,
                                        SERVER_HOST,
                                        HTTP_METHOD_POST,
                                        POST_PATH );
    }

    /************************** Disconnect. *****************************/

    if( socketContext.tcpSocket != -1 )
    {
        shutdown( socketContext.tcpSocket, SHUT_RDWR );
        close( socketContext.tcpSocket );
    }

    return returnStatus;
}

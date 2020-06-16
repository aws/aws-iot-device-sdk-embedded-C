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

/* TCP connect header. */
#include "network_utilities.h"

/* Plaintext transport header. */
#include "plaintext_transport.h"

/* HTTP API header. */
#include "http_client.h"

/**
 * @brief Length of an IPv6 address when converted to hex digits.
 */
#define IPV6_ADDRESS_STRING_LEN    ( 40 )

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
 * @brief The HTTP Client library transport layer interface.
 */
static TransportInterface_t transportInterface;

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
static int sendHttpRequest( const TransportInterface_t * pTransportInterface,
                            const char * pHost,
                            const char * pMethod,
                            const char * pPath );

/*-----------------------------------------------------------*/

static int sendHttpRequest( const TransportInterface_t * pTransportInterface,
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
    struct NetworkContext socketContext;
    NetworkServerInfo_t serverInfo;

    ( void ) argc;
    ( void ) argv;

    /**************************** Connect. ******************************/

    /* Initialize information needed to connect to server. */
    serverInfo.pHostName = SERVER_HOST;
    serverInfo.hostNameLength = strlen( SERVER_HOST );
    serverInfo.port = SERVER_PORT;

    /* Set timeouts. */
    Plaintext_SetSendTimeout( TRANSPORT_SEND_RECV_TIMEOUT_MS );
    Plaintext_SetRecvTimeout( TRANSPORT_SEND_RECV_TIMEOUT_MS );

    /* Establish TCP connection. */
    returnStatus = TCP_Connect( &socketContext.tcpSocket, &serverInfo );

    /* Define the transport interface. */
    if( returnStatus == EXIT_SUCCESS )
    {
        transportInterface.recv = Plaintext_Recv;
        transportInterface.send = Plaintext_Send;
        transportInterface.pContext = &socketContext;
    }

    /* Set an optional timeout for transport send and receive. */



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
    if( returnStatus == EXIT_SUCCESS )
    {
        returnStatus = sendHttpRequest( &transportInterface,
                                        SERVER_HOST,
                                        HTTP_METHOD_POST,
                                        POST_PATH );
    }

    /************************** Disconnect. *****************************/

    TCP_Disconnect( socketContext.tcpSocket );

    return returnStatus;
}

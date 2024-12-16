/*
 * AWS IoT Device SDK for Embedded C 202412.00
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

/* POSIX includes. */
#include <unistd.h>

/* Include Demo Config as the first non-system header. */
#include "demo_config.h"

/* Common HTTP demo utilities. */
#include "http_demo_utils.h"

/* HTTP API header. */
#include "core_http_client.h"

/* Plaintext sockets transport header. */
#include "plaintext_posix.h"

/* Check that hostname of the server is defined. */
#ifndef SERVER_HOST
    #error "Please define a SERVER_HOST."
#endif

/* Check that port of the server is defined. */
#ifndef HTTP_PORT
    #error "Please define a HTTP_PORT."
#endif

/* Check that a path for HTTP Method GET is defined. */
#ifndef GET_PATH
    #error "Please define a GET_PATH."
#endif

/* Check that a path for HTTP Method HEAD is defined. */
#ifndef HEAD_PATH
    #error "Please define a HEAD_PATH."
#endif

/* Check that a path for HTTP Method PUT is defined. */
#ifndef PUT_PATH
    #error "Please define a PUT_PATH."
#endif

/* Check that a path for HTTP Method POST is defined. */
#ifndef POST_PATH
    #error "Please define a POST_PATH."
#endif

/**
 * @brief Delay in seconds between each iteration of the demo.
 */
#define DEMO_LOOP_DELAY_SECONDS    ( 5U )

/* Check that transport timeout for transport send and receive is defined. */
#ifndef TRANSPORT_SEND_RECV_TIMEOUT_MS
    #define TRANSPORT_SEND_RECV_TIMEOUT_MS    ( 1000 )
#endif

/* Check that size of the user buffer is defined. */
#ifndef USER_BUFFER_LENGTH
    #define USER_BUFFER_LENGTH    ( 1024 )
#endif

/**
 * @brief The length of the HTTP server host name.
 */
#define SERVER_HOST_LENGTH         ( sizeof( SERVER_HOST ) - 1 )

/**
 * @brief The length of the HTTP GET method.
 */
#define HTTP_METHOD_GET_LENGTH     ( sizeof( HTTP_METHOD_GET ) - 1 )

/**
 * @brief The length of the HTTP HEAD method.
 */
#define HTTP_METHOD_HEAD_LENGTH    ( sizeof( HTTP_METHOD_HEAD ) - 1 )

/**
 * @brief The length of the HTTP PUT method.
 */
#define HTTP_METHOD_PUT_LENGTH     ( sizeof( HTTP_METHOD_PUT ) - 1 )

/**
 * @brief The length of the HTTP POST method.
 */
#define HTTP_METHOD_POST_LENGTH    ( sizeof( HTTP_METHOD_POST ) - 1 )

/**
 * @brief The length of the HTTP GET path.
 */
#define GET_PATH_LENGTH            ( sizeof( GET_PATH ) - 1 )

/**
 * @brief The length of the HTTP HEAD path.
 */
#define HEAD_PATH_LENGTH           ( sizeof( HEAD_PATH ) - 1 )

/**
 * @brief The length of the HTTP PUT path.
 */
#define PUT_PATH_LENGTH            ( sizeof( PUT_PATH ) - 1 )

/**
 * @brief The length of the HTTP POST path.
 */
#define POST_PATH_LENGTH           ( sizeof( POST_PATH ) - 1 )

/**
 * @brief Length of the request body.
 */
#define REQUEST_BODY_LENGTH        ( sizeof( REQUEST_BODY ) - 1 )

/**
 * @brief Number of HTTP paths to request.
 */
#define NUMBER_HTTP_PATHS          ( 4 )

/**
 * @brief A pair containing a path string of the URI and its length.
 */
typedef struct httpPathStrings
{
    const char * httpPath;
    size_t httpPathLength;
} httpPathStrings_t;

/**
 * @brief A pair containing an HTTP method string and its length.
 */
typedef struct httpMethodStrings
{
    const char * httpMethod;
    size_t httpMethodLength;
} httpMethodStrings_t;

/**
 * @brief A buffer used in the demo for storing HTTP request headers and
 * HTTP response headers and body.
 *
 * @note This demo shows how the same buffer can be re-used for storing the HTTP
 * response after the HTTP request is sent out. However, the user can also
 * decide to use separate buffers for storing the HTTP request and response.
 */
static uint8_t userBuffer[ USER_BUFFER_LENGTH ];

/*-----------------------------------------------------------*/

/* Each compilation unit must define the NetworkContext struct. */
struct NetworkContext
{
    PlaintextParams_t * pParams;
};

/*-----------------------------------------------------------*/

/**
 * @brief Connect to HTTP server with reconnection retries.
 *
 * @param[out] pNetworkContext The output parameter to return the created network context.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on successful connection.
 */
static int32_t connectToServer( NetworkContext_t * pNetworkContext );

/**
 * @brief Send an HTTP request based on a specified method and path, then
 * print the response received from the server.
 *
 * @param[in] pTransportInterface The transport interface for making network calls.
 * @param[in] pMethod The HTTP request method.
 * @param[in] methodLen The length of the HTTP request method.
 * @param[in] pPath The Request-URI to the objects of interest.
 * @param[in] pathLen The length of the Request-URI.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on success.
 */
static int32_t sendHttpRequest( const TransportInterface_t * pTransportInterface,
                                const char * pMethod,
                                size_t methodLen,
                                const char * pPath,
                                size_t pathLen );

/*-----------------------------------------------------------*/

static int32_t connectToServer( NetworkContext_t * pNetworkContext )
{
    int32_t returnStatus = EXIT_FAILURE;
    /* Status returned by plaintext sockets transport implementation. */
    SocketStatus_t socketStatus;
    /* Information about the server to send the HTTP requests. */
    ServerInfo_t serverInfo;

    /* Initialize server information. */
    serverInfo.pHostName = SERVER_HOST;
    serverInfo.hostNameLength = SERVER_HOST_LENGTH;
    serverInfo.port = HTTP_PORT;

    /* Establish a TCP connection with the HTTP server. This example connects
     * to the HTTP server as specified in SERVER_HOST and HTTP_PORT
     * in demo_config.h. */
    LogInfo( ( "Establishing a TCP connection with %.*s:%d.",
               ( int32_t ) SERVER_HOST_LENGTH,
               SERVER_HOST,
               HTTP_PORT ) );
    socketStatus = Plaintext_Connect( pNetworkContext,
                                      &serverInfo,
                                      TRANSPORT_SEND_RECV_TIMEOUT_MS,
                                      TRANSPORT_SEND_RECV_TIMEOUT_MS );

    if( socketStatus == SOCKETS_SUCCESS )
    {
        returnStatus = EXIT_SUCCESS;
    }
    else
    {
        returnStatus = EXIT_FAILURE;
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int32_t sendHttpRequest( const TransportInterface_t * pTransportInterface,
                                const char * pMethod,
                                size_t methodLen,
                                const char * pPath,
                                size_t pathLen )
{
    /* Return value of this method. */
    int32_t returnStatus = EXIT_SUCCESS;

    /* Configurations of the initial request headers that are passed to
     * #HTTPClient_InitializeRequestHeaders. */
    HTTPRequestInfo_t requestInfo;
    /* Represents a response returned from an HTTP server. */
    HTTPResponse_t response;
    /* Represents header data that will be sent in an HTTP request. */
    HTTPRequestHeaders_t requestHeaders;

    /* Return value of all methods from the HTTP Client library API. */
    HTTPStatus_t httpStatus = HTTPSuccess;

    assert( pMethod != NULL );
    assert( pPath != NULL );

    /* Initialize all HTTP Client library API structs to 0. */
    ( void ) memset( &requestInfo, 0, sizeof( requestInfo ) );
    ( void ) memset( &response, 0, sizeof( response ) );
    ( void ) memset( &requestHeaders, 0, sizeof( requestHeaders ) );

    /* Set time function for retry timeout on receiving the response. */
    response.getTime = getTimeMs;

    /* Initialize the request object. */
    requestInfo.pHost = SERVER_HOST;
    requestInfo.hostLen = SERVER_HOST_LENGTH;
    requestInfo.pMethod = pMethod;
    requestInfo.methodLen = methodLen;
    requestInfo.pPath = pPath;
    requestInfo.pathLen = pathLen;

    /* Set "Connection" HTTP header to "keep-alive" so that multiple requests
     * can be sent over the same established TCP connection. */
    requestInfo.reqFlags = HTTP_REQUEST_KEEP_ALIVE_FLAG;

    /* Set the buffer used for storing request headers. */
    requestHeaders.pBuffer = userBuffer;
    requestHeaders.bufferLen = USER_BUFFER_LENGTH;

    httpStatus = HTTPClient_InitializeRequestHeaders( &requestHeaders,
                                                      &requestInfo );

    if( httpStatus == HTTPSuccess )
    {
        /* Initialize the response object. The same buffer used for storing
         * request headers is reused here. */
        response.pBuffer = userBuffer;
        response.bufferLen = USER_BUFFER_LENGTH;

        LogInfo( ( "Sending HTTP %.*s request to %.*s%.*s...",
                   ( int32_t ) requestInfo.methodLen, requestInfo.pMethod,
                   ( int32_t ) SERVER_HOST_LENGTH, SERVER_HOST,
                   ( int32_t ) requestInfo.pathLen, requestInfo.pPath ) );
        LogDebug( ( "Request Headers:\n%.*s\n"
                    "Request Body:\n%.*s\n",
                    ( int32_t ) requestHeaders.headersLen,
                    ( char * ) requestHeaders.pBuffer,
                    ( int32_t ) REQUEST_BODY_LENGTH, REQUEST_BODY ) );

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

    if( httpStatus == HTTPSuccess )
    {
        LogInfo( ( "Received HTTP response from %.*s%.*s...\n"
                   "Response Headers:\n%.*s\n"
                   "Response Status:\n%u\n"
                   "Response Body:\n%.*s\n",
                   ( int32_t ) SERVER_HOST_LENGTH, SERVER_HOST,
                   ( int32_t ) requestInfo.pathLen, requestInfo.pPath,
                   ( int32_t ) response.headersLen, response.pHeaders,
                   response.statusCode,
                   ( int32_t ) response.bodyLen, response.pBody ) );
    }
    else
    {
        LogError( ( "Failed to send HTTP %.*s request to %.*s%.*s: Error=%s.",
                    ( int32_t ) requestInfo.methodLen, requestInfo.pMethod,
                    ( int32_t ) SERVER_HOST_LENGTH, SERVER_HOST,
                    ( int32_t ) requestInfo.pathLen, requestInfo.pPath,
                    HTTPClient_strerror( httpStatus ) ) );
    }

    if( httpStatus != HTTPSuccess )
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
    /* Return value of main. */
    int32_t returnStatus = EXIT_SUCCESS;
    /* The transport layer interface used by the HTTP Client library. */
    TransportInterface_t transportInterface = { NULL };
    /* The network context for the transport layer interface. */
    NetworkContext_t networkContext;
    PlaintextParams_t plaintextParams;
    /* An array of HTTP paths to request. */
    const httpPathStrings_t httpMethodPaths[] =
    {
        { GET_PATH,  GET_PATH_LENGTH  },
        { HEAD_PATH, HEAD_PATH_LENGTH },
        { PUT_PATH,  PUT_PATH_LENGTH  },
        { POST_PATH, POST_PATH_LENGTH }
    };
    /* The respective method for the HTTP paths listed in #httpMethodPaths. */
    const httpMethodStrings_t httpMethods[] =
    {
        { HTTP_METHOD_GET,  HTTP_METHOD_GET_LENGTH  },
        { HTTP_METHOD_HEAD, HTTP_METHOD_HEAD_LENGTH },
        { HTTP_METHOD_PUT,  HTTP_METHOD_PUT_LENGTH  },
        { HTTP_METHOD_POST, HTTP_METHOD_POST_LENGTH }
    };

    ( void ) argc;
    ( void ) argv;

    /* Set the pParams member of the network context with desired transport. */
    networkContext.pParams = &plaintextParams;

    for( ; ; )
    {
        int i = 0;

        /**************************** Connect. ******************************/

        /* Establish TCP connection. */
        if( returnStatus == EXIT_SUCCESS )
        {
            /* Attempt to connect to the HTTP server. If connection fails, retry after
             * a timeout. Timeout value will be exponentially increased till the maximum
             * attempts are reached or maximum timeout value is reached. The function
             * returns EXIT_FAILURE if the TCP connection cannot be established to
             * broker after configured number of attempts. */
            returnStatus = connectToServerWithBackoffRetries( connectToServer,
                                                              &networkContext );

            if( returnStatus == EXIT_FAILURE )
            {
                /* Log error to indicate connection failure after all
                 * reconnect attempts are over. */
                LogError( ( "Failed to connect to HTTP server %.*s.",
                            ( int32_t ) SERVER_HOST_LENGTH,
                            SERVER_HOST ) );
            }
        }

        /* Define the transport interface. */
        if( returnStatus == EXIT_SUCCESS )
        {
            ( void ) memset( &transportInterface, 0, sizeof( transportInterface ) );
            transportInterface.recv = Plaintext_Recv;
            transportInterface.send = Plaintext_Send;
            transportInterface.pNetworkContext = &networkContext;
        }

        /********************** Send HTTPS requests. ************************/

        for( i = 0; i < NUMBER_HTTP_PATHS; i++ )
        {
            if( returnStatus == EXIT_SUCCESS )
            {
                returnStatus = sendHttpRequest( &transportInterface,
                                                httpMethods[ i ].httpMethod,
                                                httpMethods[ i ].httpMethodLength,
                                                httpMethodPaths[ i ].httpPath,
                                                httpMethodPaths[ i ].httpPathLength );
            }
            else
            {
                break;
            }
        }

        if( returnStatus == EXIT_SUCCESS )
        {
            /* Log message indicating an iteration completed successfully. */
            LogInfo( ( "Demo completed successfully." ) );
        }

        /************************** Disconnect. *****************************/

        /* Close TCP connection. */
        ( void ) Plaintext_Disconnect( &networkContext );

        LogInfo( ( "Short delay before starting the next iteration....\n" ) );
        sleep( DEMO_LOOP_DELAY_SECONDS );
    }

    return returnStatus;
}

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

/* OpenSSL transport header. */
#include "openssl_posix.h"

/* AWS IoT Core TLS ALPN definitions for MQTT authentication */
#include "aws_iot_alpn_defs.h"

/* Check that AWS IoT Core endpoint is defined. */
#ifndef AWS_IOT_ENDPOINT
    #error "AWS_IOT_ENDPOINT must be defined to your AWS IoT Core endpoint."
#endif

/* Check that TLS port used for AWS IoT Core is defined. */
#ifndef AWS_HTTPS_PORT
    #error "Please define a AWS_HTTPS_PORT."
#endif

/* Check that a path for HTTP Method POST is defined. */
#ifndef POST_PATH
    #error "Please define a POST_PATH."
#endif

/* Check that a path for Root CA certificate is defined. */
#ifndef ROOT_CA_CERT_PATH
    #error "Please define a ROOT_CA_CERT_PATH."
#endif

/* Check that a path for the client certificate is defined. */
#ifndef CLIENT_CERT_PATH
    #error "Please define a CLIENT_CERT_PATH."
#endif

/* Check that a path for the client's private key is defined. */
#ifndef CLIENT_PRIVATE_KEY_PATH
    #error "Please define a CLIENT_PRIVATE_KEY_PATH."
#endif

/* Check that transport timeout for transport send and receive is defined. */
#ifndef TRANSPORT_SEND_RECV_TIMEOUT_MS
    #define TRANSPORT_SEND_RECV_TIMEOUT_MS    ( 1000 )
#endif

/* Check that size of the user buffer is defined. */
#ifndef USER_BUFFER_LENGTH
    #define USER_BUFFER_LENGTH    ( 2048 )
#endif

/* Check that a request body to send for the POST request is defined. */
#ifndef REQUEST_BODY
    #error "Please define a REQUEST_BODY."
#endif

/**
 * @brief The length of the AWS IoT Endpoint.
 */
#define AWS_IOT_ENDPOINT_LENGTH    ( sizeof( AWS_IOT_ENDPOINT ) - 1 )

/**
 * @brief The length of the HTTP POST method.
 */
#define HTTP_METHOD_POST_LENGTH    ( sizeof( HTTP_METHOD_POST ) - 1 )

/**
 * @brief The length of the HTTP POST path.
 */
#define POST_PATH_LENGTH           ( sizeof( POST_PATH ) - 1 )

/**
 * @brief Length of the request body.
 */
#define REQUEST_BODY_LENGTH        ( sizeof( REQUEST_BODY ) - 1 )

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
    OpensslParams_t * pParams;
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
    /* Status returned by OpenSSL transport implementation. */
    OpensslStatus_t opensslStatus;
    /* Credentials to establish the TLS connection. */
    OpensslCredentials_t opensslCredentials;
    /* Information about the server to send the HTTP requests. */
    ServerInfo_t serverInfo;

    /* Initialize TLS credentials. */
    ( void ) memset( &opensslCredentials, 0, sizeof( opensslCredentials ) );
    opensslCredentials.pClientCertPath = CLIENT_CERT_PATH;
    opensslCredentials.pPrivateKeyPath = CLIENT_PRIVATE_KEY_PATH;
    opensslCredentials.pRootCaPath = ROOT_CA_CERT_PATH;
    opensslCredentials.sniHostName = AWS_IOT_ENDPOINT;

    /* ALPN is required when communicating to AWS IoT Core over port 443 through HTTP. */
    if( AWS_HTTPS_PORT == 443 )
    {
        opensslCredentials.pAlpnProtos = AWS_IOT_ALPN_HTTP_CA_AUTH_OPENSSL;
        opensslCredentials.alpnProtosLen = AWS_IOT_ALPN_MQTT_CA_AUTH_OPENSSL_LEN;
    }

    /* Initialize server information. */
    serverInfo.pHostName = AWS_IOT_ENDPOINT;
    serverInfo.hostNameLength = AWS_IOT_ENDPOINT_LENGTH;
    serverInfo.port = AWS_HTTPS_PORT;

    /* Establish a TLS session with the HTTP server. This example connects
     * to the HTTP server as specified in AWS_IOT_ENDPOINT and AWS_HTTPS_PORT
     * in demo_config.h. */
    LogInfo( ( "Establishing a TLS session to %.*s:%d.",
               ( int32_t ) AWS_IOT_ENDPOINT_LENGTH,
               AWS_IOT_ENDPOINT,
               AWS_HTTPS_PORT ) );
    opensslStatus = Openssl_Connect( pNetworkContext,
                                     &serverInfo,
                                     &opensslCredentials,
                                     TRANSPORT_SEND_RECV_TIMEOUT_MS,
                                     TRANSPORT_SEND_RECV_TIMEOUT_MS );

    if( opensslStatus == OPENSSL_SUCCESS )
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

    /* Initialize the request object. */
    requestInfo.pHost = AWS_IOT_ENDPOINT;
    requestInfo.hostLen = AWS_IOT_ENDPOINT_LENGTH;
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
                   ( int32_t ) AWS_IOT_ENDPOINT_LENGTH, AWS_IOT_ENDPOINT,
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
                   ( int32_t ) AWS_IOT_ENDPOINT_LENGTH, AWS_IOT_ENDPOINT,
                   ( int32_t ) requestInfo.pathLen, requestInfo.pPath,
                   ( int32_t ) response.headersLen, response.pHeaders,
                   response.statusCode,
                   ( int32_t ) response.bodyLen, response.pBody ) );
    }
    else
    {
        LogError( ( "Failed to send HTTP %.*s request to %.*s%.*s: Error=%s.",
                    ( int32_t ) requestInfo.methodLen, requestInfo.pMethod,
                    ( int32_t ) AWS_IOT_ENDPOINT_LENGTH, AWS_IOT_ENDPOINT,
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
 * This example resolves the AWS IoT Core endpoint, establishes a TCP connection,
 * performs a mutually authenticated TLS handshake occurs such that all further
 * communication is encrypted. After which, HTTP Client Library API is used to
 * make a POST request to AWS IoT Core in order to publish a message to a topic
 * named topic with QoS=1 so that all clients subscribed to the topic receive
 * the message at least once. Any possible errors are also logged.
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
    OpensslParams_t opensslParams;

    ( void ) argc;
    ( void ) argv;

    /* Set the pParams member of the network context with desired transport. */
    networkContext.pParams = &opensslParams;

    /**************************** Connect. ******************************/

    /* Establish TLS connection on top of TCP connection using OpenSSL. */
    if( returnStatus == EXIT_SUCCESS )
    {
        LogInfo( ( "Performing TLS handshake on top of the TCP connection." ) );

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
                        ( int32_t ) AWS_IOT_ENDPOINT_LENGTH,
                        AWS_IOT_ENDPOINT ) );
        }
    }

    /* Define the transport interface. */
    if( returnStatus == EXIT_SUCCESS )
    {
        ( void ) memset( &transportInterface, 0, sizeof( transportInterface ) );
        transportInterface.recv = Openssl_Recv;
        transportInterface.send = Openssl_Send;
        transportInterface.pNetworkContext = &networkContext;
    }

    /*********************** Send HTTPS request. ************************/

    if( returnStatus == EXIT_SUCCESS )
    {
        returnStatus = sendHttpRequest( &transportInterface,
                                        HTTP_METHOD_POST,
                                        HTTP_METHOD_POST_LENGTH,
                                        POST_PATH,
                                        POST_PATH_LENGTH );
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Log message indicating an iteration completed successfully. */
        LogInfo( ( "Demo completed successfully." ) );
    }

    /************************** Disconnect. *****************************/

    /* End TLS session, then close TCP connection. */
    ( void ) Openssl_Disconnect( &networkContext );

    return returnStatus;
}

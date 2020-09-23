/*
 * AWS IoT Device SDK for Embedded C V202009.00
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

/**
 * @file http_system_test.c
 * @brief Integration tests for the HTTP library when communicating with AWS IoT
 * from a POSIX platform.
 */

/* Standard header includes. */
#include <string.h>
#include <stdbool.h>
#include <assert.h>
#include <stdlib.h>
#include <time.h>

/* Include config file before other non-system includes. */
#include "test_config.h"

#include "unity.h"
/* Include paths for public enums, structures, and macros. */
#include "core_http_client.h"

/* Include OpenSSL implementation of transport interface. */
#include "openssl_posix.h"

/* Retry parameters. */
#include "retry_utils.h"

/* Ensure that config macros, required for TLS connection, have been defined. */
#ifndef SERVER_HOST
    #error "SERVER_HOST should be defined for the HTTP integration tests."
#endif

#ifndef ROOT_CA_CERT_PATH
    #error "ROOT_CA_CERT_PATH should be defined for the HTTP integration tests."
#endif

#ifndef CLIENT_CERT_PATH
    #error "CLIENT_CERT_PATH should be defined for the HTTP integration tests."
#endif

#ifndef CLIENT_PRIVATE_KEY_PATH
    #error "CLIENT_PRIVATE_KEY_PATH should be defined for the HTTP integration tests."
#endif

#ifndef IOT_CORE_ALPN_PROTOCOL_NAME
    #define IOT_CORE_ALPN_PROTOCOL_NAME           ( NULL )
    #define IOT_CORE_ALPN_PROTOCOL_NAME_LENGTH    ( 0 )
#else
    #define IOT_CORE_ALPN_PROTOCOL_NAME_LENGTH    ( sizeof( IOT_CORE_ALPN_PROTOCOL_NAME ) - 1 )
#endif

/* Check that size of the user buffer is defined. */
#ifndef USER_BUFFER_LENGTH
    #define USER_BUFFER_LENGTH    ( 2048 )
#endif

/**
 * @brief Length of HTTP server host name.
 */
#define SERVER_HOST_LENGTH     ( ( uint16_t ) ( sizeof( SERVER_HOST ) - 1 ) )

/**
 * @brief Length of the request body.
 */
#define REQUEST_BODY_LENGTH    ( sizeof( REQUEST_BODY ) - 1 )

/**
 * @brief Represents the OpenSSL context used for TLS session with the broker
 * for tests.
 */
static NetworkContext_t networkContext;

/* The transport layer interface used by the HTTP Client library. */
static TransportInterface_t transportInterface;

/**
 * @brief Represents the hostname and port of the broker.
 */
static ServerInfo_t serverInfo;

/**
 * @brief TLS credentials needed to connect to the broker.
 */
static OpensslCredentials_t opensslCredentials;

/**
 * @brief Shared buffer used in the tests for storing HTTP request headers and
 * HTTP response headers and body.
 */
static uint8_t userBuffer[ USER_BUFFER_LENGTH ];

/*-----------------------------------------------------------*/

/**
 * @brief Connect to HTTP server with reconnection retries.
 *
 * If connection fails, retry is attempted after a timeout.
 * Timeout value will exponentially increase until maximum
 * timeout value is reached or the number of attempts are exhausted.
 *
 * @param[out] pNetworkContext The output parameter to return the created network context.
 *
 */
static void connectToServerWithBackoffRetries( NetworkContext_t * pNetworkContext );

/**
 * @brief Send an HTTP request based on a specified method and path, then
 * print the response received from the server.
 *
 * @param[in] pTransportInterface The transport interface for making network calls.
 * @param[in] pMethod The HTTP request method.
 * @param[in] pPath The Request-URI to the objects of interest.
 */
static void sendHttpRequest( const TransportInterface_t * pTransportInterface,
                             const char * pMethod,
                             const char * pPath );

/*-----------------------------------------------------------*/

static void connectToServerWithBackoffRetries( NetworkContext_t * pNetworkContext )
{
    /* Status returned by the retry utilities. */
    RetryUtilsStatus_t retryUtilsStatus = RetryUtilsSuccess;
    /* Struct containing the next backoff time. */
    RetryUtilsParams_t reconnectParams;
    /* Status returned by OpenSSL transport implementation. */
    OpensslStatus_t opensslStatus;

    /* Reset or initialize file-scoped global variables. */
    ( void ) memset( &opensslCredentials, 0, sizeof( opensslCredentials ) );
    opensslCredentials.pRootCaPath = ROOT_CA_CERT_PATH;
    opensslCredentials.pClientCertPath = CLIENT_CERT_PATH;
    opensslCredentials.pPrivateKeyPath = CLIENT_PRIVATE_KEY_PATH;
    opensslCredentials.pAlpnProtos = IOT_CORE_ALPN_PROTOCOL_NAME;
    opensslCredentials.alpnProtosLen = IOT_CORE_ALPN_PROTOCOL_NAME_LENGTH;

    serverInfo.pHostName = SERVER_HOST;
    serverInfo.hostNameLength = SERVER_HOST_LENGTH;
    serverInfo.port = SERVER_PORT;

    /* Initialize reconnect attempts and interval */
    RetryUtils_ParamsReset( &reconnectParams );

    /* Attempt to connect to HTTP server. If connection fails, retry after
     * a timeout. Timeout value will exponentially increase until maximum
     * attempts are reached.
     */
    do
    {
        /* Establish a TLS session, on top of TCP connection, with the HTTP server. */
        opensslStatus = Openssl_Connect( pNetworkContext,
                                         &serverInfo,
                                         &opensslCredentials,
                                         TRANSPORT_SEND_RECV_TIMEOUT_MS,
                                         TRANSPORT_SEND_RECV_TIMEOUT_MS );

        if( opensslStatus != OPENSSL_SUCCESS )
        {
            retryUtilsStatus = RetryUtils_BackoffAndSleep( &reconnectParams );
        }

        if( retryUtilsStatus == RetryUtilsRetriesExhausted )
        {
            LogDebug( ( "Connection to the server failed, all attempts exhausted." ) );
        }
    } while( ( opensslStatus != OPENSSL_SUCCESS ) && ( retryUtilsStatus == RetryUtilsSuccess ) );

    TEST_ASSERT_EQUAL( OPENSSL_SUCCESS, opensslStatus );
    TEST_ASSERT_NOT_EQUAL( -1, networkContext.socketDescriptor );
    TEST_ASSERT_NOT_NULL( networkContext.pSsl );
}

/*-----------------------------------------------------------*/

static void sendHttpRequest( const TransportInterface_t * pTransportInterface,
                             const char * pMethod,
                             const char * pPath )
{
    /* Configurations of the initial request headers that are passed to
     * #HTTPClient_InitializeRequestHeaders. */
    HTTPRequestInfo_t requestInfo;
    /* Represents a response returned from an HTTP server. */
    HTTPResponse_t response;
    /* Represents header data that will be sent in an HTTP request. */
    HTTPRequestHeaders_t requestHeaders;

    assert( pMethod != NULL );
    assert( pPath != NULL );

    /* Initialize all HTTP Client library API structs to 0. */
    ( void ) memset( &requestInfo, 0, sizeof( requestInfo ) );
    ( void ) memset( &response, 0, sizeof( response ) );
    ( void ) memset( &requestHeaders, 0, sizeof( requestHeaders ) );

    /* Initialize the request object. */
    requestInfo.pHost = SERVER_HOST;
    requestInfo.hostLen = SERVER_HOST_LENGTH;
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

    TEST_ASSERT_EQUAL( HTTP_SUCCESS, HTTPClient_InitializeRequestHeaders( &requestHeaders,
                                                                          &requestInfo ) );
    TEST_ASSERT_NOT_EQUAL( 0, requestHeaders.headersLen );

    /* Initialize the response object. The same buffer used for storing
     * request headers is reused here. */
    response.pBuffer = userBuffer;
    response.bufferLen = USER_BUFFER_LENGTH;

    LogDebug( ( "Sending HTTP %.*s request to %.*s%.*s...",
                ( int32_t ) requestInfo.methodLen, requestInfo.method,
                ( int32_t ) SERVER_HOST_LENGTH, SERVER_HOST,
                ( int32_t ) requestInfo.pathLen, requestInfo.pPath ) );
    LogDebug( ( "Request Headers:\n%.*s\n"
                "Request Body:\n%.*s\n",
                ( int32_t ) requestHeaders.headersLen,
                ( char * ) requestHeaders.pBuffer,
                ( int32_t ) REQUEST_BODY_LENGTH, REQUEST_BODY ) );

    /* Send the request and receive the response. */
    TEST_ASSERT_EQUAL( HTTP_SUCCESS, HTTPClient_Send( pTransportInterface,
                                                      &requestHeaders,
                                                      ( uint8_t * ) REQUEST_BODY,
                                                      REQUEST_BODY_LENGTH,
                                                      &response,
                                                      0 ) );

    LogDebug( ( "Received HTTP response from %.*s%.*s...\n"
                "Response Headers:\n%.*s\n"
                "Response Status:\n%u\n"
                "Response Body:\n%.*s\n",
                ( int32_t ) SERVER_HOST_LENGTH, SERVER_HOST,
                ( int32_t ) requestInfo.pathLen, requestInfo.pPath,
                ( int32_t ) response.headersLen, response.pHeaders,
                response.statusCode,
                ( int32_t ) response.bodyLen, response.pBody ) );

    /* Close connection if a "Connection: close" header is found */
    if( response.respFlags == HTTP_RESPONSE_CONNECTION_CLOSE_FLAG )
    {
        ( void ) Openssl_Disconnect( &networkContext );
    }

    /* Verify that content length is greater than 0 for GET requests. */
    if( strcmp( pMethod, HTTP_METHOD_GET ) )
    {
        TEST_ASSERT_GREATER_THAN( 0, response.contentLength );
    }

    /* Verify response body is present */
    if( strcmp( pMethod, HTTP_METHOD_HEAD ) )
    {
        TEST_ASSERT_GREATER_THAN( 0, response.bodyLen );
    }
}

/* ============================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
    /* Establish TLS session with HTTP server on top of a newly-created TCP connection. */
    connectToServerWithBackoffRetries( &networkContext );

    /* Define the transport interface. */
    ( void ) memset( &transportInterface, 0, sizeof( transportInterface ) );
    transportInterface.recv = Openssl_Recv;
    transportInterface.send = Openssl_Send;
    transportInterface.pNetworkContext = &networkContext;
}

/* Called after each test method. */
void tearDown()
{
    /* End TLS session, then close TCP connection. */
    ( void ) Openssl_Disconnect( &networkContext );
}

/* ========================== Test Cases ============================ */

/**
 * @brief Sends a GET request synchronously and verifies the result.
 */
void test_HTTP_GET_Request( void )
{
    sendHttpRequest( &transportInterface,
                     HTTP_METHOD_GET,
                     GET_PATH );
}

/**
 * @brief Sends a HEAD request synchronously and verifies the result.
 */
void test_HTTP_HEAD_Request( void )
{
    sendHttpRequest( &transportInterface,
                     HTTP_METHOD_HEAD,
                     HEAD_PATH );
}

/**
 * @brief Sends a POST request synchronously and verifies the result.
 */
void test_HTTP_POST_Request( void )
{
    sendHttpRequest( &transportInterface,
                     HTTP_METHOD_POST,
                     POST_PATH );
}

/**
 * @brief Sends a PUT request synchronously and verifies the result.
 */
void test_HTTP_PUT_Request( void )
{
    sendHttpRequest( &transportInterface,
                     HTTP_METHOD_PUT,
                     PUT_PATH );
}

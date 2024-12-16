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

/* POSIX include. */
#include <unistd.h>

/* Include config file before other non-system includes. */
#include "test_config.h"

/* Unity testing framework includes. */
#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "core_http_client.h"

/* Include OpenSSL implementation of transport interface. */
#include "openssl_posix.h"

/*Include backoff algorithm header for retry logic.*/
#include "backoff_algorithm.h"

/* Ensure that config macros, required for TLS connection, have been defined. */
#ifndef SERVER_HOST
    #error "SERVER_HOST should be defined for the HTTP integration tests."
#endif

/* Check that TLS port of the server is defined. */
#ifndef HTTPS_PORT
    #error "HTTPS_PORT should be defined for the HTTP integration tests."
#endif

#ifndef ROOT_CA_CERT_PATH
    #error "ROOT_CA_CERT_PATH should be defined for the HTTP integration tests."
#endif

/* Check that size of the user buffer is defined. */
#ifndef USER_BUFFER_LENGTH
    #define USER_BUFFER_LENGTH    ( 2048 )
#endif

/**
 * @brief Length of HTTP server host name.
 */
#define SERVER_HOST_LENGTH                       ( ( uint16_t ) ( sizeof( SERVER_HOST ) - 1 ) )

/**
 * @brief Length of the request body.
 */
#define REQUEST_BODY_LENGTH                      ( sizeof( REQUEST_BODY ) - 1 )

/**
 * @brief The maximum number of retries for connecting to server.
 */
#define CONNECTION_RETRY_MAX_ATTEMPTS            ( 5U )

/**
 * @brief The maximum back-off delay (in milliseconds) for retrying connection to server.
 */
#define CONNECTION_RETRY_MAX_BACKOFF_DELAY_MS    ( 5000U )

/**
 * @brief The base back-off delay (in milliseconds) to use for connection retry attempts.
 */
#define CONNECTION_RETRY_BACKOFF_BASE_MS         ( 500U )

/**
 * @brief Number of milliseconds in a second.
 */
#define NUM_MILLISECONDS_IN_SECOND               ( 1000U )


/**
 * @brief The maximum number of retries to attempt on network error.
 */
#define HTTP_REQUEST_MAX_RETRY_COUNT    ( 3 )

/**
 * @brief The path used for testing receiving a transfer encoding chunked
 * response.
 */
#define STR_HELPER( x )    # x
#define TO_STR( x )        STR_HELPER( x )
#define GET_CHUNKED_PATH    "/stream-bytes/" TO_STR( CHUNKED_BODY_LENGTH )

/**
 * @brief A test response for http-parser that ends header lines with linefeeds
 * only.
 */
#define HTTP_TEST_RESPONSE_LINE_FEEDS_ONLY \
    "HTTP/1.1 200 OK\n"                    \
    "Content-Length: 27\n"                 \
    "\n"                                   \
    "HTTP/0.0 0\n"                         \
    "test-header0: ab"
#define HTTP_TEST_RESPONSE_LINE_FEEDS_ONLY_BODY_LENGTH       27
#define HTTP_TEST_RESPONSE_LINE_FEEDS_ONLY_HEADERS_LENGTH    18

/**
 * @brief Represents the OpenSSL context used for TLS session with the broker
 * for tests.
 */
static NetworkContext_t networkContext;

/**
 * @brief Parameters for the Openssl Context.
 */
static OpensslParams_t opensslParams;

/**
 * @brief The transport layer interface used by the HTTP Client library.
 */
static TransportInterface_t transportInterface = { 0 };

/**
 * @brief Represents the hostname and port of the broker.
 */
static ServerInfo_t serverInfo;

/**
 * @brief TLS credentials needed to connect to the broker.
 */
static OpensslCredentials_t opensslCredentials;

/**
 * @brief A shared buffer used in the tests for storing HTTP request headers and
 * HTTP response headers and body.
 */
static uint8_t userBuffer[ USER_BUFFER_LENGTH ];

/**
 * @brief A HTTPResponse_t to share among the tests. This is used to verify
 * custom expected output.
 */
static HTTPResponse_t response;

/**
 * @brief Network data that is returned in the transportRecvStub.
 */
static uint8_t * pNetworkData = NULL;

/**
 * @brief The length of the network data to return in the transportRecvStub.
 */
static size_t networkDataLen = 0U;

/*-----------------------------------------------------------*/

/* Each compilation unit must define the NetworkContext struct. */
struct NetworkContext
{
    OpensslParams_t * pParams;
};

/*-----------------------------------------------------------*/

/**
 * @brief The random number generator to use for exponential backoff with
 * jitter retry logic.
 *
 * @return The generated random number.
 */
static uint32_t generateRandomNumber();

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

/**
 * @brief A stub for receiving test network data. This always returns success.
 *
 * @param[in] pNetworkContext Implementation-defined network context.
 * @param[in] pBuffer Buffer to receive the data into.
 * @param[in] bytesToRecv Number of bytes requested from the network.
 *
 * @return The number of bytes received. This will be the minimum of
 * networkDataLen or bytesToRead.
 */
static int32_t transportRecvStub( NetworkContext_t * pNetworkContext,
                                  void * pBuffer,
                                  size_t bytesToRead );

/**
 * @brief A stub for sending data over the network. This always returns success.
 *
 * @param[in] pNetworkContext Implementation-defined network context.
 * @param[in] pBuffer Buffer containing the bytes to send over the network stack.
 * @param[in] bytesToSend Number of bytes to send over the network.
 *
 * @return This function always returns bytesToWrite.
 */
static int32_t transportSendStub( NetworkContext_t * pNetworkContext,
                                  const void * pBuffer,
                                  size_t bytesToWrite );

/*-----------------------------------------------------------*/

static uint32_t generateRandomNumber()
{
    return( rand() );
}

/*-----------------------------------------------------------*/

static void connectToServerWithBackoffRetries( NetworkContext_t * pNetworkContext )
{
    /* Status returned by the retry utilities. */
    BackoffAlgorithmStatus_t backoffAlgStatus = BackoffAlgorithmSuccess;
    /* Struct containing the next backoff time. */
    BackoffAlgorithmContext_t reconnectParams;
    /* Status returned by OpenSSL transport implementation. */
    OpensslStatus_t opensslStatus;
    uint16_t nextRetryBackOff = 0U;
    struct timespec tp;

    /* Reset or initialize file-scoped global variables. */
    ( void ) memset( &opensslCredentials, 0, sizeof( opensslCredentials ) );
    opensslCredentials.pRootCaPath = ROOT_CA_CERT_PATH;
    opensslCredentials.sniHostName = SERVER_HOST;

    serverInfo.pHostName = SERVER_HOST;
    serverInfo.hostNameLength = SERVER_HOST_LENGTH;
    serverInfo.port = HTTPS_PORT;

    pNetworkContext->pParams = &opensslParams;

    /* Seed pseudo random number generator used in the demo for
     * backoff period calculation when retrying failed network operations
     * with broker. */

    /* Get current time to seed pseudo random number generator. */
    ( void ) clock_gettime( CLOCK_REALTIME, &tp );
    /* Seed pseudo random number generator with nanoseconds. */
    srand( tp.tv_nsec );

    /* Initialize reconnect attempts and interval */
    BackoffAlgorithm_InitializeParams( &reconnectParams,
                                       CONNECTION_RETRY_BACKOFF_BASE_MS,
                                       CONNECTION_RETRY_MAX_BACKOFF_DELAY_MS,
                                       CONNECTION_RETRY_MAX_ATTEMPTS );

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
            /* Generate a random number and get back-off value (in milliseconds) for the next connection retry. */
            backoffAlgStatus = BackoffAlgorithm_GetNextBackoff( &reconnectParams, generateRandomNumber(), &nextRetryBackOff );

            if( backoffAlgStatus == BackoffAlgorithmSuccess )
            {
                LogWarn( ( "Connection to the HTTP server failed. Retrying connection after backoff." ) );
                ( void ) sleep( nextRetryBackOff / NUM_MILLISECONDS_IN_SECOND );
            }
            else
            {
                LogError( ( "Connection to the HTTP server failed, all attempts exhausted." ) );
            }
        }
    } while( ( opensslStatus != OPENSSL_SUCCESS ) && ( backoffAlgStatus == BackoffAlgorithmSuccess ) );

    TEST_ASSERT_EQUAL( OPENSSL_SUCCESS, opensslStatus );
    TEST_ASSERT_NOT_EQUAL( -1, opensslParams.socketDescriptor );
    TEST_ASSERT_NOT_NULL( opensslParams.pSsl );
}

/*-----------------------------------------------------------*/

static void sendHttpRequest( const TransportInterface_t * pTransportInterface,
                             const char * pMethod,
                             const char * pPath )
{
    /* Status returned by methods in HTTP Client Library API. */
    HTTPStatus_t httpStatus = HTTPNetworkError;
    /* Tracks number of retry requests made to the HTTP server. */
    uint8_t retryCount = 0;

    /* Configurations of the initial request headers that are passed to
     * #HTTPClient_InitializeRequestHeaders. */
    HTTPRequestInfo_t requestInfo;
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
    requestInfo.pMethod = pMethod;
    requestInfo.methodLen = strlen( pMethod );
    requestInfo.pPath = pPath;
    requestInfo.pathLen = strlen( pPath );

    /* Set "Connection" HTTP header to "keep-alive" so that multiple requests
     * can be sent over the same established TCP connection. */
    requestInfo.reqFlags = HTTP_REQUEST_KEEP_ALIVE_FLAG;

    /* Set the buffer used for storing request headers. */
    requestHeaders.pBuffer = userBuffer;
    requestHeaders.bufferLen = USER_BUFFER_LENGTH;

    /* Initialize the response object. The same buffer used for storing
     * request headers is reused here. */
    response.pBuffer = userBuffer;
    response.bufferLen = USER_BUFFER_LENGTH;

    LogDebug( ( "Sending HTTP %.*s request to %.*s%.*s...",
                ( int32_t ) requestInfo.methodLen, requestInfo.pMethod,
                ( int32_t ) SERVER_HOST_LENGTH, SERVER_HOST,
                ( int32_t ) requestInfo.pathLen, requestInfo.pPath ) );

    /* Send request to HTTP server. If a network error is found, retry request for a
     * count of HTTP_REQUEST_MAX_RETRY_COUNT. */
    do
    {
        /* Since the request and response headers share a buffer, request headers should
         * be re-initialized after a failed request. */
        httpStatus = HTTPClient_InitializeRequestHeaders( &requestHeaders,
                                                          &requestInfo );
        TEST_ASSERT_EQUAL( HTTPSuccess, httpStatus );
        TEST_ASSERT_NOT_EQUAL( 0, requestHeaders.headersLen );

        LogDebug( ( "Request Headers:\n%.*s\n"
                    "Request Body:\n%.*s\n",
                    ( int32_t ) requestHeaders.headersLen,
                    ( char * ) requestHeaders.pBuffer,
                    ( int32_t ) REQUEST_BODY_LENGTH, REQUEST_BODY ) );

        httpStatus = HTTPClient_Send( pTransportInterface,
                                      &requestHeaders,
                                      ( uint8_t * ) REQUEST_BODY,
                                      REQUEST_BODY_LENGTH,
                                      &response,
                                      0 );

        if( httpStatus == HTTPNetworkError )
        {
            LogDebug( ( "A network error has occured, retrying request." ) );
            resetTest();
        }

        retryCount++;
    } while( ( httpStatus == HTTPNetworkError ) && ( retryCount < HTTP_REQUEST_MAX_RETRY_COUNT ) );

    TEST_ASSERT_EQUAL( HTTPSuccess, httpStatus );

    LogDebug( ( "Received HTTP response from %.*s%.*s...\n"
                "Response Headers:\n%.*s\n"
                "Response Status:\n%u\n"
                "Response Body:\n%.*s\n",
                ( int32_t ) SERVER_HOST_LENGTH, SERVER_HOST,
                ( int32_t ) requestInfo.pathLen, requestInfo.pPath,
                ( int32_t ) response.headersLen, response.pHeaders,
                response.statusCode,
                ( int32_t ) response.bodyLen, response.pBody ) );

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

/*-----------------------------------------------------------*/

static int32_t transportRecvStub( NetworkContext_t * pNetworkContext,
                                  void * pBuffer,
                                  size_t bytesToRead )
{
    size_t bytesToCopy = ( bytesToRead < networkDataLen ) ? bytesToRead : networkDataLen;

    ( void ) pNetworkContext;

    memcpy( pBuffer, pNetworkData, bytesToCopy );
    pNetworkData += bytesToCopy;
    networkDataLen -= bytesToCopy;
    return bytesToCopy;
}

/*-----------------------------------------------------------*/

static int32_t transportSendStub( NetworkContext_t * pNetworkContext,
                                  const void * pBuffer,
                                  size_t bytesToWrite )
{
    ( void ) pNetworkContext;
    ( void ) pBuffer;
    return bytesToWrite;
}


/* ============================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
    /* Clear the global response before each test. */
    memset( &response, 0, sizeof( HTTPResponse_t ) );

    /* Apply defaults and reset the transport receive data globals. */
    pNetworkData = NULL;
    networkDataLen = 0U;

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

/**
 * @brief Receive a Transfer-Encoding chunked response.
 */
void test_HTTP_Chunked_Response( void )
{
    sendHttpRequest( &transportInterface,
                     HTTP_METHOD_GET,
                     GET_CHUNKED_PATH );

    /* Verify the response is of the length configured, which means the
     * chunk header was overwritten. */
    TEST_ASSERT_EQUAL( CHUNKED_BODY_LENGTH, response.bodyLen );
}

/**
 * @brief Test how http-parser responds with a response of line-feeds only and
 * no carriage returns.
 */
void test_HTTP_LineFeedOnly_Response( void )
{
    HTTPRequestHeaders_t requestHeaders = { 0 };
    HTTPStatus_t status = HTTPSuccess;
    TransportInterface_t transport = { 0 };
    const char * dummyRequestHeaders = "GET something.txt HTTP/1.1\r\n"
                                       "Host: integration-test\r\n\r\r\n";

    requestHeaders.pBuffer = userBuffer;
    requestHeaders.bufferLen = USER_BUFFER_LENGTH;
    response.pBuffer = userBuffer;
    response.bufferLen = USER_BUFFER_LENGTH;

    transport.send = transportSendStub;
    transport.recv = transportRecvStub;

    /* Setup the data to receive on the network. */
    pNetworkData = ( uint8_t * ) HTTP_TEST_RESPONSE_LINE_FEEDS_ONLY;
    networkDataLen = sizeof( HTTP_TEST_RESPONSE_LINE_FEEDS_ONLY ) - 1U;

    /* Setup the request headers to the predefined headers. */
    requestHeaders.headersLen = strlen( dummyRequestHeaders );
    memcpy( requestHeaders.pBuffer, dummyRequestHeaders, requestHeaders.headersLen );

    status = HTTPClient_Send( &transport,
                              &requestHeaders,
                              NULL,
                              0,
                              &response,
                              HTTP_SEND_DISABLE_CONTENT_LENGTH_FLAG );

    TEST_ASSERT_EQUAL( HTTPSuccess, status );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_LINE_FEEDS_ONLY_BODY_LENGTH, response.bodyLen );
    TEST_ASSERT_EQUAL( HTTP_TEST_RESPONSE_LINE_FEEDS_ONLY_HEADERS_LENGTH, response.headersLen );
}

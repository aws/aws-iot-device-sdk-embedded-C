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
#include <stdbool.h>

/* POSIX includes. */
#include <unistd.h>
#include <fcntl.h>
#include <mqueue.h>
#include <errno.h>
#include <sys/types.h>
#include <signal.h>

/* Include Demo Config as the first non-system header. */
#include "demo_config.h"

/* Common HTTP demo utilities. */
#include "http_demo_utils.h"

/* HTTP API header. */
#include "core_http_client.h"

/* OpenSSL transport header. */
#include "openssl_posix.h"

/*Include backoff algorithm header for retry logic.*/
#include "backoff_algorithm.h"

/* Check that TLS port of the server is defined. */
#ifndef HTTPS_PORT
    #error "Please define a HTTPS_PORT."
#endif

/* Check that a path for Root CA Certificate is defined. */
#ifndef ROOT_CA_CERT_PATH
    #error "Please define a ROOT_CA_CERT_PATH."
#endif

/* Check that a presigned url for the target S3 file is defined. */
#ifndef S3_PRESIGNED_GET_URL
    #error "Please define a S3_PRESIGNED_GET_URL."
#endif

/* Check that transport timeout for transport send and receive is defined. */
#ifndef TRANSPORT_SEND_RECV_TIMEOUT_MS
    #error "Please define a TRANSPORT_SEND_RECV_TIMEOUT_MS."
#endif

/* Check that size of the user buffer is defined. */
#ifndef USER_BUFFER_LENGTH
    #error "Please define a USER_BUFFER_LENGTH."
#endif

/* Check that size of the user buffer is defined. */
#ifndef RANGE_REQUEST_LENGTH
    #error "Please define a RANGE_REQUEST_LENGTH."
#endif

/* Check the the queue size is defined. */
#ifndef QUEUE_SIZE
    #error "Please define a QUEUE_SIZE."
#endif

/**
 * @brief The name of the HTTP thread's input queue. Must begin with a slash and
 * be a valid pathname.
 */
#define REQUEST_QUEUE                             "/demo_request_queue"

/**
 * @brief The name of the HTTP thread's output queue. Must begin with a slash
 * and be a valid pathname.
 */
#define RESPONSE_QUEUE                            "/demo_response_queue"

/* Posix file permissions for the queues. Allows read and write access to the
 * user this demo is running as. */
#define QUEUE_PERMISSIONS                         0600

/**
 * @brief Length of the S3 presigned URL.
 */
#define S3_PRESIGNED_GET_URL_LENGTH               ( sizeof( S3_PRESIGNED_GET_URL ) - 1 )

/**
 * @brief The length of the HTTP GET method.
 */
#define HTTP_METHOD_GET_LENGTH                    ( sizeof( HTTP_METHOD_GET ) - 1 )

/**
 * @brief Field name of the HTTP Range header to read from server response.
 */
#define HTTP_CONTENT_RANGE_HEADER_FIELD           "Content-Range"

/**
 * @brief Length of the HTTP Range header field.
 */
#define HTTP_CONTENT_RANGE_HEADER_FIELD_LENGTH    ( sizeof( HTTP_CONTENT_RANGE_HEADER_FIELD ) - 1 )

/**
 * @brief HTTP status code returned for partial content.
 */
#define HTTP_STATUS_CODE_PARTIAL_CONTENT          206

/**
 * @brief The maximum number of times to run the loop in this demo.
 *
 * @note The demo loop is attempted to re-run only if it fails in an iteration.
 * Once the demo loop succeeds in an iteration, the demo exits successfully.
 */
#ifndef HTTP_MAX_DEMO_LOOP_COUNT
    #define HTTP_MAX_DEMO_LOOP_COUNT    ( 3 )
#endif

/**
 * @brief Time in seconds to wait between retries of the demo loop if
 * demo loop fails.
 */
#define DELAY_BETWEEN_DEMO_RETRY_ITERATIONS_S    ( 5 )

/**
 * @brief The location of the host address within string S3_PRESIGNED_GET_URL.
 */
static const char * pHost = NULL;

/**
 * @brief The length of the host address within string S3_PRESIGNED_GET_URL.
 * */
static size_t hostLen = 0;

/**
 * @brief Data type for request queue.
 *
 * In addition to sending #HTTPRequestHeaders_t, we need to send the buffer it uses.
 * The pointer to the buffer in #HTTPRequestHeaders_t will be incorrect after
 * it is received, so it will need to be fixed.
 */
typedef struct RequestItem
{
    HTTPRequestHeaders_t requestHeaders;
    uint8_t headersBuffer[ USER_BUFFER_LENGTH ];
} RequestItem_t;

/**
 * @brief Data type for response queue.
 *
 * In addition to sending the #HTTPResponse_t, we need to send the buffer it uses.
 * The pointer to the buffer in #HTTPResponse_t will be incorrect after
 * it is received, so it will need to be fixed.
 */
typedef struct ResponseItem
{
    HTTPResponse_t response;
    uint8_t responseBuffer[ USER_BUFFER_LENGTH ];
} ResponseItem_t;

/* @brief Struct used for sending requests to the HTTP thread.
 *
 * This is used by both the main and HTTP threads, though since we create the
 * HTTP thread without a shared memory space, each will have its own copy. We
 * have this as a global so that it will be located at the same address in the
 * main and HTTP threads so that way pointers remain valid when copied over.
 */
static RequestItem_t requestItem = { 0 };

/* @brief Struct used for receiving responses from the HTTP thread.
 *
 * This is used by both the main and HTTP threads, though since we create the
 * HTTP thread without a shared memory space, each will have its own copy. We
 * have this as a global so that it will be located at the same address in the
 * main and HTTP threads so that way pointers remain valid when copied over.
 */
static ResponseItem_t responseItem = { 0 };

/**
 * @brief The return status for requestS3ObjectRange() and retrieveHTTPResponse().
 */
typedef enum QueueOpStatus
{
    /**
     * @brief The function completed successfully.
     */
    QUEUE_OP_SUCCESS,

    /**
     * @brief The function was given a non-blocking queue and would have blocked
     * were it a blocking queue.
     */
    QUEUE_OP_WOULD_BLOCK,

    /**
     * @brief The function encountered an error.
     */
    QUEUE_OP_FAILURE,
} QueueOpStatus_t;

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
static int connectToServer( NetworkContext_t * pNetworkContext );

/**
 * @brief Send an HTTP request based on a specified method and path, and
 * print the response received from the server.
 *
 * @param[in] pHost The host name of the server.
 * @param[in] hostLen The length of pHost.
 * @param[in] pRequest The HTTP Request-URI.
 * @param[in] requestUriLen The length of pRequest.
 * @param[in] fileSize The length of the file at S3_PRESIGNED_GET_URL.
 * @param[in] requestQueue The queue to which HTTP requests should be written.
 * @param[in] responseQueue The queue from which HTTP responses should be read.
 *
 * @return false on failure; true on success.
 */
static bool downloadS3ObjectFile( const char * pHost,
                                  const size_t hostLen,
                                  const char * pRequest,
                                  const size_t requestUriLen,
                                  mqd_t requestQueue,
                                  mqd_t responseQueue );

/**
 * @brief Enqueue an HTTP request for a range of the S3 file.
 *
 * @param[in] requestInfo The #HTTPRequestInfo_t for configuring the request.
 * @param[in] requestQueue The queue to which HTTP requests should be written.
 * @param[in] start The position of the first byte in the range.
 * @param[in] end The position of the last byte in the range, inclusive.
 *
 * @return QUEUE_OP_FAILURE on failure; QUEUE_OP_WOULD_BLOCK if would block,
 * QUEUE_OP_SUCCESS on success.
 */
static QueueOpStatus_t requestS3ObjectRange( const HTTPRequestInfo_t * requestInfo,
                                             mqd_t requestQueue,
                                             const size_t start,
                                             const size_t end );


/**
 * @brief Processes an HTTP response from the response queue.
 *
 * @param[in] responseQueue The queue from which HTTP responses should be read.
 * @param[out] responseItem The HTTP response received.
 *
 * @return QUEUE_OP_FAILURE on failure; QUEUE_OP_WOULD_BLOCK if would block,
 * QUEUE_OP_SUCCESS on success.
 */
static QueueOpStatus_t retrieveHTTPResponse( mqd_t responseQueue,
                                             ResponseItem_t * responseItem );

/**
 * @brief Retrieve the size of the S3 object that is specified in pPath using
 * HTTP thread.
 *
 * @param[in] requestInfo The #HTTPRequestInfo_t for configuring the request.
 * @param[in] requestQueue The queue to which HTTP requests should be written.
 * @param[in] responseQueue The queue from which HTTP responses should be read.
 * @param[out] pFileSize - The size of the S3 object.
 *
 * @return false on failure; true on success.
 */
static bool getS3ObjectFileSize( const HTTPRequestInfo_t * requestInfo,
                                 mqd_t requestQueue,
                                 mqd_t responseQueue,
                                 size_t * pFileSize );

/**
 * @brief Services HTTP requests from the request queue and writes the
 * responses to the response queue.
 *
 * @param[in] pTransportInterface The transport interface for making network calls.
 *
 * @return -1 on failure; PID of HTTP thread on success.
 */
static pid_t startHTTPThread( const TransportInterface_t * pTransportInterface );

/**
 * @brief Clean up resources created by demo.
 *
 * @param[in] httpThread The HTTP thread.
 * @param[in] requestQueue The request queue.
 * @param[in] responseQueue The response queue.
 */
static void tearDown( pid_t httpThread,
                      mqd_t requestQueue,
                      mqd_t responseQueue );

/*-----------------------------------------------------------*/

static int connectToServer( NetworkContext_t * pNetworkContext )
{
    /* Status returned by OpenSSL transport implementation. */
    OpensslStatus_t opensslStatus;
    /* Credentials to establish the TLS connection. */
    OpensslCredentials_t opensslCredentials = { 0 };
    /* Information about the server to send the HTTP requests. */
    ServerInfo_t serverInfo = { 0 };

    /* The host address string extracted from S3_PRESIGNED_GET_URL. */
    char serverHost[ sizeof( S3_PRESIGNED_GET_URL ) ] = { 0 };

    /* Initialize TLS credentials. */
    opensslCredentials.pRootCaPath = ROOT_CA_CERT_PATH;
    opensslCredentials.sniHostName = serverHost;

    /* serverHost should consist only of the host address located in S3_PRESIGNED_GET_URL. */
    memcpy( serverHost, pHost, hostLen );

    /* Initialize server information. */
    serverInfo.pHostName = serverHost;
    serverInfo.hostNameLength = hostLen;
    serverInfo.port = HTTPS_PORT;

    /* Establish a TLS session with the HTTP server. This example connects
     * to the HTTP server as specified in SERVER_HOST and HTTPS_PORT
     * in demo_config.h. */
    LogInfo( ( "Establishing a TLS session with %s:%d.",
               serverHost,
               HTTPS_PORT ) );

    opensslStatus = Openssl_Connect( pNetworkContext,
                                     &serverInfo,
                                     &opensslCredentials,
                                     TRANSPORT_SEND_RECV_TIMEOUT_MS,
                                     TRANSPORT_SEND_RECV_TIMEOUT_MS );

    return opensslStatus == OPENSSL_SUCCESS ? EXIT_SUCCESS : EXIT_FAILURE;
}

/*-----------------------------------------------------------*/

static bool downloadS3ObjectFile( const char * pHost,
                                  const size_t hostLen,
                                  const char * pRequest,
                                  const size_t requestUriLen,
                                  mqd_t requestQueue,
                                  mqd_t responseQueue )
{
    bool returnStatus = true;
    QueueOpStatus_t queueOpStatus = QUEUE_OP_SUCCESS;

    size_t requestCount = 0;

    /* Configurations of the initial request headers. */
    HTTPRequestInfo_t requestInfo = { 0 };

    /* The length of the file at S3_PRESIGNED_GET_URL. */
    size_t fileSize = 0;

    /* The number of bytes we want to request within each range of the file. */
    size_t numReqBytes = 0;
    /* curByte indicates which starting byte we want to download next. */
    size_t curByte = 0;

    /* Initialize the request object. */
    requestInfo.pHost = pHost;
    requestInfo.hostLen = hostLen;
    requestInfo.pMethod = HTTP_METHOD_GET;
    requestInfo.methodLen = HTTP_METHOD_GET_LENGTH;
    requestInfo.pPath = pRequest;
    requestInfo.pathLen = requestUriLen;

    /* Set "Connection" HTTP header to "keep-alive" so that multiple requests
     * can be sent over the same established TCP connection. This is done in
     * order to download the file in parts. */
    requestInfo.reqFlags = HTTP_REQUEST_KEEP_ALIVE_FLAG;

    /* Get the length of the S3 file. */
    returnStatus = getS3ObjectFileSize( &requestInfo,
                                        requestQueue,
                                        responseQueue,
                                        &fileSize );

    if( returnStatus == true )
    {
        if( fileSize < RANGE_REQUEST_LENGTH )
        {
            numReqBytes = fileSize;
        }
        else
        {
            numReqBytes = RANGE_REQUEST_LENGTH;
        }

        /* Here we iterate sending byte range requests and retrieving responses
         * until the full file has been downloaded. We keep track of the next byte
         * to download with curByte. When this reaches the fileSize we stop
         * downloading. We keep track of the number of responses we are waiting for
         * with requestCount.
         */
        while( ( returnStatus != false ) && ( curByte < fileSize || requestCount > 0 ) )
        {
            /* Send range request if remaining. */
            if( curByte < fileSize )
            {
                queueOpStatus = requestS3ObjectRange( &requestInfo,
                                                      requestQueue,
                                                      curByte,
                                                      curByte + numReqBytes - 1 );

                if( queueOpStatus == QUEUE_OP_FAILURE )
                {
                    returnStatus = false;
                }
                else if( queueOpStatus == QUEUE_OP_SUCCESS )
                {
                    requestCount += 1;
                    curByte += numReqBytes;

                    if( ( fileSize - curByte ) < numReqBytes )
                    {
                        numReqBytes = fileSize - curByte;
                    }
                }
            }

            /* Retrieve response. */
            if( ( requestCount > 0 ) && ( queueOpStatus != QUEUE_OP_FAILURE ) )
            {
                queueOpStatus = retrieveHTTPResponse( responseQueue, &responseItem );

                if( queueOpStatus == QUEUE_OP_FAILURE )
                {
                    returnStatus = false;
                }
                else if( queueOpStatus == QUEUE_OP_SUCCESS )
                {
                    LogInfo( ( "Main thread received HTTP response" ) );
                    LogInfo( ( "Response Headers:\n%.*s",
                               ( int32_t ) responseItem.response.headersLen,
                               responseItem.response.pHeaders ) );
                    LogInfo( ( "Response Status:\n%u", responseItem.response.statusCode ) );
                    LogInfo( ( "Response Body:\n%.*s\n", ( int32_t ) responseItem.response.bodyLen,
                               responseItem.response.pBody ) );

                    if( responseItem.response.statusCode != HTTP_STATUS_CODE_PARTIAL_CONTENT )
                    {
                        LogError( ( "Recieved repsonse with unexpected status code: %d", responseItem.response.statusCode ) );
                        returnStatus = false;
                    }
                    else
                    {
                        requestCount -= 1;
                    }
                }
            }
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static QueueOpStatus_t requestS3ObjectRange( const HTTPRequestInfo_t * requestInfo,
                                             mqd_t requestQueue,
                                             const size_t start,
                                             const size_t end )
{
    QueueOpStatus_t returnStatus = QUEUE_OP_SUCCESS;
    HTTPStatus_t httpStatus = HTTPSuccess;

    /* Return value of mq_send. */
    int mqerror = 0;

    /* Set the buffer used for storing request headers. */
    requestItem.requestHeaders.pBuffer = requestItem.headersBuffer;
    requestItem.requestHeaders.bufferLen = USER_BUFFER_LENGTH;

    httpStatus = HTTPClient_InitializeRequestHeaders( &( requestItem.requestHeaders ),
                                                      requestInfo );

    if( httpStatus != HTTPSuccess )
    {
        LogError( ( "Failed to initialize HTTP request headers: Error=%s.",
                    HTTPClient_strerror( httpStatus ) ) );
        returnStatus = QUEUE_OP_FAILURE;
    }

    if( returnStatus == QUEUE_OP_SUCCESS )
    {
        httpStatus = HTTPClient_AddRangeHeader( &( requestItem.requestHeaders ),
                                                start,
                                                end );

        if( httpStatus != HTTPSuccess )
        {
            LogError( ( "Failed to add Range header to request headers: Error=%s.",
                        HTTPClient_strerror( httpStatus ) ) );
            returnStatus = QUEUE_OP_FAILURE;
        }
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Enqueue the request. */
        LogInfo( ( "Enqueuing bytes %d to %d of S3 Object:  ",
                   ( int32_t ) start,
                   ( int32_t ) end ) );
        LogInfo( ( "Request Headers:\n%.*s",
                   ( int32_t ) requestItem.requestHeaders.headersLen,
                   ( char * ) requestItem.requestHeaders.pBuffer ) );

        mqerror = mq_send( requestQueue,
                           ( char * ) &requestItem,
                           sizeof( RequestItem_t ),
                           0 );

        if( mqerror == -1 )
        {
            if( errno != EAGAIN )
            {
                /* Error other than due to not blocking. */
                LogError( ( "Failed to write to request queue with error %s.",
                            strerror( errno ) ) );
                returnStatus = QUEUE_OP_FAILURE;
            }
            else
            {
                returnStatus = QUEUE_OP_WOULD_BLOCK;
            }
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static QueueOpStatus_t retrieveHTTPResponse( mqd_t responseQueue,
                                             ResponseItem_t * responseItem )
{
    QueueOpStatus_t returnStatus = QUEUE_OP_SUCCESS;

    /* Return value of mq_receive. */
    int mqread = 0;

    /* Read response from queue. */
    mqread = mq_receive( responseQueue, ( char * ) responseItem,
                         sizeof( ResponseItem_t ), NULL );

    if( mqread == -1 )
    {
        if( errno != EAGAIN )
        {
            /* Error other than due to not blocking. */
            LogError( ( "Failed to read from response queue with error %s.",
                        strerror( errno ) ) );
            returnStatus = QUEUE_OP_FAILURE;
        }
        else
        {
            returnStatus = QUEUE_OP_WOULD_BLOCK;
        }
    }

    if( returnStatus == QUEUE_OP_SUCCESS )
    {
        if( mqread != sizeof( ResponseItem_t ) )
        {
            LogError( ( "Response from response queue has incorrect size." ) );
            returnStatus = QUEUE_OP_FAILURE;
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static bool getS3ObjectFileSize( const HTTPRequestInfo_t * requestInfo,
                                 mqd_t requestQueue,
                                 mqd_t responseQueue,
                                 size_t * pFileSize )
{
    bool returnStatus = true;
    HTTPStatus_t httpStatus = HTTPSuccess;
    QueueOpStatus_t queueOpStatus = QUEUE_OP_SUCCESS;

    /* The location of the file size in contentRangeValStr. */
    char * pFileSizeStr = NULL;

    /* String to store the Content-Range header value. */
    char * contentRangeValStr = NULL;
    size_t contentRangeValStrLength = 0;

    LogInfo( ( "Getting file object size from host..." ) );

    /* Request bytes 0 to 0. S3 will respond with a Content-Range
     * header that contains the size of the file in it. This header will look
     * like: "Content-Range: bytes 0-0/FILESIZE". The body will have a single
     * byte that we are ignoring. */
    queueOpStatus = requestS3ObjectRange( requestInfo,
                                          requestQueue,
                                          0,
                                          0 );

    if( queueOpStatus != QUEUE_OP_SUCCESS )
    {
        returnStatus = false;
    }

    if( returnStatus == true )
    {
        do
        {
            queueOpStatus = retrieveHTTPResponse( responseQueue, &responseItem );
        } while( queueOpStatus == QUEUE_OP_WOULD_BLOCK );

        if( queueOpStatus == QUEUE_OP_FAILURE )
        {
            returnStatus = false;
        }
        else if( responseItem.response.statusCode != HTTP_STATUS_CODE_PARTIAL_CONTENT )
        {
            LogError( ( "Received response with unexpected status code: %d.", responseItem.response.statusCode ) );
            returnStatus = false;
        }
    }

    if( returnStatus == true )
    {
        httpStatus = HTTPClient_ReadHeader( &responseItem.response,
                                            ( char * ) HTTP_CONTENT_RANGE_HEADER_FIELD,
                                            ( size_t ) HTTP_CONTENT_RANGE_HEADER_FIELD_LENGTH,
                                            ( const char ** ) &contentRangeValStr,
                                            &contentRangeValStrLength );

        if( httpStatus != HTTPSuccess )
        {
            LogError( ( "Failed to read Content-Range header from HTTP response: Error=%s.",
                        HTTPClient_strerror( httpStatus ) ) );
            returnStatus = false;
        }
    }

    /* Parse the Content-Range header value to get the file size. */
    if( returnStatus == true )
    {
        pFileSizeStr = strstr( contentRangeValStr, "/" );

        if( pFileSizeStr == NULL )
        {
            LogError( ( "'/' not present in Content-Range header value: %s.",
                        contentRangeValStr ) );
            returnStatus = false;
        }
    }

    if( returnStatus == true )
    {
        pFileSizeStr += sizeof( char );
        *pFileSize = ( size_t ) strtoul( pFileSizeStr, NULL, 10 );

        if( ( *pFileSize == 0 ) || ( *pFileSize == UINT32_MAX ) )
        {
            LogError( ( "Error using strtoul to get the file size from %s: fileSize=%d.",
                        pFileSizeStr, ( int32_t ) *pFileSize ) );
            returnStatus = false;
        }
    }

    if( returnStatus == true )
    {
        LogInfo( ( "The file is %d bytes long.", ( int32_t ) *pFileSize ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static pid_t startHTTPThread( const TransportInterface_t * pTransportInterface )
{
    /* Return value of fork. */
    pid_t forkPID = -1;

    /* Fork to create the HTTP thread. */
    forkPID = fork();

    if( forkPID == -1 )
    {
        LogError( ( "Error forking." ) );
    }
    else if( forkPID == 0 )
    {
        /* HTTP thread. */

        /* Queues for HTTP requests and responses. */
        mqd_t requestQueue = -1;
        mqd_t responseQueue = -1;

        /* Open queues for read/write. */
        requestQueue = mq_open( REQUEST_QUEUE, O_RDONLY );
        responseQueue = mq_open( RESPONSE_QUEUE, O_WRONLY );

        /* Initialize response struct. */
        responseItem.response.pBuffer = responseItem.responseBuffer;
        responseItem.response.bufferLen = sizeof( responseItem.responseBuffer );

        for( ; ; )
        {
            HTTPStatus_t httpStatus = HTTPSuccess;

            /* Return value of mq_receive. */
            int mqread = 0;
            /* Return value of mq_send. */
            int mqerror = 0;

            /* Read request from queue. */
            mqread = mq_receive( requestQueue,
                                 ( char * ) &requestItem,
                                 sizeof( RequestItem_t ),
                                 NULL );

            if( mqread == -1 )
            {
                LogError( ( "Failed to read from request queue with error %s.",
                            strerror( errno ) ) );
            }

            if( mqread != sizeof( RequestItem_t ) )
            {
                LogError( ( "Response from request queue has incorrect size." ) );
            }

            LogInfo( ( "HTTP thread retrieved request." ) );
            LogInfo( ( "Request Headers:\n%.*s",
                       ( int32_t ) requestItem.requestHeaders.headersLen,
                       ( char * ) requestItem.requestHeaders.pBuffer ) );

            httpStatus = HTTPClient_Send( pTransportInterface,
                                          &requestItem.requestHeaders,
                                          NULL,
                                          0,
                                          &responseItem.response,
                                          0 );

            if( httpStatus != HTTPSuccess )
            {
                LogError( ( "Failed to send HTTP request: Error=%s.",
                            HTTPClient_strerror( httpStatus ) ) );
            }
            else
            {
                LogInfo( ( "HTTP thread received HTTP response" ) );
                /* Write response to queue. */
                mqerror = mq_send( responseQueue,
                                   ( char * ) &responseItem,
                                   sizeof( ResponseItem_t ),
                                   0 );

                if( mqerror != 0 )
                {
                    LogError( ( "Failed to write to response queue with error %s.",
                                strerror( errno ) ) );
                }
            }
        }
    }

    return forkPID;
}

/*-----------------------------------------------------------*/

void tearDown( pid_t httpThread,
               mqd_t requestQueue,
               mqd_t responseQueue )
{
    /* End http task. */
    if( httpThread != -1 )
    {
        kill( httpThread, SIGTERM );
    }

    /* Close and then delete the queues. */
    if( requestQueue != -1 )
    {
        if( mq_close( requestQueue ) == -1 )
        {
            LogError( ( "Failed to close request queue with error %s.",
                        strerror( errno ) ) );
        }

        if( mq_unlink( REQUEST_QUEUE ) == -1 )
        {
            LogError( ( "Failed to delete request queue with error %s.",
                        strerror( errno ) ) );
        }
    }

    if( responseQueue != -1 )
    {
        if( mq_close( responseQueue ) == -1 )
        {
            LogError( ( "Failed to close response queue with error %s.",
                        strerror( errno ) ) );
        }

        if( mq_unlink( RESPONSE_QUEUE ) == -1 )
        {
            LogError( ( "Failed to delete response queue with error %s.",
                        strerror( errno ) ) );
        }
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Entry point of demo.
 *
 * This example resolves a domain, establishes a TCP connection, validates the
 * server's certificate using the root CA certificate defined in the config
 * header, then finally performs a TLS handshake with the HTTP server so that
 * all communication is encrypted. After which, an HTTP thread is started which
 * uses HTTP Client library API to send requests it reads from the request
 * queue, and writes the responses to the response queue. The main thread sends
 * requests on the request queue, which are used to download
 * the S3 file by sending multiple range requests. While it is doing this, the
 * main thread also reads responses from the response queue and prints them
 * until the entire file is received. If any request fails, an error
 * code is returned.
 *
 * @note This example is multi-threaded and uses statically allocated memory.
 *
 * @note This demo requires user-generated pre-signed URLs to be pasted into
 * demo_config.h. Please use the provided script "presigned_urls_gen.py"
 * (located in located in demos/http/common/src) to generate these URLs. For
 * detailed instructions, see the accompanied README.md.
 *
 * @note If your file requires more than 99 range requests to S3 (depending on
 * the size of the file and the length specified in RANGE_REQUEST_LENGTH), your
 * connection may be dropped by S3. In this case, either increase the buffer
 * size and range request length (if feasible), to reduce the number of requests
 * required, or re-establish the connection with S3 after receiving a
 * "Connection: close" response header.
 */
int main( int argc,
          char ** argv )
{
    /* Status to the host OS indicating a successful demo or not. */
    int32_t returnStatus = EXIT_SUCCESS;

    /* HTTPS Client library return status. */
    HTTPStatus_t httpStatus = HTTPSuccess;

    /* The location of the path within the pre-signed URL. */
    const char * pPath = NULL;

    /* The length of the path within the pre-signed URL. This variable is
     * defined in order to store the length returned from parsing the URL,
     * but it is unused. The path used for the requests in this demo needs
     * all the query information following the location of the object, to
     * the end of the S3 presigned URL. */
    size_t pathLen = 0;
    /* The length of the Request-URI within string S3_PRESIGNED_GET_URL */
    size_t requestUriLen = 0;

    /* The transport layer interface used by the HTTP Client library. */
    TransportInterface_t transportInterface = { 0 };
    /* The network context for the transport layer interface. */
    NetworkContext_t networkContext = { 0 };
    OpensslParams_t opensslParams = { 0 };

    /* Queue for HTTP requests. Requests are written by the main thread,
     * and serviced by the HTTP thread. */
    mqd_t requestQueue = -1;

    /* Queue for HTTP responses. Responses are written by the HTTP thread,
     * and read by the main thread. */
    mqd_t responseQueue = -1;

    /* PID of HTTP thread. */
    pid_t httpThread = -1;
    int demoRunCount = 0;

    ( void ) argc;
    ( void ) argv;

    /* Set the pParams member of the network context with desired transport. */
    networkContext.pParams = &opensslParams;

    LogInfo( ( "HTTP Client multi-threaded S3 download demo using pre-signed URL:\n%s", S3_PRESIGNED_GET_URL ) );

    /**************************** Parse Signed URL. ******************************/

    /* Retrieve the path location from S3_PRESIGNED_GET_URL. This
     * function returns the length of the path without the query into
     * pathLen. */
    httpStatus = getUrlPath( S3_PRESIGNED_GET_URL,
                             S3_PRESIGNED_GET_URL_LENGTH,
                             &pPath,
                             &pathLen );

    /* The path used for the requests in this demo needs
     * all the query information following the location of the object, to
     * the end of the S3 presigned URL. */
    requestUriLen = strlen( pPath );

    if( httpStatus != HTTPSuccess )
    {
        returnStatus = EXIT_FAILURE;
        LogError( ( "Getting the URL path from pre-signed URL failed. httpStatus=%d.",
                    httpStatus ) );
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Retrieve the address location and length from the S3_PRESIGNED_GET_URL. */
        httpStatus = getUrlAddress( S3_PRESIGNED_GET_URL,
                                    S3_PRESIGNED_GET_URL_LENGTH,
                                    &pHost,
                                    &hostLen );

        if( httpStatus != HTTPSuccess )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "Getting the URL address from pre-signed URL failed. httpStatus=%d.",
                        httpStatus ) );
        }
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        do
        {
            /**************************** Connect. ******************************/

            /* Establish a TLS connection on top of TCP connection using OpenSSL. */

            /* Attempt to connect to the HTTP server. If connection fails, retry
             * after a timeout. The timeout value will be exponentially
             * increased till the maximum attempts are reached or maximum
             * timeout value is reached. The function returns EXIT_FAILURE if
             * the TCP connection cannot be established to broker after
             * the configured number of attempts. */
            returnStatus = connectToServerWithBackoffRetries( connectToServer,
                                                              &networkContext );

            /* Define the transport interface. */
            if( returnStatus == EXIT_SUCCESS )
            {
                transportInterface.recv = Openssl_Recv;
                transportInterface.send = Openssl_Send;
                transportInterface.pNetworkContext = &networkContext;
            }

            /******************** Start queues and HTTP task. *******************/

            /* Start request and response queues. */
            if( returnStatus == EXIT_SUCCESS )
            {
                /* Settings for constructing queues. */
                struct mq_attr queueSettings;

                queueSettings.mq_maxmsg = QUEUE_SIZE;
                queueSettings.mq_msgsize = sizeof( RequestItem_t );

                requestQueue = mq_open( REQUEST_QUEUE,

                                        /* These options create a queue if it does
                                         * not already exist, and then opens it in
                                         * non-blocking mode. It is opened as
                                         * write-only as the main thread only writes
                                         * HTTP requests to it. */
                                        O_CREAT | O_NONBLOCK | O_WRONLY,
                                        QUEUE_PERMISSIONS,
                                        &queueSettings );

                if( requestQueue == -1 )
                {
                    LogError( ( "Failed to open request queue with error %s.",
                                strerror( errno ) ) );
                    returnStatus = EXIT_FAILURE;
                }

                queueSettings.mq_msgsize = sizeof( ResponseItem_t );

                responseQueue = mq_open( RESPONSE_QUEUE,

                                         /* These options create a queue if it does
                                          * not already exist, and then opens it in
                                          * non-blocking mode. It is opened as
                                          * read-only as the main thread only reads
                                          * HTTP responses from it. */
                                         O_CREAT | O_NONBLOCK | O_RDONLY,
                                         QUEUE_PERMISSIONS,
                                         &queueSettings );

                if( responseQueue == -1 )
                {
                    LogError( ( "Failed to open response queue with error %s.",
                                strerror( errno ) ) );
                    returnStatus = EXIT_FAILURE;
                }
            }

            /* Start the HTTP task which services requests in requestQueue. */

            if( returnStatus == EXIT_SUCCESS )
            {
                httpThread = startHTTPThread( &transportInterface );

                if( httpThread == -1 )
                {
                    returnStatus = EXIT_SUCCESS;
                }
            }

            /******************** Download S3 Object File. **********************/

            if( returnStatus == EXIT_SUCCESS )
            {
                bool result = false;
                result = downloadS3ObjectFile( pHost,
                                               hostLen,
                                               pPath,
                                               requestUriLen,
                                               requestQueue,
                                               responseQueue );

                if( result == false )
                {
                    returnStatus = EXIT_FAILURE;
                }
            }

            /************************** Disconnect. *****************************/

            /* End TLS session, then close TCP connection. */
            ( void ) Openssl_Disconnect( &networkContext );

            /******************** Clean up queues and HTTP task. ****************/

            tearDown( httpThread, requestQueue, responseQueue );

            /******************* Retry in case of failure. **********************/

            /* Increment the demo run count. */
            demoRunCount++;

            if( returnStatus == EXIT_SUCCESS )
            {
                LogInfo( ( "Demo iteration %d is successful.", demoRunCount ) );
            }
            /* Attempt to retry a failed iteration of demo for up to #HTTP_MAX_DEMO_LOOP_COUNT times. */
            else if( demoRunCount < HTTP_MAX_DEMO_LOOP_COUNT )
            {
                LogWarn( ( "Demo iteration %d failed. Retrying...", demoRunCount ) );
                sleep( DELAY_BETWEEN_DEMO_RETRY_ITERATIONS_S );
            }
            /* Failed all #HTTP_MAX_DEMO_LOOP_COUNT demo iterations. */
            else
            {
                LogError( ( "All %d demo iterations failed.", HTTP_MAX_DEMO_LOOP_COUNT ) );
                break;
            }
        } while( returnStatus != EXIT_SUCCESS );
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Log a message indicating an iteration completed successfully. */
        LogInfo( ( "Demo completed successfully." ) );
    }

    return returnStatus;
}

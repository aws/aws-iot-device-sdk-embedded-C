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
#include <poll.h>
#include <unistd.h>
#include <arpa/inet.h>

#include <sys/socket.h>
#include <sys/types.h>

#include <openssl/ssl.h>
#include <openssl/bio.h>

/* HTTP API header. */
#include "http_client.h"

/* Demo Config header. */
#include "demo_config.h"

/**
 * @brief Host for S3 GET Object access.
 */
#define S3_PRESIGNED_HOST                 "Please update the host for the demo"

/**
 * @brief The length of the host for S3 GET Object access.
 */
#define S3_PRESIGNED_HOST_LENGTH          ( sizeof( S3_PRESIGNED_HOST ) - 1 )

/**
 * @brief Presigned URL path for S3 GET Object access.
 */
#define S3_PRESIGNED_GET_PATH             "Please update the path for the demo"

/**
 * @brief The length of the presigned URL path for S3 GET Object access.
 */
#define S3_PRESIGNED_GET_PATH_LENGTH      ( sizeof( S3_PRESIGNED_GET_PATH ) - 1 )

/**
 * @brief Port of [resigned URL for S3 GET Object access.
 *
 * In general, port 443 is for HTTPS connections.
 */
#define S3_PRESIGNED_PORT                 443

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS    ( 5000 )

/**
 * @brief The length in bytes of the user buffer.
 */
#define USER_BUFFER_LENGTH                ( 1024 )

/**
 * @brief Length of an IPv6 address when converted to hex digits.
 */
#define IPV6_LENGTH                       ( 40 )

/**
 * @brief A string to store the resolved IP address from the host name.
 */
static char resolvedIpAddr[ IPV6_LENGTH ] = { 0 };

/**
 * @brief A buffer used to store request headers and reused after sending
 * the request to store the response headers and body.
 *
 * User can also decide to have two separate buffers for request and response.
 */
static uint8_t userBuffer[ USER_BUFFER_LENGTH ] = { 0 };

/**
 * @brief Definition of the HTTP network context.
 */
struct HTTPNetworkContext
{
    int tcpSocket;
    SSL * pSslContext;
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
 * @brief Set up a TLS connection over an existing TCP connection.
 *
 * @param[in] tcpSocket Existing TCP connection.
 * @param[out] pSslContext Pointer to SSL connection context.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on success.
 */
static int tlsSetup( int tcpSocket,
                     SSL ** pSslContext );

/**
 * @brief The transport send function that defines the transport interface.
 *
 * This is passed to the #HTTPTransportInterface.send function and used to
 * send data over the network.
 *
 * @param[in] pContext User defined context (TCP socket for this demo).
 * @param[in] pBuffer Buffer containing the bytes to send over the network stack.
 * @param[in] bytesToSend Number of bytes to write to the network.
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
 * This is passed to the #HTTPTransportInterface.recv function and used to
 * receive data over the network.
 *
 * @return Number of bytes received; negative value on error.
 */
static int32_t transportRecv( HTTPNetworkContext_t * pContext,
                              void * pBuffer,
                              size_t bytesToRecv );

/**
 * @brief Send an HTTP request based on a specified method and path.
 *
 * @param[in] pTransportInterface The transport interface for making network calls.
 * @param[in] pHost The host name of the server.
 * @param[in] pMethod The HTTP request method.
 * @param[in] pPath The Request-URI to the objects of interest.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on success.
 */
static int downloadS3ObjectFile( HTTPTransportInterface_t * pTransportInterface,
                                 const char * pHost,
                                 const char * pMethod,
                                 const char * pPath );

/**
 * @brief Retrieve the size of the S3 object that is specified in pPath.
 *
 * @param[out] pFileSize - The size of the S3 object.
 * @param[in] pTransportInterface The transport interface for making network calls.
 * @param[in] pHost The host name of the server.
 * @param[in] pMethod The HTTP request method.
 * @param[in] pPath The Request-URI to the objects of interest.
 */
static HTTPStatus_t getS3ObjectFileSize( size_t * pFileSize,
                                         HTTPTransportInterface_t * pTransportInterface,
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
        LogInfo( ( "Performing DNS lookup on %.*s.",
                   ( int32_t ) S3_PRESIGNED_HOST_LENGTH,
                   S3_PRESIGNED_HOST ) );

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

            LogInfo( ( "Attempting to connect to resolved IP address: %s.",
                       resolvedIpAddr ) );

            returnStatus = connect( *pTcpSocket, pServerInfo, serverInfoLength );

            if( returnStatus == -1 )
            {
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

static int tlsSetup( int tcpSocket,
                     SSL ** pSslContext )
{
    int sslStatus = 0, bytesWritten = 0;
    BIO * pRootCaBio = NULL;
    X509 * pRootCa = NULL;

    assert( tcpSocket >= 0 );

    /* Setup for creating a TLS client. */
    SSL_CTX * pSslSetup = SSL_CTX_new( TLS_client_method() );

    if( pSslSetup != NULL )
    {
        /* Set auto retry mode for the blocking calls to SSL_read and SSL_write.
         * The mask returned by SSL_CTX_set_mode does not need to be checked. */
        ( void ) SSL_CTX_set_mode( pSslSetup, SSL_MODE_AUTO_RETRY );

        pRootCaBio = BIO_new( BIO_s_mem() );
        /* Add the root server CA, which is defined in the config header file. */
        bytesWritten = BIO_write( pRootCaBio, SERVER_CERTIFICATE, SERVER_CERTIFICATE_LENGTH );
    }

    if( bytesWritten == SERVER_CERTIFICATE_LENGTH )
    {
        pRootCa = PEM_read_bio_X509( pRootCaBio, NULL, NULL, NULL );

        if( pRootCa != NULL )
        {
            sslStatus = X509_STORE_add_cert( SSL_CTX_get_cert_store( pSslSetup ),
                                             pRootCa );
        }
        else
        {
            LogError( ( "Failed to parse the provided server certificate:\n%s\n"
                        "Please validate the certificate.",
                        SERVER_CERTIFICATE ) );
        }
    }
    else
    {
        LogError( ( "Failed to write server certificate to BIO: "
                    "bytesWritten=%d", bytesWritten ) );
    }

    /* Set up the TLS connection. */
    if( sslStatus == 1 )
    {
        /* Create a new SSL context. */
        *pSslContext = SSL_new( pSslSetup );

        if( *pSslContext != NULL )
        {
            /* Enable SSL peer verification. */
            SSL_set_verify( *pSslContext, SSL_VERIFY_PEER, NULL );

            sslStatus = SSL_set_fd( *pSslContext, tcpSocket );
        }
        else
        {
            LogError( ( "Failed to create a new SSL context." ) );
            sslStatus = 0;
        }

        /* Perform the TLS handshake. */
        if( sslStatus == 1 )
        {
            sslStatus = SSL_connect( *pSslContext );
        }
        else
        {
            LogError( ( "Failed to set the socket fd to SSL context." ) );
        }

        if( sslStatus == 1 )
        {
            if( SSL_get_verify_result( *pSslContext ) != X509_V_OK )
            {
                sslStatus = 0;
            }
        }
        else
        {
            LogError( ( "Failed to perform TLS handshake." ) );
        }

        /* Clean up on error. */
        if( sslStatus == 0 )
        {
            SSL_free( *pSslContext );
            *pSslContext = NULL;
        }
    }
    else
    {
        LogError( ( "Failed to add certificate to store." ) );
    }

    if( pRootCaBio != NULL )
    {
        BIO_free( pRootCaBio );
    }

    if( pRootCa != NULL )
    {
        X509_free( pRootCa );
    }

    if( pSslSetup != NULL )
    {
        SSL_CTX_free( pSslSetup );
    }

    /* Log failure or success and return the correct exit status. */
    if( sslStatus == 0 )
    {
        LogError( ( "Failed to establish a TLS connection to %.*s.",
                    ( int32_t ) S3_PRESIGNED_HOST_LENGTH,
                    S3_PRESIGNED_HOST ) );
        return EXIT_FAILURE;
    }
    else
    {
        LogInfo( ( "Established a TLS connection to %.*s.\n\n",
                   ( int32_t ) S3_PRESIGNED_HOST_LENGTH,
                   S3_PRESIGNED_HOST ) );
        return EXIT_SUCCESS;
    }
}

/*-----------------------------------------------------------*/

static int32_t transportSend( HTTPNetworkContext_t * pNetworkContext,
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
    fileDescriptor.fd = SSL_get_fd( pNetworkContext->pSslContext );

    /* Poll the file descriptor to check if SSL_Write can be done now. */
    pollStatus = poll( &fileDescriptor, 1, TRANSPORT_SEND_RECV_TIMEOUT_MS );

    if( pollStatus > 0 )
    {
        bytesSent = ( int32_t ) SSL_write( pNetworkContext->pSslContext, pBuffer, bytesToSend );
    }
    else if( pollStatus == 0 )
    {
        LogDebug( ( "Timed out while polling SSL socket for write buffer availability." ) );
    }
    else
    {
        LogError( ( "Polling of the SSL socket for write buffer availability failed"
                    " with status %d.",
                    pollStatus ) );
        bytesSent = -1;
    }

    return bytesSent;
}

/*-----------------------------------------------------------*/

static int32_t transportRecv( HTTPNetworkContext_t * pNetworkContext,
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
    fileDescriptor.fd = SSL_get_fd( pNetworkContext->pSslContext );

    /* Check if there are any pending data available for read. */
    bytesAvailableToRead = SSL_pending( pNetworkContext->pSslContext );

    /* Poll only if there is no data available yet to read. */
    if( bytesAvailableToRead <= 0 )
    {
        pollStatus = poll( &fileDescriptor, 1, TRANSPORT_SEND_RECV_TIMEOUT_MS );
    }

    /* SSL read of data. */
    if( ( pollStatus > 0 ) || ( bytesAvailableToRead > 0 ) )
    {
        bytesReceived = ( int32_t ) SSL_read( pNetworkContext->pSslContext, pBuffer, bytesToRecv );
    }
    /* Poll timed out. */
    else if( pollStatus == 0 )
    {
        LogInfo( ( "Poll timed out and there is no data to read from the buffer." ) );
    }
    else
    {
        LogError( ( "Poll returned with status = %d.", pollStatus ) );
        bytesReceived = -1;
    }

    return bytesReceived;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t getS3ObjectFileSize( size_t * pFileSize,
                                         HTTPTransportInterface_t * pTransportInterface,
                                         const char * pHost,
                                         const char * pMethod,
                                         const char * pPath )
{
    HTTPStatus_t httpStatus = HTTP_SUCCESS;
    HTTPRequestHeaders_t requestHeaders = { 0 };
    HTTPRequestInfo_t requestInfo = { 0 };
    HTTPResponse_t response = { 0 };
    /* The location of the file size in the contentRangeValStr. */
    char * pFileSizeStr = NULL;

    /* String to store the Content-Range header value. */
    char * contentRangeValStr = NULL;
    size_t contentRangeValStrLength = 0;

    assert( pTransportInterface != NULL );
    assert( pMethod != NULL );

    /* Initialize the request object. */
    requestInfo.pHost = pHost;
    requestInfo.hostLen = strlen( pHost );
    requestInfo.method = pMethod;
    requestInfo.methodLen = strlen( pMethod );
    requestInfo.pPath = pPath;
    requestInfo.pathLen = strlen( pPath );

    /* Set "Connection" HTTP header to "keep-alive" so that multiple requests
     * can be sent over the same established TCP connection. We are doing this
     * because we are downloading the file in parts. */
    requestInfo.flags = HTTP_REQUEST_KEEP_ALIVE_FLAG;

    /* Set the buffer used for storing request headers. */
    requestHeaders.pBuffer = userBuffer;
    requestHeaders.bufferLen = USER_BUFFER_LENGTH;

    /* Initialize the response object. The same buffer used for storing
     * request headers is reused here. */
    response.pBuffer = userBuffer;
    response.bufferLen = USER_BUFFER_LENGTH;

    httpStatus = HTTPClient_InitializeRequestHeaders( &requestHeaders,
                                                      &requestInfo );

    if( httpStatus == HTTP_SUCCESS )
    {
        /* Add the header to get bytes=0-0. S3 will respond with a Content-Range
         * header that contains the size of the file in it. This header will look
         * like: "Content-Range: bytes 0-0/FILESIZE". The body will have a single
         * byte that we are ignoring. */
        httpStatus = HTTPClient_AddRangeHeader( &requestHeaders, 0, 0 );
    }

    if( httpStatus == HTTP_SUCCESS )
    {
        /* Send the request and receive the response. */
        httpStatus = HTTPClient_Send( pTransportInterface,
                                      &requestHeaders,
                                      NULL,
                                      0,
                                      &response,
                                      0 );
        LogInfo( ( "Received HTTP response from %s%s...",
                   S3_PRESIGNED_HOST, pPath ) );
        LogInfo( ( "Response Headers:\n%.*s",
                   ( int32_t ) response.headersLen,
                   response.pHeaders ) );
        LogInfo( ( "Response Status:\n%u",
                   response.statusCode ) );
        LogInfo( ( "Response Body:\n%.*s\n",
                   ( int32_t ) response.bodyLen,
                   response.pBody ) );
    }

    if( httpStatus == HTTP_SUCCESS )
    {
        httpStatus = HTTPClient_ReadHeader( &response,
                                            ( const uint8_t * ) HTTP_CONTENT_RANGE_HEADER_FIELD,
                                            ( size_t ) HTTP_CONTENT_RANGE_HEADER_FIELD_LENGTH,
                                            ( const uint8_t ** ) &contentRangeValStr,
                                            &contentRangeValStrLength );
    }

    if( httpStatus == HTTP_SUCCESS )
    {
        /* Parse the Content-Range header value to get the file size. */
        pFileSizeStr = strstr( contentRangeValStr, "/" );

        if( pFileSizeStr == NULL )
        {
            LogError( ( "'/' not present in Content-Range header value: %s.",
                        contentRangeValStr ) );
        }

        pFileSizeStr += sizeof( char );
        *pFileSize = ( size_t ) strtoul( pFileSizeStr, NULL, 10 );

        if( ( *pFileSize == 0 ) || ( *pFileSize == UINT32_MAX ) )
        {
            LogError( ( "Error using strtoul to get the file size from %s. Error returned: %d",
                        pFileSizeStr, *pFileSize ) );
            httpStatus = HTTP_INVALID_PARAMETER;
        }
    }

    return httpStatus;
}

static int downloadS3ObjectFile( HTTPTransportInterface_t * pTransportInterface,
                                 const char * pHost,
                                 const char * pMethod,
                                 const char * pPath )
{
    HTTPStatus_t httpStatus = HTTP_SUCCESS;
    HTTPRequestHeaders_t requestHeaders = { 0 };
    HTTPRequestInfo_t requestInfo = { 0 };
    HTTPResponse_t response = { 0 };
    /* The size of the file we are trying to download in S3. */
    size_t fileSize = 0;
    /* The number of bytes we want to request with in each range of the file bytes. */
    size_t numReqBytes = 0;
    /* curByte indicates which starting byte we want to download next. */
    size_t curByte = 0;

    assert( pTransportInterface != NULL );
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

    /* Initialize the response object. The same buffer used for storing
     * request headers is reused here. */
    response.pBuffer = userBuffer;
    response.bufferLen = USER_BUFFER_LENGTH;

    /* Verify the file exists by retrieving the file size. */
    httpStatus = getS3ObjectFileSize( &fileSize,
                                      pTransportInterface,
                                      pHost,
                                      pMethod,
                                      pPath );

    if( fileSize < USER_BUFFER_LENGTH )
    {
        numReqBytes = fileSize;
    }

    /* Here we iterate sending byte range requests until the full file has been
     * downloaded. We keep track of the next byte to download with curByte.
     * When this reaches the fileSize we stop downloading. */
    while( curByte < fileSize && httpStatus == HTTP_SUCCESS )
    {
        if( httpStatus == HTTP_SUCCESS )
        {
            httpStatus = HTTPClient_InitializeRequestHeaders( &requestHeaders,
                                                              &requestInfo );
        }

        if( httpStatus == HTTP_SUCCESS )
        {
            httpStatus = HTTPClient_AddRangeHeader( &requestHeaders,
                                                    curByte,
                                                    curByte + numReqBytes - 1 );
        }

        if( httpStatus == HTTP_SUCCESS )
        {
            LogInfo( ( "Downloading S3 Object from %s%s...: %d out of %d bytes",
                       pMethod, S3_PRESIGNED_HOST,
                       curByte, fileSize ) );
            LogInfo( ( "Request Headers:\n%.*s",
                       ( int32_t ) requestHeaders.headersLen,
                       ( char * ) requestHeaders.pBuffer ) );
            httpStatus = HTTPClient_Send( pTransportInterface,
                                          &requestHeaders,
                                          NULL,
                                          0,
                                          &response,
                                          0 );
        }

        if( httpStatus == HTTP_SUCCESS )
        {
            LogInfo( ( "Received HTTP response from %s%s...",
                       S3_PRESIGNED_HOST, pPath ) );
            LogInfo( ( "Response Headers:\n%.*s",
                       ( int32_t ) response.headersLen,
                       response.pHeaders ) );
            LogInfo( ( "Response Status:\n%u",
                       response.statusCode ) );
            LogInfo( ( "Response Body:\n%.*s\n",
                       ( int32_t ) response.bodyLen,
                       response.pBody ) );

            /* We increment by the contentLength because the server may not have
             * sent us the range we request. */
            curByte += response.contentLength;

            if( ( fileSize - curByte ) < numReqBytes )
            {
                numReqBytes = fileSize - curByte;
            }
        }
        else
        {
            LogError( ( "Sending HTTP %s request to %s%s failed with status = %u.",
                        pMethod, S3_PRESIGNED_HOST, pPath, httpStatus ) );
        }
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
    HTTPNetworkContext_t networkContext = { 0 };
    HTTPTransportInterface_t transportInterface = { 0 };

    /**************************** Connect. ******************************/

    /* Establish TCP connection. */
    returnStatus = connectToServer( S3_PRESIGNED_HOST, S3_PRESIGNED_PORT, &networkContext.tcpSocket );

    /* Establish TLS connection on top of TCP connection. */
    if( returnStatus == EXIT_SUCCESS )
    {
        LogInfo( ( "Performing TLS handshake on top of the TCP connection." ) );
        returnStatus = tlsSetup( networkContext.tcpSocket,
                                 &networkContext.pSslContext );
    }

    /* Define the transport interface. */
    if( returnStatus == EXIT_SUCCESS )
    {
        transportInterface.recv = transportRecv;
        transportInterface.send = transportSend;
        transportInterface.pContext = &networkContext;
    }

    /******************** Download S3 Object File. **********************/

    /* The client is now connected to the server. This example will download the
     * S3 file by sending multiple GET requests, filling up the response buffer
     * each time until all parts are downloaded. If any request fails, an error
     * code is returned. */

    if( returnStatus == EXIT_SUCCESS )
    {
        returnStatus = downloadS3ObjectFile( &transportInterface,
                                             S3_PRESIGNED_HOST,
                                             HTTP_METHOD_GET,
                                             S3_PRESIGNED_GET_PATH );
    }

    /************************** Disconnect. *****************************/

    /* Close TLS session if established. */
    if( networkContext.pSslContext != NULL )
    {
        /* SSL shutdown should be called twice: once to send "close notify" and
         * once more to receive the peer's "close notify". */
        if( SSL_shutdown( networkContext.pSslContext ) == 0 )
        {
            ( void ) SSL_shutdown( networkContext.pSslContext );
        }

        SSL_free( networkContext.pSslContext );
    }

    if( networkContext.tcpSocket != -1 )
    {
        shutdown( networkContext.tcpSocket, SHUT_RDWR );
        close( networkContext.tcpSocket );
    }

    return returnStatus;
}

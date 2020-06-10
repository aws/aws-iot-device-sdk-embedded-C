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

/* Check that hostname of the server is defined. */
#ifndef SERVER_HOST
    #error "Please define a SERVER_HOST."
#endif

/* Check that TLS port of the server is defined. */
#ifndef SERVER_PORT
    #error "Please define a SERVER_PORT."
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

/* Check that transport timeout for transport send and receive is defined. */
#ifndef TRANSPORT_SEND_RECV_TIMEOUT_MS
    #define TRANSPORT_SEND_RECV_TIMEOUT_MS    ( 1000 )
#endif

/* Check that size of the user buffer is defined. */
#ifndef USER_BUFFER_LENGTH
    #define USER_BUFFER_LENGTH    ( 1024 )
#endif

/* Check that a request body to send for PUT and POST requests is defined. */
#ifndef REQUEST_BODY
    #error "Please define a REQUEST_BODY."
#endif

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
 * @brief Definition of the HTTP network context.
 *
 * @note For this TLS demo, the socket descriptor and SSL context is used.
 */
struct HTTPNetworkContext
{
    int tcpSocket;
    SSL * pSslContext;
};

/**
 * @brief Structure based on the definition of the HTTP network context.
 */
static HTTPNetworkContext_t networkContext;

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
 * This is passed as the #HTTPTransportInterface.send function and used to
 * send data over the network.
 *
 * @param[in] pContext User defined context (TCP socket for this demo).
 * @param[in] pBuffer Buffer containing the bytes to send over the network stack.
 * @param[in] bytesToSend Number of bytes to write to the network.
 *
 * @return Number of bytes sent if successful; otherwise negative value on error.
 */
static int32_t transportSend( HTTPNetworkContext_t * pContext,
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
 * This is passed to the #HTTPTransportInterface.recv function and used to
 * receive data over the network.
 *
 * @return Number of bytes received if successful; otherwise negative value on error.
 */
static int32_t transportRecv( HTTPNetworkContext_t * pContext,
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

static int tlsSetup( int tcpSocket,
                     SSL ** pSslContext )
{
    int sslStatus = 0;
    char * cwd = getcwd( NULL, 0 );
    FILE * pRootCaFile = NULL;
    X509 * pRootCa = NULL;

    /* Setup for creating a TLS client. */
    SSL_CTX * pSslSetup = SSL_CTX_new( TLS_client_method() );

    if( pSslSetup != NULL )
    {
        /* Set auto retry mode for the blocking calls to SSL_read and SSL_write.
         * The mask returned by SSL_CTX_set_mode does not need to be checked. */
        ( void ) SSL_CTX_set_mode( pSslSetup, SSL_MODE_AUTO_RETRY );

        /* OpenSSL does not provide a single function for reading and loading certificates
         * from files into stores, so the file API must be called. */
        pRootCaFile = fopen( SERVER_CERT_PATH, "r" );

        /* Check if an absolute directory is being used. */
        if( ( SERVER_CERT_PATH[ 0 ] == '/' ) || ( SERVER_CERT_PATH[ 0 ] == '\\' ) )
        {
            LogInfo( ( "Attempting to open root CA certificate: Path=%.*s.",
                       ( int32_t ) SERVER_CERT_PATH_LENGTH,
                       SERVER_CERT_PATH ) );
        }
        else
        {
            LogInfo( ( "Attempting to open root CA certificate: Path=%s/%.*s.",
                       cwd,
                       ( int32_t ) SERVER_CERT_PATH_LENGTH,
                       SERVER_CERT_PATH ) );
        }

        if( pRootCaFile != NULL )
        {
            pRootCa = PEM_read_X509( pRootCaFile, NULL, NULL, NULL );
        }
        else
        {
            LogError( ( "Unable to find the root CA certificate file: "
                        "SERVER_CERT_PATH=%.*s.",
                        ( int32_t ) SERVER_CERT_PATH_LENGTH,
                        SERVER_CERT_PATH ) );
        }

        if( pRootCa != NULL )
        {
            /* Add the server's root CA to the set of trusted certificates. */
            sslStatus = X509_STORE_add_cert( SSL_CTX_get_cert_store( pSslSetup ),
                                             pRootCa );
        }
        else
        {
            LogError( ( "Failed to parse the root CA certificate from"
                        " file %.*s. Please validate the certificate.",
                        ( int32_t ) SERVER_CERT_PATH_LENGTH,
                        SERVER_CERT_PATH ) );
        }
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

    if( cwd != NULL )
    {
        free( cwd );
    }

    if( pRootCaFile != NULL )
    {
        ( void ) fclose( pRootCaFile );
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
        LogError( ( "Failed to establish a TLS connection: Host=%.*s.",
                    ( int32_t ) SERVER_HOST_LENGTH,
                    SERVER_HOST ) );
        return EXIT_FAILURE;
    }
    else
    {
        LogInfo( ( "Established a TLS connection: Host=%.*s.\n\n",
                   ( int32_t ) SERVER_HOST_LENGTH,
                   SERVER_HOST ) );
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
        LogError( ( "Polling of the SSL socket for write buffer availability failed:"
                    " status=%d",
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

static int sendHttpRequest( const HTTPTransportInterface_t * pTransportInterface,
                            const char * pHost,
                            const char * pMethod,
                            const char * pPath )
{
    /* Return value of this method. */
    int returnStatus = EXIT_SUCCESS;

    /* Configurations of the initial request headers that are passed to
     * #HTTPClient_InitializeRequestHeaders. */
    HTTPRequestInfo_t requestInfo;
    /* Represents a response returned from an HTTP server. */
    HTTPResponse_t response;
    /* Represents header data that will be sent in an HTTP request. */
    HTTPRequestHeaders_t requestHeaders;

    /* Return value of all methods from the HTTP Client library API. */
    HTTPStatus_t httpStatus = HTTP_SUCCESS;

    /* Initialize all HTTP Client library API structs to 0. */
    memset( &requestInfo, 0, sizeof( requestInfo ) );
    memset( &response, 0, sizeof( response ) );
    memset( &requestHeaders, 0, sizeof( requestHeaders ) );

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
        LogDebug( ( "Request Headers:\n%.*s",
                    ( int32_t ) requestHeaders.headersLen,
                    ( char * ) requestHeaders.pBuffer ) );
        LogDebug( ( "Request Body:\n%.*s\n",
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
 * This example resolves a domain, establishes a TCP connection, validates the
 * server's certificate using the root CA certificate defined in the config header,
 * then finally performs a TLS handshake with the HTTP server so that all communication
 * is encrypted. After which, HTTP Client library API is used to send a GET, HEAD,
 * PUT, and POST request in that order. For each request, the HTTP response from the
 * server (or an error code) is logged.
 *
 * @note This example is single-threaded and uses statically allocated memory.
 *
 */
int main( int argc,
          char ** argv )
{
    /* Return value of main. */
    int returnStatus = EXIT_SUCCESS;
    /* The HTTP Client library transport layer interface. */
    HTTPTransportInterface_t transportInterface;

    ( void ) argc;
    ( void ) argv;

    /**************************** Connect. ******************************/

    /* Establish TCP connection. */
    returnStatus = connectToServer( SERVER_HOST, SERVER_PORT, &networkContext.tcpSocket );

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
        memset( &transportInterface, 0, sizeof( transportInterface ) );
        transportInterface.recv = transportRecv;
        transportInterface.send = transportSend;
        transportInterface.pContext = &networkContext;
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
        ( void ) shutdown( networkContext.tcpSocket, SHUT_RDWR );
        ( void ) close( networkContext.tcpSocket );
    }

    return returnStatus;
}

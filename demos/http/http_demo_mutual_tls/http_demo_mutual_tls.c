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

/* OpenSSL includes. */
#include <openssl/ssl.h>
#include <openssl/bio.h>

/* HTTP API header. */
#include "http_client.h"

/* Demo Config header. */
#include "demo_config.h"

/* Check that hostname of the server is defined. */
#ifndef IOT_CORE_ENDPOINT
    #error "Please define a IOT_CORE_ENDPOINT."
#endif

/* Check that TLS port of the server is defined. */
#ifndef IOT_CORE_PORT
    #error "Please define a IOT_CORE_PORT."
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
 * @brief The length of the HTTP server host name.
 */
#define IOT_CORE_ENDPOINT_LENGTH          ( sizeof( IOT_CORE_ENDPOINT ) - 1 )

/**
 * @brief The length of the HTTP POST method.
 */
#define HTTP_METHOD_POST_LENGTH           ( sizeof( HTTP_METHOD_POST ) - 1 )

/**
 * @brief The length of the HTTP POST path.
 */
#define POST_PATH_LENGTH                  ( sizeof( POST_PATH ) - 1 )

/**
 * @brief Length of path to root CA certificate of AWS IoT Core.
 */
#define ROOT_CA_CERT_PATH_LENGTH          ( sizeof( ROOT_CA_CERT_PATH ) - 1 )

/**
 * @brief Length of path to client's certificate.
 */
#define CLIENT_CERT_PATH_LENGTH           ( sizeof( CLIENT_CERT_PATH ) - 1 )

/**
 * @brief Length of path to client's key.
 */
#define CLIENT_PRIVATE_KEY_PATH_LENGTH    ( sizeof( CLIENT_PRIVATE_KEY_PATH ) - 1 )

/**
 * @brief Length of the request body.
 */
#define REQUEST_BODY_LENGTH               ( sizeof( REQUEST_BODY ) - 1 )

/**
 * @brief Length of an IPv6 address when converted to hex digits.
 */
#define IPV6_ADDRESS_STRING_LENGTH        ( 40 )

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
 * @param[out] pTcpSocket The output parameter to return the created socket descriptor.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on success.
 */
static int connectToServer( const char * pServer,
                            size_t serverLen,
                            uint16_t port,
                            int * pTcpSocket );

/**
 * @brief Reads TLS credentials from the filesystem for mutual authentication.
 *
 * Uses OpenSSL to import the root CA certificate, client certificate, and
 * client certificate private key.
 *
 * @param[in] pSslContext Destination for the imported credentials.
 * @param[in] pRootCaPath Path to the root CA certificate.
 * @param[in] rootCaPathLen Length of path to the root CA certificate.
 * @param[in] pClientCertPath Path to the client certificate.
 * @param[in] clientCertPathLen Length of path to the client certificate.
 * @param[in] pClientPrivateKeyPath Path to the client certificate private key.
 * @param[in] clientPrivateKeyPathLen Length of path to the client certificate private key.
 *
 * @return 1 on success; otherwise, failure;
 */
static int readCredentials( SSL_CTX * pSslContext,
                            const char * pRootCaPath,
                            size_t rootCaPathLen,
                            const char * pClientCertPath,
                            size_t clientCertPathLen,
                            const char * pClientPrivateKeyPath,
                            size_t clientPrivateKeyPathLen );

/**
 * @brief Set up a TLS connection over an existing TCP connection.
 *
 * @param[in] tcpSocket Socket descriptor corresponding to the existing TCP connection.
 * @param[out] pSslContext The output parameter to return the created SSL context.
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
 * @param[in] pContext User defined context (TCP socket and SSL context for this demo).
 * @param[in] pBuffer Buffer containing the bytes to send over the network stack.
 * @param[in] bytesToSend Number of bytes to send over the network.
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
 * @param[in] pContext User defined context (TCP socket and SSL context for this demo).
 * @param[out] pBuffer Buffer to read network data into.
 * @param[in] bytesToRead Number of bytes requested from the network.
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
 * @param[in] pMethod The HTTP request method.
 * @param[in] methodLen The length of the HTTP request method.
 * @param[in] pPath The Request-URI to the objects of interest.
 * @param[in] pathLen The length of the Request-URI.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on success.
 */
static int sendHttpRequest( const HTTPTransportInterface_t * pTransportInterface,
                            const char * pMethod,
                            size_t methodLen,
                            const char * pPath,
                            size_t pathLen );

/*-----------------------------------------------------------*/

static int connectToServer( const char * pServer,
                            size_t serverLen,
                            uint16_t port,
                            int * pTcpSocket )
{
    int returnStatus = EXIT_SUCCESS;
    struct addrinfo hints, * pIndex, * pListHead = NULL;
    struct sockaddr * pServerInfo;
    uint16_t netPort = htons( port );
    socklen_t serverInfoLength;
    char resolvedIpAddr[ IPV6_ADDRESS_STRING_LENGTH ];

    /* Initialize string to store the resolved IP address from the host name. */
    ( void ) memset( resolvedIpAddr, 0, IPV6_ADDRESS_STRING_LENGTH );
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
        LogInfo( ( "Performing DNS lookup: Host=%.*s.",
                   ( int32_t ) IOT_CORE_ENDPOINT_LENGTH, IOT_CORE_ENDPOINT ) );

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

            LogInfo( ( "Attempting to connect to server: Host=%.*s, IP address=%s.",
                       ( int32_t ) IOT_CORE_ENDPOINT_LENGTH, IOT_CORE_ENDPOINT, resolvedIpAddr ) );

            returnStatus = connect( *pTcpSocket, pServerInfo, serverInfoLength );

            if( returnStatus == -1 )
            {
                LogError( ( "Failed to connect to server: Host=%.*s, IP address=%s.",
                            ( int32_t ) IOT_CORE_ENDPOINT_LENGTH, IOT_CORE_ENDPOINT, resolvedIpAddr ) );
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
            LogError( ( "Could not connect to any resolved IP address from %.*s.",
                        ( int32_t ) serverLen,
                        pServer ) );
            returnStatus = EXIT_FAILURE;
        }
        else
        {
            LogInfo( ( "Established TCP connection: Server=%.*s.\n",
                       ( int32_t ) serverLen,
                       pServer ) );
            returnStatus = EXIT_SUCCESS;
        }
    }
    else
    {
        LogError( ( "Could not resolve host %.*s.\n",
                    ( int32_t ) serverLen,
                    pServer ) );
        returnStatus = EXIT_FAILURE;
    }

    if( pListHead != NULL )
    {
        freeaddrinfo( pListHead );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int readCredentials( SSL_CTX * pSslContext,
                            const char * pRootCaPath,
                            size_t rootCaPathLen,
                            const char * pClientCertPath,
                            size_t clientCertPathLen,
                            const char * pClientPrivateKeyPath,
                            size_t clientPrivateKeyPathLen )
{
    int sslStatus = 0;
    char * cwd = getcwd( NULL, 0 );
    FILE * pRootCaFile = NULL;
    X509 * pRootCa = NULL;

    assert( pRootCaPath != NULL );
    assert( rootCaPathLen > 0 );
    assert( pClientCertPath != NULL );
    assert( clientCertPathLen > 0 );
    assert( pClientPrivateKeyPath != NULL );
    assert( clientPrivateKeyPathLen > 0 );

    /* OpenSSL does not provide a single function for reading and loading certificates
     * from files into stores, so the file API must be called. Start with the
     * root certificate. */
    if( ( pRootCaPath != NULL ) && ( rootCaPathLen > 0 ) )
    {
        /* Log the absolute directory based on first character of root CA path. */
        if( ( pRootCaPath[ 0 ] == '/' ) || ( pRootCaPath[ 0 ] == '\\' ) )
        {
            LogInfo( ( "Attempting to open root CA certificate: Path=%.*s.",
                       ( int32_t ) rootCaPathLen,
                       pRootCaPath ) );
        }
        else
        {
            LogInfo( ( "Attempting to open root CA certificate: Path=%s/%.*s.",
                       cwd,
                       ( int32_t ) rootCaPathLen,
                       pRootCaPath ) );
        }

        pRootCaFile = fopen( pRootCaPath, "r" );

        if( pRootCaFile == NULL )
        {
            LogError( ( "fopen failed to find the root CA certificate file: "
                        "ROOT_CA_PATH=%.*s.",
                        ( int32_t ) rootCaPathLen,
                        pRootCaPath ) );
            sslStatus = -1;
        }
        else
        {
            /* Read the root CA into an X509 object, then close its file handle. */
            pRootCa = PEM_read_X509( pRootCaFile, NULL, NULL, NULL );

            if( pRootCa == NULL )
            {
                LogError( ( "PEM_read_X509 failed to parse root CA." ) );
                sslStatus = -1;
            }

            if( fclose( pRootCaFile ) != 0 )
            {
                LogWarn( ( "fclose failed to close file %.*s",
                           ( int32_t ) rootCaPathLen,
                           pRootCaPath ) );
            }
        }

        sslStatus = X509_STORE_add_cert( SSL_CTX_get_cert_store( pSslContext ),
                                         pRootCa );

        if( sslStatus != 1 )
        {
            LogError( ( "X509_STORE_add_cert failed to add root CA to certificate store." ) );
        }
        else
        {
            LogInfo( ( "Successfully imported root CA." ) );
        }
    }

    if( ( sslStatus == 1 ) &&
        ( pClientCertPath != NULL ) && ( clientCertPathLen > 0 ) )
    {
        /* Log the absolute directory based on first character of client certificate path. */
        if( ( pClientCertPath[ 0 ] == '/' ) || ( pClientCertPath[ 0 ] == '\\' ) )
        {
            LogInfo( ( "Attempting to open client's certificate: Path=%.*s.",
                       ( int32_t ) rootCaPathLen,
                       pRootCaPath ) );
        }
        else
        {
            LogInfo( ( "Attempting to open client's certificate: Path=%s/%.*s.",
                       cwd,
                       ( int32_t ) rootCaPathLen,
                       pRootCaPath ) );
        }

        sslStatus = SSL_CTX_use_certificate_chain_file( pSslContext,
                                                        pClientCertPath );

        /* Import the client certificate. */
        if( sslStatus != 1 )
        {
            LogError( ( "SSL_CTX_use_certificate_chain_file failed to import "
                        "client certificate at %.*s.",
                        ( int32_t ) clientCertPathLen,
                        pClientCertPath ) );
        }
        else
        {
            LogInfo( ( "Successfully imported client certificate." ) );
        }
    }

    if( ( sslStatus == 1 ) &&
        ( pClientPrivateKeyPath != NULL ) && ( clientPrivateKeyPathLen > 0 ) )
    {
        /* Log the absolute directory based on first character of client certificate path. */
        if( ( pClientPrivateKeyPath[ 0 ] == '/' ) || ( pClientPrivateKeyPath[ 0 ] == '\\' ) )
        {
            LogInfo( ( "Attempting to open client's private key: Path=%.*s.",
                       ( int32_t ) clientPrivateKeyPathLen,
                       pClientPrivateKeyPath ) );
        }
        else
        {
            LogInfo( ( "Attempting to open client's private key: Path=%s/%.*s.",
                       cwd,
                       ( int32_t ) clientPrivateKeyPathLen,
                       pClientPrivateKeyPath ) );
        }

        sslStatus = SSL_CTX_use_PrivateKey_file( pSslContext,
                                                 pClientPrivateKeyPath,
                                                 SSL_FILETYPE_PEM );

        /* Import the client certificate private key. */
        if( sslStatus != 1 )
        {
            LogError( ( "SSL_CTX_use_PrivateKey_file failed to import client "
                        "certificate private key at %.*s.",
                        ( int32_t ) clientPrivateKeyPathLen,
                        pClientPrivateKeyPath ) );
        }
        else
        {
            LogInfo( ( "Successfully imported client certificate private key." ) );
        }
    }

    /* Free the root CA object. */
    if( pRootCa != NULL )
    {
        X509_free( pRootCa );
    }

    /* Free cwd because getcwd calls malloc. */
    if( cwd != NULL )
    {
        free( cwd );
    }

    return sslStatus;
}

/*-----------------------------------------------------------*/

static int tlsSetup( int tcpSocket,
                     SSL ** pSslContext )
{
    int returnStatus = EXIT_SUCCESS;
    long verifyPeerCertStatus = X509_V_OK;
    int sslStatus = 0;

    /* Setup for creating a TLS client. */
    SSL_CTX * pSslSetup = SSL_CTX_new( TLS_client_method() );

    if( pSslSetup != NULL )
    {
        /* Set auto retry mode for the blocking calls to SSL_read and SSL_write.
         * The mask returned by SSL_CTX_set_mode does not need to be checked. */
        ( void ) SSL_CTX_set_mode( pSslSetup, SSL_MODE_AUTO_RETRY );

        sslStatus = readCredentials( pSslSetup,
                                     ROOT_CA_CERT_PATH,
                                     ROOT_CA_CERT_PATH_LENGTH,
                                     CLIENT_CERT_PATH,
                                     CLIENT_CERT_PATH_LENGTH,
                                     CLIENT_PRIVATE_KEY_PATH,
                                     CLIENT_PRIVATE_KEY_PATH_LENGTH );

        /* Setup authentication. */
        if( sslStatus != 1 )
        {
            LogError( ( "Setting up credentials failed." ) );
        }
        else
        {
            LogInfo( ( "Setting up credentials succeeded." ) );
        }
    }

    /* Set up the TLS connection. */
    if( sslStatus == 1 )
    {
        /* Create a new SSL context. */
        *pSslContext = SSL_new( pSslSetup );

        if( *pSslContext == NULL )
        {
            LogError( ( "SSL_new failed to create a new SSL context." ) );
            sslStatus = 0;
        }
        else
        {
            /* Enable SSL peer verification. */
            SSL_set_verify( *pSslContext, SSL_VERIFY_PEER, NULL );

            sslStatus = SSL_set_fd( *pSslContext, tcpSocket );

            if( sslStatus != 1 )
            {
                LogError( ( "SSL_set_fd failed to set the socket fd to SSL context." ) );
            }
        }

        /* Perform the TLS handshake. */
        if( sslStatus == 1 )
        {
            sslStatus = SSL_connect( *pSslContext );

            if( sslStatus != 1 )
            {
                LogError( ( "SSL_connect failed to perform TLS handshake." ) );
            }
        }

        /* Verify X509 certificate from peer. */
        if( sslStatus == 1 )
        {
            verifyPeerCertStatus = SSL_get_verify_result( *pSslContext );

            if( verifyPeerCertStatus != X509_V_OK )
            {
                LogError( ( "SSL_get_verify_result failed to verify X509 "
                            "certificate from peer." ) );
                sslStatus = 0;
            }
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
        LogError( ( "X509_STORE_add_cert failed to add certificate to store." ) );
    }

    /* Log failure or success and return the correct exit status. */
    if( sslStatus == 0 )
    {
        LogError( ( "Failed to establish a TLS connection: Host=%.*s.",
                    ( int32_t ) IOT_CORE_ENDPOINT_LENGTH,
                    IOT_CORE_ENDPOINT ) );
        returnStatus = EXIT_FAILURE;
    }
    else
    {
        LogInfo( ( "Established a TLS connection: Host=%.*s.\n\n",
                   ( int32_t ) IOT_CORE_ENDPOINT_LENGTH,
                   IOT_CORE_ENDPOINT ) );
        returnStatus = EXIT_SUCCESS;
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int32_t transportSend( HTTPNetworkContext_t * pNetworkContext,
                              const void * pBuffer,
                              size_t bytesToSend )
{
    int32_t bytesSent = 0;
    int pollStatus = 0;
    struct pollfd fileDescriptor;

    /* Initialize the file descriptor. */
    fileDescriptor.events = POLLOUT;
    fileDescriptor.revents = 0;
    /* Set the file descriptor for poll. */
    fileDescriptor.fd = pNetworkContext->tcpSocket;

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
    struct pollfd fileDescriptor;

    /* Initialize the file descriptor. */
    fileDescriptor.events = POLLIN | POLLPRI;
    fileDescriptor.revents = 0;
    /* Set the file descriptor for poll. */
    fileDescriptor.fd = SSL_get_fd( pNetworkContext->pSslContext );

    /* Check if there are any pending data available for read. */
    bytesAvailableToRead = SSL_pending( pNetworkContext->pSslContext );

    /* Poll only if there is no data available yet to read. */
    if( bytesAvailableToRead <= 0 )
    {
        pollStatus = poll( &fileDescriptor, 1, TRANSPORT_SEND_RECV_TIMEOUT_MS );
    }

    /* bytesAvailableToRead > 0 means that there was pending data to be read.
     * pollStatus > 0 means that there was no pending data, but it became available
     * during polling. If either holds true, read the available data. */
    if( ( bytesAvailableToRead > 0 ) || ( pollStatus > 0 ) )
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
                            const char * pMethod,
                            size_t methodLen,
                            const char * pPath,
                            size_t pathLen )
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

    assert( pMethod != NULL );
    assert( methodLen > 0 );

    /* Initialize all HTTP Client library API structs to 0. */
    ( void ) memset( &requestInfo, 0, sizeof( requestInfo ) );
    ( void ) memset( &response, 0, sizeof( response ) );
    ( void ) memset( &requestHeaders, 0, sizeof( requestHeaders ) );

    /* Initialize the request object. */
    requestInfo.pHost = IOT_CORE_ENDPOINT;
    requestInfo.hostLen = IOT_CORE_ENDPOINT_LENGTH;
    requestInfo.method = pMethod;
    requestInfo.methodLen = methodLen;
    requestInfo.pPath = pPath;
    requestInfo.pathLen = pathLen;

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

        LogInfo( ( "Sending HTTP %.*s request to %.*s%.*s...",
                   ( int32_t ) methodLen, pMethod,
                   ( int32_t ) IOT_CORE_ENDPOINT_LENGTH, IOT_CORE_ENDPOINT,
                   ( int32_t ) pathLen, pPath ) );
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

    if( httpStatus == HTTP_SUCCESS )
    {
        LogInfo( ( "Received HTTP response from %.*s%.*s...\n"
                   "Response Headers:\n%.*s\n"
                   "Response Status:\n%u\n"
                   "Response Body:\n%.*s\n",
                   ( int32_t ) IOT_CORE_ENDPOINT_LENGTH, IOT_CORE_ENDPOINT,
                   ( int32_t ) pathLen, pPath,
                   ( int32_t ) response.headersLen, response.pHeaders,
                   response.statusCode,
                   ( int32_t ) response.bodyLen, response.pBody ) );
    }
    else
    {
        LogError( ( "Failed to send HTTP %.*s request to %.*s%.*s: Error=%s.",
                    ( int32_t ) methodLen, pMethod,
                    ( int32_t ) IOT_CORE_ENDPOINT_LENGTH, IOT_CORE_ENDPOINT,
                    ( int32_t ) pathLen, pPath,
                    HTTPClient_strerror( httpStatus ) ) );
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
    int returnStatus = EXIT_SUCCESS;
    /* The HTTP Client library transport layer interface. */
    HTTPTransportInterface_t transportInterface;

    ( void ) argc;
    ( void ) argv;

    /**************************** Connect. ******************************/

    /* Establish TCP connection. */
    returnStatus = connectToServer( IOT_CORE_ENDPOINT, IOT_CORE_ENDPOINT_LENGTH,
                                    IOT_CORE_PORT, &networkContext.tcpSocket );

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
        ( void ) memset( &transportInterface, 0, sizeof( transportInterface ) );
        transportInterface.recv = transportRecv;
        transportInterface.send = transportSend;
        transportInterface.pContext = &networkContext;
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

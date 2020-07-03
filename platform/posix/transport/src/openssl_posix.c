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
#include <string.h>

/* POSIX socket includes. */
#include <errno.h>
#include <poll.h>
#include <time.h>
#include <unistd.h>

#include <sys/socket.h>
#include <sys/types.h>

/* Transport interface include. */
#include "transport_interface.h"

#include "openssl_posix.h"

/*-----------------------------------------------------------*/

/**
 * @brief Label of root CA when calling @ref logPath.
 */
#define ROOT_CA_LABEL              "Root CA certificate"

/**
 * @brief Label of client certificate when calling @ref logPath.
 */
#define CLIENT_CERT_LABEL          "client's certificate"

/**
 * @brief Label of client key when calling @ref logPath.
 */
#define CLIENT_KEY_LABEL           "client's key"

/**
 * @brief Number of milliseconds in one second.
 */
#define ONE_SEC_TO_MS              ( 1000 )

/**
 * @brief Number of microseconds in one millisecond.
 */
#define ONE_MS_TO_US               ( 1000 )

/**
 * @brief Default timeout for polling.
 */
#define DEFAULT_POLL_TIMEOUT_MS    ( 200 )

/*-----------------------------------------------------------*/

/**
 * @brief Log the absolute path given a relative or absolute path.
 *
 * @param[in] path Relative or absolute path.
 * @param[in] fileLabel NULL-terminated string describing the file label to log.
 */
#if ( LIBRARY_LOG_LEVEL == LOG_DEBUG )
    static void logPath( const char * path,
                         const char * fileLabel );
#endif /* #if ( LIBRARY_LOG_LEVEL == LOG_DEBUG ) */

/**
 * @brief Add X509 certificate to the trusted list of root certificates.
 *
 * OpenSSL does not provide a single function for reading and loading certificates
 * from files into stores, so the file API must be called. Start with the
 * root certificate.
 *
 * @param[out] pSslContext SSL context to which the trusted server root CA is to be added.
 * @param[in] pRootCaPath Filepath string to the trusted server root CA.
 *
 * @return 1 on success; -1, 0 on failure;
 */
static int setRootCa( SSL_CTX * pSslContext,
                      const char * pRootCaPath );

/**
 * @brief Set X509 certificate as client certificate for the server to authenticate.
 *
 * @param[out] pSslContext SSL context to which the client certificate is to be set.
 * @param[in] pClientCertPath Filepath string to the client certificate.
 *
 * @return 1 on success; 0 failure;
 */
static int setClientCertificate( SSL_CTX * pSslContext,
                                 const char * pClientCertPath );

/**
 * @brief Set private key for the client's certificate.
 *
 * @param[out] pSslContext SSL context to which the private key is to be added.
 * @param[in] pPrivateKeyPath Filepath string to the client private key.
 *
 * @return 1 on success; 0 on failure;
 */
static int setPrivateKey( SSL_CTX * pSslContext,
                          const char * pPrivateKeyPath );

/**
 * @brief Passes TLS credentials to the OpenSSL library.
 *
 * Provides the root CA certificate, client certificate, and private key to the
 * OpenSSL library. If the client certificate or private key is not NULL, mutual
 * authentication is used when performing the TLS handshake.
 *
 * @param[out] pSslContext SSL context to which the credentials are to be imported.
 * @param[in] pOpensslCredentials TLS credentials to be imported.
 *
 * @return 1 on success; -1, 0 on failure;
 */
static int setCredentials( SSL_CTX * pSslContext,
                           const OpensslCredentials_t * pOpensslCredentials );

/**
 * @brief Set optional configurations for the TLS connection.
 *
 * This function is used to set SNI, MFLN, and ALPN protocols.
 *
 * @param[in] pSsl SSL context to which the optional configurations are to be set.
 * @param[in] pOpensslCredentials TLS credentials containing configurations.
 */
static void setOptionalConfigurations( SSL * pSsl,
                                       const OpensslCredentials_t * pOpensslCredentials );

/*-----------------------------------------------------------*/

#if ( LIBRARY_LOG_LEVEL == LOG_DEBUG )
    static void logPath( const char * path,
                         const char * fileType )
    {
        char * cwd = NULL;

        assert( path != NULL );
        assert( fileType != NULL );

        /* Log the absolute directory based on first character of path. */
        if( ( path[ 0 ] == '/' ) || ( path[ 0 ] == '\\' ) )
        {
            LogDebug( ( "Attempting to open %s: Path=%s.",
                        fileType,
                        path ) );
        }
        else
        {
            cwd = getcwd( NULL, 0 );
            LogDebug( ( "Attempting to open %s: Path=%s/%s.",
                        fileType,
                        cwd,
                        path ) );
        }

        /* Free cwd because getcwd calls malloc. */
        if( cwd != NULL )
        {
            free( cwd );
        }
    }
#endif /* #if ( LIBRARY_LOG_LEVEL == LOG_DEBUG ) */
/*-----------------------------------------------------------*/

static int setRootCa( SSL_CTX * pSslContext,
                      const char * pRootCaPath )
{
    int sslStatus = 1;
    FILE * pRootCaFile = NULL;
    X509 * pRootCa = NULL;

    assert( pSslContext != NULL );
    assert( pRootCaPath != NULL );

    #if ( LIBRARY_LOG_LEVEL == LOG_DEBUG )
        logPath( pRootCaPath, ROOT_CA_LABEL );
    #endif

    pRootCaFile = fopen( pRootCaPath, "r" );

    if( pRootCaFile == NULL )
    {
        LogError( ( "fopen failed to find the root CA certificate file: "
                    "ROOT_CA_PATH=%s.",
                    pRootCaPath ) );
        sslStatus = -1;
    }

    if( sslStatus == 1 )
    {
        /* Read the root CA into an X509 object. */
        pRootCa = PEM_read_X509( pRootCaFile, NULL, NULL, NULL );

        if( pRootCa == NULL )
        {
            LogError( ( "PEM_read_X509 failed to parse root CA." ) );
            sslStatus = -1;
        }
    }

    if( sslStatus == 1 )
    {
        /* Add the certificate to the context. */
        sslStatus = X509_STORE_add_cert( SSL_CTX_get_cert_store( pSslContext ),
                                         pRootCa );

        if( sslStatus != 1 )
        {
            LogError( ( "X509_STORE_add_cert failed to add root CA to certificate store." ) );
            sslStatus = -1;
        }
    }

    /* Close the file if it was successfully opened. */
    if( pRootCaFile != NULL )
    {
        if( fclose( pRootCaFile ) != 0 )
        {
            LogWarn( ( "fclose failed to close file %s",
                       pRootCaPath ) );
        }
    }

    /* Log the success message if we successfully imported the root CA. */
    if( sslStatus == 1 )
    {
        LogDebug( ( "Successfully imported root CA." ) );
    }

    return sslStatus;
}
/*-----------------------------------------------------------*/

static int setClientCertificate( SSL_CTX * pSslContext,
                                 const char * pClientCertPath )
{
    int sslStatus = -1;

    assert( pSslContext != NULL );
    assert( pClientCertPath != NULL );

    #if ( LIBRARY_LOG_LEVEL == LOG_DEBUG )
        logPath( pClientCertPath, CLIENT_CERT_LABEL );
    #endif

    /* Import the client certificate. */
    sslStatus = SSL_CTX_use_certificate_chain_file( pSslContext,
                                                    pClientCertPath );

    if( sslStatus != 1 )
    {
        LogError( ( "SSL_CTX_use_certificate_chain_file failed to import "
                    "client certificate at %s.",
                    pClientCertPath ) );
    }
    else
    {
        LogDebug( ( "Successfully imported client certificate." ) );
    }

    return sslStatus;
}
/*-----------------------------------------------------------*/

static int setPrivateKey( SSL_CTX * pSslContext,
                          const char * pPrivateKeyPath )
{
    int sslStatus = -1;

    assert( pSslContext != NULL );
    assert( pPrivateKeyPath != NULL );

    #if ( LIBRARY_LOG_LEVEL == LOG_DEBUG )
        logPath( pPrivateKeyPath, CLIENT_KEY_LABEL );
    #endif

    /* Import the client certificate private key. */
    sslStatus = SSL_CTX_use_PrivateKey_file( pSslContext,
                                             pPrivateKeyPath,
                                             SSL_FILETYPE_PEM );

    if( sslStatus != 1 )
    {
        LogError( ( "SSL_CTX_use_PrivateKey_file failed to import client "
                    "certificate private key at %s.",
                    pPrivateKeyPath ) );
    }
    else
    {
        LogDebug( ( "Successfully imported client certificate private key." ) );
    }

    return sslStatus;
}
/*-----------------------------------------------------------*/

static int setCredentials( SSL_CTX * pSslContext,
                           const OpensslCredentials_t * pOpensslCredentials )
{
    int sslStatus = 0;

    assert( pSslContext != NULL );
    assert( pOpensslCredentials != NULL );

    if( pOpensslCredentials->pRootCaPath != NULL )
    {
        sslStatus = setRootCa( pSslContext,
                               pOpensslCredentials->pRootCaPath );
    }

    if( ( sslStatus == 1 ) &&
        ( pOpensslCredentials->pClientCertPath != NULL ) )
    {
        sslStatus = setClientCertificate( pSslContext,
                                          pOpensslCredentials->pClientCertPath );
    }

    if( ( sslStatus == 1 ) &&
        ( pOpensslCredentials->pPrivateKeyPath != NULL ) )
    {
        sslStatus = setPrivateKey( pSslContext,
                                   pOpensslCredentials->pPrivateKeyPath );
    }

    return sslStatus;
}
/*-----------------------------------------------------------*/

static void setOptionalConfigurations( SSL * pSsl,
                                       const OpensslCredentials_t * pOpensslCredentials )
{
    int sslStatus = -1;

    assert( pSsl != NULL );
    assert( pOpensslCredentials != NULL );

    /* Set TLS ALPN if requested. */
    if( ( pOpensslCredentials->pAlpnProtos != NULL ) &&
        ( pOpensslCredentials->alpnProtosLen > 0 ) )
    {
        LogDebug( ( "Setting ALPN protos." ) );
        sslStatus = SSL_set_alpn_protos( pSsl,
                                         ( unsigned char * ) pOpensslCredentials->pAlpnProtos,
                                         ( unsigned int ) pOpensslCredentials->alpnProtosLen );

        if( sslStatus != 0 )
        {
            LogError( ( "SSL_set_alpn_protos failed to set ALPN protos. %s",
                        pOpensslCredentials->pAlpnProtos ) );
        }
    }

    /* Set TLS MFLN if requested. */
    if( pOpensslCredentials->maxFragmentLength > 0 )
    {
        LogDebug( ( "Setting max send fragment length %lu.",
                    ( unsigned long ) pOpensslCredentials->maxFragmentLength ) );

        /* Set the maximum send fragment length. */
        sslStatus = SSL_set_max_send_fragment( pSsl,
                                               ( long ) pOpensslCredentials->maxFragmentLength );

        if( sslStatus != 1 )
        {
            LogError( ( "Failed to set max send fragment length %lu.",
                        ( unsigned long ) pOpensslCredentials->maxFragmentLength ) );
        }
        else
        {
            /* Change the size of the read buffer to match the
             * maximum fragment length + some extra bytes for overhead. */
            SSL_set_default_read_buffer_len( pSsl,
                                             pOpensslCredentials->maxFragmentLength +
                                             SSL3_RT_MAX_ENCRYPTED_OVERHEAD );
        }
    }

    /* Enable SNI if requested. */
    if( pOpensslCredentials->sniHostName != NULL )
    {
        LogDebug( ( "Setting server name %s for SNI.",
                    pOpensslCredentials->sniHostName ) );

        sslStatus = SSL_set_tlsext_host_name( pSsl,
                                              pOpensslCredentials->sniHostName );

        if( sslStatus != 1 )
        {
            LogError( ( "Failed to set server name %s for SNI.",
                        pOpensslCredentials->sniHostName ) );
        }
    }
}
/*-----------------------------------------------------------*/

OpensslStatus_t Openssl_Connect( NetworkContext_t * pNetworkContext,
                                 const ServerInfo_t * pServerInfo,
                                 const OpensslCredentials_t * pOpensslCredentials,
                                 uint32_t sendTimeoutMs,
                                 uint32_t recvTimeoutMs )
{
    SocketStatus_t socketStatus = SOCKETS_SUCCESS;
    OpensslStatus_t returnStatus = OPENSSL_SUCCESS;
    long verifyPeerCertStatus = X509_V_OK;
    int sslStatus = 0;
    SSL_CTX * pSslContext = NULL;

    /* Validate parameters. */
    if( pNetworkContext == NULL )
    {
        LogError( ( "Parameter check failed: pNetworkContext is NULL." ) );
        returnStatus = OPENSSL_INVALID_PARAMETER;
    }
    else if( pOpensslCredentials == NULL )
    {
        LogError( ( "Parameter check failed: pOpensslCredentials is NULL." ) );
        returnStatus = OPENSSL_INVALID_PARAMETER;
    }
    else
    {
        /* Empty else. */
    }

    /* Establish the TCP connection. */
    if( returnStatus == OPENSSL_SUCCESS )
    {
        socketStatus = Sockets_Connect( &pNetworkContext->socketDescriptor,
                                        pServerInfo,
                                        sendTimeoutMs,
                                        recvTimeoutMs );

        if( socketStatus == SOCKETS_INVALID_PARAMETER )
        {
            returnStatus = OPENSSL_INVALID_PARAMETER;
        }
        else if( socketStatus == SOCKETS_DNS_FAILURE )
        {
            returnStatus = OPENSSL_DNS_FAILURE;
        }
        else if( socketStatus == SOCKETS_CONNECT_FAILURE )
        {
            returnStatus = OPENSSL_CONNECT_FAILURE;
        }
        else
        {
            /* Empty else. */
        }
    }

/* Create SSL context. */
    if( returnStatus == OPENSSL_SUCCESS )
    {
        pSslContext = SSL_CTX_new( TLS_client_method() );

        if( pSslContext == NULL )
        {
            LogError( ( "Creation of a new SSL_CTX object failed." ) );
            returnStatus = OPENSSL_API_ERROR;
        }
    }

    /* Setup credentials. */
    if( returnStatus == OPENSSL_SUCCESS )
    {
        /* Set auto retry mode for the blocking calls to SSL_read and SSL_write.
         * The mask returned by SSL_CTX_set_mode does not need to be checked. */
        ( void ) SSL_CTX_set_mode( pSslContext, SSL_MODE_AUTO_RETRY );

        sslStatus = setCredentials( pSslContext,
                                    pOpensslCredentials );

        if( sslStatus != 1 )
        {
            LogError( ( "Setting up credentials failed." ) );
            returnStatus = OPENSSL_INVALID_CREDENTIALS;
        }
    }

    /* Create a new SSL session. */
    if( returnStatus == OPENSSL_SUCCESS )
    {
        pNetworkContext->pSsl = SSL_new( pSslContext );

        if( pNetworkContext->pSsl == NULL )
        {
            LogError( ( "SSL_new failed to create a new SSL context." ) );
            returnStatus = OPENSSL_API_ERROR;
        }
    }

    /* Setup the socket to use for communication. */
    if( returnStatus == OPENSSL_SUCCESS )
    {
        /* Enable SSL peer verification. */
        SSL_set_verify( pNetworkContext->pSsl, SSL_VERIFY_PEER, NULL );

        sslStatus = SSL_set_fd( pNetworkContext->pSsl, pNetworkContext->socketDescriptor );

        if( sslStatus != 1 )
        {
            LogError( ( "SSL_set_fd failed to set the socket fd to SSL context." ) );
            returnStatus = OPENSSL_API_ERROR;
        }
    }

    /* Perform the TLS handshake. */
    if( returnStatus == OPENSSL_SUCCESS )
    {
        setOptionalConfigurations( pNetworkContext->pSsl, pOpensslCredentials );

        sslStatus = SSL_connect( pNetworkContext->pSsl );

        if( sslStatus != 1 )
        {
            LogError( ( "SSL_connect failed to perform TLS handshake." ) );
            returnStatus = OPENSSL_HANDSHAKE_FAILED;
        }
    }

    /* Verify X509 certificate from peer. */
    if( returnStatus == OPENSSL_SUCCESS )
    {
        verifyPeerCertStatus = SSL_get_verify_result( pNetworkContext->pSsl );

        if( verifyPeerCertStatus != X509_V_OK )
        {
            LogError( ( "SSL_get_verify_result failed to verify X509 "
                        "certificate from peer." ) );
            returnStatus = OPENSSL_HANDSHAKE_FAILED;
        }
    }

    /* Free the SSL context. */
    if( pSslContext != NULL )
    {
        SSL_CTX_free( pSslContext );
    }

    /* Clean up on error. */
    if( ( returnStatus != OPENSSL_SUCCESS ) && ( sslStatus == 0 ) )
    {
        SSL_free( pNetworkContext->pSsl );
        pNetworkContext->pSsl = NULL;
    }

    /* Log failure or success depending on status. */
    if( returnStatus != OPENSSL_SUCCESS )
    {
        LogError( ( "Failed to establish a TLS connection." ) );
    }
    else
    {
        LogDebug( ( "Established a TLS connection." ) );
    }

    return returnStatus;
}
/*-----------------------------------------------------------*/

OpensslStatus_t Openssl_Disconnect( NetworkContext_t * pNetworkContext )
{
    OpensslStatus_t returnStatus = OPENSSL_SUCCESS;
    SocketStatus_t socketStatus = SOCKETS_SUCCESS;

    if( pNetworkContext == NULL )
    {
        LogError( ( "Parameter check failed: pNetworkContext is NULL." ) );
        returnStatus = OPENSSL_INVALID_PARAMETER;
    }
    else if( pNetworkContext->pSsl != NULL )
    {
        /* SSL shutdown should be called twice: once to send "close notify" and
         * once more to receive the peer's "close notify". */
        if( SSL_shutdown( pNetworkContext->pSsl ) == 0 )
        {
            ( void ) SSL_shutdown( pNetworkContext->pSsl );
        }

        SSL_free( pNetworkContext->pSsl );
    }
    else
    {
        /* Empty else. */
    }

    /* Tear down the socket connection. */
    socketStatus = Sockets_Disconnect( pNetworkContext->socketDescriptor );

    if( socketStatus == SOCKETS_INVALID_PARAMETER )
    {
        returnStatus = OPENSSL_INVALID_PARAMETER;
    }

    return returnStatus;
}
/*-----------------------------------------------------------*/

int32_t Openssl_Recv( NetworkContext_t * pNetworkContext,
                      void * pBuffer,
                      size_t bytesToRecv )
{
    int32_t bytesReceived = 0, recvTimeoutMs = DEFAULT_POLL_TIMEOUT_MS;
    int pollStatus = -1, bytesAvailableToRead = 0, getTimeoutStatus = -1;
    struct pollfd fileDescriptor;
    struct timeval transportTimeout;
    socklen_t sockLen = sizeof( transportTimeout );

    /* Set the file descriptor for poll. */
    fileDescriptor.events = POLLIN | POLLPRI;
    fileDescriptor.revents = 0;
    fileDescriptor.fd = pNetworkContext->socketDescriptor;

    /* Get the receive timeout from the socket to use for polling. */
    getTimeoutStatus = getsockopt( fileDescriptor.fd,
                                   SOL_SOCKET,
                                   SO_RCVTIMEO,
                                   &transportTimeout,
                                   &sockLen );

    if( ( getTimeoutStatus == 0 ) &&
        ( transportTimeout.tv_sec > 0 ) &&
        ( transportTimeout.tv_usec > 0 ) )
    {
        recvTimeoutMs = ONE_SEC_TO_MS * transportTimeout.tv_sec;
        recvTimeoutMs += transportTimeout.tv_usec / ONE_MS_TO_US;
    }

    /* Check if there are any pending data available for read. */
    bytesAvailableToRead = SSL_pending( pNetworkContext->pSsl );

    /* Poll only if there is no data available yet to read. */
    if( bytesAvailableToRead <= 0 )
    {
        pollStatus = poll( &fileDescriptor, 1, -1 );
    }

    /* SSL read of data. */
    if( ( pollStatus > 0 ) || ( bytesAvailableToRead > 0 ) )
    {
        bytesReceived = ( int32_t ) SSL_read( pNetworkContext->pSsl,
                                              pBuffer,
                                              bytesToRecv );
    }
    /* Poll timed out. */
    else if( pollStatus == 0 )
    {
        LogDebug( ( "Poll timed out and there is no data to read from the buffer." ) );
    }
    else
    {
        LogError( ( "Poll returned with status = %d.", pollStatus ) );
        bytesReceived = -1;
    }

    return bytesReceived;
}
/*-----------------------------------------------------------*/

int32_t Openssl_Send( NetworkContext_t * pNetworkContext,
                      const void * pBuffer,
                      size_t bytesToSend )
{
    int32_t bytesSent = 0, sendTimeoutMs = DEFAULT_POLL_TIMEOUT_MS;
    int pollStatus = 0, getTimeoutStatus = -1;
    struct pollfd fileDescriptor;
    struct timeval transportTimeout;
    socklen_t sockLen = sizeof( transportTimeout );

    /* Set the file descriptor for poll. */
    fileDescriptor.events = POLLOUT;
    fileDescriptor.revents = 0;
    fileDescriptor.fd = pNetworkContext->socketDescriptor;

    /* Get the send timeout from the socket to use for polling. */
    getTimeoutStatus = getsockopt( fileDescriptor.fd,
                                   SOL_SOCKET,
                                   SO_SNDTIMEO,
                                   &transportTimeout,
                                   &sockLen );

    if( ( getTimeoutStatus == 0 ) &&
        ( transportTimeout.tv_sec > 0 ) &&
        ( transportTimeout.tv_usec > 0 ) )
    {
        sendTimeoutMs = ONE_SEC_TO_MS * transportTimeout.tv_sec;
        sendTimeoutMs += transportTimeout.tv_usec / ONE_MS_TO_US;
    }

    /* Poll the file descriptor to check if SSL_Write can be done now. */
    pollStatus = poll( &fileDescriptor, 1, sendTimeoutMs );

    if( pollStatus > 0 )
    {
        bytesSent = ( int32_t ) SSL_write( pNetworkContext->pSsl,
                                           pBuffer,
                                           bytesToSend );
        LogInfo( ( "Bytes sent over SSL: %d", bytesSent ) );
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

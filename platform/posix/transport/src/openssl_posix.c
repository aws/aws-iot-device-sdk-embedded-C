/* Standard includes. */
#include <assert.h>
#include <stdlib.h>
#include <string.h>

/* POSIX socket includes. */
#include <limits.h>
#include <errno.h>
#include <netdb.h>
#include <time.h>
#include <poll.h>
#include <unistd.h>
#include <arpa/inet.h>

#include <sys/socket.h>
#include <sys/types.h>

/* OpenSSL include. */
#include <openssl/ssl.h>

/* Transport interface include. */
#include "transport_interface.h"

#include "Openssl_posix.h"

/*-----------------------------------------------------------*/

/**
 * @brief Timeout for transport send.
 *
 * @note Setting to a negative value implies an infinite timeout.
 */
static int tlsSendTimeout = -1;

/**
 * @brief Timeout for transport recv.
 *
 * @note Setting to a negative value implies an infinite timeout.
 */
static int tlsRecvTimeout = -1;

/**
 * @brief Definition of the HTTP network context.
 *
 * @note For this transport implementation, the socket descriptor and
 * SSL context is used.
 */
struct NetworkContext
{
    int tcpSocket;
    SSL * pSslContext;
};

/**
 * @brief A null-terminated string for the SNI host name.
 *
 * @note If SNI is enabled, this NULL-terminated string is set to
 * #OpensslCredentials.sniHostName, then passed to SSL_set_tlsext_host_name(...).
 */
static char sniHostName[ HOST_NAME_MAX + 1 ];

/*-----------------------------------------------------------*/

/**
 * @brief Passes TLS credentials to the OpenSSL library.
 *
 * Provides the root CA certificate, client certificate, and private key to the
 * OpenSSL library. If the client certificate or private key is not NULL, mutual
 * authentication is used when performing the TLS handshake.
 *
 * @param[in] pSslContext Destination for the imported credentials.
 * @param[in] pOpensslCredentials TLS credentials to be validated.
 *
 * @return 1 on success; otherwise, failure;
 */
static int readCredentials( SSL_CTX * pSslContext,
                            OpensslCredentials_t * pOpensslCredentials );

/*-----------------------------------------------------------*/

static int readCredentials( SSL_CTX * pSslContext,
                            OpensslCredentials_t * pOpensslCredentials )
{
    int sslStatus = 0;
    char * cwd = getcwd( NULL, 0 );
    FILE * pRootCaFile = NULL;
    X509 * pRootCa = NULL;

    assert( pOpensslCredentials->pRootCaPath != NULL );
    assert( pOpensslCredentials->rootCaPathLen > 0 );

    /* OpenSSL does not provide a single function for reading and loading certificates
     * from files into stores, so the file API must be called. Start with the
     * root certificate. */
    if( ( pOpensslCredentials->pRootCaPath != NULL ) && ( pOpensslCredentials->rootCaPathLen > 0 ) )
    {
        /* Log the absolute directory based on first character of root CA path. */
        if( ( pOpensslCredentials->pRootCaPath[ 0 ] == '/' ) ||
            ( pOpensslCredentials->pRootCaPath[ 0 ] == '\\' ) )
        {
            LogDebug( ( "Attempting to open root CA certificate: Path=%.*s.",
                        ( int32_t ) pOpensslCredentials->rootCaPathLen,
                        pOpensslCredentials->pRootCaPath ) );
        }
        else
        {
            LogDebug( ( "Attempting to open root CA certificate: Path=%s/%.*s.",
                        cwd,
                        ( int32_t ) pOpensslCredentials->rootCaPathLen,
                        pOpensslCredentials->pRootCaPath ) );
        }

        pRootCaFile = fopen( pOpensslCredentials->pRootCaPath, "r" );

        if( pRootCaFile == NULL )
        {
            LogError( ( "fopen failed to find the root CA certificate file: "
                        "ROOT_CA_PATH=%.*s.",
                        ( int32_t ) pOpensslCredentials->rootCaPathLen,
                        pOpensslCredentials->pRootCaPath ) );
            sslStatus = -1;
        }
        else
        {
            /* Read the root CA into an X509 object, then close its file handle. */
            pRootCa = PEM_read_X509( pRootCaFile, NULL, NULL, NULL );

            if( fclose( pRootCaFile ) != 0 )
            {
                LogWarn( ( "fclose failed to close file %.*s",
                           ( int32_t ) pOpensslCredentials->rootCaPathLen,
                           pOpensslCredentials->pRootCaPath ) );
            }
        }

        if( pRootCa == NULL )
        {
            LogError( ( "PEM_read_X509 failed to parse root CA." ) );
            sslStatus = -1;
        }
        else
        {
            sslStatus = X509_STORE_add_cert( SSL_CTX_get_cert_store( pSslContext ),
                                             pRootCa );
        }

        if( sslStatus != 1 )
        {
            LogError( ( "X509_STORE_add_cert failed to add root CA to certificate store." ) );
        }
        else
        {
            LogDebug( ( "Successfully imported root CA." ) );
        }
    }

    if( ( sslStatus == 1 ) &&
        ( pOpensslCredentials->pClientCertPath != NULL ) &&
        ( pOpensslCredentials->clientCertPathLen > 0 ) )
    {
        /* Log the absolute directory based on first character of client certificate path. */
        if( ( pOpensslCredentials->pClientCertPath[ 0 ] == '/' ) || ( pOpensslCredentials->pClientCertPath[ 0 ] == '\\' ) )
        {
            LogDebug( ( "Attempting to open client's certificate: Path=%.*s.",
                        ( int32_t ) pOpensslCredentials->rootCaPathLen,
                        pOpensslCredentials->pRootCaPath ) );
        }
        else
        {
            LogDebug( ( "Attempting to open client's certificate: Path=%s/%.*s.",
                        cwd,
                        ( int32_t ) pOpensslCredentials->rootCaPathLen,
                        pOpensslCredentials->pRootCaPath ) );
        }

        sslStatus = SSL_CTX_use_certificate_chain_file( pSslContext,
                                                        pOpensslCredentials->pClientCertPath );

        /* Import the client certificate. */
        if( sslStatus != 1 )
        {
            LogError( ( "SSL_CTX_use_certificate_chain_file failed to import "
                        "client certificate at %.*s.",
                        ( int32_t ) pOpensslCredentials->clientCertPathLen,
                        pOpensslCredentials->pClientCertPath ) );
        }
        else
        {
            LogDebug( ( "Successfully imported client certificate." ) );
        }
    }

    if( ( sslStatus == 1 ) &&
        ( pOpensslCredentials->pPrivateKeyPath != NULL ) &&
        ( pOpensslCredentials->privateKeyPathLen > 0 ) )
    {
        /* Log the absolute directory based on first character of client certificate path. */
        if( ( pOpensslCredentials->pPrivateKeyPath[ 0 ] == '/' ) || ( pOpensslCredentials->pPrivateKeyPath[ 0 ] == '\\' ) )
        {
            LogDebug( ( "Attempting to open client's private key: Path=%.*s.",
                        ( int32_t ) pOpensslCredentials->privateKeyPathLen,
                        pOpensslCredentials->pPrivateKeyPath ) );
        }
        else
        {
            LogDebug( ( "Attempting to open client's private key: Path=%s/%.*s.",
                        cwd,
                        ( int32_t ) pOpensslCredentials->privateKeyPathLen,
                        pOpensslCredentials->pPrivateKeyPath ) );
        }

        sslStatus = SSL_CTX_use_PrivateKey_file( pSslContext,
                                                 pOpensslCredentials->pPrivateKeyPath,
                                                 SSL_FILETYPE_PEM );

        /* Import the client certificate private key. */
        if( sslStatus != 1 )
        {
            LogError( ( "SSL_CTX_use_PrivateKey_file failed to import client "
                        "certificate private key at %.*s.",
                        ( int32_t ) pOpensslCredentials->privateKeyPathLen,
                        pOpensslCredentials->pPrivateKeyPath ) );
        }
        else
        {
            LogDebug( ( "Successfully imported client certificate private key." ) );
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

void Openssl_SetSendTimeout( int timeout )
{
    tlsSendTimeout = timeout;
}

void Openssl_SetRecvTimeout( int timeout )
{
    tlsRecvTimeout = timeout;
}

OpensslStatus_t Openssl_Connect( NetworkContext_t pNetworkContext,
                                 OpensslCredentials_t * pOpensslCredentials )
{
    OpensslStatus_t returnStatus = OPENSSL_SUCCESS;
    long verifyPeerCertStatus = X509_V_OK;
    int sslStatus = 0;
    SSL_CTX * pSslSetup = NULL;

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
        /* Empty else for MISRA 15.7 compliance. */
    }

    /* Setup for creating a TLS client. */
    if( returnStatus == OPENSSL_SUCCESS )
    {
        pSslSetup = SSL_CTX_new( TLS_client_method() );

        if( pSslSetup == NULL )
        {
            LogError( ( "Creation of a new SSL_CTX object failed." ) );
            returnStatus = OPENSSL_API_ERROR;
        }
        else
        {
            /* Set auto retry mode for the blocking calls to SSL_read and SSL_write.
             * The mask returned by SSL_CTX_set_mode does not need to be checked. */
            ( void ) SSL_CTX_set_mode( pSslSetup, SSL_MODE_AUTO_RETRY );
        }
    }

    /* Set credentials for the TLS handshake. */
    if( returnStatus == OPENSSL_SUCCESS )
    {
        sslStatus = readCredentials( pSslSetup,
                                     pOpensslCredentials );

        /* Setup authentication. */
        if( sslStatus != 1 )
        {
            LogError( ( "Setting up credentials failed." ) );
            returnStatus = OPENSSL_INVALID_CREDENTIALS;
        }
        else
        {
            LogDebug( ( "Setting up credentials succeeded." ) );
        }
    }

    /* Set up the TLS connection. */
    if( returnStatus == OPENSSL_SUCCESS )
    {
        /* Create a new SSL context. */
        pNetworkContext->pSslContext = SSL_new( pSslSetup );

        if( pNetworkContext->pSslContext == NULL )
        {
            LogError( ( "SSL_new failed to create a new SSL context." ) );
            returnStatus = OPENSSL_API_ERROR;
        }
        else
        {
            /* Enable SSL peer verification. */
            SSL_set_verify( pNetworkContext->pSslContext, SSL_VERIFY_PEER, NULL );

            sslStatus = SSL_set_fd( pNetworkContext->pSslContext, pNetworkContext->tcpSocket );

            if( sslStatus != 1 )
            {
                LogError( ( "SSL_set_fd failed to set the socket fd to SSL context." ) );
                returnStatus = OPENSSL_API_ERROR;
            }
        }
    }

    /* Set configurations for TLS connection. Note that returnStatus is never
     * set below because failing to set these configurations does not invalidate
     * the TLS connection. */
    if( returnStatus == OPENSSL_SUCCESS )
    {
        /* Set TLS ALPN if requested. */
        if( ( pOpensslCredentials->pAlpnProtos != NULL ) &&
            ( pOpensslCredentials->alpnProtosLen > 0 ) )
        {
            LogDebug( ( "Setting ALPN protos." ) );
            sslStatus = SSL_set_alpn_protos( pNetworkContext->pSslContext,
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
            sslStatus = SSL_set_max_send_fragment( pNetworkContext->pSslContext,
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
                SSL_set_default_read_buffer_len( pNetworkContext->pSslContext,
                                                 pOpensslCredentials->maxFragmentLength +
                                                 SSL3_RT_MAX_ENCRYPTED_OVERHEAD );
            }
        }

        /* Enable SNI if requested. */
        if( ( pOpensslCredentials->sniHostName != NULL ) &&
            ( pOpensslCredentials->sniHostNameLen > 0 ) )
        {
            LogDebug( ( "Setting server name %.*s for SNI.",
                        pOpensslCredentials->sniHostName,
                        pOpensslCredentials->sniHostNameLen ) );

            /* NULL-terminated string is required for SSL_set_tlsext_host_name. */
            sniHostName[ pOpensslCredentials->sniHostNameLen ] = '\0';
            ( void ) memcpy( sniHostName,
                             pOpensslCredentials->sniHostName,
                             pOpensslCredentials->sniHostNameLen );

            sslStatus = SSL_set_tlsext_host_name( pNetworkContext->pSslContext,
                                                  sniHostName );

            if( sslStatus != 1 )
            {
                LogError( ( "Failed to set server name %.*s for SNI.",
                            ( int32_t ) pOpensslCredentials->sniHostNameLen,
                            pOpensslCredentials->sniHostName ) );
            }
        }
    }

    /* Perform the TLS handshake. */
    if( returnStatus == OPENSSL_SUCCESS )
    {
        sslStatus = SSL_connect( pNetworkContext->pSslContext );

        if( sslStatus != 1 )
        {
            LogError( ( "SSL_connect failed to perform TLS handshake." ) );
            returnStatus = OPENSSL_HANDSHAKE_FAILED;
        }
    }

    /* Verify X509 certificate from peer. */
    if( returnStatus == OPENSSL_SUCCESS )
    {
        verifyPeerCertStatus = SSL_get_verify_result( pNetworkContext->pSslContext );

        if( verifyPeerCertStatus != X509_V_OK )
        {
            LogError( ( "SSL_get_verify_result failed to verify X509 "
                        "certificate from peer." ) );
            returnStatus = OPENSSL_HANDSHAKE_FAILED;
        }
    }

    /* Clean up on error. */
    if( ( returnStatus != OPENSSL_SUCCESS ) && ( sslStatus == 0 ) )
    {
        SSL_free( pNetworkContext->pSslContext );
        pNetworkContext->pSslContext = NULL;
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

OpensslStatus_t Openssl_Disconnect( NetworkContext_t pNetworkContext )
{
    OpensslStatus_t returnStatus = OPENSSL_SUCCESS;

    if( pNetworkContext == NULL )
    {
        LogError( ( "Parameter check failed: pNetworkContext is NULL." ) );
        returnStatus = OPENSSL_INVALID_PARAMETER;
    }
    else if( pNetworkContext->pSslContext != NULL )
    {
        /* SSL shutdown should be called twice: once to send "close notify" and
         * once more to receive the peer's "close notify". */
        if( SSL_shutdown( pNetworkContext->pSslContext ) == 0 )
        {
            ( void ) SSL_shutdown( pNetworkContext->pSslContext );
        }

        SSL_free( pNetworkContext->pSslContext );
    }
    else
    {
        /* Empty else for MISRA 15.7 compliance. */
    }

    return returnStatus;
}

int32_t Openssl_Recv( NetworkContext_t pNetworkContext,
                      void * pBuffer,
                      size_t bytesToRecv )
{
    int32_t bytesReceived = 0;
    int pollStatus = -1, bytesAvailableToRead = 0;
    struct pollfd fileDescriptor;

    /* Initialize the file descriptor for poll. */
    fileDescriptor.events = POLLIN | POLLPRI;
    fileDescriptor.revents = 0;
    fileDescriptor.fd = SSL_get_fd( pNetworkContext->pSslContext );

    /* Check if there are any pending data available for read. */
    bytesAvailableToRead = SSL_pending( pNetworkContext->pSslContext );

    /* Poll only if there is no data available yet to read. */
    if( bytesAvailableToRead <= 0 )
    {
        pollStatus = poll( &fileDescriptor, 1, tlsRecvTimeout );
    }

    /* SSL read of data. */
    if( ( pollStatus > 0 ) || ( bytesAvailableToRead > 0 ) )
    {
        bytesReceived = ( int32_t ) SSL_read( pNetworkContext->pSslContext,
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

int32_t Openssl_Send( NetworkContext_t pNetworkContext,
                      const void * pBuffer,
                      size_t bytesToSend )
{
    int32_t bytesSent = 0;
    int pollStatus = 0;
    struct pollfd fileDescriptor;

    /* Initialize the file descriptor for poll. */
    fileDescriptor.events = POLLOUT;
    fileDescriptor.revents = 0;
    fileDescriptor.fd = SSL_get_fd( pNetworkContext->pSslContext );

    /* Poll the file descriptor to check if SSL_Write can be done now. */
    pollStatus = poll( &fileDescriptor, 1, tlsRecvTimeout );

    if( pollStatus > 0 )
    {
        bytesSent = ( int32_t ) SSL_write( pNetworkContext->pSslContext,
                                           pBuffer,
                                           bytesToSend );
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

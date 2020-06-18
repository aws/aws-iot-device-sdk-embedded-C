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

/* OpenSSL include. */
#include <openssl/ssl.h>

/* Transport interface include. */
#include "transport_interface.h"

#include "openssl_posix.h"

/**
 * @brief Definition of the HTTP network context.
 *
 * @note For this TLS demo, the socket descriptor and SSL context is used.
 */
struct NetworkContext
{
    int tcpSocket;
    SSL * pSslContext;
};

/**
 * @brief Passes TLS credentials to the OpenSSL library.
 *
 * Provides the root CA certificate, client certificate, and private key to the
 * OpenSSL library. If the client certificate or private key is not NULL, mutual
 * authentication is used when performing the TLS handshake.
 *
 * @param[in] pSslContext Destination for the imported credentials.
 * @param[in] pNetworkCredentials TLS credentials to be validated.
 *
 * @return 1 on success; otherwise, failure;
 */
static int readCredentials( SSL_CTX * pSslContext,
                            NetworkCredentials_t * pNetworkCredentials );

static int readCredentials( SSL_CTX * pSslContext,
                            NetworkCredentials_t * pNetworkCredentials )
{
    int sslStatus = 0;
    char * cwd = getcwd( NULL, 0 );
    FILE * pRootCaFile = NULL;
    X509 * pRootCa = NULL;

    assert( pNetworkCredentials->pRootCaPath != NULL );
    assert( pNetworkCredentials->rootCaPathLen > 0 );

    /* OpenSSL does not provide a single function for reading and loading certificates
     * from files into stores, so the file API must be called. Start with the
     * root certificate. */
    if( ( pNetworkCredentials->pRootCaPath != NULL ) && ( pNetworkCredentials->rootCaPathLen > 0 ) )
    {
        /* Log the absolute directory based on first character of root CA path. */
        if( ( pNetworkCredentials->pRootCaPath[ 0 ] == '/' ) || ( pNetworkCredentials->pRootCaPath[ 0 ] == '\\' ) )
        {
            LogInfo( ( "Attempting to open root CA certificate: Path=%.*s.",
                       ( int32_t ) pNetworkCredentials->rootCaPathLen,
                       pNetworkCredentials->pRootCaPath ) );
        }
        else
        {
            LogInfo( ( "Attempting to open root CA certificate: Path=%s/%.*s.",
                       cwd,
                       ( int32_t ) pNetworkCredentials->rootCaPathLen,
                       pNetworkCredentials->pRootCaPath ) );
        }

        pRootCaFile = fopen( pNetworkCredentials->pRootCaPath, "r" );

        if( pRootCaFile == NULL )
        {
            LogError( ( "fopen failed to find the root CA certificate file: "
                        "ROOT_CA_PATH=%.*s.",
                        ( int32_t ) pNetworkCredentials->rootCaPathLen,
                        pNetworkCredentials->pRootCaPath ) );
            sslStatus = -1;
        }
        else
        {
            /* Read the root CA into an X509 object, then close its file handle. */
            pRootCa = PEM_read_X509( pRootCaFile, NULL, NULL, NULL );

            if( fclose( pRootCaFile ) != 0 )
            {
                LogWarn( ( "fclose failed to close file %.*s",
                           ( int32_t ) pNetworkCredentials->rootCaPathLen,
                           pNetworkCredentials->pRootCaPath ) );
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
            LogInfo( ( "Successfully imported root CA." ) );
        }
    }

    if( ( sslStatus == 1 ) &&
        ( pNetworkCredentials->pClientCertPath != NULL ) && ( pNetworkCredentials->clientCertPathLen > 0 ) )
    {
        /* Log the absolute directory based on first character of client certificate path. */
        if( ( pNetworkCredentials->pClientCertPath[ 0 ] == '/' ) || ( pNetworkCredentials->pClientCertPath[ 0 ] == '\\' ) )
        {
            LogInfo( ( "Attempting to open client's certificate: Path=%.*s.",
                       ( int32_t ) pNetworkCredentials->rootCaPathLen,
                       pNetworkCredentials->pRootCaPath ) );
        }
        else
        {
            LogInfo( ( "Attempting to open client's certificate: Path=%s/%.*s.",
                       cwd,
                       ( int32_t ) pNetworkCredentials->rootCaPathLen,
                       pNetworkCredentials->pRootCaPath ) );
        }

        sslStatus = SSL_CTX_use_certificate_chain_file( pSslContext,
                                                        pNetworkCredentials->pClientCertPath );

        /* Import the client certificate. */
        if( sslStatus != 1 )
        {
            LogError( ( "SSL_CTX_use_certificate_chain_file failed to import "
                        "client certificate at %.*s.",
                        ( int32_t ) pNetworkCredentials->clientCertPathLen,
                        pNetworkCredentials->pClientCertPath ) );
        }
        else
        {
            LogInfo( ( "Successfully imported client certificate." ) );
        }
    }

    if( ( sslStatus == 1 ) &&
        ( pNetworkCredentials->pPrivateKeyPath != NULL ) && ( pNetworkCredentials->privateKeyPathLen > 0 ) )
    {
        /* Log the absolute directory based on first character of client certificate path. */
        if( ( pNetworkCredentials->pPrivateKeyPath[ 0 ] == '/' ) || ( pNetworkCredentials->pPrivateKeyPath[ 0 ] == '\\' ) )
        {
            LogInfo( ( "Attempting to open client's private key: Path=%.*s.",
                       ( int32_t ) pNetworkCredentials->privateKeyPathLen,
                       pNetworkCredentials->pPrivateKeyPath ) );
        }
        else
        {
            LogInfo( ( "Attempting to open client's private key: Path=%s/%.*s.",
                       cwd,
                       ( int32_t ) pNetworkCredentials->privateKeyPathLen,
                       pNetworkCredentials->pPrivateKeyPath ) );
        }

        sslStatus = SSL_CTX_use_PrivateKey_file( pSslContext,
                                                 pNetworkCredentials->pPrivateKeyPath,
                                                 SSL_FILETYPE_PEM );

        /* Import the client certificate private key. */
        if( sslStatus != 1 )
        {
            LogError( ( "SSL_CTX_use_PrivateKey_file failed to import client "
                        "certificate private key at %.*s.",
                        ( int32_t ) pNetworkCredentials->privateKeyPathLen,
                        pNetworkCredentials->pPrivateKeyPath ) );
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

NetworkStatus_t OpenSSL_Establish( NetworkContext_t pNetworkContext,
                                   NetworkCredentials_t * pNetworkCredentials )
{
    int returnStatus = EXIT_SUCCESS;
    long verifyPeerCertStatus = X509_V_OK;
    int sslStatus = 0;
    SSL_CTX * pSslSetup = NULL;

    /* Setup for creating a TLS client. */
    pSslSetup = SSL_CTX_new( TLS_client_method() );

    if( pSslSetup != NULL )
    {
        /* Set auto retry mode for the blocking calls to SSL_read and SSL_write.
         * The mask returned by SSL_CTX_set_mode does not need to be checked. */
        ( void ) SSL_CTX_set_mode( pSslSetup, SSL_MODE_AUTO_RETRY );

        sslStatus = readCredentials( pSslSetup,
                                     pNetworkCredentials );

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
        pNetworkContext->pSslContext = SSL_new( pSslSetup );

        if( pNetworkContext->pSslContext == NULL )
        {
            LogError( ( "SSL_new failed to create a new SSL context." ) );
            sslStatus = 0;
        }
        else
        {
            /* Enable SSL peer verification. */
            SSL_set_verify( pNetworkContext->pSslContext, SSL_VERIFY_PEER, NULL );

            sslStatus = SSL_set_fd( pNetworkContext->pSslContext, pNetworkContext->tcpSocket );

            if( sslStatus != 1 )
            {
                LogError( ( "SSL_set_fd failed to set the socket fd to SSL context." ) );
            }
        }

        if( ( sslStatus == 1 ) &&
            ( pNetworkCredentials->pAlpnProtos != NULL ) && ( pNetworkCredentials->alpnProtosLen > 0 ) )
        {
            sslStatus = SSL_set_alpn_protos( pNetworkContext->pSslContext,
                                             ( unsigned char * ) pNetworkCredentials->pAlpnProtos,
                                             ( unsigned int ) pNetworkCredentials->alpnProtosLen );

            if( sslStatus != 0 )
            {
                LogError( ( "SSL_set_alpn_protos failed to set ALPN protos. %s",
                            pNetworkCredentials->pAlpnProtos ) );
            }
            else
            {
                sslStatus = 1;
            }
        }

        /* Perform the TLS handshake. */
        if( sslStatus == 1 )
        {
            sslStatus = SSL_connect( pNetworkContext->pSslContext );

            if( sslStatus != 1 )
            {
                LogError( ( "SSL_connect failed to perform TLS handshake." ) );
            }
        }

        /* Verify X509 certificate from peer. */
        if( sslStatus == 1 )
        {
            verifyPeerCertStatus = SSL_get_verify_result( pNetworkContext->pSslContext );

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
            SSL_free( pNetworkContext->pSslContext );
            pNetworkContext->pSslContext = NULL;
        }
    }
    else
    {
        LogError( ( "X509_STORE_add_cert failed to add certificate to store." ) );
    }

    /* Log failure or success and return the correct exit status. */
    if( sslStatus == 0 )
    {
        LogError( ( "Failed to establish a TLS connection." ) );
        returnStatus = EXIT_FAILURE;
    }
    else
    {
        LogInfo( ( "Established a TLS connection." ) );
        returnStatus = EXIT_SUCCESS;
    }

    return returnStatus;
}

NetworkStatus_t OpenSSL_Terminate( NetworkContext_t pNetworkContext )
{
    if( pNetworkContext->pSslContext != NULL )
    {
        /* SSL shutdown should be called twice: once to send "close notify" and
         * once more to receive the peer's "close notify". */
        if( SSL_shutdown( pNetworkContext->pSslContext ) == 0 )
        {
            ( void ) SSL_shutdown( pNetworkContext->pSslContext );
        }

        SSL_free( pNetworkContext->pSslContext );
    }
}

int32_t OpenSSL_Send( NetworkContext_t pNetworkContext,
                      const void * pBuffer,
                      size_t bytesToSend )
{
    int32_t bytesReceived = 0;
    int pollStatus = -1, bytesAvailableToRead = 0;
    struct pollfd fileDescriptor =
    {
        .events  = POLLIN | POLLPRI,
        .revents = 0
    };

    /* Set the file descriptor for poll. */
    fileDescriptor.fd = SSL_get_fd( pSslContext );

    /* Check if there are any pending data available for read. */
    bytesAvailableToRead = SSL_pending( pSslContext );

    /* Poll only if there is no data available yet to read. */
    if( bytesAvailableToRead <= 0 )
    {
        pollStatus = poll( &fileDescriptor, 1, TRANSPORT_SEND_RECV_TIMEOUT_MS );
    }

    /* SSL read of data. */
    if( ( pollStatus > 0 ) || ( bytesAvailableToRead > 0 ) )
    {
        bytesReceived = ( int32_t ) SSL_read( pSslContext, pBuffer, bytesToRecv );
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

int32_t OpenSSL_Recv( NetworkContext_t pNetworkContext,
                      void * pBuffer,
                      size_t bytesToRecv )
{
    int32_t bytesSent = 0;
    int pollStatus = 0;
    struct pollfd fileDescriptor =
    {
        .events  = POLLOUT,
        .revents = 0
    };

    /* Set the file descriptor for poll. */
    fileDescriptor.fd = SSL_get_fd( pSslContext );

    /* Poll the file descriptor to check if SSL_Write can be done now. */
    pollStatus = poll( &fileDescriptor, 1, TRANSPORT_SEND_RECV_TIMEOUT_MS );

    if( pollStatus > 0 )
    {
        bytesSent = ( int32_t ) SSL_write( pSslContext, pMessage, bytesToSend );
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

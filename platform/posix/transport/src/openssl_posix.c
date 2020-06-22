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

#include "openssl_posix.h"

/*-----------------------------------------------------------*/

/**
 * @brief Label of root CA when calling @ref logPath.
 */
#define ROOT_CA_LABEL        "Root CA certificate"

/**
 * @brief Label of client certificate when calling @ref logPath.
 */
#define CLIENT_CERT_LABEL    "client's certificate"

/**
 * @brief Label of client key when calling @ref logPath.
 */
#define CLIENT_KEY_LABEL     "client's key"

/*-----------------------------------------------------------*/

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

/*-----------------------------------------------------------*/

/**
 * @brief Log the absolute path given a relative or absolute path.
 *
 * @param[in] path Relative or absolute path.
 * @param[in] pathLen Length of the relative or absolute path.
 * @param[in] fileLabel NULL-terminated string of file label to log.
 */
static void logPath( const char * path,
                     size_t pathLen,
                     const char * fileLabel );

/**
 * @brief Add X509 certificate to trusted list of root certificates.
 *
 * OpenSSL does not provide a single function for reading and loading certificates
 * from files into stores, so the file API must be called. Start with the
 * root certificate.
 *
 * @param[out] pSslSetup Destination for the trusted server root CA.
 * @param[in] pRootCaPath Filepath string to the trusted server root CA.
 * @param[in] rootCaPathLen brief Length associated with trusted server root CA.
 *
 * @return 1 on success; otherwise, failure;
 */
static int setRootCa( SSL_CTX * pSslSetup,
                      const char * pRootCaPath,
                      size_t rootCaPathLen );

/**
 * @brief Set X509 certificate as client certificate for the server to authenticate.
 *
 * @param[out] pSslSetup Destination for the client certificate.
 * @param[in] pClientCertPath Filepath string to the client certificate.
 * @param[in] clientCertPathLen brief Length associated with client certificate.
 *
 * @return 1 on success; otherwise, failure;
 */
static int setClientCertificate( SSL_CTX * pSslSetup,
                                 const char * pClientCertPath,
                                 size_t clientCertPathLen );

/**
 * @brief Set private key for the client's certificate.
 *
 * @param[out] pSslSetup Destination for the private key.
 * @param[in] pPrivateKeyPath Filepath string to the client certificate's private key.
 * @param[in] privateKeyPathLen brief Length associated with client certificate's private key.
 *
 * @return 1 on success; otherwise, failure;
 */
static int setPrivateKey( SSL_CTX * pSslSetup,
                          const char * pPrivateKeyPath,
                          size_t privateKeyPathLen );

/**
 * @brief Passes TLS credentials to the OpenSSL library.
 *
 * Provides the root CA certificate, client certificate, and private key to the
 * OpenSSL library. If the client certificate or private key is not NULL, mutual
 * authentication is used when performing the TLS handshake.
 *
 * @param[out] pSslSetup Destination for the imported credentials.
 * @param[in] pOpensslCredentials TLS credentials to be validated.
 *
 * @return 1 on success; otherwise, failure;
 */
static int setCredentials( SSL_CTX * pSslSetup,
                           OpensslCredentials_t * pOpensslCredentials );

/**
 * @brief Set optional configurations for the TLS connection.
 *
 * This function is used to set SNI, MFLN, and ALPN protocols.
 *
 * @param[in] pSslContext Destination for the imported credentials.
 * @param[in] pOpensslCredentials TLS credentials containing configurations.
 */
static void setOptionalConfigurations( SSL * pSslContext,
                                       OpensslCredentials_t * pOpensslCredentials );

/*-----------------------------------------------------------*/

static void logPath( const char * path,
                     size_t pathLen,
                     const char * fileType )
{
    char * cwd = getcwd( NULL, 0 );

    /* Log the absolute directory based on first character of path. */
    if( ( path[ 0 ] == '/' ) || ( path[ 0 ] == '\\' ) )
    {
        LogDebug( ( "Attempting to open %s: Path=%.*s.",
                    fileType,
                    ( int32_t ) pathLen,
                    path ) );
    }
    else
    {
        LogDebug( ( "Attempting to open %s: Path=%s/%.*s.",
                    fileType,
                    cwd,
                    ( int32_t ) pathLen,
                    path ) );
    }

    /* Free cwd because getcwd calls malloc. */
    if( cwd != NULL )
    {
        free( cwd );
    }
}

static int setRootCa( SSL_CTX * pSslSetup,
                      const char * pRootCaPath,
                      size_t rootCaPathLen )
{
    int sslStatus = 0;
    FILE * pRootCaFile = NULL;
    X509 * pRootCa = NULL;

    logPath( pRootCaPath, rootCaPathLen, ROOT_CA_LABEL );

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

        if( fclose( pRootCaFile ) != 0 )
        {
            LogWarn( ( "fclose failed to close file %.*s",
                       ( int32_t ) rootCaPathLen,
                       pRootCaPath ) );
        }
    }

    if( pRootCa == NULL )
    {
        LogError( ( "PEM_read_X509 failed to parse root CA." ) );
        sslStatus = -1;
    }
    else
    {
        sslStatus = X509_STORE_add_cert( SSL_CTX_get_cert_store( pSslSetup ),
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

    return sslStatus;
}

static int setClientCertificate( SSL_CTX * pSslSetup,
                                 const char * pClientCertPath,
                                 size_t clientCertPathLen )
{
    int sslStatus = -1;
    char * clientCertPathNullTerm = NULL;

    logPath( pClientCertPath, clientCertPathLen, CLIENT_CERT_LABEL );

    /* NULL-terminated string is required for SSL_CTX_use_certificate_chain_file. */
    clientCertPathNullTerm = malloc( ( sizeof( pClientCertPath ) *
                                       clientCertPathLen ) + 1 );
    ( void ) memcpy( clientCertPathNullTerm,
                     pClientCertPath,
                     clientCertPathLen );
    clientCertPathNullTerm[ clientCertPathLen ] = '\0';

    sslStatus = SSL_CTX_use_certificate_chain_file( pSslSetup,
                                                    clientCertPathNullTerm );

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
        LogDebug( ( "Successfully imported client certificate." ) );
    }

    if( clientCertPathNullTerm != NULL )
    {
        free( clientCertPathNullTerm );
    }

    return sslStatus;
}

static int setPrivateKey( SSL_CTX * pSslSetup,
                          const char * pPrivateKeyPath,
                          size_t privateKeyPathLen )
{
    int sslStatus = -1;
    char * privateKeyPathNullTerm = NULL;

    logPath( pPrivateKeyPath, privateKeyPathLen, CLIENT_KEY_LABEL );

    /* NULL-terminated string is required for SSL_CTX_use_PrivateKey_file. */
    privateKeyPathNullTerm = malloc( ( sizeof( pPrivateKeyPath ) *
                                       privateKeyPathLen ) + 1 );
    ( void ) memcpy( privateKeyPathNullTerm,
                     pPrivateKeyPath,
                     privateKeyPathLen );
    privateKeyPathNullTerm[ privateKeyPathLen ] = '\0';

    sslStatus = SSL_CTX_use_PrivateKey_file( pSslSetup,
                                             privateKeyPathNullTerm,
                                             SSL_FILETYPE_PEM );

    /* Import the client certificate private key. */
    if( sslStatus != 1 )
    {
        LogError( ( "SSL_CTX_use_PrivateKey_file failed to import client "
                    "certificate private key at %.*s.",
                    ( int32_t ) privateKeyPathLen,
                    pPrivateKeyPath ) );
    }
    else
    {
        LogDebug( ( "Successfully imported client certificate private key." ) );
    }

    if( privateKeyPathNullTerm != NULL )
    {
        free( privateKeyPathNullTerm );
    }

    return sslStatus;
}

static int setCredentials( SSL_CTX * pSslSetup,
                           OpensslCredentials_t * pOpensslCredentials )
{
    int sslStatus = 0;

    if( ( pOpensslCredentials->pRootCaPath != NULL ) &&
        ( pOpensslCredentials->rootCaPathLen > 0 ) )
    {
        sslStatus = setRootCa( pSslSetup,
                               pOpensslCredentials->pRootCaPath,
                               pOpensslCredentials->rootCaPathLen );
    }

    if( ( sslStatus == 1 ) &&
        ( pOpensslCredentials->pClientCertPath != NULL ) &&
        ( pOpensslCredentials->clientCertPathLen > 0 ) )
    {
        sslStatus = setClientCertificate( pSslSetup,
                                          pOpensslCredentials->pClientCertPath,
                                          pOpensslCredentials->clientCertPathLen );
    }

    if( ( sslStatus == 1 ) &&
        ( pOpensslCredentials->pPrivateKeyPath != NULL ) &&
        ( pOpensslCredentials->privateKeyPathLen > 0 ) )
    {
        sslStatus = setPrivateKey( pSslSetup,
                                   pOpensslCredentials->pPrivateKeyPath,
                                   pOpensslCredentials->privateKeyPathLen );
    }

    return sslStatus;
}

static void setOptionalConfigurations( SSL * pSslContext,
                                       OpensslCredentials_t * pOpensslCredentials )
{
    int sslStatus = -1;
    char * sniHostName = NULL;

    /* Set TLS ALPN if requested. */
    if( ( pOpensslCredentials->pAlpnProtos != NULL ) &&
        ( pOpensslCredentials->alpnProtosLen > 0 ) )
    {
        LogDebug( ( "Setting ALPN protos." ) );
        sslStatus = SSL_set_alpn_protos( pSslContext,
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
        sslStatus = SSL_set_max_send_fragment( pSslContext,
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
            SSL_set_default_read_buffer_len( pSslContext,
                                             pOpensslCredentials->maxFragmentLength +
                                             SSL3_RT_MAX_ENCRYPTED_OVERHEAD );
        }
    }

    /* Enable SNI if requested. */
    if( ( pOpensslCredentials->sniHostName != NULL ) &&
        ( pOpensslCredentials->sniHostNameLen > 0 ) )
    {
        LogDebug( ( "Setting server name %.*s for SNI.",
                    ( int32_t ) pOpensslCredentials->sniHostNameLen,
                    pOpensslCredentials->sniHostName ) );

        /* NULL-terminated string is required for SSL_set_tlsext_host_name. */
        sniHostName = malloc( ( sizeof( pOpensslCredentials->sniHostName ) *
                                pOpensslCredentials->sniHostNameLen ) + 1 );
        ( void ) memcpy( sniHostName,
                         pOpensslCredentials->sniHostName,
                         pOpensslCredentials->sniHostNameLen );
        sniHostName[ pOpensslCredentials->sniHostNameLen ] = '\0';

        sslStatus = SSL_set_tlsext_host_name( pSslContext,
                                              sniHostName );

        if( sslStatus != 1 )
        {
            LogError( ( "Failed to set server name %.*s for SNI.",
                        ( int32_t ) pOpensslCredentials->sniHostNameLen,
                        pOpensslCredentials->sniHostName ) );
        }

        /* Free the malloc'd SNI host name. */
        if( sniHostName != NULL )
        {
            free( sniHostName );
        }
    }
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
        sslStatus = setCredentials( pSslSetup,
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

    /* Perform the TLS handshake. */
    if( returnStatus == OPENSSL_SUCCESS )
    {
        setOptionalConfigurations( pNetworkContext->pSslContext, pOpensslCredentials );

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

    /* Free the SSL context setup. */
    if( pSslSetup != NULL )
    {
        SSL_CTX_free( pSslSetup );
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

    /* SSL read of data. */
    bytesReceived = ( int32_t ) SSL_read( pNetworkContext->pSslContext,
                                          pBuffer,
                                          bytesToRecv );

    if( bytesReceived <= 0 )
    {
        LogError( ( "Transport send of OpenSSL failed"
                    " with status %d.", bytesReceived ) );
    }

    return bytesReceived;
}

int32_t Openssl_Send( NetworkContext_t pNetworkContext,
                      const void * pBuffer,
                      size_t bytesToSend )
{
    int32_t bytesSent = 0;

    bytesSent = ( int32_t ) SSL_write( pNetworkContext->pSslContext,
                                       pBuffer,
                                       bytesToSend );

    if( bytesSent <= 0 )
    {
        LogError( ( "Transport send of OpenSSL failed"
                    " with status %d.", bytesSent ) );
    }

    return bytesSent;
}

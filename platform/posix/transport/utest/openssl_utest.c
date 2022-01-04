/*
 * AWS IoT Device SDK for Embedded C 202108.00
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

#include <string.h>
#include <stdbool.h>
#include <stdlib.h>
#include "/usr/include/errno.h"

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "openssl_posix.h"

#include "mock_unistd_api.h"
#include "mock_openssl_api.h"
#include "mock_sockets_posix.h"
#include "mock_stdio_api.h"
#include "mock_poll.h"

/* The send and receive timeout to set for the socket. */
#define SEND_RECV_TIMEOUT       0

/* The host and port from which to establish the connection. */
#define HOSTNAME                "amazon.com"
#define PORT                    80

/* Credentials for the TLS connection. */
#define ROOT_CA_CERT_PATH       "fake/path.crt"
#define CLIENT_CERT_PATH        "\\fake\\path.crt"
#define PRIVATE_KEY_PATH        "/fake/path.crt"

/* Configuration parameters for the TLS connection. */
#define MFLN                    42
#define ALPN_PROTOS             "x-amzn-mqtt-ca"

/* Parameters to pass to #Openssl_Send and #Openssl_Recv. */
#define BYTES_TO_SEND           4
#define BYTES_TO_RECV           4
#define SSL_READ_WRITE_ERROR    -1

/* The size of the buffer passed to #Openssl_Send and #Openssl_Recv. */
#define BUFFER_LEN              4

/* Each compilation unit must define the NetworkContext struct. */
struct NetworkContext
{
    OpensslParams_t * pParams;
};

/* Objects used by the OpenSSL transport implementation. */
static ServerInfo_t serverInfo = { 0 };
static OpensslCredentials_t opensslCredentials = { 0 };
static OpensslParams_t opensslParams = { 0 };
static NetworkContext_t networkContext = { 0 };
static uint8_t opensslBuffer[ BUFFER_LEN ] = { 0 };

/* Objects from the OpenSSL API. */
static SSL ssl;
static SSL_METHOD sslMethod;
static SSL_CTX sslCtx;
static FILE rootCaFile;
static X509 rootCa;
static X509_STORE CaStore;

/**
 * @brief OpenSSL Connect / Disconnect return status.
 */
typedef enum FunctionNames
{
    Sockets_Connect_fn = 0,
    SSL_CTX_new_fn,
    fopen_fn,
    PEM_read_X509_fn,
    X509_STORE_add_cert_fn,
    SSL_CTX_use_certificate_chain_file_fn,
    SSL_CTX_use_PrivateKey_file_fn,
    SSL_new_fn,
    SSL_set1_host_fn,
    SSL_set_fd_fn,
    SSL_set_alpn_protos_fn,
    SSL_set_max_send_fragment_fn,
    SSL_set_tlsext_host_name_fn,
    SSL_connect_fn,
    SSL_get_verify_result_fn
} FunctionNames_t;

/* ============================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
    serverInfo.pHostName = HOSTNAME;
    serverInfo.hostNameLength = strlen( HOSTNAME );
    serverInfo.port = PORT;

    networkContext.pParams = &opensslParams;

    memset( &opensslCredentials, 0, sizeof( OpensslCredentials_t ) );
    opensslCredentials.pRootCaPath = ROOT_CA_CERT_PATH;
    opensslCredentials.pClientCertPath = CLIENT_CERT_PATH;
    opensslCredentials.pPrivateKeyPath = PRIVATE_KEY_PATH;
    opensslCredentials.pAlpnProtos = ALPN_PROTOS;
    opensslCredentials.alpnProtosLen = strlen( ALPN_PROTOS );
    opensslCredentials.maxFragmentLength = MFLN;
    opensslCredentials.sniHostName = HOSTNAME;
}

/* Called after each test method. */
void tearDown()
{
}

/* Called at the beginning of the whole suite. */
void suiteSetUp()
{
}

/* Called at the end of the whole suite. */
int suiteTearDown( int numFailures )
{
    return numFailures;
}

/* ========================================================================== */

/**
 * @brief Converts the sockets wrapper status to openssl status.
 *
 * @param[in] socketStatus Sockets wrapper status.
 *
 * @return #OPENSSL_SUCCESS, #OPENSSL_INVALID_PARAMETER, #OPENSSL_DNS_FAILURE,
 * and #OPENSSL_CONNECT_FAILURE.
 */
static OpensslStatus_t convertToOpensslStatus( SocketStatus_t socketStatus )
{
    OpensslStatus_t opensslStatus = OPENSSL_INVALID_PARAMETER;

    switch( socketStatus )
    {
        case SOCKETS_SUCCESS:
            opensslStatus = OPENSSL_SUCCESS;
            break;

        case SOCKETS_INVALID_PARAMETER:
            opensslStatus = OPENSSL_INVALID_PARAMETER;
            break;

        case SOCKETS_DNS_FAILURE:
            opensslStatus = OPENSSL_DNS_FAILURE;
            break;

        case SOCKETS_CONNECT_FAILURE:
            opensslStatus = OPENSSL_CONNECT_FAILURE;
            break;

        default:
            LogError( ( "Unexpected status received from socket wrapper: Socket status = %u",
                        socketStatus ) );
    }

    return opensslStatus;
}

/**
 * @brief Expect function calls based on the specified function to fail.
 *
 * @param[in] functionToFail The function called from #Openssl_Connect to fail.
 * @param[in] retValue The return value of the function to fail.
 *
 * @note If the #functionToFail is not a value from #FunctionNames_t, then
 * every method will be expected to succeed. This implies a return value of
 * #OPENSSL_SUCCESS.
 *
 * @return #OPENSSL_SUCCESS, #OPENSSL_INVALID_PARAMETER, #OPENSSL_DNS_FAILURE,
 * #OPENSSL_INSUFFICIENT_MEMORY, #OPENSSL_API_ERROR, #OPENSSL_INVALID_CREDENTIALS,
 * #OPENSSL_HANDSHAKE_FAILED, and #OPENSSL_CONNECT_FAILURE.
 */
static OpensslStatus_t failFunctionFrom_Openssl_Connect( FunctionNames_t functionToFail,
                                                         const void * retValue )
{
    OpensslStatus_t returnStatus = OPENSSL_SUCCESS;
    SocketStatus_t socketStatus = SOCKETS_SUCCESS;
    bool fileOpened = false,
         sslCtxCreated = false, sslCreated = false;

    /* Depending on the function to fail,
     * this function must return the correct status to expect. */
    if( functionToFail == Sockets_Connect_fn )
    {
        TEST_ASSERT_NOT_NULL( retValue );
        socketStatus = *( ( SocketStatus_t * ) retValue );
        Sockets_Connect_ExpectAnyArgsAndReturn( socketStatus );
        returnStatus = convertToOpensslStatus( socketStatus );
    }
    else if( returnStatus == OPENSSL_SUCCESS )
    {
        Sockets_Connect_ExpectAnyArgsAndReturn( SOCKETS_SUCCESS );
    }

    /* Calls like this can't fail no matter what you return. */
    if( returnStatus == OPENSSL_SUCCESS )
    {
        TLS_client_method_ExpectAndReturn( &sslMethod );
    }

    if( functionToFail == SSL_CTX_new_fn )
    {
        SSL_CTX_new_ExpectAnyArgsAndReturn( NULL );
        returnStatus = OPENSSL_API_ERROR;
    }
    else if( returnStatus == OPENSSL_SUCCESS )
    {
        SSL_CTX_new_ExpectAnyArgsAndReturn( &sslCtx );
        sslCtxCreated = true;
    }

    /* SSL_CTX_set_mode is actually what the API uses, but CMock expects the
     * actual method rather than the macro wrapper. */
    if( returnStatus == OPENSSL_SUCCESS )
    {
        SSL_CTX_ctrl_ExpectAnyArgsAndReturn( 1 );
    }

    /* Path to Root CA must be set for handshake to succeed. */
    if( opensslCredentials.pRootCaPath == NULL )
    {
        returnStatus = OPENSSL_INVALID_CREDENTIALS;
    }
    else
    {
        /* These calls are only expected when #LIBRARY_LOG_LEVEL
         * is set to #LOG_DEBUG. */
        #if ( LIBRARY_LOG_LEVEL == LOG_DEBUG )
            if( returnStatus == OPENSSL_SUCCESS )
            {
                getcwd_ExpectAnyArgsAndReturn( NULL );
            }
        #endif

        if( functionToFail == fopen_fn )
        {
            fopen_ExpectAnyArgsAndReturn( NULL );
            returnStatus = OPENSSL_INVALID_CREDENTIALS;
        }
        else if( returnStatus == OPENSSL_SUCCESS )
        {
            fopen_ExpectAnyArgsAndReturn( &rootCaFile );
            fileOpened = true;
        }

        if( functionToFail == PEM_read_X509_fn )
        {
            PEM_read_X509_ExpectAnyArgsAndReturn( NULL );
            returnStatus = OPENSSL_INVALID_CREDENTIALS;
        }
        else if( returnStatus == OPENSSL_SUCCESS )
        {
            PEM_read_X509_ExpectAnyArgsAndReturn( &rootCa );
        }

        if( returnStatus == OPENSSL_SUCCESS )
        {
            SSL_CTX_get_cert_store_ExpectAnyArgsAndReturn( &CaStore );
        }

        if( functionToFail == X509_STORE_add_cert_fn )
        {
            X509_STORE_add_cert_ExpectAnyArgsAndReturn( -1 );
            returnStatus = OPENSSL_INVALID_CREDENTIALS;
        }
        else if( returnStatus == OPENSSL_SUCCESS )
        {
            X509_STORE_add_cert_ExpectAnyArgsAndReturn( 1 );
        }

        if( fileOpened )
        {
            /* Fail fclose on a branch path for coverage. */
            if( functionToFail == PEM_read_X509_fn )
            {
                fclose_ExpectAnyArgsAndReturn( -1 );
            }
            else
            {
                X509_free_ExpectAnyArgs();
                fclose_ExpectAnyArgsAndReturn( 0 );
            }
        }
    }

    if( opensslCredentials.pClientCertPath != NULL )
    {
        if( functionToFail == SSL_CTX_use_certificate_chain_file_fn )
        {
            SSL_CTX_use_certificate_chain_file_ExpectAnyArgsAndReturn( -1 );
            returnStatus = OPENSSL_INVALID_CREDENTIALS;
        }
        else if( returnStatus == OPENSSL_SUCCESS )
        {
            SSL_CTX_use_certificate_chain_file_ExpectAnyArgsAndReturn( 1 );
        }
    }

    if( opensslCredentials.pPrivateKeyPath != NULL )
    {
        if( functionToFail == SSL_CTX_use_PrivateKey_file_fn )
        {
            SSL_CTX_use_PrivateKey_file_ExpectAnyArgsAndReturn( -1 );
            returnStatus = OPENSSL_INVALID_CREDENTIALS;
        }
        else if( returnStatus == OPENSSL_SUCCESS )
        {
            SSL_CTX_use_PrivateKey_file_ExpectAnyArgsAndReturn( 1 );
        }
    }

    if( functionToFail == SSL_new_fn )
    {
        SSL_new_ExpectAnyArgsAndReturn( NULL );
        returnStatus = OPENSSL_API_ERROR;
    }
    else if( returnStatus == OPENSSL_SUCCESS )
    {
        SSL_new_ExpectAnyArgsAndReturn( &ssl );
        sslCreated = true;
    }

    if( functionToFail == SSL_set1_host_fn )
    {
        SSL_set1_host_ExpectAnyArgsAndReturn( 0 );
        returnStatus = OPENSSL_API_ERROR;
    }
    else if( returnStatus == OPENSSL_SUCCESS )
    {
        SSL_set1_host_ExpectAnyArgsAndReturn( 1 );
    }

    if( returnStatus == OPENSSL_SUCCESS )
    {
        SSL_set_verify_ExpectAnyArgs();
    }

    if( functionToFail == SSL_set_fd_fn )
    {
        SSL_set_fd_ExpectAnyArgsAndReturn( -1 );
        returnStatus = OPENSSL_API_ERROR;
    }
    else if( returnStatus == OPENSSL_SUCCESS )
    {
        SSL_set_fd_ExpectAnyArgsAndReturn( 1 );
    }

    /* For any functions that set optional TLS configurations,
     * none of them should cause Openssl_Connect to fail even when they do. */
    if( ( opensslCredentials.pAlpnProtos != NULL ) &&
        ( opensslCredentials.alpnProtosLen > 0 ) )
    {
        if( functionToFail == SSL_set_alpn_protos_fn )
        {
            SSL_set_alpn_protos_ExpectAnyArgsAndReturn( 1 );
        }
        else if( returnStatus == OPENSSL_SUCCESS )
        {
            SSL_set_alpn_protos_ExpectAnyArgsAndReturn( 0 );
        }
    }

    if( opensslCredentials.maxFragmentLength > 0 )
    {
        if( functionToFail == SSL_set_max_send_fragment_fn )
        {
            SSL_ctrl_ExpectAnyArgsAndReturn( 0 );
        }
        else if( returnStatus == OPENSSL_SUCCESS )
        {
            SSL_ctrl_ExpectAnyArgsAndReturn( 1 );
            SSL_set_default_read_buffer_len_ExpectAnyArgs();
        }
    }

    if( opensslCredentials.sniHostName != NULL )
    {
        if( functionToFail == SSL_set_tlsext_host_name_fn )
        {
            SSL_ctrl_ExpectAnyArgsAndReturn( 0 );
        }
        else if( returnStatus == OPENSSL_SUCCESS )
        {
            SSL_ctrl_ExpectAnyArgsAndReturn( 1 );
        }
    }

    if( functionToFail == SSL_connect_fn )
    {
        SSL_connect_ExpectAnyArgsAndReturn( -1 );
        returnStatus = OPENSSL_HANDSHAKE_FAILED;
    }
    else if( returnStatus == OPENSSL_SUCCESS )
    {
        SSL_connect_ExpectAnyArgsAndReturn( 1 );
    }

    if( functionToFail == SSL_get_verify_result_fn )
    {
        SSL_get_verify_result_ExpectAnyArgsAndReturn( -1 );
        returnStatus = OPENSSL_HANDSHAKE_FAILED;
    }
    else if( returnStatus == OPENSSL_SUCCESS )
    {
        SSL_get_verify_result_ExpectAnyArgsAndReturn( X509_V_OK );
    }

    /* Expect objects to be freed depending upon whether they were created. */
    if( sslCtxCreated )
    {
        SSL_CTX_free_ExpectAnyArgs();
    }

    if( ( returnStatus != OPENSSL_SUCCESS ) && sslCreated )
    {
        SSL_free_ExpectAnyArgs();
    }

    return returnStatus;
}

/**
 * @brief Test that #Openssl_Connect is able to fail on NULL parameters and forward
 * the right status from Sockets_Connect.
 */
void test_Openssl_Connect_Invalid_Params( void )
{
    OpensslStatus_t returnStatus, expectedStatus;
    SocketStatus_t socketError;

    returnStatus = Openssl_Connect( NULL,
                                    &serverInfo,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( OPENSSL_INVALID_PARAMETER, returnStatus );

    networkContext.pParams = NULL;
    returnStatus = Openssl_Connect( &networkContext,
                                    &serverInfo,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( OPENSSL_INVALID_PARAMETER, returnStatus );
    networkContext.pParams = &opensslParams;

    /* Fail Sockets_Connect(...) */

    /* NULL serverInfo is handled by Sockets_Connect, so we appropriately
     * return SOCKETS_INVALID_PARAMETER. */
    socketError = SOCKETS_INVALID_PARAMETER;
    expectedStatus = failFunctionFrom_Openssl_Connect( Sockets_Connect_fn, &socketError );
    returnStatus = Openssl_Connect( &networkContext,
                                    NULL,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );

    /* Mock a DNS failure from the call to the sockets connect wrapper. */
    socketError = SOCKETS_DNS_FAILURE;
    expectedStatus = failFunctionFrom_Openssl_Connect( Sockets_Connect_fn, &socketError );
    returnStatus = Openssl_Connect( &networkContext,
                                    &serverInfo,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );

    /* Mock a connection failure from the call to the sockets connect wrapper. */
    socketError = SOCKETS_CONNECT_FAILURE;
    expectedStatus = failFunctionFrom_Openssl_Connect( Sockets_Connect_fn, &socketError );
    returnStatus = Openssl_Connect( &networkContext,
                                    NULL,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );

    /* Mock an unknown SOCKETS error for the default case in the switch. */
    socketError = SOCKETS_INSUFFICIENT_MEMORY;
    expectedStatus = failFunctionFrom_Openssl_Connect( Sockets_Connect_fn, &socketError );
    returnStatus = Openssl_Connect( &networkContext,
                                    NULL,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );

    returnStatus = Openssl_Connect( &networkContext,
                                    &serverInfo,
                                    NULL,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( OPENSSL_INVALID_PARAMETER, returnStatus );
}

/**
 * @brief Test that #Openssl_Connect is able to return an error when initializing
 * an OpenSSL object fails.
 */
void test_Openssl_Connect_Initializing_Objects_Fails( void )
{
    OpensslStatus_t returnStatus, expectedStatus;
    FunctionNames_t initializeFunctions[] = { SSL_CTX_new_fn, SSL_new_fn, SSL_set_fd_fn };
    uint16_t i;

    for( i = 0; i < sizeof( initializeFunctions ) / sizeof( FunctionNames_t ); i++ )
    {
        expectedStatus = failFunctionFrom_Openssl_Connect( initializeFunctions[ i ],
                                                           NULL );
        returnStatus = Openssl_Connect( &networkContext,
                                        &serverInfo,
                                        &opensslCredentials,
                                        SEND_RECV_TIMEOUT,
                                        SEND_RECV_TIMEOUT );
        TEST_ASSERT_EQUAL( expectedStatus, returnStatus );
    }
}

/**
 * @brief Test that #Openssl_Connect is able to return an error when setting
 * credentials such as keys and certificates for the TLS handshake.
 */
void test_Openssl_Connect_Setting_TLS_Credentials_Fails( void )
{
    OpensslStatus_t returnStatus, expectedStatus;
    FunctionNames_t credentialFunctions[] =
    {
        fopen_fn,               PEM_read_X509_fn,
        X509_STORE_add_cert_fn, SSL_CTX_use_certificate_chain_file_fn,
        SSL_CTX_use_PrivateKey_file_fn
    };
    uint16_t i;

    for( i = 0; i < sizeof( credentialFunctions ) / sizeof( FunctionNames_t ); i++ )
    {
        expectedStatus = failFunctionFrom_Openssl_Connect( credentialFunctions[ i ], NULL );
        returnStatus = Openssl_Connect( &networkContext,
                                        &serverInfo,
                                        &opensslCredentials,
                                        SEND_RECV_TIMEOUT,
                                        SEND_RECV_TIMEOUT );
        TEST_ASSERT_EQUAL( expectedStatus, returnStatus );
    }
}

/**
 * @brief Test that #Openssl_Connect is able to return an error when setting
 * extra configuration parameters for the TLS connection.
 */
void test_Openssl_Connect_Setting_TLS_Configurations_Fails( void )
{
    OpensslStatus_t returnStatus, expectedStatus;
    FunctionNames_t configFunctions[] =
    {
        SSL_set_alpn_protos_fn, SSL_set_max_send_fragment_fn,
        SSL_set_tlsext_host_name_fn
    };
    uint16_t i;

    for( i = 0; i < sizeof( configFunctions ) / sizeof( FunctionNames_t ); i++ )
    {
        expectedStatus = failFunctionFrom_Openssl_Connect( configFunctions[ i ], NULL );
        returnStatus = Openssl_Connect( &networkContext,
                                        &serverInfo,
                                        &opensslCredentials,
                                        SEND_RECV_TIMEOUT,
                                        SEND_RECV_TIMEOUT );
        TEST_ASSERT_EQUAL( expectedStatus, returnStatus );
    }
}

/**
 * @brief Test that #Openssl_Connect is able to return #OPENSSL_HANDSHAKE_FAILED
 * when failing to perform the TLS handshake.
 */
void test_Openssl_Connect_Handshake_Fails( void )
{
    OpensslStatus_t returnStatus, expectedStatus;
    FunctionNames_t connectFunctions[] =
    {
        SSL_set1_host_fn, SSL_connect_fn, SSL_get_verify_result_fn
    };
    uint16_t i;

    for( i = 0; i < sizeof( connectFunctions ) / sizeof( FunctionNames_t ); i++ )
    {
        expectedStatus = failFunctionFrom_Openssl_Connect( connectFunctions[ i ],
                                                           NULL );
        returnStatus = Openssl_Connect( &networkContext,
                                        &serverInfo,
                                        &opensslCredentials,
                                        SEND_RECV_TIMEOUT,
                                        SEND_RECV_TIMEOUT );
        TEST_ASSERT_EQUAL( expectedStatus, returnStatus );
    }
}

/**
 * @brief Cover cases in which TLS credentials and configuration parameters are
 * set to NULL.
 */
void test_Openssl_Connect_NULL_Members_In_Creds_And_Configs( void )
{
    OpensslStatus_t returnStatus, expectedStatus = OPENSSL_INVALID_CREDENTIALS;

    /* Coverage for NULL pRootCaPath. */
    memset( &opensslCredentials, 0, sizeof( OpensslCredentials_t ) );
    expectedStatus = failFunctionFrom_Openssl_Connect( SSL_get_verify_result_fn + 1,
                                                       NULL );
    returnStatus = Openssl_Connect( &networkContext,
                                    &serverInfo,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );

    /* Coverage for NULL pClientCertPath, pPrivateKeyPath, pAlpnProtos, sniHostName,
     * and maxFragmentLength == 0. */
    opensslCredentials.pRootCaPath = ROOT_CA_CERT_PATH;
    expectedStatus = failFunctionFrom_Openssl_Connect( SSL_get_verify_result_fn + 1,
                                                       NULL );
    returnStatus = Openssl_Connect( &networkContext,
                                    &serverInfo,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );

    /* Coverage for alpnProtosLen == 0. */
    opensslCredentials.pAlpnProtos = ALPN_PROTOS;
    expectedStatus = failFunctionFrom_Openssl_Connect( SSL_get_verify_result_fn + 1,
                                                       NULL );
    returnStatus = Openssl_Connect( &networkContext,
                                    &serverInfo,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );
}

/**
 * @brief Test the happy path case in which the TLS connection is established.
 */
void test_Openssl_Connect_Succeeds( void )
{
    OpensslStatus_t returnStatus;

    /* Set the parameter to one more that the max enum value of the function names
     * so that no functions fail for this happy path case. */
    ( void ) failFunctionFrom_Openssl_Connect( SSL_get_verify_result_fn + 1,
                                               NULL );
    returnStatus = Openssl_Connect( &networkContext,
                                    &serverInfo,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( OPENSSL_SUCCESS, returnStatus );
}

/**
 * @brief Test that #Openssl_Disconnect is able to return
 * #OPENSSL_INVALID_PARAMETER when #NetworkContext_t is NULL.
 */
void test_Openssl_Disconnect_NULL_Network_Context( void )
{
    OpensslStatus_t returnStatus;

    returnStatus = Openssl_Disconnect( NULL );
    TEST_ASSERT_EQUAL( OPENSSL_INVALID_PARAMETER, returnStatus );

    networkContext.pParams = NULL;
    returnStatus = Openssl_Disconnect( &networkContext );
    TEST_ASSERT_EQUAL( OPENSSL_INVALID_PARAMETER, returnStatus );
}

/**
 * @brief Test the happy path cases for #Openssl_Disconnect.
 */
void test_Openssl_Disconnect_Succeeds( void )
{
    OpensslStatus_t returnStatus;

    /* First, SSL object is NULL. */
    opensslParams.pSsl = NULL;
    Sockets_Disconnect_ExpectAnyArgsAndReturn( SOCKETS_SUCCESS );
    returnStatus = Openssl_Disconnect( &networkContext );
    TEST_ASSERT_EQUAL( OPENSSL_SUCCESS, returnStatus );

    /* Now, set SSL object for coverage. */
    networkContext.pParams = &opensslParams;
    opensslParams.pSsl = &ssl;
    SSL_shutdown_ExpectAnyArgsAndReturn( 0 );
    SSL_shutdown_ExpectAnyArgsAndReturn( 0 );
    SSL_free_ExpectAnyArgs();
    Sockets_Disconnect_ExpectAnyArgsAndReturn( SOCKETS_SUCCESS );
    returnStatus = Openssl_Disconnect( &networkContext );
    TEST_ASSERT_EQUAL( OPENSSL_SUCCESS, returnStatus );

    /* Coverage for the case in which the first SSL_shutdown fails. */
    opensslParams.pSsl = &ssl;
    SSL_shutdown_ExpectAnyArgsAndReturn( 1 );
    SSL_free_ExpectAnyArgs();
    Sockets_Disconnect_ExpectAnyArgsAndReturn( SOCKETS_SUCCESS );
    returnStatus = Openssl_Disconnect( &networkContext );
    TEST_ASSERT_EQUAL( OPENSSL_SUCCESS, returnStatus );
}

/**
 * @brief Test that #Openssl_Send is able to return that 0 bytes are sent over
 * the network stack when passing any invalid parameters.
 */
void test_Openssl_Send_Invalid_Params( void )
{
    int32_t bytesSent;

    bytesSent = Openssl_Send( NULL, opensslBuffer, BYTES_TO_SEND );
    TEST_ASSERT_EQUAL( -1, bytesSent );

    networkContext.pParams = NULL;
    bytesSent = Openssl_Send( &networkContext, opensslBuffer, BYTES_TO_SEND );
    TEST_ASSERT_EQUAL( -1, bytesSent );
    networkContext.pParams = &opensslParams;

    /* SSL object must not be NULL. Otherwise, no bytes are sent. */
    opensslParams.pSsl = NULL;
    bytesSent = Openssl_Send( &networkContext, opensslBuffer, BYTES_TO_SEND );
    TEST_ASSERT_EQUAL( -1, bytesSent );
    opensslParams.pSsl = &ssl;

    bytesSent = Openssl_Send( &networkContext, NULL, BYTES_TO_SEND );
    TEST_ASSERT_EQUAL( -1, bytesSent );

    bytesSent = Openssl_Send( &networkContext, opensslBuffer, 0 );
    TEST_ASSERT_EQUAL( -1, bytesSent );
}

/**
 * @brief Test the happy path case when #Openssl_Send is able to send all bytes
 * over the network stack successfully.
 */
void test_Openssl_Send_All_Bytes_Sent_Successfully( void )
{
    int32_t bytesSent;

    opensslParams.pSsl = &ssl;
    poll_ExpectAnyArgsAndReturn( 1 );
    SSL_write_ExpectAnyArgsAndReturn( BYTES_TO_SEND );
    bytesSent = Openssl_Send( &networkContext, opensslBuffer, BYTES_TO_SEND );
    TEST_ASSERT_EQUAL( BYTES_TO_SEND, bytesSent );
}

/**
 * @brief Test that #Openssl_Send returns an error when #SSL_write fails to send
 * data over the network stack.
 */
void test_Openssl_Send_Network_Error( void )
{
    int32_t bytesSent;

    opensslParams.pSsl = &ssl;
    poll_ExpectAnyArgsAndReturn( 1 );
    SSL_write_ExpectAnyArgsAndReturn( SSL_READ_WRITE_ERROR );

    /* Several errors can be returned from #SSL_get_error as mentioned here:
     * https://www.openssl.org/docs/man1.1.1/man3/SSL_get_error.html */
    SSL_get_error_ExpectAnyArgsAndReturn( SSL_ERROR_ZERO_RETURN );
    bytesSent = Openssl_Send( &networkContext, opensslBuffer, BYTES_TO_SEND );
    TEST_ASSERT_EQUAL( SSL_READ_WRITE_ERROR, bytesSent );
    TEST_ASSERT_TRUE( bytesSent < 0 );

    /* Test that a non-retryable zero error code is converted to -1 by the API. */
    poll_ExpectAnyArgsAndReturn( 1 );
    SSL_write_ExpectAnyArgsAndReturn( 0 );
    SSL_get_error_ExpectAnyArgsAndReturn( SSL_ERROR_ZERO_RETURN );
    bytesSent = Openssl_Send( &networkContext, opensslBuffer, BYTES_TO_SEND );
    TEST_ASSERT_EQUAL( -1, bytesSent );

    /* Test that a poll error results in the function under test returning -1. */
    poll_ExpectAnyArgsAndReturn( -1 );
    bytesSent = Openssl_Send( &networkContext, opensslBuffer, BYTES_TO_SEND );
    TEST_ASSERT_EQUAL( -1, bytesSent );
}

/**
 * @brief Test that #Openssl_Send returns 0 when `poll` returns 0.
 */
void test_Openssl_Send_Poll_No_Events( void )
{
    int32_t bytesSent;

    poll_ExpectAnyArgsAndReturn( 0 );
    bytesSent = Openssl_Send( &networkContext, opensslBuffer, BYTES_TO_SEND );
    TEST_ASSERT_EQUAL( 0, bytesSent );
}

/**
 * @brief Test that #Openssl_Recv is able to return that 0 bytes are received
 * from the network stack when passing any invalid parameters.
 */
void test_Openssl_Recv_Invalid_Params( void )
{
    int32_t bytesReceived;

    bytesReceived = Openssl_Recv( NULL, opensslBuffer, BYTES_TO_RECV );
    TEST_ASSERT_EQUAL( -1, bytesReceived );

    networkContext.pParams = NULL;
    bytesReceived = Openssl_Recv( &networkContext, opensslBuffer, BYTES_TO_RECV );
    TEST_ASSERT_EQUAL( -1, bytesReceived );
    networkContext.pParams = &opensslParams;

    /* SSL object must not be NULL. Otherwise, no bytes are sent. */
    opensslParams.pSsl = NULL;
    bytesReceived = Openssl_Recv( &networkContext, opensslBuffer, BYTES_TO_RECV );
    TEST_ASSERT_EQUAL( -1, bytesReceived );
    opensslParams.pSsl = &ssl;

    bytesReceived = Openssl_Recv( &networkContext, NULL, BYTES_TO_RECV );
    TEST_ASSERT_EQUAL( -1, bytesReceived );

    bytesReceived = Openssl_Recv( &networkContext, opensslBuffer, 0 );
    TEST_ASSERT_EQUAL( -1, bytesReceived );
}

/**
 * @brief Test the happy path case when #Openssl_Recv is able to receive all
 * expected bytes over the network stack successfully.
 */
void test_Openssl_Recv_All_Bytes_Received_Successfully( void )
{
    int32_t bytesReceived;

    /* No pending data from last read. */
    opensslParams.pSsl = &ssl;
    SSL_read_ExpectAnyArgsAndReturn( BYTES_TO_RECV );
    bytesReceived = Openssl_Recv( &networkContext, opensslBuffer, BYTES_TO_RECV );
    TEST_ASSERT_EQUAL( BYTES_TO_RECV, bytesReceived );

    /* Pending data from last read. */
    SSL_pending_ExpectAnyArgsAndReturn( BYTES_TO_RECV );
    SSL_read_ExpectAnyArgsAndReturn( 1U );
    bytesReceived = Openssl_Recv( &networkContext, opensslBuffer, 1U );
    TEST_ASSERT_EQUAL( 1U, bytesReceived );
}

/**
 * @brief Test that #Openssl_Recv returns an error when #SSL_read fails to
 * receive data over the network stack.
 */
void test_Openssl_Recv_Network_Error( void )
{
    int32_t bytesReceived;

    opensslParams.pSsl = &ssl;

    SSL_read_ExpectAnyArgsAndReturn( SSL_READ_WRITE_ERROR );
    /* SSL_ERROR_ZERO_RETURN means the peer has closed the connection. */
    SSL_get_error_ExpectAnyArgsAndReturn( SSL_ERROR_ZERO_RETURN );
    bytesReceived = Openssl_Recv( &networkContext, opensslBuffer, BYTES_TO_RECV );

    /* SSL_ERROR_WANT_READ implies there is no data to receive, so we expect
     * that no bytes have been received. */
    TEST_ASSERT_EQUAL( SSL_READ_WRITE_ERROR, bytesReceived );
    TEST_ASSERT_TRUE( bytesReceived < 0 );

    /* Test that a non-retryable zero error code is converted to -1 by the API. */
    SSL_read_ExpectAnyArgsAndReturn( 0 );
    SSL_get_error_ExpectAnyArgsAndReturn( SSL_ERROR_ZERO_RETURN );
    bytesReceived = Openssl_Recv( &networkContext, opensslBuffer, BYTES_TO_RECV );
    TEST_ASSERT_EQUAL( -1, bytesReceived );

    /* Test that a poll error results in the function under test returning -1. */
    SSL_pending_ExpectAnyArgsAndReturn( 0 );
    poll_ExpectAnyArgsAndReturn( -1 );
    bytesReceived = Openssl_Recv( &networkContext, opensslBuffer, 1U );
    TEST_ASSERT_EQUAL( -1, bytesReceived );
}

/**
 * @brief Test that #Openssl_Recv returns 0 when `poll` returns 0.
 */
void test_Openssl_Recv_Poll_No_Events( void )
{
    int32_t bytesReceived;

    SSL_pending_ExpectAnyArgsAndReturn( 0 );
    poll_ExpectAnyArgsAndReturn( 0 );
    bytesReceived = Openssl_Recv( &networkContext, opensslBuffer, 1U );
    TEST_ASSERT_EQUAL( 0, bytesReceived );
}

/**
 * @brief Test that #Openssl_Recv returns zero bytes sent when #SSL_read returns
 * an error to retry operation.
 */
void test_Openssl_Recv_Zero_Return_Value( void )
{
    int32_t bytesReceived;

    opensslParams.pSsl = &ssl;
    SSL_read_ExpectAnyArgsAndReturn( SSL_READ_WRITE_ERROR );

    /* Test when SSL_get_error() returns an SSL_ERROR_WANT_READ error. */
    SSL_get_error_ExpectAnyArgsAndReturn( SSL_ERROR_WANT_READ );
    bytesReceived = Openssl_Recv( &networkContext, opensslBuffer, BYTES_TO_RECV );
    TEST_ASSERT_EQUAL( 0, bytesReceived );
}

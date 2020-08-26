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

#define NUM_ADDR_INFO        3
#define SEND_RECV_TIMEOUT    0
#define HOSTNAME             "amazon.com"
#define PORT                 80
#define ROOT_CA_CERT_PATH    "fake/path"
#define CLIENT_CERT_PATH     "\\fake\\path"
#define PRIVATE_KEY_PATH     "/fake/path"
#define SOCKET_FD            5
#define MFLN                 42
#define ALPN_PROTOS          "x-amzn-mqtt-ca"

static ServerInfo_t serverInfo = { 0 };
static OpensslCredentials_t opensslCredentials = { 0 };
static NetworkContext_t networkContext = { 0 };

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

static OpensslStatus_t failFunctionFrom_Openssl_Connect( FunctionNames_t functionToFail,
                                                         void * retValue )
{
    OpensslStatus_t returnStatus = OPENSSL_SUCCESS;
    bool fileOpened = false,
         sslCtxCreated = false, sslCreated = false;
    SSL ssl;
    SSL_METHOD sslMethod;
    SSL_CTX sslCtx;
    FILE rootCaFile;
    X509 rootCa;
    X509_STORE CaStore;

    /* Depending on the function to fail,
     * this function must return the correct status to expect. */

    if( functionToFail == Sockets_Connect_fn )
    {
        TEST_ASSERT_NOT_NULL( retValue );
        SocketStatus_t socketStatus = *( ( SocketStatus_t * ) retValue );
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

    if( opensslCredentials.pRootCaPath != NULL )
    {
        /* SSL_CTX_set_mode is actually what the API uses, but CMock expects the
         * actual method rather than the macro wrapper. */
        if( returnStatus == OPENSSL_SUCCESS )
        {
            SSL_CTX_ctrl_ExpectAnyArgsAndReturn( 1 );
            getcwd_ExpectAnyArgsAndReturn( ROOT_CA_CERT_PATH );
            free_ExpectAnyArgs();
        }

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

    /* Fail Sockets_Connect(...) */

    /* NULL serverInfo is handled by Sockets_Connect, so we appropriately
     * return SOCKETS_INVALID_PARAMETER. */
    socketError = SOCKETS_INVALID_PARAMETER;
    expectedStatus = failFunctionFrom_Openssl_Connect( 0, &socketError );
    returnStatus = Openssl_Connect( &networkContext,
                                    NULL,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );

    /* Mock a DNS failure from the call to the sockets connect wrapper. */
    socketError = SOCKETS_DNS_FAILURE;
    expectedStatus = failFunctionFrom_Openssl_Connect( 0, &socketError );
    returnStatus = Openssl_Connect( &networkContext,
                                    &serverInfo,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );

    /* Mock a connection failure from the call to the sockets connect wrapper. */
    socketError = SOCKETS_CONNECT_FAILURE;
    expectedStatus = failFunctionFrom_Openssl_Connect( 0, &socketError );
    returnStatus = Openssl_Connect( &networkContext,
                                    NULL,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );

    /* Mock an unknown SOCKETS error for the default case in the switch. */
    socketError = SOCKETS_INSUFFICIENT_MEMORY;
    expectedStatus = failFunctionFrom_Openssl_Connect( 0, &socketError );
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

void test_Openssl_Connect_Invalid_Params( void )
{
}

void test_Openssl_Connect_Initializing_Objects_Fails( void )
{
    OpensslStatus_t returnStatus, expectedStatus;
    int i;
    uint8_t initializers[] = { SSL_CTX_new_fn, SSL_new_fn, SSL_set_fd_fn };

    for( i = 0; i < sizeof( initializers ); i++ )
    {
        expectedStatus = failFunctionFrom_Openssl_Connect( initializers[ i ],
                                                           NULL );
        returnStatus = Openssl_Connect( &networkContext,
                                        &serverInfo,
                                        &opensslCredentials,
                                        SEND_RECV_TIMEOUT,
                                        SEND_RECV_TIMEOUT );
        TEST_ASSERT_EQUAL( expectedStatus, returnStatus );
    }
}

void test_Openssl_Connect_Setting_TLS_Credentials_Fails( void )
{
    OpensslStatus_t returnStatus, expectedStatus;
    int i;

    for( i = fopen_fn; i <= SSL_CTX_use_PrivateKey_file_fn; i++ )
    {
        expectedStatus = failFunctionFrom_Openssl_Connect( i, NULL );
        returnStatus = Openssl_Connect( &networkContext,
                                        &serverInfo,
                                        &opensslCredentials,
                                        SEND_RECV_TIMEOUT,
                                        SEND_RECV_TIMEOUT );
        TEST_ASSERT_EQUAL( expectedStatus, returnStatus );
    }
}

void test_Openssl_Connect_Setting_TLS_Configurations_Fails( void )
{
    OpensslStatus_t returnStatus, expectedStatus;
    int i;

    for( i = SSL_set_alpn_protos_fn; i <= SSL_set_tlsext_host_name_fn; i++ )
    {
        expectedStatus = failFunctionFrom_Openssl_Connect( i, NULL );
        returnStatus = Openssl_Connect( &networkContext,
                                        &serverInfo,
                                        &opensslCredentials,
                                        SEND_RECV_TIMEOUT,
                                        SEND_RECV_TIMEOUT );
        TEST_ASSERT_EQUAL( expectedStatus, returnStatus );
    }
}

void test_Openssl_Connect_Handshake_Fails( void )
{
    OpensslStatus_t returnStatus, expectedStatus;
    int i;

    for( i = SSL_connect_fn; i <= SSL_get_verify_result_fn; i++ )
    {
        expectedStatus = failFunctionFrom_Openssl_Connect( i, NULL );
        returnStatus = Openssl_Connect( &networkContext,
                                        &serverInfo,
                                        &opensslCredentials,
                                        SEND_RECV_TIMEOUT,
                                        SEND_RECV_TIMEOUT );
        TEST_ASSERT_EQUAL( expectedStatus, returnStatus );
    }
}

void test_Openssl_Connect_Succeeds( void )
{
    OpensslStatus_t returnStatus, expectedStatus;

    /* Set the parameter to one more that the max enum value of the function names
     * so that no functions fail for this happy path case. */
    expectedStatus = failFunctionFrom_Openssl_Connect( SSL_get_verify_result_fn + 1,
                                                       NULL );
    returnStatus = Openssl_Connect( &networkContext,
                                    &serverInfo,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );
}

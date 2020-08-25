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

static ServerInfo_t serverInfo = { 0 };
static OpensslCredentials_t opensslCredentials = { 0 };
static NetworkContext_t networkContext = { 0 };

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

static OpensslStatus_t setClientCertificate_failNthMethod( int n,
                                                           int * start )
{
    int index = *start;

    *start = index;
}

static OpensslStatus_t failNthMethod_Openssl_Connect( int n,
                                                      void * retValue )
{
    OpensslStatus_t returnStatus = OPENSSL_SUCCESS;
    bool failed = false, fileOpened = false,
         sslCtxCreated = false, sslCreated = false;
    int index = 0;
    SSL ssl;
    SSL_METHOD sslMethod;
    SSL_CTX sslCtx;
    FILE rootCaFile;
    X509 rootCa;
    X509_STORE CaStore;

    /* If index matches n,
     * then we should fail and return the correct status to expect. */

    /* The index == 0. */
    if( index == n )
    {
        TEST_ASSERT_NOT_NULL( retValue );
        SocketStatus_t socketStatus = *( ( SocketStatus_t * ) retValue );
        Sockets_Connect_ExpectAnyArgsAndReturn( socketStatus );
        returnStatus = convertToOpensslStatus( socketStatus );
        failed = true;
    }
    else
    {
        if( !failed )
        {
            Sockets_Connect_ExpectAnyArgsAndReturn( SOCKETS_SUCCESS );
        }
    }

    index++;

    /* The index == 1, but this call can't fail no matter what you return. */
    if( !failed )
    {
        TLS_client_method_ExpectAndReturn( &sslMethod );
    }

    index++;

    /* The index == 2. */
    if( index == n )
    {
        SSL_CTX_new_ExpectAnyArgsAndReturn( ( SSL_CTX * ) retValue );
        returnStatus = OPENSSL_API_ERROR;
        failed = true;
    }
    else
    {
        if( !failed )
        {
            SSL_CTX_new_ExpectAnyArgsAndReturn( &sslCtx );
            sslCtxCreated = true;
        }
    }

    index++;

    /* The index == 3, but these calls can't fail. */

    if( opensslCredentials.pRootCaPath != NULL )
    {
        /* SSL_CTX_set_mode is actually what the API uses, but CMock expects the
         * actual method rather than the method wrapper. */
        if( !failed )
        {
            SSL_CTX_ctrl_ExpectAnyArgsAndReturn( 1 );
            getcwd_ExpectAnyArgsAndReturn( ROOT_CA_CERT_PATH );
            free_ExpectAnyArgs();
        }

        index++;

        /* The index == 4. */
        if( index == n )
        {
            fopen_ExpectAnyArgsAndReturn( NULL );
            returnStatus = OPENSSL_INVALID_CREDENTIALS;
            failed = true;
        }
        else
        {
            if( !failed )
            {
                fopen_ExpectAnyArgsAndReturn( &rootCaFile );
                fileOpened = true;
            }
        }

        index++;

        /* The index == 5. */
        if( index == n )
        {
            PEM_read_X509_ExpectAnyArgsAndReturn( NULL );
            returnStatus = OPENSSL_INVALID_CREDENTIALS;
            failed = true;
        }
        else
        {
            if( !failed )
            {
                PEM_read_X509_ExpectAnyArgsAndReturn( &rootCa );
            }
        }

        index++;

        /* The index == 6. */
        if( !failed )
        {
            SSL_CTX_get_cert_store_ExpectAnyArgsAndReturn( &CaStore );
        }

        index++;

        /* The index == 7. */
        if( index == n )
        {
            X509_STORE_add_cert_ExpectAnyArgsAndReturn( -1 );
            returnStatus = OPENSSL_INVALID_CREDENTIALS;
            failed = true;
        }
        else
        {
            if( !failed )
            {
                X509_STORE_add_cert_ExpectAnyArgsAndReturn( 1 );
            }
        }

        index++;

        if( fileOpened )
        {
            fclose_ExpectAnyArgsAndReturn( 0 );
        }
    }

    if( opensslCredentials.pClientCertPath != NULL )
    {
        /* The index == 8. */
        if( index == n )
        {
            SSL_CTX_use_certificate_chain_file_ExpectAnyArgsAndReturn( -1 );
            returnStatus = OPENSSL_INVALID_CREDENTIALS;
            failed = true;
        }
        else
        {
            if( !failed )
            {
                SSL_CTX_use_certificate_chain_file_ExpectAnyArgsAndReturn( 1 );
            }
        }

        index++;
    }

    if( opensslCredentials.pPrivateKeyPath != NULL )
    {
        /* The index == 9. */
        if( index == n )
        {
            SSL_CTX_use_PrivateKey_file_ExpectAnyArgsAndReturn( -1 );
            returnStatus = OPENSSL_INVALID_CREDENTIALS;
            failed = true;
        }
        else
        {
            if( !failed )
            {
                SSL_CTX_use_PrivateKey_file_ExpectAnyArgsAndReturn( 1 );
            }
        }

        index++;
    }

    /* The index == 10. */
    if( index == n )
    {
        SSL_new_ExpectAnyArgsAndReturn( NULL );
        returnStatus = OPENSSL_API_ERROR;
        failed = true;
    }
    else
    {
        if( !failed )
        {
            SSL_new_ExpectAnyArgsAndReturn( &ssl );
            sslCreated = true;
        }
    }

    index++;

    /* The index == 11. */
    if( !failed )
    {
        SSL_set_verify_ExpectAnyArgs();
    }

    index++;

    /* The index == 12. */
    if( index == n )
    {
        SSL_set_fd_ExpectAnyArgsAndReturn( -1 );
        returnStatus = OPENSSL_API_ERROR;
        failed = true;
    }
    else
    {
        if( !failed )
        {
            SSL_set_fd_ExpectAnyArgsAndReturn( 1 );
        }
    }

    index++;

    if( ( opensslCredentials.pAlpnProtos != NULL ) &&
        ( opensslCredentials.alpnProtosLen > 0 ) )
    {
        if( index == n )
        {
            SSL_set_alpn_protos_ExpectAnyArgsAndReturn( 1 );
            returnStatus = OPENSSL_API_ERROR;
            failed = true;
        }
        else
        {
            if( !failed )
            {
                SSL_set_alpn_protos_ExpectAnyArgsAndReturn( 0 );
            }
        }
    }

    if( opensslCredentials.maxFragmentLength > 0 )
    {
        if( index == n )
        {
            SSL_ctrl_ExpectAnyArgsAndReturn( -1 );
            returnStatus = OPENSSL_API_ERROR;
            failed = true;
        }
        else
        {
            if( !failed )
            {
                SSL_ctrl_ExpectAnyArgsAndReturn( 1 );
            }
        }

        if( !failed )
        {
            SSL_set_default_read_buffer_len_ExpectAnyArgs();
        }
    }

    if( opensslCredentials.sniHostName > 0 )
    {
        if( index == n )
        {
            SSL_ctrl_ExpectAnyArgsAndReturn( -1 );
            returnStatus = OPENSSL_API_ERROR;
            failed = true;
        }
        else
        {
            if( !failed )
            {
                SSL_ctrl_ExpectAnyArgsAndReturn( 1 );
            }
        }
    }

    /* The index == 13. */
    if( index == n )
    {
        SSL_connect_ExpectAnyArgsAndReturn( -1 );
        returnStatus = OPENSSL_API_ERROR;
        failed = true;
    }
    else
    {
        if( !failed )
        {
            SSL_connect_ExpectAnyArgsAndReturn( 1 );
        }
    }

    index++;

    /* The index == 14. */
    if( index == n )
    {
        SSL_get_verify_result_ExpectAnyArgsAndReturn( -1 );
        returnStatus = OPENSSL_API_ERROR;
        failed = true;
    }
    else
    {
        if( !failed )
        {
            SSL_get_verify_result_ExpectAnyArgsAndReturn( X509_V_OK );
        }
    }

    index++;

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
    expectedStatus = failNthMethod_Openssl_Connect( 0, &socketError );
    returnStatus = Openssl_Connect( &networkContext,
                                    NULL,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );

    /* Suppose a DNS failure occurs from the call to the sockets connect wrapper. */
    socketError = SOCKETS_DNS_FAILURE;
    expectedStatus = failNthMethod_Openssl_Connect( 0, &socketError );
    returnStatus = Openssl_Connect( &networkContext,
                                    &serverInfo,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );

    /* Suppose a connection failure occurs from the call to the sockets connect wrapper. */
    socketError = SOCKETS_CONNECT_FAILURE;
    expectedStatus = failNthMethod_Openssl_Connect( 0, &socketError );
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

void test_Openssl_Connect_API_calls_fail( void )
{
    OpensslStatus_t returnStatus, expectedStatus;

    /* Fail SSL_CTX_new(...) */
    expectedStatus = failNthMethod_Openssl_Connect( 2, NULL );
    returnStatus = Openssl_Connect( &networkContext,
                                    &serverInfo,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );

    /* Fail fopen(...) */
    expectedStatus = failNthMethod_Openssl_Connect( 4, NULL );
    returnStatus = Openssl_Connect( &networkContext,
                                    &serverInfo,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );

    /* Fail fopen(...) */
    expectedStatus = failNthMethod_Openssl_Connect( 4, NULL );
    returnStatus = Openssl_Connect( &networkContext,
                                    &serverInfo,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );

    /* Fail PEM_read_X509(...). */
    expectedStatus = failNthMethod_Openssl_Connect( 5, NULL );
    returnStatus = Openssl_Connect( &networkContext,
                                    &serverInfo,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );

    /* Fail PEM_read_X509(...) but fail fclose(...) for coverage. */

    /*expectedStatus = failNthMethod_Openssl_Connect( 5, NULL );
     * fclose_ExpectAnyArgsAndReturn( -1 );
     * returnStatus = Openssl_Connect( &networkContext,
     *                              &serverInfo,
     *                              &opensslCredentials,
     *                              SEND_RECV_TIMEOUT,
     *                              SEND_RECV_TIMEOUT );
     * TEST_ASSERT_EQUAL( expectedStatus, returnStatus );*/

    /* Fail X509_STORE_add_cert(...). */
    expectedStatus = failNthMethod_Openssl_Connect( 7, NULL );
    returnStatus = Openssl_Connect( &networkContext,
                                    &serverInfo,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );

    expectedStatus = failNthMethod_Openssl_Connect( 8, NULL );
    returnStatus = Openssl_Connect( &networkContext,
                                    &serverInfo,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );

    expectedStatus = failNthMethod_Openssl_Connect( 9, NULL );
    returnStatus = Openssl_Connect( &networkContext,
                                    &serverInfo,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );

    expectedStatus = failNthMethod_Openssl_Connect( 10, NULL );
    returnStatus = Openssl_Connect( &networkContext,
                                    &serverInfo,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );

    expectedStatus = failNthMethod_Openssl_Connect( 11, NULL );
    returnStatus = Openssl_Connect( &networkContext,
                                    &serverInfo,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );
}

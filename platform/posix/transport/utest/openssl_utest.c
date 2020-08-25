#include <string.h>
#include <stdbool.h>
#include <stdlib.h>
#include "/usr/include/errno.h"

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "openssl_posix.h"

#include "mock_netdb.h"
#include "mock_socket.h"
#include "mock_inet.h"
#include "mock_openssl_api.h"
#include "mock_sockets_posix.h"
#include "mock_stdio_api.h"

#define NUM_ADDR_INFO        3
#define SEND_RECV_TIMEOUT    0
#define HOSTNAME             "amazon.com"
#define PORT                 80
#define ROOT_CA_CERT_PATH    "fake/path"
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

static OpensslStatus_t failNthExpectedMethodFromConnect( int n,
                                                         void * retValue )
{
    int index = 0;
    SSL_METHOD sslMethod;
    SSL_CTX sslCtx;
    FILE rootCaFile;
    X509 rootCa;
    X509_STORE CaStore;

    /* If index matches n,
     * then we should fail and return the correct status to expect. */
    if( index == n )
    {
        TEST_ASSERT_NOT_NULL( retValue );
        SocketStatus_t socketStatus = *( ( SocketStatus_t * ) retValue );
        Sockets_Connect_ExpectAnyArgsAndReturn( socketStatus );
        return convertToOpensslStatus( socketStatus );
    }
    else
    {
        Sockets_Connect_ExpectAnyArgsAndReturn( SOCKETS_SUCCESS );
        index++;
    }

    TLS_client_method_ExpectAndReturn( &sslMethod );
    index++;

    if( index == n )
    {
        SSL_CTX_new_ExpectAnyArgsAndReturn( ( SSL_CTX * ) retValue );
        return OPENSSL_API_ERROR;
    }
    else
    {
        SSL_CTX_new_ExpectAnyArgsAndReturn( &sslCtx );
        index++;
    }

    SSL_CTX_set_mode_ExpectAnyArgsAndReturn( 1 );
    index++;

    if( index == n )
    {
        fopen_ExpectAnyArgsAndReturn( NULL );
        return OPENSSL_INVALID_CREDENTIALS;
    }
    else
    {
        fopen_ExpectAnyArgsAndReturn( &rootCaFile );
        index++;
    }

    if( index == n )
    {
        PEM_read_X509_ExpectAnyArgsAndReturn( NULL );
        return OPENSSL_INVALID_CREDENTIALS;
    }
    else
    {
        PEM_read_X509_ExpectAnyArgsAndReturn( &rootCa );
        index++;
    }

    SSL_CTX_get_cert_store_ExpectAnyArgsAndReturn( &CaStore );
    index++;

    if( index == n )
    {
        X509_STORE_add_cert_ExpectAnyArgsAndReturn( -1 );
        return OPENSSL_INVALID_CREDENTIALS;
    }
    else
    {
        X509_STORE_add_cert_ExpectAnyArgsAndReturn( 1 );
        index++;
    }
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
    expectedStatus = failNthExpectedMethodFromConnect( 0, &socketError );
    returnStatus = Openssl_Connect( &networkContext,
                                    NULL,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );

    /* Suppose a DNS failure occurs from the call to the sockets connect wrapper. */
    socketError = SOCKETS_DNS_FAILURE;
    expectedStatus = failNthExpectedMethodFromConnect( 0, &socketError );
    returnStatus = Openssl_Connect( &networkContext,
                                    &serverInfo,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );

    /* Suppose a connection failure occurs from the call to the sockets connect wrapper. */
    socketError = SOCKETS_CONNECT_FAILURE;
    expectedStatus = failNthExpectedMethodFromConnect( 0, &socketError );
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
    expectedStatus = failNthExpectedMethodFromConnect( 2, NULL );
    returnStatus = Openssl_Connect( &networkContext,
                                    &serverInfo,
                                    &opensslCredentials,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( expectedStatus, returnStatus );
}

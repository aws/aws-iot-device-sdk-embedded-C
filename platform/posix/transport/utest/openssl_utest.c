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

#define NUM_ADDR_INFO        3
#define SEND_RECV_TIMEOUT    0
#define HOSTNAME             "amazon.com"
#define PORT                 80
#define ROOT_CA_CERT_PATH    "fake/path"
#define SOCKET_FD            5

static ServerInfo_t serverInfo = { 0 };
static OpensslCredentials_t opensslCredentials = { 0 };
static NetworkContext_t networkContext = { 0 };

static void (* func_ptr[])() =
{
    Sockets_Connect_ExpectAnyArgsAndReturn,
    TLS_client_method_ExpectAndReturn,
    SSL_CTX_new_ExpectAnyArgsAndReturn
};

static void * successReturnVal[] =
{
    SOCKETS_SUCCESS
    NULL,
    NULL
};

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

static void failNthExpectedMethodFromConnect( int index )
{
}

void test_Openssl_Connect_Invalid_Params( void )
{
    OpensslStatus_t opensslStatus;

    opensslStatus = Openssl_Connect( NULL,
                                     &serverInfo,
                                     &opensslCredentials,
                                     SEND_RECV_TIMEOUT,
                                     SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( OPENSSL_INVALID_PARAMETER, opensslStatus );

    /* NULL serverInfo is handled by Sockets_Connect, so we appropriately
     * return SOCKETS_INVALID_PARAMETER. */
    Sockets_Connect_ExpectAnyArgsAndReturn( SOCKETS_INVALID_PARAMETER );
    opensslStatus = Openssl_Connect( &networkContext,
                                     NULL,
                                     &opensslCredentials,
                                     SEND_RECV_TIMEOUT,
                                     SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( OPENSSL_INVALID_PARAMETER, opensslStatus );

    opensslStatus = Openssl_Connect( &networkContext,
                                     &serverInfo,
                                     NULL,
                                     SEND_RECV_TIMEOUT,
                                     SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( OPENSSL_INVALID_PARAMETER, opensslStatus );
}

void test_Openssl_Connect_SSL_CTX_new_fails( void )
{
    OpensslStatus_t opensslStatus;

    Sockets_Connect_ExpectAnyArgsAndReturn( SOCKETS_SUCCESS );
    TLS_client_method_ExpectAndReturn( NULL );
    SSL_CTX_new_ExpectAnyArgsAndReturn( NULL );
    opensslStatus = Openssl_Connect( &networkContext,
                                     &serverInfo,
                                     &opensslCredentials,
                                     SEND_RECV_TIMEOUT,
                                     SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( OPENSSL_API_ERROR, opensslStatus );
}

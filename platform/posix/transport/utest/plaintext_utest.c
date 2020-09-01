#include <string.h>
#include <stdbool.h>
#include <stdlib.h>
#include <errno.h>

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "plaintext_posix.h"

#include "mock_sockets_posix.h"
#include "mock_stdio_api.h"
#include "mock_socket.h"

/* The send and receive timeout to set for the socket. */
#define SEND_RECV_TIMEOUT    0

/* The host and port from which to establish the connection. */
#define HOSTNAME             "amazon.com"
#define PORT                 80

/* Parameters to pass to #Plaintext_Send and #Plaintext_Recv. */
#define BYTES_TO_SEND        4
#define BYTES_TO_RECV        4

/* The size of the buffer passed to #Plaintext_Send and #Plaintext_Recv. */
#define BUFFER_LEN           4

/* An unknown transport status for the default case. */
#define UNKNOWN_ERRNO        42

/* The error returned from #send or #recv. */
#define SEND_RECV_ERROR      -1

static ServerInfo_t serverInfo;
static NetworkContext_t networkContext;
static uint8_t plaintextBuffer[ BUFFER_LEN ] = { 0 };

/* Possible transport status codes referencing the ones from #errno.h. The last
 * one is used for the default case. */
static uint8_t errorNumbers[] =
{
    EBADF,     ECONNRESET,  EDESTADDRREQ, EINTR,
    EINVAL,    ENOTCONN,    ENOTSOCK,     EOPNOTSUPP,
    ETIMEDOUT, EMSGSIZE,    EPIPE,
    EAGAIN,    EWOULDBLOCK, UNKNOWN_ERRNO
};

/* ============================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
    serverInfo.pHostName = HOSTNAME;
    serverInfo.hostNameLength = strlen( HOSTNAME );
    serverInfo.port = PORT;
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
 * @brief Test that #Plaintext_Connect forwards the status from #Sockets_Connect.
 *
 * @note #Plaintext_Connect is just a wrapper function to #Sockets_Connect.
 */
void test_Plaintext_Connect_Forwards_From_Sockets_Connect( void )
{
    SocketStatus_t socketStatus;

    Sockets_Connect_ExpectAnyArgsAndReturn( SOCKETS_SUCCESS );
    socketStatus = Plaintext_Connect( &networkContext,
                                      &serverInfo,
                                      SEND_RECV_TIMEOUT,
                                      SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( SOCKETS_SUCCESS, socketStatus );
}

/**
 * @brief Test that #Plaintext_Disconnect forwards the status from #Sockets_Disconnect.
 *
 * @note #Plaintext_Disconnect is just a wrapper function to #Sockets_Disconnect.
 */
void test_Plaintext_Disconnect_Forwards_From_Sockets_Disconnect( void )
{
    SocketStatus_t socketStatus;

    Sockets_Disconnect_ExpectAnyArgsAndReturn( SOCKETS_SUCCESS );
    socketStatus = Plaintext_Disconnect( &networkContext );
    TEST_ASSERT_EQUAL( SOCKETS_SUCCESS, socketStatus );
}

/**
 * @brief Test that #Plaintext_Recv returns an error when #recv fails to
 * receive data over the network stack.
 */
void test_Plaintext_Recv_All_Bytes_Received_Successfully( void )
{
    int32_t bytesReceived;

    recv_ExpectAnyArgsAndReturn( BYTES_TO_RECV );
    bytesReceived = Plaintext_Recv( &networkContext,
                                    plaintextBuffer,
                                    BYTES_TO_RECV );
    TEST_ASSERT_EQUAL( BYTES_TO_RECV, bytesReceived );
}

/**
 * @brief Test that #Plaintext_Recv returns an error when #recv receives
 * zero bytes from #recv implying that the peer has closed the connection.
 */
void test_Plaintext_Recv_Zero_Bytes_Received( void )
{
    int32_t bytesReceived;

    recv_ExpectAnyArgsAndReturn( 0 );
    bytesReceived = Plaintext_Recv( &networkContext,
                                    plaintextBuffer,
                                    BYTES_TO_RECV );
    TEST_ASSERT_EQUAL( SEND_RECV_ERROR, bytesReceived );
}

/**
 * @brief Test that #Plaintext_Recv returns an error when #recv fails to
 * receive data over the network stack.
 */
void test_Plaintext_Recv_Network_Error( void )
{
    int32_t bytesReceived;
    uint8_t i;

    for( i = 0; i < sizeof( errorNumbers ); i++ )
    {
        recv_ExpectAnyArgsAndReturn( SEND_RECV_ERROR );
        errno = errorNumbers[ i ];
        bytesReceived = Plaintext_Recv( &networkContext,
                                        plaintextBuffer,
                                        BYTES_TO_RECV );

        /* EAGAIN / EWOULDBLOCK imply no data to receive. */
        if( ( errno == EAGAIN ) || ( errno == EWOULDBLOCK ) )
        {
            TEST_ASSERT_EQUAL( 0, bytesReceived );
        }
        else
        {
            TEST_ASSERT_EQUAL( SEND_RECV_ERROR, bytesReceived );
        }
    }
}

/**
 * @brief Test the happy path case when #Plaintext_Send is able to send all bytes
 * over the network stack successfully.
 */
void test_Plaintext_Send_All_Bytes_Sent_Successfully( void )
{
    int32_t bytesSent;

    send_ExpectAnyArgsAndReturn( BYTES_TO_SEND );
    bytesSent = Plaintext_Send( &networkContext,
                                plaintextBuffer,
                                BYTES_TO_SEND );
    TEST_ASSERT_EQUAL( BYTES_TO_SEND, bytesSent );
}

/**
 * @brief Test that #Plaintext_Send returns an error when #send fails to send
 * data over the network stack.
 */
void test_Plaintext_Send_Network_Error( void )
{
    int32_t bytesSent;
    uint8_t i;

    for( i = 0; i < sizeof( errorNumbers ); i++ )
    {
        send_ExpectAnyArgsAndReturn( SEND_RECV_ERROR );
        errno = errorNumbers[ i ];
        bytesSent = Plaintext_Send( &networkContext,
                                    plaintextBuffer,
                                    BYTES_TO_SEND );

        /* EAGAIN / EWOULDBLOCK imply no data to send. */
        if( ( errno == EAGAIN ) || ( errno == EWOULDBLOCK ) )
        {
            TEST_ASSERT_EQUAL( 0, bytesSent );
        }
        else
        {
            TEST_ASSERT_EQUAL( SEND_RECV_ERROR, bytesSent );
        }
    }
}

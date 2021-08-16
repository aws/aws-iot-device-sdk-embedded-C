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
#include "plaintext_posix.h"

#include "mock_sockets_posix.h"
#include "mock_stdio_api.h"
#include "mock_poll.h"
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

/* Each compilation unit must define the NetworkContext struct. */
struct NetworkContext
{
    PlaintextParams_t * pParams;
};

static ServerInfo_t serverInfo = { 0 };
static NetworkContext_t networkContext = { 0 };
static PlaintextParams_t plaintextParams = { 0 };
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

    networkContext.pParams = &plaintextParams;
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
 * @brief Test that a NULL network context returns an error.
 */
void test_Plaintext_Connect_Invalid_Params( void )
{
    SocketStatus_t socketStatus = SOCKETS_SUCCESS;
    NetworkContext_t networkContext = { 0 };

    socketStatus = Plaintext_Connect( NULL,
                                      &serverInfo,
                                      SEND_RECV_TIMEOUT,
                                      SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( SOCKETS_INVALID_PARAMETER, socketStatus );

    networkContext.pParams = NULL;
    socketStatus = Plaintext_Connect( &networkContext,
                                      &serverInfo,
                                      SEND_RECV_TIMEOUT,
                                      SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( SOCKETS_INVALID_PARAMETER, socketStatus );
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
 * @brief Test that a NULL network context returns an error.
 */
void test_Plaintext_Disconnect_Invalid_Params( void )
{
    SocketStatus_t socketStatus = SOCKETS_SUCCESS;
    NetworkContext_t networkContext = { 0 };

    socketStatus = Plaintext_Disconnect( NULL );
    TEST_ASSERT_EQUAL( SOCKETS_INVALID_PARAMETER, socketStatus );

    networkContext.pParams = NULL;
    socketStatus = Plaintext_Disconnect( &networkContext );
    TEST_ASSERT_EQUAL( SOCKETS_INVALID_PARAMETER, socketStatus );
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
 * @brief Test that #Plaintext_Recv returns 0 bytes when the socket has no activity.
 */
void test_Plaintext_Recv_Socket_Timeout( void )
{
    int32_t bytesReceived;

    poll_ExpectAnyArgsAndReturn( 0 );
    bytesReceived = Plaintext_Recv( &networkContext,
                                    plaintextBuffer,
                                    1U );
    TEST_ASSERT_EQUAL( 0, bytesReceived );
}

/**
 * @brief Test that #Plaintext_Recv returns an error when calling #select on the
 * socket fails.
 */
void test_Plaintext_Recv_Poll_Error( void )
{
    int32_t bytesReceived;

    poll_ExpectAnyArgsAndReturn( -1 );
    bytesReceived = Plaintext_Recv( &networkContext,
                                    plaintextBuffer,
                                    1U );
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

        TEST_ASSERT_EQUAL( SEND_RECV_ERROR, bytesReceived );
    }
}

/**
 * @brief Test the happy path case when #Plaintext_Send is able to send all bytes
 * over the network stack successfully.
 */
void test_Plaintext_Send_All_Bytes_Sent_Successfully( void )
{
    int32_t bytesSent;

    poll_ExpectAnyArgsAndReturn( 1 );
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
        poll_ExpectAnyArgsAndReturn( 1 );
        send_ExpectAnyArgsAndReturn( SEND_RECV_ERROR );
        errno = errorNumbers[ i ];
        bytesSent = Plaintext_Send( &networkContext,
                                    plaintextBuffer,
                                    BYTES_TO_SEND );

        TEST_ASSERT_EQUAL( SEND_RECV_ERROR, bytesSent );
    }
}

/**
 * @brief Test that #Plaintext_Send returns an error when #send receives
 * zero bytes from #send implying that the peer has closed the connection.
 */
void test_Plaintext_Send_Zero_Bytes_Received( void )
{
    int32_t bytesSent;

    poll_ExpectAnyArgsAndReturn( 1 );
    send_ExpectAnyArgsAndReturn( 0 );
    bytesSent = Plaintext_Send( &networkContext,
                                plaintextBuffer,
                                BYTES_TO_SEND );
    TEST_ASSERT_EQUAL( SEND_RECV_ERROR, bytesSent );
}

/**
 * @brief Test that #Plaintext_Send returns 0 bytes when the socket has no activity.
 */
void test_Plaintext_Send_Socket_Timeout( void )
{
    int32_t bytesSent;

    poll_ExpectAnyArgsAndReturn( 0 );
    bytesSent = Plaintext_Send( &networkContext,
                                plaintextBuffer,
                                BYTES_TO_SEND );
    TEST_ASSERT_EQUAL( 0, bytesSent );
}

/**
 * @brief Test that #Plaintext_Send returns an error when calling #select on the
 * socket fails.
 */
void test_Plaintext_Send_Poll_Error( void )
{
    int32_t bytesSent;

    poll_ExpectAnyArgsAndReturn( -1 );
    bytesSent = Plaintext_Send( &networkContext,
                                plaintextBuffer,
                                BYTES_TO_SEND );
    TEST_ASSERT_EQUAL( SEND_RECV_ERROR, bytesSent );
}

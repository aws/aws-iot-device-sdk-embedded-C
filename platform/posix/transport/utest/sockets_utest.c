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
#include "sockets_posix.h"

#include "mock_netdb.h"
#include "mock_socket.h"
#include "mock_inet.h"
#include "mock_unistd_api.h"
#include "mock_stdio_api.h"

/* The number of #addrinfo objects to create in the linked list. */
#define NUM_ADDR_INFO        3

/* The send and receive timeout to set for the socket. */
#define SEND_RECV_TIMEOUT    0

/* The host and port from which to establish the connection. */
#define HOSTNAME             "amazon.com"
#define PORT                 80

static struct addrinfo * addrInfo;
static ServerInfo_t serverInfo;

/**
 * @brief Allocate a linked list that mocks a set of DNS records returned from
 * a call to #getaddrinfo.
 *
 * @param[in] head The first entry of the linked list.
 */
static void allocateAddrInfoLinkedList( struct addrinfo ** head )
{
    struct addrinfo * index = NULL, * next = NULL;
    struct sockaddr * ai_addr = NULL;
    uint16_t i;

    TEST_ASSERT_NOT_NULL( head );

    for( i = 0; i < NUM_ADDR_INFO; i++ )
    {
        next = malloc( sizeof( struct addrinfo ) );
        memset( next, 0, sizeof( struct addrinfo ) );
        next->ai_family = AF_UNSPEC;
        next->ai_socktype = SOCK_STREAM;
        next->ai_protocol = IPPROTO_TCP;
        next->ai_next = NULL;

        /* Every other IP address will be IPv4 for coverage. */
        ai_addr = malloc( sizeof( struct sockaddr ) );

        if( i % 2 )
        {
            ai_addr->sa_family = AF_INET6;
        }
        else
        {
            ai_addr->sa_family = AF_INET;
        }

        next->ai_addr = ai_addr;

        if( i == 0 )
        {
            index = next;
            *head = index;
        }
        else
        {
            index->ai_next = next;
            index = index->ai_next;
        }
    }
}

/**
 * @brief Deallocate the linked list created by a call to #allocateAddrInfoLinkedList.
 *
 * @param[in] head The first entry of the linked list.
 */
static void freeAddrInfoLinkedList( struct addrinfo * head )
{
    struct addrinfo * tmp;

    TEST_ASSERT_NOT_NULL( head );

    while( head != NULL )
    {
        tmp = head;
        head = head->ai_next;
        free( tmp );
        free( tmp->ai_addr );
    }
}

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
    allocateAddrInfoLinkedList( &addrInfo );
}

/* Called at the end of the whole suite. */
int suiteTearDown( int numFailures )
{
    freeAddrInfoLinkedList( addrInfo );
    return numFailures;
}

/* ========================================================================== */

/**
 * @brief Expect any methods called from #Sockets_Connect.
 *
 * @param[in] connectSuccessIndex The index at which the #connect function succeeds.
 */
static void expectSocketsConnectCalls( int32_t connectSuccessIndex )
{
    uint16_t i;

    TEST_ASSERT_TRUE( connectSuccessIndex <= NUM_ADDR_INFO );

    getaddrinfo_ExpectAnyArgsAndReturn( 0 );
    getaddrinfo_ReturnThruPtr___pai( &addrInfo );

    for( i = 1; i <= NUM_ADDR_INFO; i++ )
    {
        /* Fail the first socket() call for coverage. */
        if( i == 1 )
        {
            socket_ExpectAnyArgsAndReturn( -1 );
            continue;
        }
        else
        {
            socket_ExpectAnyArgsAndReturn( 1 );
        }

        inet_ntop_ExpectAnyArgsAndReturn( NULL );

        /* The last iteration should make connect() succeed. */
        if( i == connectSuccessIndex )
        {
            connect_ExpectAnyArgsAndReturn( 0 );
            break;
        }
        else
        {
            connect_ExpectAnyArgsAndReturn( -1 );
            close_ExpectAnyArgsAndReturn( 0 );
        }
    }

    freeaddrinfo_ExpectAnyArgs();
}

/**
 * @brief Test that #Sockets_Disconnect succeeds when a valid socket is passed.
 */
void test_Sockets_Disconnect_Valid_Socket( void )
{
    SocketStatus_t socketStatus;
    int tcpSocket = 1;

    shutdown_ExpectAnyArgsAndReturn( 0 );
    close_ExpectAnyArgsAndReturn( 0 );

    socketStatus = Sockets_Disconnect( tcpSocket );
    TEST_ASSERT_EQUAL( SOCKETS_SUCCESS, socketStatus );
}

/**
 * @brief Test that #Sockets_Disconnect fails when an invalid socket (non-positive)
 * is passed.
 */
void test_Sockets_Disconnect_Invalid_Socket( void )
{
    SocketStatus_t socketStatus;
    int tcpSocket = 0;

    socketStatus = Sockets_Disconnect( tcpSocket );
    TEST_ASSERT_EQUAL( SOCKETS_INVALID_PARAMETER, socketStatus );
}

/**
 * @brief Test that #Sockets_Connect fails when invalid parameters are passed
 * to the function.
 */
void test_Sockets_Connect_Invalid_Params( void )
{
    SocketStatus_t socketStatus;
    int tcpSocket = 1;

    /* Passing a NULL socket should fail. */
    socketStatus = Sockets_Connect( NULL,
                                    &serverInfo,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( SOCKETS_INVALID_PARAMETER, socketStatus );

    /* Passing a NULL #ServerInfo_t object should fail. */
    socketStatus = Sockets_Connect( &tcpSocket,
                                    NULL,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( SOCKETS_INVALID_PARAMETER, socketStatus );

    /* Passing a NULL hostName should fail. */
    memset( &serverInfo, 0, sizeof( ServerInfo_t ) );
    socketStatus = Sockets_Connect( &tcpSocket,
                                    &serverInfo,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( SOCKETS_INVALID_PARAMETER, socketStatus );

    /* This should still fail because hostNameLength is initialized to 0. */
    serverInfo.pHostName = HOSTNAME;
    socketStatus = Sockets_Connect( &tcpSocket,
                                    &serverInfo,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( SOCKETS_INVALID_PARAMETER, socketStatus );
}

/**
 * @brief Test that #SOCKETS_DNS_FAILURE is correctly returned when the call
 * to #getaddrinfo returns an error.
 */
void test_Sockets_Connect_DNS_Lookup_Fails( void )
{
    SocketStatus_t socketStatus;
    int tcpSocket = 1;

    getaddrinfo_ExpectAnyArgsAndReturn( -1 );

    socketStatus = Sockets_Connect( &tcpSocket,
                                    &serverInfo,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( SOCKETS_DNS_FAILURE, socketStatus );
}

/**
 * @brief Test that #Sockets_Connect returns #SOCKETS_CONNECT_FAILURE during
 * an attempt to connect to all IP addresses returned from the DNS lookup.
 */
void test_Sockets_Connect_Every_IP_Address_Fails( void )
{
    SocketStatus_t socketStatus;
    int tcpSocket = 1;

    /* -1 implies that every call to #connect will fail. */
    expectSocketsConnectCalls( -1 );

    socketStatus = Sockets_Connect( &tcpSocket,
                                    &serverInfo,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( SOCKETS_CONNECT_FAILURE, socketStatus );
}

/**
 * @brief Test that #Sockets_Connect returns the right error depending upon
 * the status received from #errno.
 */
void test_Sockets_Connect_Fail_setsockopt( void )
{
    SocketStatus_t socketStatus, expectedSocketStatus;
    int tcpSocket = 1;
    uint16_t i = 1;
    int32_t allErrorCases[] =
    {
        EBADF,       EDOM,     EINVAL, EISCONN,
        ENOPROTOOPT, ENOTSOCK, ENOMEM, ENOBUFS
    };

    for( i = 0; i < ( sizeof( allErrorCases ) / sizeof( int32_t ) ); i++ )
    {
        expectSocketsConnectCalls( NUM_ADDR_INFO );
        errno = allErrorCases[ i ];

        if( i % 2 )
        {
            setsockopt_ExpectAnyArgsAndReturn( -1 );
        }
        else
        {
            setsockopt_ExpectAnyArgsAndReturn( 0 );
            setsockopt_ExpectAnyArgsAndReturn( -1 );
        }

        socketStatus = Sockets_Connect( &tcpSocket,
                                        &serverInfo,
                                        SEND_RECV_TIMEOUT,
                                        SEND_RECV_TIMEOUT );

        if( ( errno == ENOMEM ) || ( errno == ENOBUFS ) )
        {
            expectedSocketStatus = SOCKETS_INSUFFICIENT_MEMORY;
        }
        else if( ( errno == ENOTSOCK ) || ( errno == EDOM ) || ( errno == EBADF ) )
        {
            expectedSocketStatus = SOCKETS_INVALID_PARAMETER;
        }
        else
        {
            expectedSocketStatus = SOCKETS_API_ERROR;
        }

        TEST_ASSERT_EQUAL( expectedSocketStatus, socketStatus );
    }
}

/**
 * @brief Test the happy path case in which #Sockets_Connect is able to connect
 * to one of the IP addresses from the retrieved DNS records.
 */
void test_Sockets_Connect_Succeed_On_Nth_IP_Address( void )
{
    SocketStatus_t socketStatus;
    int tcpSocket = 1;

    expectSocketsConnectCalls( NUM_ADDR_INFO );
    setsockopt_ExpectAnyArgsAndReturn( 0 );
    setsockopt_ExpectAnyArgsAndReturn( 0 );

    socketStatus = Sockets_Connect( &tcpSocket,
                                    &serverInfo,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( SOCKETS_SUCCESS, socketStatus );
}

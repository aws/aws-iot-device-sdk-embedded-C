#include <string.h>
#include <stdbool.h>
#include <stdlib.h>

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "sockets_posix.h"

#include "mock_netdb.h"
#include "mock_socket.h"
#include "mock_inet.h"
#include "mock_close.h"

#define NUM_ADDR_INFO        3
#define SEND_RECV_TIMEOUT    0
#define HOSTNAME             "amazon.com"
#define PORT                 80

/* ============================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp()
{
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

int32_t errno;

static void allocateAddrInfoLinkedList( struct addrinfo ** head )
{
    struct addrinfo * index = NULL, * next = NULL;
    struct sockaddr * ai_addr = NULL;
    int i;

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

static void setsockoptFailWithError( int32_t errorNumber )
{
    SocketStatus_t socketStatus;
    ServerInfo_t serverInfo;
    int tcpSocket = 1, i = 1;
    struct addrinfo * addrInfo;

    allocateAddrInfoLinkedList( &addrInfo );
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

        /* Every call to connect() should fail. */
        connect_ExpectAnyArgsAndReturn( -1 );
        close_ExpectAnyArgsAndReturn( 0 );
    }

    freeaddrinfo_ExpectAnyArgs();

    errno = errorNumber;

    freeAddrInfoLinkedList( addrInfo );
}

/**
 * @brief Test Sockets_Disconnect.
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

void test_Sockets_Disconnect_Invalid_Socket( void )
{
    SocketStatus_t socketStatus;
    int tcpSocket = 0;

    socketStatus = Sockets_Disconnect( tcpSocket );
    TEST_ASSERT_EQUAL( SOCKETS_INVALID_PARAMETER, socketStatus );
}

void test_Sockets_Connect_Invalid_Params( void )
{
    SocketStatus_t socketStatus;
    ServerInfo_t serverInfo;
    int tcpSocket = 1;

    /* Passing a NULL socket should fail. */
    socketStatus = Sockets_Connect( NULL,
                                    &serverInfo,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( SOCKETS_INVALID_PARAMETER, socketStatus );

    /* Passing a hostName should fail. */
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

void test_Sockets_Connect_DNS_Lookup_Fails( void )
{
    SocketStatus_t socketStatus;
    ServerInfo_t serverInfo;
    int tcpSocket = 1;

    serverInfo.pHostName = HOSTNAME;
    serverInfo.hostNameLength = strlen( HOSTNAME );
    serverInfo.port = PORT;

    getaddrinfo_ExpectAnyArgsAndReturn( -1 );

    socketStatus = Sockets_Connect( &tcpSocket,
                                    &serverInfo,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( SOCKETS_DNS_FAILURE, socketStatus );
}

void test_Sockets_Connect_Every_IP_Address_Fails( void )
{
    SocketStatus_t socketStatus;
    ServerInfo_t serverInfo;
    int tcpSocket = 1, i = 1;
    struct addrinfo * addrInfo;

    serverInfo.pHostName = HOSTNAME;
    serverInfo.hostNameLength = strlen( HOSTNAME );
    serverInfo.port = PORT;

    allocateAddrInfoLinkedList( &addrInfo );
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

        /* Every call to connect() should fail. */
        connect_ExpectAnyArgsAndReturn( -1 );
        close_ExpectAnyArgsAndReturn( 0 );
    }

    freeaddrinfo_ExpectAnyArgs();

    socketStatus = Sockets_Connect( &tcpSocket,
                                    &serverInfo,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( SOCKETS_CONNECT_FAILURE, socketStatus );

    freeAddrInfoLinkedList( addrInfo );
}

void test_Sockets_Connect_Fail_setsockopt( void )
{
}

void test_Sockets_Connect_Succeed_On_Nth_IP_Address( void )
{
    SocketStatus_t socketStatus;
    ServerInfo_t serverInfo;
    int tcpSocket = 1, i = 1;
    struct addrinfo * addrInfo;

    serverInfo.pHostName = HOSTNAME;
    serverInfo.hostNameLength = strlen( HOSTNAME );
    serverInfo.port = PORT;

    allocateAddrInfoLinkedList( &addrInfo );
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
        if( i < NUM_ADDR_INFO )
        {
            connect_ExpectAnyArgsAndReturn( -1 );
            close_ExpectAnyArgsAndReturn( 0 );
        }
        else
        {
            connect_ExpectAnyArgsAndReturn( 0 );
        }
    }

    freeaddrinfo_ExpectAnyArgs();
    setsockopt_ExpectAnyArgsAndReturn( 0 );
    setsockopt_ExpectAnyArgsAndReturn( 0 );

    socketStatus = Sockets_Connect( &tcpSocket,
                                    &serverInfo,
                                    SEND_RECV_TIMEOUT,
                                    SEND_RECV_TIMEOUT );
    TEST_ASSERT_EQUAL( SOCKETS_SUCCESS, socketStatus );

    freeAddrInfoLinkedList( addrInfo );
}

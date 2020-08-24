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
#include "mock_openssl_api.h"

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

void test_Openssl_Connect_Invalid_Params( void )
{
}

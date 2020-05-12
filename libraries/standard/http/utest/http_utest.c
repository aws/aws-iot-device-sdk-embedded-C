#include <stdbool.h>

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "http_client.h"

/* Private includes for internal macros. */
#include "private/http_client_internal.h"
#include "private/http_client_parse.h"

/* ============================ UNITY FIXTURES ============================== */
void setUp( void )
{
}

/* called before each testcase */
void tearDown( void )
{
}

/* called at the beginning of the whole suite */
void suiteSetUp()
{
}

/* called at the end of the whole suite */
int suiteTearDown( int numFailures )
{
}

/* ====================== Testing HTTPClient_AddHeader ====================== */
void test_Http_AddHeader_invalid_params( void )
{
    TEST_ASSERT_EQUAL( HTTPClient_AddHeader( NULL, NULL, 0, NULL, 0 ),
                       HTTP_INVALID_PARAMETER );
}

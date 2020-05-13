#include <stdbool.h>

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "http_client.h"

/* Private includes for internal macros. */
#include "private/http_client_internal.h"
#include "private/http_client_parse.h"

/* Headers data with "\r\n\r\n" terminator to be pre-populated in buffer before
 * call to AddRangeHeader(). */
#define PREEXISTING_HEADER_DATA         "POST / HTTP/1.1 \r\nAuthorization: None\r\n\r\n"
#define PREEXISTING_HEADER_DATA_LEN     ( sizeof( PREEXISTING_HEADER_DATA ) - 1 )

/* Headers data without "\r\n\r\n" terminator to be pre-populated in buffer before
 * call to AddRangeHeader(). */
#define PREEXISTING_REQUEST_LINE        "POST / HTTP/1.1 \r\n"
#define PREEXISTING_REQUEST_LINE_LEN    ( sizeof( PREEXISTING_REQUEST_LINE ) - 1 )

/* Type to store expected headers data. */
typedef struct _headers
{
    uint8_t buffer[ HTTP_TEST_BUFFER_SIZE ];
    size_t dataLen;
} _headers_t;

/* ============================ Helper Functions ============================== */

static void setupBuffersWithPreexistingHeader( HTTPRequestHeaders_t * requestHeaders,
                                               const uint8_t * testBuffer,
                                               const uint8_t * expectedHeaders,
                                               const char * preexistingData )
{
    size_t dataLen = strlen( preexistingData );

    requestHeaders.pBuffer = testBuffer;
    requestHeaders.bufferLen = sizeof( testBuffer );
    /* We add 1 bytes as snprintf() writes a null byte at the end. */
    int numBytes = snprintf( ( char * ) requestHeaders.pBuffer,
                             dataLen + 1,
                             "%s",
                             preexistingData );
    ok( numBytes == ( int ) dataLen );
    requestHeaders.headersLen = dataLen;

    /* Fill the same data in the expected buffer as HTTPClient_AddRangeHeaders()
     * is not expected to change it. */
    ok( memcpy( expectedHeaders.buffer, requestHeaders.pBuffer,
                requestHeaders.headersLen )
        == expectedHeaders.buffer );
    expectedHeaders.dataLen = requestHeaders.headersLen;
}

static void addRangeToExpectedHeaders( const char * expectedHeaders,
                                       const char * expectedRange,
                                       bool terminatorExists )
{
    size_t rangeRequestLen = RANGE_REQUEST_HEADER_DATA_PREFIX_LEN +
                             strlen( expectedRange ) +
                             2 * HTTP_HEADER_LINE_SEPARATOR_LEN;
    int numBytes =
        snprintf( ( char * ) expectedHeaders.buffer +
                  expectedHeaders.dataLen -
                  ( terminatorExists ? HTTP_HEADER_LINE_SEPARATOR_LEN : 0 ),
                  /* We add 1 bytes as snprintf() writes a null byte at the end. */
                  rangeRequestLen + 1,
                  "%s%s\r\n\r\n",
                  RANGE_REQUEST_HEADER_DATA_PREFIX,
                  expectedRange );

    ok( ( size_t ) numBytes == rangeRequestLen );
    expectedHeaders.dataLen += rangeRequestLen -
                               ( terminatorExists ? HTTP_HEADER_LINE_SEPARATOR_LEN : 0 );
}

/* File-scoped Global variables */
static HTTPStatus_t retCode = HTTP_NOT_SUPPORTED;

/* ============================ UNITY FIXTURES ============================== */
void setUp( void )
{
}

/* called before each testcase */
void tearDown( void )
{
    retCode = HTTP_NOT_SUPPORTED;
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

/* ====================== Testing HTTPClient_AddRangeHeader ====================== */

void test_Http_AddRangeHeader_Invalid_Params( void )
{
    /* Request header parameter is NULL. */
    tearDown();
    retCode = HTTPClient_AddRangeHeader( NULL,
                                         0 /* rangeStart */,
                                         0 /* rageEnd */ );
    TEST_ASSERT_EQUAL( retCode, HTTP_INVALID_PARAMETER );

    /* Underlying buffer is NULL in request headers. */
    tearDown();
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         0 /* rangeStart */,
                                         0 /* rageEnd */ );
    TEST_ASSERT_EQUAL( retCode, HTTP_INVALID_PARAMETER );

    /* Request Header Size is zero. */
    tearDown();
    testHeaders.pBuffer = &testBuffer[ 0 ];
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         0 /* rangeStart */,
                                         0 /* rageEnd */ );
    TEST_ASSERT_EQUAL( retCode, HTTP_INSUFFICIENT_MEMORY );

    /* Test incorrect combinations of rangeStart and rangeEnd. */

    /* rangeStart > rangeEnd */
    tearDown();
    testHeaders.pBuffer = &testBuffer[ 0 ];
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         10 /* rangeStart */,
                                         5 /* rageEnd */ );
    TEST_ASSERT_EQUAL( retCode, HTTP_INVALID_PARAMETER );

    /* rangeStart is negative but rangeStart is non-End of File. */
    tearDown();
    testHeaders.pBuffer = &testBuffer[ 0 ];
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         -10 /* rangeStart */,
                                         RANGE_REQUEST_END_OF_FILE + 1 /* rageEnd */ );
    TEST_ASSERT_EQUAL( retCode, HTTP_INVALID_PARAMETER );
    tearDown();
    testHeaders.pBuffer = &testBuffer[ 0 ];
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         -50 /* rangeStart */,
                                         -10 /* rageEnd */ );
    TEST_ASSERT_EQUAL( retCode, HTTP_INVALID_PARAMETER );
}

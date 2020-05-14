#include <stdbool.h>
#include <string.h>

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "http_client.h"

/* Private includes for internal macros. */
#include "private/http_client_internal.h"
#include "private/http_client_parse.h"

/* Default size for request buffer. */
#define HTTP_TEST_BUFFER_SIZE           ( 100 )

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

static void setupBuffersWithPreexistingHeader( HTTPRequestHeaders_t * testRequestHeaders,
                                               uint8_t * testBuffer,
                                               _headers_t * expectedHeaders,
                                               const char * preexistingData )
{
    size_t dataLen = strlen( preexistingData );

    testRequestHeaders->pBuffer = testBuffer;
    testRequestHeaders->bufferLen = sizeof( testBuffer );
    /* We add 1 bytes as snprintf() writes a null byte at the end. */
    int numBytes = snprintf( ( char * ) testRequestHeaders->pBuffer,
                             dataLen + 1,
                             "%s",
                             preexistingData );
    TEST_ASSERT( numBytes == ( int ) dataLen );
    testRequestHeaders->headersLen = dataLen;

    /* Fill the same data in the expected buffer as HTTPClient_AddRangeHeaders()
     * is not expected to change it. */
    TEST_ASSERT( memcpy( expectedHeaders->buffer, testRequestHeaders->pBuffer,
                         testRequestHeaders->headersLen )
                 == expectedHeaders->buffer );
    expectedHeaders->dataLen = testRequestHeaders->headersLen;
}

static void addRangeToExpectedHeaders( _headers_t * expectedHeaders,
                                       const char * expectedRange,
                                       bool terminatorExists )
{
    size_t rangeRequestLen = RANGE_REQUEST_HEADER_FIELD_LEN +
                             RANGE_REQUEST_HEADER_VALUE_PREFIX_LEN +
                             strlen( expectedRange ) +
                             2 * HTTP_HEADER_LINE_SEPARATOR_LEN;
    int numBytes =
        snprintf( ( char * ) expectedHeaders->buffer +
                  expectedHeaders->dataLen -
                  ( terminatorExists ? HTTP_HEADER_LINE_SEPARATOR_LEN : 0 ),
                  /* We add 1 bytes as snprintf() writes a null byte at the end. */
                  rangeRequestLen + 1,
                  "%s%s%s\r\n\r\n",
                  RANGE_REQUEST_HEADER_FIELD,
                  RANGE_REQUEST_HEADER_VALUE_PREFIX,
                  expectedRange );

    TEST_ASSERT_EQUAL( ( size_t ) numBytes, rangeRequestLen );
    expectedHeaders->dataLen += rangeRequestLen -
                                ( terminatorExists ? HTTP_HEADER_LINE_SEPARATOR_LEN : 0 );
}

/* File-scoped Global variables */
static HTTPStatus_t retCode = HTTP_NOT_SUPPORTED;
static uint8_t testBuffer[ HTTP_TEST_BUFFER_SIZE ] = { 0 };
static HTTPRequestHeaders_t testHeaders = { 0 };
static _headers_t expectedHeaders = { 0 };
static int testRangeStart = 0;
static int testRangeEnd = 0;
/* ============================ UNITY FIXTURES ============================== */
void setUp( void )
{
    memset( &testHeaders, 0, sizeof( testHeaders ) );
    memset( testBuffer, 0, sizeof( testBuffer ) );
    memset( &expectedHeaders, 0, sizeof( expectedHeaders ) );
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
    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, retCode );

    /* Underlying buffer is NULL in request headers. */
    tearDown();
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         0 /* rangeStart */,
                                         0 /* rageEnd */ );
    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, retCode );

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
    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, retCode );

    /* rangeStart is negative but rangeStart is non-End of File. */
    tearDown();
    testHeaders.pBuffer = &testBuffer[ 0 ];
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         -10 /* rangeStart */,
                                         HTTP_RANGE_REQUEST_END_OF_FILE + 1 /* rageEnd */ );
    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, retCode );
    tearDown();
    testHeaders.pBuffer = &testBuffer[ 0 ];
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         -50 /* rangeStart */,
                                         -10 /* rageEnd */ );
    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, retCode );
}

/* Test Insufficient memory failure when the buffer has one less byte than required. */
void test_Http_AddRangeHeader_Insufficient_Memory( void )
{
    setupBuffersWithPreexistingHeader( &testHeaders,
                                       testBuffer,
                                       &expectedHeaders,
                                       PREEXISTING_HEADER_DATA );
    size_t preHeadersLen = testHeaders.headersLen;
    testRangeStart = 5;
    testRangeEnd = 10;
    addRangeToExpectedHeaders( &expectedHeaders,
                               "5-10" /*expected range*/,
                               true );

    /* Update headers buffer size to be one byte short of required size to add
     * Range Request header. */
    testHeaders.bufferLen = expectedHeaders.dataLen - 1;

    /* Re-write the expected headers buffer to store a copy of the test headers
     * to use for verification later. */
    memcpy( expectedHeaders.buffer, testHeaders.pBuffer, testHeaders.bufferLen );

    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         testRangeStart,
                                         testRangeEnd );
    TEST_ASSERT_EQUAL( HTTP_INSUFFICIENT_MEMORY, retCode );
    /* Verify the headers input parameter is unaltered. */
    TEST_ASSERT_EQUAL( testHeaders.headersLen, preHeadersLen );
    TEST_ASSERT_EQUAL( testHeaders.bufferLen, expectedHeaders.dataLen - 1 );
    TEST_ASSERT_EQUAL( 0, memcmp( testHeaders.pBuffer,
                                  expectedHeaders.buffer,
                                  testHeaders.bufferLen ) );
}


void test_Http_AddRangeHeader_Happy_Path( void )
{
    /* Case 1: Headers buffer contains header data ending with "\r\n\r\n". */

    /* Range specification of the form [rangeStart, rangeEnd]. */
    /* Test with 0 as the range values */
    tearDown();
    setupBuffersWithPreexistingHeader( &testHeaders, testBuffer,
                                       &expectedHeaders,
                                       PREEXISTING_HEADER_DATA );
    testRangeStart = 0;
    testRangeEnd = 0;
    addRangeToExpectedHeaders( &expectedHeaders,
                               "0-0" /*expected range*/,
                               true );
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         testRangeStart,
                                         testRangeEnd );
    TEST_ASSERT_EQUAL( HTTP_SUCCESS, retCode );
    /* Verify the the Range Request header data. */
    TEST_ASSERT_EQUAL( testHeaders.headersLen, expectedHeaders.dataLen );
    TEST_ASSERT( memcmp( testHeaders.pBuffer, expectedHeaders.buffer, expectedHeaders.dataLen )
                 == 0 );
    /* Verify that the bufferLen data was not tampered with. */
    TEST_ASSERT_EQUAL( testHeaders.bufferLen, sizeof( testBuffer ) );

    /* Test for [0, eof) range */
    tearDown();
    setupBuffersWithPreexistingHeader( &testHeaders, testBuffer,
                                       &expectedHeaders,
                                       PREEXISTING_HEADER_DATA );
    testRangeStart = 0;
    testRangeEnd = HTTP_RANGE_REQUEST_END_OF_FILE;
    addRangeToExpectedHeaders( &expectedHeaders,
                               "0-" /*expected range*/,
                               true );
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         testRangeStart,
                                         testRangeEnd );
    TEST_ASSERT_EQUAL( HTTP_SUCCESS, retCode );
    /* Verify the the Range Request header data. */
    TEST_ASSERT_EQUAL( testHeaders.headersLen, expectedHeaders.dataLen );
    TEST_ASSERT( memcmp( testHeaders.pBuffer, expectedHeaders.buffer, expectedHeaders.dataLen )
                 == 0 );
    /* Verify that the bufferLen data was not tampered with. */
    TEST_ASSERT_EQUAL( testHeaders.bufferLen, sizeof( testBuffer ) );

    tearDown();
    setupBuffersWithPreexistingHeader( &testHeaders, testBuffer,
                                       &expectedHeaders,
                                       PREEXISTING_HEADER_DATA );
    testRangeStart = 10;
    testRangeEnd = 100;
    addRangeToExpectedHeaders( &expectedHeaders,
                               "10-100" /*expected range*/,
                               true );
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         testRangeStart,
                                         testRangeEnd );
    TEST_ASSERT_EQUAL( HTTP_SUCCESS, retCode );
    /* Verify the the Range Request header data. */
    TEST_ASSERT_EQUAL( testHeaders.headersLen, expectedHeaders.dataLen );
    TEST_ASSERT( memcmp( testHeaders.pBuffer, expectedHeaders.buffer, expectedHeaders.dataLen )
                 == 0 );
    /* Verify that the bufferLen data was not tampered with. */
    TEST_ASSERT_EQUAL( testHeaders.bufferLen, sizeof( testBuffer ) );

    /* Range specification of the form [rangeStart,)
     * i.e. for all bytes >= rangeStart. */
    tearDown();
    setupBuffersWithPreexistingHeader( &testHeaders, testBuffer,
                                       &expectedHeaders,
                                       PREEXISTING_HEADER_DATA );
    testRangeStart = 100;
    testRangeEnd = HTTP_RANGE_REQUEST_END_OF_FILE;
    addRangeToExpectedHeaders( &expectedHeaders,
                               "100-" /*expected range*/,
                               true );
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         testRangeStart,
                                         testRangeEnd );
    TEST_ASSERT_EQUAL( HTTP_SUCCESS, retCode );
    /* Verify the the Range Request header data. */
    TEST_ASSERT_EQUAL( testHeaders.headersLen, expectedHeaders.dataLen );
    TEST_ASSERT( memcmp( testHeaders.pBuffer, expectedHeaders.buffer, expectedHeaders.dataLen )
                 == 0 );
    /* Verify that the bufferLen data was not tampered with. */
    TEST_ASSERT_EQUAL( testHeaders.bufferLen, sizeof( testBuffer ) );

    /* Range specification for the last N bytes. */
    tearDown();
    setupBuffersWithPreexistingHeader( &testHeaders, testBuffer,
                                       &expectedHeaders,
                                       PREEXISTING_HEADER_DATA );
    testRangeStart = -50;
    testRangeEnd = HTTP_RANGE_REQUEST_END_OF_FILE;
    addRangeToExpectedHeaders( &expectedHeaders,
                               "-50" /*expected range*/,
                               true );
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         testRangeStart,
                                         testRangeEnd );
    TEST_ASSERT_EQUAL( HTTP_SUCCESS, retCode );
    /* Verify the the Range Request header data. */
    TEST_ASSERT_EQUAL( testHeaders.headersLen, expectedHeaders.dataLen );
    TEST_ASSERT( memcmp( testHeaders.pBuffer, expectedHeaders.buffer, expectedHeaders.dataLen )
                 == 0 );
    /* Verify that the bufferLen data was not tampered with. */
    TEST_ASSERT_EQUAL( testHeaders.bufferLen, sizeof( testBuffer ) );

    /* Test with LARGE range values. */
    tearDown();
    setupBuffersWithPreexistingHeader( &testHeaders, testBuffer,
                                       &expectedHeaders,
                                       PREEXISTING_HEADER_DATA );
    testRangeStart = INT32_MAX;
    testRangeEnd = INT32_MAX;
    addRangeToExpectedHeaders( &expectedHeaders,
                               "2147483647-2147483647" /*expected range*/,
                               true );
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         testRangeStart,
                                         testRangeEnd );
    TEST_ASSERT_EQUAL( HTTP_SUCCESS, retCode );
    /* Verify the the Range Request header data. */
    TEST_ASSERT_EQUAL( testHeaders.headersLen, expectedHeaders.dataLen );
    TEST_ASSERT( memcmp( testHeaders.pBuffer, expectedHeaders.buffer, expectedHeaders.dataLen )
                 == 0 );
    /* Verify that the bufferLen data was not tampered with. */
    TEST_ASSERT_EQUAL( testHeaders.bufferLen, sizeof( testBuffer ) );

    /* Case 2: Headers buffer does not contain data with trailing "\r\n\r\n". */

    /* Range specification of the form [rangeStart, rangeEnd]. */
    /* Test with 0 as the range values */
    tearDown();
    setupBuffersWithPreexistingHeader( &testHeaders, testBuffer,
                                       &expectedHeaders,
                                       PREEXISTING_REQUEST_LINE );
    testRangeStart = 0;
    testRangeEnd = 0;
    addRangeToExpectedHeaders( &expectedHeaders,
                               "0-0" /*expected range*/,
                               false );
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         testRangeStart,
                                         testRangeEnd );
    TEST_ASSERT_EQUAL( HTTP_SUCCESS, retCode );
    /* Verify the the Range Request header data. */
    TEST_ASSERT_EQUAL( testHeaders.headersLen, expectedHeaders.dataLen );
    TEST_ASSERT( memcmp( testHeaders.pBuffer, expectedHeaders.buffer, expectedHeaders.dataLen )
                 == 0 );
    /* Verify that the bufferLen data was not tampered with. */
    TEST_ASSERT_EQUAL( testHeaders.bufferLen, sizeof( testBuffer ) );
}

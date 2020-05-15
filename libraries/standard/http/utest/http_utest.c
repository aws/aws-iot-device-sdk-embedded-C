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

#define HTTP_METHOD_GET_LEN           ( sizeof( HTTP_METHOD_GET ) - 1 )
#define HTTP_TEST_REQUEST_PATH        "/robots.txt"
#define HTTP_TEST_REQUEST_PATH_LEN    ( sizeof( HTTP_TEST_REQUEST_PATH ) - 1 )
#define HTTP_TEST_HOST_VALUE          "amazon.com"
#define HTTP_TEST_HOST_VALUE_LEN      ( sizeof( HTTP_TEST_HOST_VALUE ) - 1 )
#define HTTP_TEST_REQUEST_LINE   \
    ( HTTP_METHOD_GET " "        \
      HTTP_TEST_REQUEST_PATH " " \
      HTTP_PROTOCOL_VERSION "\r\n" )
#define HTTP_TEST_REQUEST_LINE_LEN    ( sizeof( HTTP_TEST_REQUEST_LINE ) - 1 )

/* Used for format parameter in snprintf(...). */
#define HTTP_TEST_HEADER_FORMAT \
    "%s %s %s\r\n"              \
    "%s: %s\r\n"                \
    "%s: %s\r\n"                \
    "%s: %s\r\n\r\n"

/* Length of the following template HTTP header.
 *   <HTTP_METHOD_GET> <HTTP_TEST_REQUEST_PATH> <HTTP_PROTOCOL_VERSION> \r\n
 *   <HTTP_USER_AGENT_FIELD>: <HTTP_USER_AGENT_FIELD_LEN> \r\n
 *   <HTTP_HOST_FIELD>: <HTTP_TEST_HOST_VALUE> \r\n
 *   <HTTP_CONNECTION_FIELD>: \r\n
 *   \r\n
 * This is used to initialize the expectedHeader string. Note the missing
 * <HTTP_TEST_CONNECTION_VALUE>. This is added later on depending on the
 * value of HTTP_REQUEST_KEEP_ALIVE_FLAG in pRequestInfo->flags. */
#define HTTP_TEST_PREFIX_HEADER_LEN                                 \
    ( HTTP_METHOD_GET_LEN + SPACE_CHARACTER_LEN +                   \
      HTTP_TEST_REQUEST_PATH_LEN + SPACE_CHARACTER_LEN +            \
      HTTP_PROTOCOL_VERSION_LEN + HTTP_HEADER_LINE_SEPARATOR_LEN +  \
      HTTP_USER_AGENT_FIELD_LEN + HTTP_HEADER_FIELD_SEPARATOR_LEN + \
      HTTP_USER_AGENT_VALUE_LEN + HTTP_HEADER_LINE_SEPARATOR_LEN +  \
      HTTP_HOST_FIELD_LEN + HTTP_HEADER_FIELD_SEPARATOR_LEN +       \
      HTTP_TEST_HOST_VALUE_LEN + HTTP_HEADER_LINE_SEPARATOR_LEN +   \
      HTTP_CONNECTION_FIELD_LEN + HTTP_HEADER_FIELD_SEPARATOR_LEN + \
      HTTP_HEADER_LINE_SEPARATOR_LEN +                              \
      HTTP_HEADER_LINE_SEPARATOR_LEN )

/* Add HTTP_CONNECTION_KEEP_ALIVE_VALUE_LEN to account for longest possible
 * length of template header. */
#define HTTP_TEST_MAX_INITIALIZED_HEADER_LEN \
    ( HTTP_TEST_PREFIX_HEADER_LEN + HTTP_CONNECTION_KEEP_ALIVE_VALUE_LEN )

/* Add 1 because snprintf(...) writes a null byte at the end. */
#define HTTP_TEST_INITIALIZED_HEADER_BUFFER_LEN \
    ( HTTP_TEST_MAX_INITIALIZED_HEADER_LEN + 1 )

#define HTTP_TEST_BUFFER_LEN    1024

/* File-scoped Global variables */
static HTTPStatus_t retCode = HTTP_NOT_SUPPORTED;
static uint8_t testBuffer[ HTTP_TEST_BUFFER_SIZE ] = { 0 };
static HTTPRequestHeaders_t testHeaders = { 0 };
static _headers_t expectedHeaders = { 0 };
static int testRangeStart = 0;
static int testRangeEnd = 0;
static uint8_t httpBuffer[ HTTP_TEST_BUFFER_LEN ] = { 0 };

/* ============================ Helper Functions ============================== */

/**
 * @brief Fills the test input buffer and expectation buffers with pre-existing data
 * before calling the API function under test.
 */
static void setupBuffersWithPreexistingHeader( HTTPRequestHeaders_t * testRequestHeaders,
                                               uint8_t * testBuffer,
                                               size_t bufferSize,
                                               _headers_t * expectedHeaders,
                                               const char * preexistingData )
{
    size_t dataLen = strlen( preexistingData );

    testRequestHeaders->pBuffer = testBuffer;
    testRequestHeaders->bufferLen = bufferSize;
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

/**
 * @brief Common utility for adding the expected range string for a AddRangeRequest test case
 * in the expectation buffer.
 */
static void addRangeToExpectedHeaders( _headers_t * expectedHeaders,
                                       const char * expectedRange,
                                       bool terminatorExists )
{
    size_t rangeRequestLen = RANGE_REQUEST_HEADER_FIELD_LEN +
                             HTTP_HEADER_FIELD_SEPARATOR_LEN +
                             RANGE_REQUEST_HEADER_VALUE_PREFIX_LEN +
                             strlen( expectedRange ) +
                             2 * HTTP_HEADER_LINE_SEPARATOR_LEN;
    int numBytes =
        snprintf( ( char * ) expectedHeaders->buffer +
                  expectedHeaders->dataLen -
                  ( terminatorExists ? HTTP_HEADER_LINE_SEPARATOR_LEN : 0 ),
                  /* We add 1 bytes as snprintf() writes a null byte at the end. */
                  rangeRequestLen + 1,
                  "%s%s%s%s\r\n\r\n",
                  RANGE_REQUEST_HEADER_FIELD,
                  HTTP_HEADER_FIELD_SEPARATOR,
                  RANGE_REQUEST_HEADER_VALUE_PREFIX,
                  expectedRange );

    TEST_ASSERT_EQUAL( ( size_t ) numBytes, rangeRequestLen );
    expectedHeaders->dataLen += rangeRequestLen -
                                ( terminatorExists ? HTTP_HEADER_LINE_SEPARATOR_LEN : 0 );
}

/* ============================ UNITY FIXTURES ============================== */
void setUp( void )
{
}

/* called before each testcase */
void tearDown( void )
{
    retCode = HTTP_NOT_SUPPORTED;
    memset( &testHeaders, 0, sizeof( testHeaders ) );
    memset( testBuffer, 0, sizeof( testBuffer ) );
    memset( &expectedHeaders, 0, sizeof( expectedHeaders ) );
}

/* called at the beginning of the whole suite */
void suiteSetUp()
{
}

/* called at the end of the whole suite */
int suiteTearDown( int numFailures )
{
}

/* ============== Testing HTTPClient_InitializeRequestHeaders =============== */

/**
 * @brief Initialize pRequestInfo with test-defined macros.
 *
 * @param[in] pRequestInfo Initial request header configurations.
 */
static void setupRequestInfo( HTTPRequestInfo_t * pRequestInfo )
{
    pRequestInfo->method = HTTP_METHOD_GET;
    pRequestInfo->methodLen = HTTP_METHOD_GET_LEN;
    pRequestInfo->pPath = HTTP_TEST_REQUEST_PATH;
    pRequestInfo->pathLen = HTTP_TEST_REQUEST_PATH_LEN;
    pRequestInfo->pHost = HTTP_TEST_HOST_VALUE;
    pRequestInfo->hostLen = HTTP_TEST_HOST_VALUE_LEN;
    pRequestInfo->flags = 0;
}

/**
 *
 * @param[in] pRequestHeaders Request header buffer information.
 * @param[in] bufferLen Size of the buffer.
 */
static void setupBuffer( HTTPRequestHeaders_t * pRequestHeaders,
                         size_t bufferLen )
{
    pRequestHeaders->pBuffer = httpBuffer;
    pRequestHeaders->bufferLen = bufferLen;
}

/**
 * @brief Test happy path with zero-initialized requestHeaders and requestInfo.
 */
void test_Http_InitializeRequestHeaders_happy_path()
{
    HTTPStatus_t test_err = HTTP_INTERNAL_ERROR;
    HTTPRequestHeaders_t requestHeaders = { 0 };
    HTTPRequestInfo_t requestInfo = { 0 };
    size_t expectedHeaderLen = HTTP_TEST_MAX_INITIALIZED_HEADER_LEN;
    char expectedHeader[ HTTP_TEST_INITIALIZED_HEADER_BUFFER_LEN ] = { 0 };
    int numBytes = 0;

    setupRequestInfo( &requestInfo );
    setupBuffer( &requestHeaders, expectedHeaderLen );

    /* Happy Path testing. */
    expectedHeaderLen = HTTP_TEST_PREFIX_HEADER_LEN +
                        HTTP_CONNECTION_CLOSE_VALUE_LEN;
    numBytes = snprintf( expectedHeader, expectedHeaderLen + 1,
                         HTTP_TEST_HEADER_FORMAT,
                         HTTP_METHOD_GET, HTTP_TEST_REQUEST_PATH,
                         HTTP_PROTOCOL_VERSION,
                         HTTP_USER_AGENT_FIELD, HTTP_USER_AGENT_VALUE,
                         HTTP_HOST_FIELD, HTTP_TEST_HOST_VALUE,
                         HTTP_CONNECTION_FIELD, HTTP_CONNECTION_CLOSE_VALUE );
    TEST_ASSERT_EQUAL( numBytes, expectedHeaderLen );
    test_err = HTTPClient_InitializeRequestHeaders( &requestHeaders, &requestInfo );
    TEST_ASSERT_EQUAL_MEMORY( requestHeaders.pBuffer, expectedHeader, expectedHeaderLen );
    TEST_ASSERT_EQUAL( requestHeaders.headersLen, expectedHeaderLen );
    TEST_ASSERT_EQUAL( test_err, HTTP_SUCCESS );
}

/**
 * @brief Test NULL parameters, following order of else-if blocks in the HTTP library.
 */
void test_Http_InitializeRequestHeaders_invalid_params()
{
    HTTPStatus_t test_err = HTTP_INTERNAL_ERROR;
    HTTPRequestHeaders_t requestHeaders = { 0 };
    HTTPRequestInfo_t requestInfo = { 0 };
    size_t expectedHeaderLen = HTTP_TEST_MAX_INITIALIZED_HEADER_LEN;
    char expectedHeader[ HTTP_TEST_INITIALIZED_HEADER_BUFFER_LEN ] = { 0 };

    /* Test NULL parameters, following order of else-if blocks. */
    test_err = HTTPClient_InitializeRequestHeaders( NULL, &requestInfo );
    TEST_ASSERT_EQUAL( test_err, HTTP_INVALID_PARAMETER );
    /* TEST requestInfo.pBuffer == NULL */
    test_err = HTTPClient_InitializeRequestHeaders( &requestHeaders, &requestInfo );
    TEST_ASSERT_EQUAL( test_err, HTTP_INVALID_PARAMETER );
    requestHeaders.pBuffer = httpBuffer;
    requestHeaders.bufferLen = HTTP_TEST_INITIALIZED_HEADER_BUFFER_LEN;
    test_err = HTTPClient_InitializeRequestHeaders( &requestHeaders, NULL );
    TEST_ASSERT_EQUAL( test_err, HTTP_INVALID_PARAMETER );
    /* Test requestInfo members are NULL */
    test_err = HTTPClient_InitializeRequestHeaders( &requestHeaders, &requestInfo );
    TEST_ASSERT_EQUAL( test_err, HTTP_INVALID_PARAMETER );
    requestInfo.method = HTTP_METHOD_GET;
    test_err = HTTPClient_InitializeRequestHeaders( &requestHeaders, &requestInfo );
    TEST_ASSERT_EQUAL( test_err, HTTP_INVALID_PARAMETER );
    requestInfo.pHost = HTTP_TEST_HOST_VALUE;
    test_err = HTTPClient_InitializeRequestHeaders( &requestHeaders, &requestInfo );
    TEST_ASSERT_EQUAL( test_err, HTTP_INVALID_PARAMETER );
    requestInfo.pPath = HTTP_TEST_REQUEST_PATH;
    requestInfo.pathLen = HTTP_TEST_REQUEST_PATH_LEN;
    test_err = HTTPClient_InitializeRequestHeaders( &requestHeaders, &requestInfo );
    TEST_ASSERT_EQUAL( test_err, HTTP_INVALID_PARAMETER );
    requestInfo.methodLen = HTTP_METHOD_GET_LEN;
    test_err = HTTPClient_InitializeRequestHeaders( &requestHeaders, &requestInfo );
    TEST_ASSERT_EQUAL( test_err, HTTP_INVALID_PARAMETER );
    requestInfo.hostLen = HTTP_TEST_HOST_VALUE_LEN;
}

/**
 * @brief Test default path "/" if path == NULL. Also, check that the "Connection"
 * header is set to "keep-alive" when HTTP_REQUEST_KEEP_ALIVE_FLAG in requestHeaders
 * is activated.
 */
void test_Http_InitializeRequestHeaders_req_info()
{
    HTTPStatus_t test_err = HTTP_INTERNAL_ERROR;
    HTTPRequestHeaders_t requestHeaders = { 0 };
    HTTPRequestInfo_t requestInfo = { 0 };
    size_t expectedHeaderLen = HTTP_TEST_MAX_INITIALIZED_HEADER_LEN;
    char expectedHeader[ HTTP_TEST_INITIALIZED_HEADER_BUFFER_LEN ] = { 0 };
    int numBytes = 0;

    setupRequestInfo( &requestInfo );
    setupBuffer( &requestHeaders, expectedHeaderLen );

    requestInfo.pPath = 0;
    requestInfo.flags = HTTP_REQUEST_KEEP_ALIVE_FLAG;
    expectedHeaderLen = HTTP_TEST_PREFIX_HEADER_LEN -
                        HTTP_TEST_REQUEST_PATH_LEN +
                        HTTP_EMPTY_PATH_LEN +
                        HTTP_CONNECTION_KEEP_ALIVE_VALUE_LEN;
    numBytes = snprintf( expectedHeader, expectedHeaderLen + 1,
                         HTTP_TEST_HEADER_FORMAT,
                         HTTP_METHOD_GET, HTTP_EMPTY_PATH,
                         HTTP_PROTOCOL_VERSION,
                         HTTP_USER_AGENT_FIELD, HTTP_USER_AGENT_VALUE,
                         HTTP_HOST_FIELD, HTTP_TEST_HOST_VALUE,
                         HTTP_CONNECTION_FIELD, HTTP_CONNECTION_KEEP_ALIVE_VALUE );
    TEST_ASSERT_EQUAL( numBytes, expectedHeaderLen );

    requestHeaders.pBuffer = httpBuffer;
    requestHeaders.bufferLen = expectedHeaderLen;
    test_err = HTTPClient_InitializeRequestHeaders( &requestHeaders, &requestInfo );
    TEST_ASSERT_EQUAL_MEMORY( requestHeaders.pBuffer, expectedHeader, expectedHeaderLen );
    TEST_ASSERT_EQUAL( requestHeaders.headersLen, expectedHeaderLen );
    TEST_ASSERT_EQUAL( test_err, HTTP_SUCCESS );
}

/**
 * @brief Test HTTP_INSUFFICIENT_MEMORY from having requestHeaders.bufferLen less than
 * what is required to fit HTTP_TEST_REQUEST_LINE.
 */
void test_Http_InitializeRequestHeaders_insufficient_memory()
{
    HTTPStatus_t test_err = HTTP_INTERNAL_ERROR;
    HTTPRequestHeaders_t requestHeaders = { 0 };
    HTTPRequestInfo_t requestInfo = { 0 };
    size_t expectedHeaderLen = HTTP_TEST_MAX_INITIALIZED_HEADER_LEN;
    char expectedHeader[ HTTP_TEST_INITIALIZED_HEADER_BUFFER_LEN ] = { 0 };

    setupRequestInfo( &requestInfo );
    setupBuffer( &requestHeaders, expectedHeaderLen );

    requestHeaders.bufferLen = HTTP_TEST_REQUEST_LINE_LEN - 1;

    test_err = HTTPClient_InitializeRequestHeaders( &requestHeaders, &requestInfo );
    TEST_ASSERT_EQUAL( test_err, HTTP_INSUFFICIENT_MEMORY );
    TEST_ASSERT_TRUE( strncmp( ( char * ) requestHeaders.pBuffer,
                               HTTP_TEST_REQUEST_LINE,
                               HTTP_TEST_REQUEST_LINE_LEN ) != 0 );
}

/* ============== Testing HTTPClient_AddRangeHeader ================== */

/**
 * @brief Testing with invalid parameter inputs.
 */
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

/**
 * @brief Test Insufficient memory failure when the buffer has one less byte than required.
 */
void test_Http_AddRangeHeader_Insufficient_Memory( void )
{
    setupBuffersWithPreexistingHeader( &testHeaders,
                                       testBuffer,
                                       sizeof( testBuffer ),
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
    TEST_ASSERT_EQUAL( preHeadersLen, testHeaders.headersLen );
    TEST_ASSERT_EQUAL( expectedHeaders.dataLen - 1, testHeaders.bufferLen );
    TEST_ASSERT_EQUAL_MEMORY( expectedHeaders.buffer,
                              testHeaders.pBuffer,
                              testHeaders.bufferLen );
}

/**
 * @brief Test addition of range header in a buffer not containing any header.
 */
void test_Http_AddRangeHeader_Without_Trailing_Terminator( void )
{
    /* Headers buffer does not contain data with trailing "\r\n\r\n". */

    /* Range specification of the form [rangeStart, rangeEnd]. */
    /* Test with 0 as the range values */
    setupBuffersWithPreexistingHeader( &testHeaders, testBuffer,
                                       sizeof( testBuffer ),
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
    TEST_ASSERT_EQUAL( expectedHeaders.dataLen, testHeaders.headersLen );
    TEST_ASSERT_EQUAL_MEMORY( expectedHeaders.buffer,
                              testHeaders.pBuffer,
                              testHeaders.bufferLen );
    /* Verify that the bufferLen data was not tampered with. */
    TEST_ASSERT_EQUAL( sizeof( testBuffer ), testHeaders.bufferLen );
}

/**
 * @brief Test for Range specification of the form [rangeStart, rangeEnd].
 */
void test_Http_AddRangeHeader_RangeType_File_SubRange( void )
{
    /* Headers buffer contains header data ending with "\r\n\r\n". */

    /* Test with 0 as the range values */
    setupBuffersWithPreexistingHeader( &testHeaders, testBuffer,
                                       sizeof( testBuffer ),
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
    TEST_ASSERT_EQUAL( expectedHeaders.dataLen, testHeaders.headersLen );
    TEST_ASSERT_EQUAL_MEMORY( expectedHeaders.buffer,
                              testHeaders.pBuffer,
                              testHeaders.bufferLen );
    /* Verify that the bufferLen data was not tampered with. */
    TEST_ASSERT_EQUAL( sizeof( testBuffer ), testHeaders.bufferLen );

    tearDown();
    setupBuffersWithPreexistingHeader( &testHeaders, testBuffer,
                                       sizeof( testBuffer ),
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
    TEST_ASSERT_EQUAL( expectedHeaders.dataLen, testHeaders.headersLen );
    TEST_ASSERT_EQUAL_MEMORY( expectedHeaders.buffer,
                              testHeaders.pBuffer,
                              testHeaders.bufferLen );
    /* Verify that the bufferLen data was not tampered with. */
    TEST_ASSERT_EQUAL( sizeof( testBuffer ), testHeaders.bufferLen );
}

/**
 * @brief Test for adding request header for the [0, eof) range.
 */
void test_Http_AddRangeHeader_RangeType_Entire_File( void )
{
    setupBuffersWithPreexistingHeader( &testHeaders, testBuffer,
                                       sizeof( testBuffer ),
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
    TEST_ASSERT_EQUAL( expectedHeaders.dataLen, testHeaders.headersLen );
    TEST_ASSERT_EQUAL_MEMORY( expectedHeaders.buffer,
                              testHeaders.pBuffer,
                              testHeaders.bufferLen );
    /* Verify that the bufferLen data was not tampered with. */
    TEST_ASSERT_EQUAL( sizeof( testBuffer ), testHeaders.bufferLen );
}

/**
 * @brief Test for Range specification of the form [rangeStart, eof).
 */
void test_Http_AddRangeHeader_RangeType_All_Bytes_From_RangeStart( void )
{
    /* Range specification of the form [rangeStart,)
     * i.e. for all bytes >= rangeStart. */
    tearDown();
    setupBuffersWithPreexistingHeader( &testHeaders, testBuffer,
                                       sizeof( testBuffer ),
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
    TEST_ASSERT_EQUAL( expectedHeaders.dataLen, testHeaders.headersLen );
    TEST_ASSERT_EQUAL_MEMORY( expectedHeaders.buffer,
                              testHeaders.pBuffer,
                              testHeaders.bufferLen );
    /* Verify that the bufferLen data was not tampered with. */
    TEST_ASSERT_EQUAL( sizeof( testBuffer ), testHeaders.bufferLen );
}

/**
 * @brief Test for adding range request for the last N bytes.
 */
void test_Http_AddRangeHeader_RangeType_LastNBytes( void )
{
    /* Range specification for the last N bytes. */
    setupBuffersWithPreexistingHeader( &testHeaders, testBuffer,
                                       sizeof( testBuffer ),
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
    TEST_ASSERT_EQUAL( expectedHeaders.dataLen, testHeaders.headersLen );
    TEST_ASSERT_EQUAL_MEMORY( expectedHeaders.buffer,
                              testHeaders.pBuffer,
                              testHeaders.bufferLen );
    /* Verify that the bufferLen data was not tampered with. */
    TEST_ASSERT_EQUAL( sizeof( testBuffer ), testHeaders.bufferLen );
}

/**
 * @brief Test addition of range request header with large integers.
 */
void test_Http_AddRangeHeader_With_Max_INT32_Range_Values( void )
{
    /* Test with LARGE range values. */
    setupBuffersWithPreexistingHeader( &testHeaders, testBuffer,
                                       sizeof( testBuffer ),
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
    TEST_ASSERT_EQUAL( expectedHeaders.dataLen, testHeaders.headersLen );
    TEST_ASSERT_EQUAL_MEMORY( expectedHeaders.buffer,
                              testHeaders.pBuffer,
                              testHeaders.bufferLen );
    /* Verify that the bufferLen data was not tampered with. */
    TEST_ASSERT_EQUAL( sizeof( testBuffer ), testHeaders.bufferLen );
}

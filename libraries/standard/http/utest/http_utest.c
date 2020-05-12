#include <string.h>

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "http_client.h"

/* Private includes for internal macros. */
#include "private/http_client_internal.h"
#include "private/http_client_parse.h"

/* Include mock implementation of http-parser dependency. */
#include "mock_http_parser.h"

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

/* Template HTTP header fields and values. */
#define HTTP_TEST_HEADER_FIELD               "Authorization"
#define HTTP_TEST_HEADER_FIELD_LEN           ( sizeof( HTTP_TEST_HEADER_FIELD ) - 1 )
#define HTTP_TEST_HEADER_VALUE               "None"
#define HTTP_TEST_HEADER_VALUE_LEN           ( sizeof( HTTP_TEST_HEADER_VALUE ) - 1 )
/* Template for first line of HTTP header. */
#define HTTP_TEST_HEADER_REQUEST_LINE        "GET / HTTP/1.1 \r\n"
#define HTTP_TEST_HEADER_REQUEST_LINE_LEN    ( sizeof( HTTP_TEST_HEADER_REQUEST_LINE ) - 1 )
#define HTTP_REQUEST_HEADERS_INITIALIZER     { 0 }
/* Template for snprintf(...) strings. */
#define HTTP_TEST_SINGLE_HEADER_FORMAT       "%s%s: %s\r\n\r\n"
#define HTTP_TEST_DOUBLE_HEADER_FORMAT       "%s%s: %s\r\n%s: %s\r\n\r\n"

/* Length of the following template HTTP header.
 *   <HTTP_TEST_HEADER_REQUEST_LINE> \r\n
 *   <HTTP_TEST_HEADER_FIELD>: <HTTP_TEST_HEADER_VALUE> \r\n
 *   \r\n
 * This is used to initialize the expectedHeader string. */
#define HTTP_TEST_SINGLE_HEADER_LEN       \
    ( HTTP_TEST_HEADER_REQUEST_LINE_LEN + \
      HTTP_TEST_HEADER_FIELD_LEN +        \
      HTTP_HEADER_FIELD_SEPARATOR_LEN +   \
      HTTP_TEST_HEADER_VALUE_LEN +        \
      HTTP_HEADER_LINE_SEPARATOR_LEN +    \
      HTTP_HEADER_LINE_SEPARATOR_LEN )

/* The longest possible header used for these unit tests. */
#define HTTP_TEST_DOUBLE_HEADER_LEN     \
    ( HTTP_TEST_SINGLE_HEADER_LEN +     \
      HTTP_TEST_HEADER_FIELD_LEN +      \
      HTTP_HEADER_FIELD_SEPARATOR_LEN + \
      HTTP_TEST_HEADER_VALUE_LEN +      \
      HTTP_HEADER_LINE_SEPARATOR_LEN )

#define HTTP_TEST_DOUBLE_HEADER_BUFFER_LEN \
    ( HTTP_TEST_DOUBLE_HEADER_LEN + 1 )

/* Template HTTP response for testing HTTPClient_ReadHeader API. */
static const char * pTestResponse = "HTTP/1.1 200 OK\r\n"
                                    "test-header0: test-value0\r\n"
                                    "test-header1: test-value1\r\n"
                                    "test-header2: test-value2\r\n"
                                    "\r\n";

#define HEADER_IN_BUFFER        "test-header1"
#define HEADER_NOT_IN_BUFFER    "header-not-in-buffer"

/* File-scoped Global variables */
static HTTPStatus_t retCode = HTTP_INTERNAL_ERROR;
static uint8_t testBuffer[ HTTP_TEST_BUFFER_SIZE ] = { 0 };
static HTTPRequestHeaders_t testHeaders = { 0 };
static _headers_t expectedHeaders = { 0 };
static int testRangeStart = 0;
static int testRangeEnd = 0;
static const uint8_t * pValueLoc = NULL;
static size_t valueLen = 0u;
static HTTPResponse_t testResponse = { 0 };
static const size_t headerFieldInRespLoc = 44;
static const size_t headerFieldInRespLen = sizeof( "test-header1" ) - 1u;
static const size_t headerValInRespLoc = 58;
static const size_t headerValInRespLen = sizeof( "test-value1" ) - 1u;
static http_parser * pCapturedParser = NULL;
static http_parser_settings * pCapturedSettings = NULL;
static const char * pExpectedBuffer = NULL;
static size_t expectedBufferSize = 0u;
static uint8_t invokeHeaderFieldCallback = 0u;
static const char * pFieldLocToReturn = NULL;
static size_t fieldLenToReturn = 0u;
static uint8_t invokeHeaderValueCallback = 0u;
static const char * pValueLocToReturn = NULL;
static size_t valueLenToReturn = 0u;
static int expectedValCbRetVal = 0;
static uint8_t invokeHeaderCompleteCallback = 0u;
static unsigned int parserErrNo = 0;

/* ============================ Helper Functions ============================== */

/**
 * @brief Callback that is passed to the mock of http_parse_init function
 * to set test expectations on input arguments sent by the HTTP API function under
 * test.
 */
void parserInitExpectationCb( http_parser * parser,
                              enum http_parser_type type,
                              int cmock_num_calls )
{
    /* Disable unused parameter warning. */
    ( void ) cmock_num_calls;

    TEST_ASSERT_NOT_NULL( parser );
    pCapturedParser = parser;

    TEST_ASSERT_EQUAL( HTTP_RESPONSE, type );
}

/**
 * @brief Callback that is passed to the mock of http_parse_settings_init function
 * to set test expectations on input arguments sent by the HTTP API function under
 * test.
 */
void parserSettingsInitExpectationCb( http_parser_settings * settings,
                                      int cmock_num_calls )
{
    /* Disable unused parameter warning. */
    ( void ) cmock_num_calls;

    TEST_ASSERT_NOT_NULL( settings );
    pCapturedSettings = settings;
}

/**
 * @brief Callback that is passed to the mock of http_parse_execute() function
 * to set test expectations on input arguments, and inject behavior of invoking
 * http-parser callbacks depending on test-case specific configuration of the
 * function.
 */
size_t parserExecuteExpectationsCb( http_parser * parser,
                                    const http_parser_settings * settings,
                                    const char * data,
                                    size_t len,
                                    int cmock_num_calls )
{
    /* Disable unused parameter warning. */
    ( void ) cmock_num_calls;

    TEST_ASSERT_NOT_NULL( settings );
    TEST_ASSERT_EQUAL( pCapturedParser, parser );
    TEST_ASSERT_NOT_NULL( parser );
    TEST_ASSERT_EQUAL( pCapturedSettings, settings );

    TEST_ASSERT_EQUAL( expectedBufferSize, len );
    TEST_ASSERT_EQUAL( pExpectedBuffer, data );

    if( invokeHeaderFieldCallback == 1u )
    {
        TEST_ASSERT_EQUAL( HTTP_PARSER_CONTINUE_PARSING,
                           settings->on_header_field( parser,
                                                      pFieldLocToReturn,
                                                      fieldLenToReturn ) );
    }

    if( invokeHeaderValueCallback == 1u )
    {
        TEST_ASSERT_EQUAL( expectedValCbRetVal,
                           settings->on_header_value( parser,
                                                      pValueLocToReturn,
                                                      valueLenToReturn ) );
    }

    if( invokeHeaderCompleteCallback == 1u )
    {
        TEST_ASSERT_EQUAL( HTTP_PARSER_STOP_PARSING,
                           settings->on_headers_complete( parser ) );
    }

    /* Set the error value in the parser. */
    parser->http_errno = parserErrNo;
    return len;
}

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
    int numBytes = snprintf( ( char * ) testRequestHeaders->pBuffer,
                             bufferSize,
                             "%s",
                             preexistingData );
    /* Make sure that the entire pre-existing data was printed to the buffer. */
    TEST_ASSERT_GREATER_THAN( 0, numBytes );
    TEST_ASSERT_LESS_THAN( bufferSize, ( size_t ) numBytes );
    testRequestHeaders->headersLen = dataLen;

    /* Fill the same data in the expected buffer as HTTPClient_AddRangeHeaders()
     * is not expected to change it. */
    memcpy( expectedHeaders->buffer, testRequestHeaders->pBuffer,
            testRequestHeaders->headersLen );
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
    size_t expectedRangeLen = RANGE_REQUEST_HEADER_FIELD_LEN +
                              HTTP_HEADER_FIELD_SEPARATOR_LEN +
                              RANGE_REQUEST_HEADER_VALUE_PREFIX_LEN +
                              strlen( expectedRange ) +
                              2 * HTTP_HEADER_LINE_SEPARATOR_LEN;

    int numBytes =
        snprintf( ( char * ) expectedHeaders->buffer +
                  expectedHeaders->dataLen -
                  ( terminatorExists ? HTTP_HEADER_LINE_SEPARATOR_LEN : 0 ),
                  sizeof( expectedHeaders->buffer ) - expectedHeaders->dataLen,
                  "%s%s%s%s\r\n\r\n",
                  RANGE_REQUEST_HEADER_FIELD,
                  HTTP_HEADER_FIELD_SEPARATOR,
                  RANGE_REQUEST_HEADER_VALUE_PREFIX,
                  expectedRange );

    /* Make sure that the Range request was printed to the buffer. */
    TEST_ASSERT_GREATER_THAN( 0, numBytes );
    TEST_ASSERT_LESS_THAN( sizeof( expectedHeaders->buffer ), ( size_t ) numBytes );

    expectedHeaders->dataLen += expectedRangeLen -
                                ( terminatorExists ? HTTP_HEADER_LINE_SEPARATOR_LEN : 0 );
}

/* ============================ UNITY FIXTURES ============================== */

/* Called before each test method. */
void setUp()
{
    testResponse.pBuffer = ( uint8_t * ) &pTestResponse[ 0 ];
    testResponse.bufferLen = strlen( pTestResponse );

    /* Configure the http_parser mocks with their callbacks. */
    http_parser_init_AddCallback( parserInitExpectationCb );
    http_parser_settings_init_AddCallback( parserSettingsInitExpectationCb );
    http_parser_execute_AddCallback( parserExecuteExpectationsCb );

    /* Ignore the calls to http_errno_description. */
    http_errno_description_IgnoreAndReturn( "Mocked HTTP Parser Status" );
}

/* Called after each test method. */
void tearDown()
{
    retCode = HTTP_INTERNAL_ERROR;
    memset( &testHeaders, 0, sizeof( testHeaders ) );
    memset( testBuffer, 0, sizeof( testBuffer ) );
    memset( &expectedHeaders, 0, sizeof( expectedHeaders ) );
    memset( &testResponse,
            0,
            sizeof( testResponse ) );
    pValueLoc = NULL;
    valueLen = 0u;
    pValueLoc = NULL;
    valueLen = 0u;
    pExpectedBuffer = &pTestResponse[ 0 ];
    expectedBufferSize = strlen( pTestResponse );
    invokeHeaderFieldCallback = 0u;
    pFieldLocToReturn = NULL;
    fieldLenToReturn = 0u;
    invokeHeaderValueCallback = 0u;
    pValueLocToReturn = NULL;
    expectedValCbRetVal = 0;
    valueLenToReturn = 0u;
    invokeHeaderCompleteCallback = 0u;
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
 * @brief Initialize pRequestHeaders with static buffer.
 *
 * @param[in] pRequestHeaders Request header buffer information.
 */
static void setupBuffer( HTTPRequestHeaders_t * pRequestHeaders )
{
    pRequestHeaders->pBuffer = testBuffer;
    pRequestHeaders->bufferLen = sizeof( testBuffer );
}

/**
 * @brief Test happy path with zero-initialized requestHeaders and requestInfo.
 */
void test_Http_InitializeRequestHeaders_Happy_Path()
{
    HTTPStatus_t httpStatus = HTTP_INTERNAL_ERROR;
    HTTPRequestHeaders_t requestHeaders = { 0 };
    HTTPRequestInfo_t requestInfo = { 0 };
    int numBytes = 0;

    setupRequestInfo( &requestInfo );
    expectedHeaders.dataLen = HTTP_TEST_PREFIX_HEADER_LEN +
                              HTTP_CONNECTION_CLOSE_VALUE_LEN;
    setupBuffer( &requestHeaders );

    /* Happy Path testing. */
    numBytes = snprintf( ( char * ) expectedHeaders.buffer, sizeof( expectedHeaders.buffer ),
                         HTTP_TEST_HEADER_FORMAT,
                         HTTP_METHOD_GET, HTTP_TEST_REQUEST_PATH,
                         HTTP_PROTOCOL_VERSION,
                         HTTP_USER_AGENT_FIELD, HTTP_USER_AGENT_VALUE,
                         HTTP_HOST_FIELD, HTTP_TEST_HOST_VALUE,
                         HTTP_CONNECTION_FIELD, HTTP_CONNECTION_CLOSE_VALUE );
    /* Make sure that the entire pre-existing data was printed to the buffer. */
    TEST_ASSERT_GREATER_THAN( 0, numBytes );
    TEST_ASSERT_LESS_THAN( sizeof( expectedHeaders.buffer ), ( size_t ) numBytes );

    httpStatus = HTTPClient_InitializeRequestHeaders( &requestHeaders, &requestInfo );
    TEST_ASSERT_EQUAL( HTTP_SUCCESS, httpStatus );
    TEST_ASSERT_EQUAL( expectedHeaders.dataLen, requestHeaders.headersLen );
    TEST_ASSERT_EQUAL_MEMORY( expectedHeaders.buffer, requestHeaders.pBuffer,
                              expectedHeaders.dataLen );
}

/**
 * @brief Test NULL parameters, following order of else-if blocks in the HTTP library.
 */
void test_Http_InitializeRequestHeaders_Invalid_Params()
{
    HTTPStatus_t httpStatus = HTTP_INTERNAL_ERROR;
    HTTPRequestHeaders_t requestHeaders = { 0 };
    HTTPRequestInfo_t requestInfo = { 0 };

    /* Test NULL parameters, following order of else-if blocks. */
    httpStatus = HTTPClient_InitializeRequestHeaders( NULL, &requestInfo );
    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, httpStatus );

    /* TEST requestInfo.pBuffer == NULL */
    httpStatus = HTTPClient_InitializeRequestHeaders( &requestHeaders, &requestInfo );
    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, httpStatus );
    requestHeaders.pBuffer = testBuffer;
    requestHeaders.bufferLen = HTTP_TEST_INITIALIZED_HEADER_BUFFER_LEN;

    /* Test requestInfo == NULL. */
    httpStatus = HTTPClient_InitializeRequestHeaders( &requestHeaders, NULL );
    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, httpStatus );

    /* Test requestInfo.method == NULL. */
    httpStatus = HTTPClient_InitializeRequestHeaders( &requestHeaders, &requestInfo );
    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, httpStatus );
    requestInfo.method = HTTP_METHOD_GET;

    /* Test requestInfo.pHost == NULL. */
    httpStatus = HTTPClient_InitializeRequestHeaders( &requestHeaders, &requestInfo );
    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, httpStatus );

    /* Test requestInfo.methodLen == 0. */
    requestInfo.pHost = HTTP_TEST_HOST_VALUE;
    httpStatus = HTTPClient_InitializeRequestHeaders( &requestHeaders, &requestInfo );
    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, httpStatus );

    /* Test requestInfo.hostLen == 0. */
    requestInfo.methodLen = HTTP_METHOD_GET_LEN;
    httpStatus = HTTPClient_InitializeRequestHeaders( &requestHeaders, &requestInfo );
    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, httpStatus );
}

/**
 * @brief Test default path "/" if path == NULL. Also, check that the "Connection"
 * header is set to "keep-alive" when HTTP_REQUEST_KEEP_ALIVE_FLAG in requestHeaders
 * is activated.
 */
void test_Http_InitializeRequestHeaders_ReqInfo()
{
    HTTPStatus_t httpStatus = HTTP_INTERNAL_ERROR;
    HTTPRequestHeaders_t requestHeaders = { 0 };
    HTTPRequestInfo_t requestInfo = { 0 };
    int numBytes = 0;

    setupRequestInfo( &requestInfo );
    expectedHeaders.dataLen = HTTP_TEST_PREFIX_HEADER_LEN -
                              HTTP_TEST_REQUEST_PATH_LEN +
                              HTTP_EMPTY_PATH_LEN +
                              HTTP_CONNECTION_KEEP_ALIVE_VALUE_LEN;
    setupBuffer( &requestHeaders );

    requestInfo.pPath = 0;
    requestInfo.flags = HTTP_REQUEST_KEEP_ALIVE_FLAG;
    numBytes = snprintf( ( char * ) expectedHeaders.buffer, sizeof( expectedHeaders.buffer ),
                         HTTP_TEST_HEADER_FORMAT,
                         HTTP_METHOD_GET, HTTP_EMPTY_PATH,
                         HTTP_PROTOCOL_VERSION,
                         HTTP_USER_AGENT_FIELD, HTTP_USER_AGENT_VALUE,
                         HTTP_HOST_FIELD, HTTP_TEST_HOST_VALUE,
                         HTTP_CONNECTION_FIELD, HTTP_CONNECTION_KEEP_ALIVE_VALUE );
    /* Make sure that the entire pre-existing data was printed to the buffer. */
    TEST_ASSERT_GREATER_THAN( 0, numBytes );
    TEST_ASSERT_LESS_THAN( sizeof( expectedHeaders.buffer ), ( size_t ) numBytes );

    requestHeaders.pBuffer = testBuffer;
    requestHeaders.bufferLen = expectedHeaders.dataLen;
    httpStatus = HTTPClient_InitializeRequestHeaders( &requestHeaders, &requestInfo );
    TEST_ASSERT_EQUAL( HTTP_SUCCESS, httpStatus );
    TEST_ASSERT_EQUAL( expectedHeaders.dataLen, requestHeaders.headersLen );
    TEST_ASSERT_EQUAL_MEMORY( expectedHeaders.buffer, requestHeaders.pBuffer,
                              expectedHeaders.dataLen );
}

/**
 * @brief Test HTTP_INSUFFICIENT_MEMORY from having requestHeaders.bufferLen less than
 * what is required to fit HTTP_TEST_REQUEST_LINE.
 */
void test_Http_InitializeRequestHeaders_Insufficient_Memory()
{
    HTTPStatus_t httpStatus = HTTP_INTERNAL_ERROR;
    HTTPRequestHeaders_t requestHeaders = { 0 };
    HTTPRequestInfo_t requestInfo = { 0 };

    expectedHeaders.dataLen = HTTP_TEST_MAX_INITIALIZED_HEADER_LEN;

    setupRequestInfo( &requestInfo );
    setupBuffer( &requestHeaders );

    requestHeaders.bufferLen = HTTP_TEST_REQUEST_LINE_LEN - 1;

    httpStatus = HTTPClient_InitializeRequestHeaders( &requestHeaders, &requestInfo );
    TEST_ASSERT_EQUAL( HTTP_INSUFFICIENT_MEMORY, httpStatus );
    TEST_ASSERT_TRUE( strncmp( ( char * ) requestHeaders.pBuffer,
                               HTTP_TEST_REQUEST_LINE,
                               HTTP_TEST_REQUEST_LINE_LEN ) != 0 );
}

/* ===================== Testing HTTPClient_AddHeader ======================= */

/**
 * @brief Prefill the user buffer with HTTP_TEST_HEADER_REQUEST_LINE and call
 * HTTPClient_AddHeader using HTTP_TEST_HEADER_FIELD and HTTP_TEST_HEADER_VALUE.
 */
void test_Http_AddHeader_Happy_Path()
{
    HTTPStatus_t httpStatus = HTTP_INTERNAL_ERROR;
    HTTPRequestHeaders_t requestHeaders = { 0 };
    int numBytes = 0;

    setupBuffer( &requestHeaders );

    /* Add 1 because snprintf(...) writes a null byte at the end. */
    numBytes = snprintf( expectedHeaders.buffer, sizeof( expectedHeaders.buffer ),
                         HTTP_TEST_SINGLE_HEADER_FORMAT,
                         HTTP_TEST_HEADER_REQUEST_LINE,
                         HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_VALUE );
    /* Make sure that the entire pre-existing data was printed to the buffer. */
    TEST_ASSERT_GREATER_THAN( 0, numBytes );
    TEST_ASSERT_LESS_THAN( sizeof( expectedHeaders.buffer ), ( size_t ) numBytes );
    expectedHeaders.dataLen = HTTP_TEST_SINGLE_HEADER_LEN;

    /* Set parameters for requestHeaders. */
    numBytes = snprintf( ( char * ) requestHeaders.pBuffer,
                         HTTP_TEST_HEADER_REQUEST_LINE_LEN + 1,
                         HTTP_TEST_HEADER_REQUEST_LINE );
    /* Make sure that the entire pre-existing data was printed to the buffer. */
    TEST_ASSERT_GREATER_THAN( 0, numBytes );
    TEST_ASSERT_LESS_THAN( requestHeaders.bufferLen, ( size_t ) numBytes );
    /* We correctly set headersLen after writing request line to requestHeaders.pBuffer. */
    requestHeaders.headersLen = HTTP_TEST_HEADER_REQUEST_LINE_LEN;

    /* Run the method to test. */
    httpStatus = HTTPClient_AddHeader( &requestHeaders,
                                       HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_FIELD_LEN,
                                       HTTP_TEST_HEADER_VALUE, HTTP_TEST_HEADER_VALUE_LEN );
    TEST_ASSERT_EQUAL( expectedHeaders.dataLen, requestHeaders.headersLen );
    TEST_ASSERT_EQUAL_MEMORY( expectedHeaders.buffer,
                              requestHeaders.pBuffer, expectedHeaders.dataLen );
    TEST_ASSERT_EQUAL( HTTP_SUCCESS, httpStatus );
}

/**
 * @brief Test invalid parameters, following order of else-if blocks in the HTTP library.
 */
void test_Http_AddHeader_Invalid_Parameters()
{
    HTTPStatus_t httpStatus = HTTP_INTERNAL_ERROR;
    HTTPRequestHeaders_t requestHeaders = { 0 };

    /* Test a NULL request headers interface. */
    httpStatus = HTTPClient_AddHeader( NULL,
                                       HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_FIELD_LEN,
                                       HTTP_TEST_HEADER_VALUE, HTTP_TEST_HEADER_VALUE_LEN );
    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, httpStatus );

    /* Test a NULL pBuffer member of request headers. */
    requestHeaders.pBuffer = NULL;
    httpStatus = HTTPClient_AddHeader( &requestHeaders,
                                       HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_FIELD_LEN,
                                       HTTP_TEST_HEADER_VALUE, HTTP_TEST_HEADER_VALUE_LEN );
    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, httpStatus );

    /* Test NULL header field. */
    requestHeaders.pBuffer = testBuffer;
    requestHeaders.bufferLen = HTTP_TEST_DOUBLE_HEADER_LEN;
    httpStatus = HTTPClient_AddHeader( &requestHeaders,
                                       NULL, HTTP_TEST_HEADER_FIELD_LEN,
                                       HTTP_TEST_HEADER_VALUE, HTTP_TEST_HEADER_VALUE_LEN );
    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, httpStatus );

    /* Test NULL header value. */
    httpStatus = HTTPClient_AddHeader( &requestHeaders,
                                       HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_FIELD_LEN,
                                       NULL, HTTP_TEST_HEADER_VALUE_LEN );
    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, httpStatus );

    /* Test that fieldLen > 0. */
    httpStatus = HTTPClient_AddHeader( &requestHeaders,
                                       HTTP_TEST_HEADER_FIELD, 0,
                                       HTTP_TEST_HEADER_VALUE, HTTP_TEST_HEADER_VALUE_LEN );
    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, httpStatus );

    /* Test that valueLen > 0. */
    httpStatus = HTTPClient_AddHeader( &requestHeaders,
                                       HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_FIELD_LEN,
                                       HTTP_TEST_HEADER_VALUE, 0 );
    TEST_ASSERT_EQUAL( HTTP_INVALID_PARAMETER, httpStatus );
}

/**
 * @brief Test adding extra header with sufficient memory.
 */
void test_Http_AddHeader_Extra_Header_Sufficient_Memory()
{
    HTTPStatus_t httpStatus = HTTP_INTERNAL_ERROR;
    HTTPRequestHeaders_t requestHeaders = { 0 };
    int numBytes = 0;

    setupBuffer( &requestHeaders );

    /* Add 1 because snprintf(...) writes a null byte at the end. */
    numBytes = snprintf( expectedHeaders.buffer, sizeof( expectedHeaders.buffer ),
                         HTTP_TEST_DOUBLE_HEADER_FORMAT,
                         HTTP_TEST_HEADER_REQUEST_LINE,
                         HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_VALUE,
                         HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_VALUE );
    /* Make sure that the entire pre-existing data was printed to the buffer. */
    TEST_ASSERT_GREATER_THAN( 0, numBytes );
    TEST_ASSERT_LESS_THAN( sizeof( expectedHeaders.buffer ), ( size_t ) numBytes );
    expectedHeaders.dataLen = HTTP_TEST_DOUBLE_HEADER_LEN;

    /* Prefill the buffer with a request line and header. */
    numBytes = snprintf( ( char * ) requestHeaders.pBuffer,
                         HTTP_TEST_SINGLE_HEADER_LEN + 1,
                         HTTP_TEST_SINGLE_HEADER_FORMAT,
                         HTTP_TEST_HEADER_REQUEST_LINE,
                         HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_VALUE );
    TEST_ASSERT_EQUAL( HTTP_TEST_SINGLE_HEADER_LEN, numBytes );
    requestHeaders.headersLen = HTTP_TEST_SINGLE_HEADER_LEN;
    requestHeaders.bufferLen = expectedHeaders.dataLen;

    /* Run the method to test. */
    httpStatus = HTTPClient_AddHeader( &requestHeaders,
                                       HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_FIELD_LEN,
                                       HTTP_TEST_HEADER_VALUE, HTTP_TEST_HEADER_VALUE_LEN );
    TEST_ASSERT_EQUAL( expectedHeaders.dataLen, requestHeaders.headersLen );
    TEST_ASSERT_EQUAL_MEMORY( expectedHeaders.buffer,
                              requestHeaders.pBuffer, expectedHeaders.dataLen );
    TEST_ASSERT_EQUAL( HTTP_SUCCESS, httpStatus );
}

/**
 * @brief Test adding extra header with insufficient memory.
 */
void test_Http_AddHeader_Extra_Header_Insufficient_Memory()
{
    HTTPStatus_t httpStatus = HTTP_INTERNAL_ERROR;
    HTTPRequestHeaders_t requestHeaders = { 0 };
    int numBytes = 0;

    setupBuffer( &requestHeaders );

    /* Add 1 because snprintf(...) writes a null byte at the end. */
    numBytes = snprintf( expectedHeaders.buffer, sizeof( expectedHeaders.buffer ),
                         HTTP_TEST_SINGLE_HEADER_FORMAT,
                         HTTP_TEST_HEADER_REQUEST_LINE,
                         HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_VALUE );
    /* Make sure that the entire pre-existing data was printed to the buffer. */
    TEST_ASSERT_GREATER_THAN( 0, numBytes );
    TEST_ASSERT_LESS_THAN( sizeof( expectedHeaders.buffer ), ( size_t ) numBytes );
    expectedHeaders.dataLen = HTTP_TEST_SINGLE_HEADER_LEN;

    /* Prefill the buffer with a request line and header. */
    numBytes = snprintf( ( char * ) requestHeaders.pBuffer,
                         HTTP_TEST_SINGLE_HEADER_LEN + 1,
                         HTTP_TEST_SINGLE_HEADER_FORMAT,
                         HTTP_TEST_HEADER_REQUEST_LINE,
                         HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_VALUE );
    /* Make sure that the entire pre-existing data was printed to the buffer. */
    TEST_ASSERT_GREATER_THAN( 0, numBytes );
    TEST_ASSERT_LESS_THAN( requestHeaders.bufferLen, ( size_t ) numBytes );
    requestHeaders.headersLen = HTTP_TEST_SINGLE_HEADER_LEN;
    requestHeaders.bufferLen = requestHeaders.headersLen;

    /* Run the method to test. */
    httpStatus = HTTPClient_AddHeader( &requestHeaders,
                                       HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_FIELD_LEN,
                                       HTTP_TEST_HEADER_VALUE, HTTP_TEST_HEADER_VALUE_LEN );
    TEST_ASSERT_EQUAL( expectedHeaders.dataLen, requestHeaders.headersLen );
    TEST_ASSERT_EQUAL_MEMORY( expectedHeaders.buffer,
                              requestHeaders.pBuffer, expectedHeaders.dataLen );
    TEST_ASSERT_EQUAL( HTTP_INSUFFICIENT_MEMORY, httpStatus );
}

/**
 * @brief Test HTTP_INSUFFICIENT_MEMORY error from having buffer size less than
 * what is required to fit a single HTTP header.
 */
void test_Http_AddHeader_Single_Header_Insufficient_Memory()
{
    HTTPStatus_t httpStatus = HTTP_INTERNAL_ERROR;
    HTTPRequestHeaders_t requestHeaders = { 0 };
    int numBytes = 0;

    setupBuffer( &requestHeaders );

    /* Add 1 because snprintf(...) writes a null byte at the end. */
    numBytes = snprintf( ( char * ) testBuffer,
                         HTTP_TEST_HEADER_REQUEST_LINE_LEN + 1,
                         HTTP_TEST_HEADER_REQUEST_LINE );
    /* Make sure that the entire pre-existing data was printed to the buffer. */
    TEST_ASSERT_GREATER_THAN( 0, numBytes );
    TEST_ASSERT_LESS_THAN( sizeof( testBuffer ), ( size_t ) numBytes );
    requestHeaders.headersLen = HTTP_TEST_HEADER_REQUEST_LINE_LEN;
    requestHeaders.pBuffer = testBuffer;
    requestHeaders.bufferLen = HTTP_TEST_SINGLE_HEADER_LEN - 1;

    /* Run the method to test. */
    httpStatus = HTTPClient_AddHeader( &requestHeaders,
                                       HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_FIELD_LEN,
                                       HTTP_TEST_HEADER_VALUE, HTTP_TEST_HEADER_VALUE_LEN );
    TEST_ASSERT_EQUAL( HTTP_INSUFFICIENT_MEMORY, httpStatus );
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
    /* The input buffer size is zero! */
    testHeaders.bufferLen = 0u;
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         0 /* rangeStart */,
                                         10 /* rageEnd */ );
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

    /* Update the expected header with the complete the range request header
     * to determine the total required size of the buffer. */
    addRangeToExpectedHeaders( &expectedHeaders,
                               "5-10" /*expected range*/,
                               1u );

    /* Change the input headers buffer size to be one byte short of the required
     * size to add Range Request header. */
    testHeaders.bufferLen = expectedHeaders.dataLen - 1;

    /* As the call to the API function is expected to fail, we need to store a
     * local copy of the input headers buffer to verify that the data has not changed
     * after the API call returns. Thus, overwrite the expected headers buffer with the
     * copy of the complete input headers buffer to use for verification later. */
    TEST_ASSERT_GREATER_OR_EQUAL( testHeaders.bufferLen, sizeof( expectedHeaders.buffer ) );
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
                               0u );
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
                               1u );
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
                               1u );
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
                               1u );
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
                               1u );
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
                               1u );
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
                               1u );
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

/* ========================================================================== */

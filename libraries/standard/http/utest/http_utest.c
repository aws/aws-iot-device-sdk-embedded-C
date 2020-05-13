#include <stdbool.h>

#include "unity.h"

/* Include paths for public enums, structures, and macros. */
#include "http_client.h"

/* Private includes for internal macros. */
#include "private/http_client_internal.h"
#include "private/http_client_parse.h"

#define HTTP_TEST_REQUEST_METHOD        "GET"
#define HTTP_TEST_REQUEST_METHOD_LEN    ( sizeof( HTTP_TEST_REQUEST_METHOD ) - 1 )
#define HTTP_TEST_REQUEST_PATH          "/robots.txt"
#define HTTP_TEST_REQUEST_PATH_LEN      ( sizeof( HTTP_TEST_REQUEST_PATH ) - 1 )
#define HTTP_TEST_HOST_VALUE            "amazon.com"
#define HTTP_TEST_HOST_VALUE_LEN        ( sizeof( HTTP_TEST_HOST_VALUE ) - 1 )
#define HTTP_TEST_REQUEST_LINE     \
    ( HTTP_TEST_REQUEST_METHOD " " \
      HTTP_TEST_REQUEST_PATH " "   \
      HTTP_PROTOCOL_VERSION "\r\n" )
#define HTTP_TEST_REQUEST_LINE_LEN      ( sizeof( HTTP_TEST_REQUEST_LINE ) - 1 )

/* Used for format parameter in snprintf(...). */
#define HTTP_TEST_HEADER_FORMAT \
    "%s %s %s\r\n"              \
    "%s: %s\r\n"                \
    "%s: %s\r\n"                \
    "%s: %s\r\n\r\n"

/* Length of the following template HTTP header.
 *   <HTTP_TEST_REQUEST_METHOD> <HTTP_TEST_REQUEST_PATH> <HTTP_PROTOCOL_VERSION> \r\n
 *   <HTTP_USER_AGENT_FIELD>: <HTTP_USER_AGENT_FIELD_LEN> \r\n
 *   <HTTP_HOST_FIELD>: <HTTP_TEST_HOST_VALUE> \r\n
 *   <HTTP_CONNECTION_FIELD>: \r\n
 *   \r\n
 * This is used to initialize the expectedHeader string. Note the missing
 * <HTTP_TEST_CONNECTION_VALUE>. This is added later on depending on the
 * value of HTTP_REQUEST_KEEP_ALIVE_FLAG in pRequestInfo->flags. */
#define HTTP_TEST_PREFIX_HEADER_LEN                                 \
    ( HTTP_TEST_REQUEST_METHOD_LEN + SPACE_CHARACTER_LEN +          \
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

static uint8_t httpBuffer[ HTTP_TEST_BUFFER_LEN ] = { 0 };

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

/* ============== Testing HTTPClient_InitializeRequestHeaders =============== */

/**
 * @brief Initialize pRequestInfo with test-defined macros.
 *
 * @param[in] pRequestInfo Initial request header configurations.
 */
static void setupRequestInfo( HTTPRequestInfo_t * pRequestInfo )
{
    pRequestInfo->method = HTTP_TEST_REQUEST_METHOD;
    pRequestInfo->methodLen = HTTP_TEST_REQUEST_METHOD_LEN;
    pRequestInfo->pPath = HTTP_TEST_REQUEST_PATH;
    pRequestInfo->pathLen = HTTP_TEST_REQUEST_PATH_LEN;
    pRequestInfo->pHost = HTTP_TEST_HOST_VALUE;
    pRequestInfo->hostLen = HTTP_TEST_HOST_VALUE_LEN;
    pRequestInfo->flags = 0;
}

/**
 * @brief Initialize pRequestHeaders based on parameters.
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
                         HTTP_TEST_REQUEST_METHOD, HTTP_TEST_REQUEST_PATH,
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
    requestInfo.method = HTTP_TEST_REQUEST_METHOD;
    test_err = HTTPClient_InitializeRequestHeaders( &requestHeaders, &requestInfo );
    TEST_ASSERT_EQUAL( test_err, HTTP_INVALID_PARAMETER );
    requestInfo.pHost = HTTP_TEST_HOST_VALUE;
    test_err = HTTPClient_InitializeRequestHeaders( &requestHeaders, &requestInfo );
    TEST_ASSERT_EQUAL( test_err, HTTP_INVALID_PARAMETER );
    requestInfo.pPath = HTTP_TEST_REQUEST_PATH;
    requestInfo.pathLen = HTTP_TEST_REQUEST_PATH_LEN;
    test_err = HTTPClient_InitializeRequestHeaders( &requestHeaders, &requestInfo );
    TEST_ASSERT_EQUAL( test_err, HTTP_INVALID_PARAMETER );
    requestInfo.methodLen = HTTP_TEST_REQUEST_METHOD_LEN;
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
                         HTTP_TEST_REQUEST_METHOD, HTTP_EMPTY_PATH,
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

/* ========================================================================== */

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
 * value of HTTP_REQUEST_KEEP_ALIVE_FLAG in pReqInfo->flags. */
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
#define HTTP_TEST_MAX_HEADER_LEN \
    ( HTTP_TEST_PREFIX_HEADER_LEN + HTTP_CONNECTION_KEEP_ALIVE_VALUE_LEN )

/* Add 1 because snprintf(...) writes a null byte at the end. */
#define HTTP_TEST_BUFFER_SIZE    ( HTTP_TEST_MAX_HEADER_LEN + 1 )


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
void setupReqInfo( HTTPRequestInfo_t * pReqInfo )
{
    pReqInfo->method = HTTP_TEST_REQUEST_METHOD;
    pReqInfo->methodLen = HTTP_TEST_REQUEST_METHOD_LEN;
    pReqInfo->pPath = HTTP_TEST_REQUEST_PATH;
    pReqInfo->pathLen = HTTP_TEST_REQUEST_PATH_LEN;
    pReqInfo->pHost = HTTP_TEST_HOST_VALUE;
    pReqInfo->hostLen = HTTP_TEST_HOST_VALUE_LEN;
    pReqInfo->flags = 0;
}

void setupBuffer( HTTPRequestHeaders_t * pReqHeaders,
                  uint8_t * buffer,
                  size_t expectedHeaderLen )
{
    pReqHeaders->pBuffer = buffer;
    pReqHeaders->bufferLen = expectedHeaderLen;
}

void test_Http_InitializeRequestHeaders_happy_path()
{
    HTTPStatus_t test_err = HTTP_INTERNAL_ERROR;
    HTTPRequestHeaders_t reqHeaders = { 0 };
    HTTPRequestInfo_t reqInfo = { 0 };
    uint8_t buffer[ HTTP_TEST_BUFFER_SIZE ] = { 0 };
    char expectedHeader[ HTTP_TEST_BUFFER_SIZE ] = { 0 };
    size_t expectedHeaderLen = HTTP_TEST_MAX_HEADER_LEN;

    setupReqInfo( &reqInfo );
    setupBuffer( &reqHeaders, buffer, expectedHeaderLen );

    /* Happy Path testing. */
    expectedHeaderLen = HTTP_TEST_PREFIX_HEADER_LEN +
                        HTTP_CONNECTION_CLOSE_VALUE_LEN;
    int numBytes = snprintf( expectedHeader, expectedHeaderLen + 1,
                             HTTP_TEST_HEADER_FORMAT,
                             HTTP_TEST_REQUEST_METHOD, HTTP_TEST_REQUEST_PATH,
                             HTTP_PROTOCOL_VERSION,
                             HTTP_USER_AGENT_FIELD, HTTP_USER_AGENT_VALUE,
                             HTTP_HOST_FIELD, HTTP_TEST_HOST_VALUE,
                             HTTP_CONNECTION_FIELD, HTTP_CONNECTION_CLOSE_VALUE );
    TEST_ASSERT_EQUAL( numBytes, expectedHeaderLen );
    test_err = HTTPClient_InitializeRequestHeaders( &reqHeaders, &reqInfo );
    TEST_ASSERT_EQUAL_MEMORY( reqHeaders.pBuffer, expectedHeader, expectedHeaderLen );
    TEST_ASSERT_EQUAL( reqHeaders.headersLen, expectedHeaderLen );
    TEST_ASSERT_EQUAL( test_err, HTTP_SUCCESS );
}

void test_Http_InitializeRequestHeaders_invalid_params()
{
    HTTPStatus_t test_err = HTTP_INTERNAL_ERROR;
    HTTPRequestHeaders_t reqHeaders = { 0 };
    HTTPRequestInfo_t reqInfo = { 0 };
    uint8_t buffer[ HTTP_TEST_BUFFER_SIZE ] = { 0 };
    char expectedHeader[ HTTP_TEST_BUFFER_SIZE ] = { 0 };
    size_t expectedHeaderLen = HTTP_TEST_MAX_HEADER_LEN;

    /* Test NULL parameters, following order of else-if blocks. */
    test_err = HTTPClient_InitializeRequestHeaders( NULL, &reqInfo );
    TEST_ASSERT_EQUAL( test_err, HTTP_INVALID_PARAMETER );
    /* TEST reqInfo.pBuffer == NULL */
    test_err = HTTPClient_InitializeRequestHeaders( &reqHeaders, &reqInfo );
    TEST_ASSERT_EQUAL( test_err, HTTP_INVALID_PARAMETER );
    reqHeaders.pBuffer = buffer;
    reqHeaders.bufferLen = HTTP_TEST_BUFFER_SIZE;
    test_err = HTTPClient_InitializeRequestHeaders( &reqHeaders, NULL );
    TEST_ASSERT_EQUAL( test_err, HTTP_INVALID_PARAMETER );
    /* Test reqInfo members are NULL */
    test_err = HTTPClient_InitializeRequestHeaders( &reqHeaders, &reqInfo );
    TEST_ASSERT_EQUAL( test_err, HTTP_INVALID_PARAMETER );
    reqInfo.method = HTTP_TEST_REQUEST_METHOD;
    test_err = HTTPClient_InitializeRequestHeaders( &reqHeaders, &reqInfo );
    TEST_ASSERT_EQUAL( test_err, HTTP_INVALID_PARAMETER );
    reqInfo.pHost = HTTP_TEST_HOST_VALUE;
    test_err = HTTPClient_InitializeRequestHeaders( &reqHeaders, &reqInfo );
    TEST_ASSERT_EQUAL( test_err, HTTP_INVALID_PARAMETER );
    reqInfo.pPath = HTTP_TEST_REQUEST_PATH;
    reqInfo.pathLen = HTTP_TEST_REQUEST_PATH_LEN;
    test_err = HTTPClient_InitializeRequestHeaders( &reqHeaders, &reqInfo );
    TEST_ASSERT_EQUAL( test_err, HTTP_INVALID_PARAMETER );
    reqInfo.methodLen = HTTP_TEST_REQUEST_METHOD_LEN;
    test_err = HTTPClient_InitializeRequestHeaders( &reqHeaders, &reqInfo );
    TEST_ASSERT_EQUAL( test_err, HTTP_INVALID_PARAMETER );
    reqInfo.hostLen = HTTP_TEST_HOST_VALUE_LEN;
}

void test_Http_InitializeRequestHeaders_keep_alive_header()
{
    HTTPStatus_t test_err = HTTP_INTERNAL_ERROR;
    HTTPRequestHeaders_t reqHeaders = { 0 };
    HTTPRequestInfo_t reqInfo = { 0 };
    uint8_t buffer[ HTTP_TEST_BUFFER_SIZE ] = { 0 };
    char expectedHeader[ HTTP_TEST_BUFFER_SIZE ] = { 0 };
    size_t expectedHeaderLen = HTTP_TEST_MAX_HEADER_LEN;

    setupReqInfo( &reqInfo );
    setupBuffer( &reqHeaders, buffer, expectedHeaderLen );

    reqInfo.flags = HTTP_REQUEST_KEEP_ALIVE_FLAG;
    expectedHeaderLen = HTTP_TEST_PREFIX_HEADER_LEN + \
                        HTTP_CONNECTION_KEEP_ALIVE_VALUE_LEN;
    int numBytes = snprintf( expectedHeader, expectedHeaderLen + 1,
                             HTTP_TEST_HEADER_FORMAT,
                             HTTP_TEST_REQUEST_METHOD, HTTP_TEST_REQUEST_PATH,
                             HTTP_PROTOCOL_VERSION,
                             HTTP_USER_AGENT_FIELD, HTTP_USER_AGENT_VALUE,
                             HTTP_HOST_FIELD, HTTP_TEST_HOST_VALUE,
                             HTTP_CONNECTION_FIELD, HTTP_CONNECTION_KEEP_ALIVE_VALUE );
    TEST_ASSERT_EQUAL( numBytes, expectedHeaderLen );

    reqHeaders.pBuffer = buffer;
    reqHeaders.bufferLen = expectedHeaderLen;
    test_err = HTTPClient_InitializeRequestHeaders( &reqHeaders, &reqInfo );
    TEST_ASSERT_EQUAL_MEMORY( reqHeaders.pBuffer, expectedHeader, expectedHeaderLen );
    TEST_ASSERT_EQUAL( reqHeaders.headersLen, expectedHeaderLen );
    TEST_ASSERT_EQUAL( test_err, HTTP_SUCCESS );
}

void test_Http_InitializeRequestHeaders_insufficient_memory()
{
    HTTPStatus_t test_err = HTTP_INTERNAL_ERROR;
    HTTPRequestHeaders_t reqHeaders = { 0 };
    HTTPRequestInfo_t reqInfo = { 0 };
    uint8_t buffer[ HTTP_TEST_BUFFER_SIZE ] = { 0 };
    char expectedHeader[ HTTP_TEST_BUFFER_SIZE ] = { 0 };
    size_t expectedHeaderLen = HTTP_TEST_MAX_HEADER_LEN;

    setupReqInfo( &reqInfo );
    setupBuffer( &reqHeaders, buffer, expectedHeaderLen );

    reqHeaders.bufferLen = HTTP_TEST_REQUEST_LINE_LEN - 1;

    test_err = HTTPClient_InitializeRequestHeaders( &reqHeaders, &reqInfo );
    TEST_ASSERT_EQUAL( test_err, HTTP_INSUFFICIENT_MEMORY );
    TEST_ASSERT_TRUE( strncmp( ( char * ) reqHeaders.pBuffer,
                               HTTP_TEST_REQUEST_LINE,
                               HTTP_TEST_REQUEST_LINE_LEN ) != 0 );
}

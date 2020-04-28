#include <string.h>

#include "common.h"

/* Functions are pulled out into their own C files to be tested as a unit. */
#include "_writeRequestLine.c"
#include "_addHeader.c"
#include "HTTPClient_InitializeRequestHeaders.c"

#define HTTP_TEST_REQUEST_METHOD        "GET"
#define HTTP_TEST_REQUEST_METHOD_LEN    ( sizeof( HTTP_TEST_REQUEST_METHOD ) - 1 )
#define HTTP_TEST_REQUEST_PATH          "/robots.txt"
#define HTTP_TEST_REQUEST_PATH_LEN      ( sizeof( HTTP_TEST_REQUEST_PATH ) - 1 )
#define HTTP_TEST_HOST_VALUE            "amazon.com"
#define HTTP_TEST_HOST_VALUE_LEN        ( sizeof( HTTP_TEST_HOST_VALUE ) - 1 )

/* Used for format parameter in snprintf(...). */
#define HTTP_TEST_HEADER_FORMAT \
    "%s %s %s\r\n"              \
    "%s: %s\r\n"                \
    "%s: %s\r\n"                \
    "%s: %s\r\n\r\n"

#define HTTP_REQUEST_HEADERS_INITIALIZER    { 0 }
#define HTTP_REQUEST_INFO_INITIALIZER       { 0 }

/* Length of the following template HTTP header.
 *   <HTTP_TEST_REQUEST_METHOD> <HTTP_TEST_REQUEST_PATH> <HTTP_PROTOCOL_VERSION> \r\n
 *   <HTTP_USER_AGENT_FIELD>: <HTTP_USER_AGENT_FIELD_LEN> \r\n
 *   <HTTP_HOST_FIELD>: <HTTP_TEST_HOST_VALUE> \r\n
 *   <HTTP_CONNECTION_FIELD>: \r\n
 *   \r\n
 * This is used to initialize the expectedHeader string. Note the missing
 * <HTTP_TEST_CONNECTION_VALUE>. This is added later on depending on the
 * value of HTTP_REQUEST_KEEP_ALIVE_FLAG in reqInfo->flags. */
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


int main()
{
    HTTPRequestHeaders_t reqHeaders = HTTP_REQUEST_HEADERS_INITIALIZER;
    HTTPRequestHeaders_t reqHeadersDflt = HTTP_REQUEST_HEADERS_INITIALIZER;
    HTTPRequestInfo_t reqInfo = HTTP_REQUEST_INFO_INITIALIZER;
    HTTPRequestInfo_t reqInfoDflt = HTTP_REQUEST_INFO_INITIALIZER;
    HTTPStatus_t test_err = HTTP_NOT_SUPPORTED;
    uint8_t buffer[ HTTP_TEST_BUFFER_SIZE ] = { 0 };
    char expectedHeader[ HTTP_TEST_BUFFER_SIZE ] = { 0 };
    size_t expectedHeaderLen = HTTP_TEST_MAX_HEADER_LEN;

/* Write template reqInfo to pass as parameter to
 * HTTPClient_InitializeRequestHeaders() method. */
#define fillReqInfoTemplate()                             \
    do {                                                  \
        reqInfo.method = HTTP_TEST_REQUEST_METHOD;        \
        reqInfo.methodLen = HTTP_TEST_REQUEST_METHOD_LEN; \
        reqInfo.pPath = HTTP_TEST_REQUEST_PATH;           \
        reqInfo.pathLen = HTTP_TEST_REQUEST_PATH_LEN;     \
        reqInfo.pHost = HTTP_TEST_HOST_VALUE;             \
        reqInfo.hostLen = HTTP_TEST_HOST_VALUE_LEN;       \
        reqInfo.flags = 0;                                \
    }                                                     \
    while( 0 )

#define reset()                                                    \
    do {                                                           \
        test_err = HTTP_NOT_SUPPORTED;                             \
        reqHeaders = reqHeadersDflt;                               \
        reqInfo = reqInfoDflt;                                     \
        memset( buffer, 0, HTTP_TEST_BUFFER_SIZE );                \
        memset( expectedHeader, 0, HTTP_TEST_MAX_HEADER_LEN + 1 ); \
    }                                                              \
    while( 0 )

    plan( 17 );

    /* Happy Path testing. */
    reset();
    expectedHeaderLen = HTTP_TEST_PREFIX_HEADER_LEN + \
                        HTTP_CONNECTION_CLOSE_VALUE_LEN;
    ok( snprintf( expectedHeader, expectedHeaderLen + 1,
                  HTTP_TEST_HEADER_FORMAT,
                  HTTP_TEST_REQUEST_METHOD, HTTP_TEST_REQUEST_PATH, HTTP_PROTOCOL_VERSION,
                  HTTP_USER_AGENT_FIELD, HTTP_USER_AGENT_VALUE,
                  HTTP_HOST_FIELD, HTTP_TEST_HOST_VALUE,
                  HTTP_CONNECTION_FIELD, HTTP_CONNECTION_CLOSE_VALUE )
        == expectedHeaderLen );
    /* Set parameters for reqHeaders. */
    reqHeaders.pBuffer = buffer;
    reqHeaders.bufferLen = expectedHeaderLen;
    /* Set parameters for reqInfo. */
    fillReqInfoTemplate();
    test_err = HTTPClient_InitializeRequestHeaders( &reqHeaders, &reqInfo );
    ok( strncmp( ( char * ) reqHeaders.pBuffer,
                 expectedHeader, expectedHeaderLen ) == 0 );
    ok( reqHeaders.headersLen == expectedHeaderLen );
    ok( test_err == HTTP_SUCCESS );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test NULL parameters, following order of else-if blocks. */
    test_err = HTTPClient_InitializeRequestHeaders( NULL, &reqInfo );
    ok( test_err == HTTP_INVALID_PARAMETER );
    /* reqInfo.pBuffer should be NULL after reset(). */
    test_err = HTTPClient_InitializeRequestHeaders( &reqHeaders, &reqInfo );
    ok( test_err == HTTP_INVALID_PARAMETER );
    reqHeaders.pBuffer = buffer;
    reqHeaders.bufferLen = HTTP_TEST_BUFFER_SIZE;
    test_err = HTTPClient_InitializeRequestHeaders( &reqHeaders, NULL );
    ok( test_err == HTTP_INVALID_PARAMETER );
    /* reqInfo members should be NULL after reset(). */
    test_err = HTTPClient_InitializeRequestHeaders( &reqHeaders, &reqInfo );
    ok( test_err == HTTP_INVALID_PARAMETER );
    reqInfo.method = HTTP_TEST_REQUEST_METHOD;
    test_err = HTTPClient_InitializeRequestHeaders( &reqHeaders, &reqInfo );
    ok( test_err == HTTP_INVALID_PARAMETER );
    reqInfo.pHost = HTTP_TEST_HOST_VALUE;
    test_err = HTTPClient_InitializeRequestHeaders( &reqHeaders, &reqInfo );
    ok( test_err == HTTP_INVALID_PARAMETER );
    reqInfo.pPath = HTTP_TEST_REQUEST_PATH;
    reqInfo.pathLen = HTTP_TEST_REQUEST_PATH_LEN;
    test_err = HTTPClient_InitializeRequestHeaders( &reqHeaders, &reqInfo );
    ok( test_err == HTTP_INVALID_PARAMETER );
    reqInfo.methodLen = HTTP_TEST_REQUEST_METHOD_LEN;
    test_err = HTTPClient_InitializeRequestHeaders( &reqHeaders, &reqInfo );
    ok( test_err == HTTP_INVALID_PARAMETER );
    reqInfo.hostLen = HTTP_TEST_HOST_VALUE_LEN;
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test HTTP_REQUEST_KEEP_ALIVE_FLAG. */
    fillReqInfoTemplate();
    reqInfo.flags = HTTP_REQUEST_KEEP_ALIVE_FLAG;
    expectedHeaderLen = HTTP_TEST_PREFIX_HEADER_LEN + \
                        HTTP_CONNECTION_KEEP_ALIVE_VALUE_LEN;
    ok( snprintf( expectedHeader, expectedHeaderLen + 1,
                  HTTP_TEST_HEADER_FORMAT,
                  HTTP_TEST_REQUEST_METHOD, HTTP_TEST_REQUEST_PATH,
                  HTTP_PROTOCOL_VERSION,
                  HTTP_USER_AGENT_FIELD, HTTP_USER_AGENT_VALUE,
                  HTTP_HOST_FIELD, HTTP_TEST_HOST_VALUE,
                  HTTP_CONNECTION_FIELD, HTTP_CONNECTION_KEEP_ALIVE_VALUE )
        == expectedHeaderLen );
    reqHeaders.pBuffer = buffer;
    reqHeaders.bufferLen = expectedHeaderLen;
    test_err = HTTPClient_InitializeRequestHeaders( &reqHeaders, &reqInfo );
    ok( strncmp( ( char * ) reqHeaders.pBuffer,
                 expectedHeader, expectedHeaderLen ) == 0 );
    ok( reqHeaders.headersLen == expectedHeaderLen );
    ok( test_err == HTTP_SUCCESS );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test default path "/" if path == NULL. */
    fillReqInfoTemplate();
    reqInfo.pPath = NULL;
    expectedHeaderLen = ( HTTP_TEST_PREFIX_HEADER_LEN - HTTP_TEST_REQUEST_PATH_LEN ) + \
                        HTTP_EMPTY_PATH_LEN +                                          \
                        HTTP_CONNECTION_CLOSE_VALUE_LEN;
    ok( snprintf( expectedHeader, expectedHeaderLen + 1,
                  HTTP_TEST_HEADER_FORMAT,
                  HTTP_TEST_REQUEST_METHOD, HTTP_EMPTY_PATH, HTTP_PROTOCOL_VERSION,
                  HTTP_USER_AGENT_FIELD, HTTP_USER_AGENT_VALUE,
                  HTTP_HOST_FIELD, HTTP_TEST_HOST_VALUE,
                  HTTP_CONNECTION_FIELD, HTTP_CONNECTION_CLOSE_VALUE )
        == expectedHeaderLen );
    reqHeaders.pBuffer = buffer;
    reqHeaders.bufferLen = expectedHeaderLen;
    test_err = HTTPClient_InitializeRequestHeaders( &reqHeaders, &reqInfo );
    ok( strncmp( ( char * ) reqHeaders.pBuffer,
                 expectedHeader, expectedHeaderLen ) == 0 );
    ok( reqHeaders.headersLen == expectedHeaderLen );
    ok( test_err == HTTP_SUCCESS );
    reset();

    /* -----------------------------------------------------------------------*/

    return grade();
}

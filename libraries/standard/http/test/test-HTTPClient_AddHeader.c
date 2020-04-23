#include <string.h>

#include "common.h"

/* Functions are pulled out into their own C files to be tested as a unit. */
#include "_addHeader.c"
#include "HTTPClient_AddHeader.c"

/* Template HTTP header fields and values. */
#define HTTP_TEST_HEADER_FIELD               "Authorization"
#define HTTP_TEST_HEADER_FIELD_LEN           ( uint8_t ) ( sizeof( HTTP_TEST_HEADER_FIELD ) - 1 )
#define HTTP_TEST_HEADER_VALUE               "None"
#define HTTP_TEST_HEADER_VALUE_LEN           ( uint8_t ) ( sizeof( HTTP_TEST_HEADER_VALUE ) - 1 )
/* Template for first line of HTTP header. */
#define HTTP_TEST_HEADER_REQUEST_LINE        "GET / HTTP/1.1 \r\n"
#define HTTP_TEST_HEADER_REQUEST_LINE_LEN    ( uint8_t ) ( sizeof( HTTP_TEST_HEADER_REQUEST_LINE ) - 1 )
#define HTTP_REQUEST_HEADERS_INITIALIZER     { 0 }
/* Default size for request buffer. */
#define HTTP_TEST_BUFFER_SIZE                ( 100 )

/* Length of the following template HTTP header.
 *   <HTTP_TEST_HEADER_REQUEST_LINE> \r\n
 *   <HTTP_TEST_HEADER_FIELD>: <HTTP_TEST_HEADER_VALUE> \r\n
 *   \r\n
 * This is used to initialize the correctHeader string. */
#define HTTP_TEST_SUFFICIENT_HEADER_LEN   \
    ( HTTP_TEST_HEADER_REQUEST_LINE_LEN + \
      HTTP_TEST_HEADER_FIELD_LEN +        \
      HTTP_HEADER_FIELD_SEPARATOR_LEN +   \
      HTTP_TEST_HEADER_VALUE_LEN +        \
      HTTP_HEADER_LINE_SEPARATOR_LEN +    \
      HTTP_HEADER_LINE_SEPARATOR_LEN )

int main()
{
    HTTPRequestHeaders_t reqHeaders = HTTP_REQUEST_HEADERS_INITIALIZER;
    HTTPRequestHeaders_t reqHeadersDflt = HTTP_REQUEST_HEADERS_INITIALIZER;
    HTTPStatus_t test_err = HTTP_NOT_SUPPORTED;
    uint8_t buffer[ HTTP_TEST_BUFFER_SIZE ] = { 0 };
    uint8_t smallBuffer[ HTTP_TEST_SUFFICIENT_HEADER_LEN - 1 ] = { 0 };
    char correctHeader[ HTTP_TEST_BUFFER_SIZE ] = { 0 };
    size_t correctHeaderLen = HTTP_TEST_SUFFICIENT_HEADER_LEN;
    struct Header
    {
        char field[ 100 ];
        size_t fieldLen;
        char value[ 100 ];
        size_t valueLen;
    }
    header;

/* Write template header field and value to a struct to pass as
 * parameters to HTTPClient_AddHeader() method. */
#define fillHeaderStructTemplate()                                    \
    do {                                                              \
        memcpy( header.field,                                         \
                HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_FIELD_LEN ); \
        header.fieldLen = HTTP_TEST_HEADER_FIELD_LEN;                 \
        memcpy( header.value,                                         \
                HTTP_TEST_HEADER_VALUE, HTTP_TEST_HEADER_VALUE_LEN ); \
        header.valueLen = HTTP_TEST_HEADER_VALUE_LEN;                 \
    }                                                                 \
    while( 0 )

#define reset()                                                      \
    do {                                                             \
        test_err = HTTP_NOT_SUPPORTED;                               \
        reqHeaders = reqHeadersDflt;                                 \
        memset( buffer, 0, HTTP_TEST_BUFFER_SIZE );                  \
        memset( correctHeader, 0, HTTP_TEST_SUFFICIENT_HEADER_LEN ); \
        memset( header.field, 0, 100 );                              \
        header.fieldLen = 0;                                         \
        memset( header.value, 0, 100 );                              \
        header.valueLen = 0;                                         \
    }                                                                \
    while( 0 )

    plan( 22 );

    /* Test the happy path. */
    reset();
    fillTemplateHeaderStruct();
    /* We add 1 because snprintf() writes a null byte at the end. */
    snprintf( correctHeader, HTTP_TEST_SUFFICIENT_HEADER_LEN + 1,
              "%s%s: %s\r\n\r\n",
              HTTP_TEST_HEADER_REQUEST_LINE,
              HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_VALUE );
    correctHeaderLen = HTTP_TEST_SUFFICIENT_HEADER_LEN;
    /* Set parameters for reqHeaders. */
    memcpy( buffer, HTTP_TEST_HEADER_REQUEST_LINE, HTTP_TEST_HEADER_REQUEST_LINE_LEN );
    reqHeaders.pBuffer = buffer;
    reqHeaders.bufferLen = HTTP_TEST_BUFFER_SIZE;
    reqHeaders.headersLen = HTTP_TEST_HEADER_REQUEST_LINE_LEN;
    reqHeaders.flags = 0;
    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     header.field, header.fieldLen,
                                     header.value, header.valueLen );
    ok( strncmp( ( char * ) reqHeaders.pBuffer,
                 correctHeader, correctHeaderLen ) == 0 );
    ok( reqHeaders.headersLen == correctHeaderLen );
    ok( test_err == HTTP_SUCCESS );
    /* Add extra header with insufficient memory. */
    reqHeaders.bufferLen = reqHeaders.headersLen;
    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     header.field, header.fieldLen,
                                     header.value, header.valueLen );
    ok( strncmp( ( char * ) reqHeaders.pBuffer,
                 correctHeader, correctHeaderLen ) == 0 );
    ok( reqHeaders.headersLen == correctHeaderLen );
    ok( test_err == HTTP_INSUFFICIENT_MEMORY );
    /* Add extra header with sufficient memory. */
    reqHeaders.bufferLen = HTTP_TEST_BUFFER_SIZE;
    correctHeaderLen = HTTP_TEST_SUFFICIENT_HEADER_LEN +                         \
                       HTTP_TEST_HEADER_FIELD_LEN + HTTP_TEST_HEADER_VALUE_LEN + \
                       HTTP_HEADER_FIELD_SEPARATOR_LEN + HTTP_HEADER_LINE_SEPARATOR_LEN;
    /* We add 1 because snprintf() writes a null byte at the end. */
    snprintf( correctHeader, correctHeaderLen + 1,
              "%s%s: %s\r\n%s: %s\r\n\r\n",
              HTTP_TEST_HEADER_REQUEST_LINE,
              HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_VALUE,
              HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_VALUE );
    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     header.field, header.fieldLen,
                                     header.value, header.valueLen );
    ok( strncmp( ( char * ) reqHeaders.pBuffer,
                 correctHeader, correctHeaderLen ) == 0 );
    ok( reqHeaders.headersLen == correctHeaderLen );
    ok( test_err == HTTP_SUCCESS );

    /* Test NULL parameters. */
    reset();
    test_err = HTTPClient_AddHeader( NULL,
                                     header.field, header.fieldLen,
                                     header.value, header.valueLen );
    ok( test_err == HTTP_INVALID_PARAMETER );

    /* reqHeaders should have NULL pBuffer upon reset(). */
    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     header.field, header.fieldLen,
                                     header.value, header.valueLen );
    ok( test_err == HTTP_INVALID_PARAMETER );

    /* reqHeaders.pBuffer == NULL checked before NULL fields and values. */
    reqHeaders.pBuffer = buffer;
    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     NULL, header.fieldLen,
                                     header.value, header.valueLen );
    ok( test_err == HTTP_INVALID_PARAMETER );

    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     header.field, header.fieldLen,
                                     NULL, header.valueLen );
    ok( test_err == HTTP_INVALID_PARAMETER );

    /* Test length of fieldLen and valueLen. */
    reset();
    reqHeaders.pBuffer = buffer;
    /* Test if length > 0. */
    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     header.field, 0,
                                     header.value, header.valueLen );
    ok( test_err == HTTP_INVALID_PARAMETER );
    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     header.field, header.fieldLen,
                                     header.value, 0 );
    ok( test_err == HTTP_INVALID_PARAMETER );
    /* Test if length < MAX. */
    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     header.field, ( UINT32_MAX >> 2 ) + 1,
                                     header.value, header.valueLen );
    ok( test_err == HTTP_INVALID_PARAMETER );
    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     header.field, header.fieldLen,
                                     header.value, ( UINT32_MAX >> 2 ) + 1 );
    ok( test_err == HTTP_INVALID_PARAMETER );

    /* Test "Content-Length" header if HTTP_REQUEST_DISABLE_CONTENT_LENGTH_FLAG
     * is deactivated. */
    reset();
    memcpy( header.field, HTTP_CONTENT_LENGTH_FIELD, HTTP_CONTENT_LENGTH_FIELD_LEN );
    header.fieldLen = HTTP_CONTENT_LENGTH_FIELD_LEN;
    memcpy( header.value, HTTP_TEST_HEADER_VALUE, HTTP_TEST_HEADER_VALUE_LEN );
    header.valueLen = HTTP_TEST_HEADER_VALUE_LEN;
    reqHeaders.pBuffer = buffer;
    reqHeaders.flags = 0;
    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     header.field, header.fieldLen,
                                     header.value, header.valueLen );
    ok( test_err == HTTP_INVALID_PARAMETER );

    /* Test "Connection" header field. */
    reset();
    memcpy( header.field, HTTP_CONNECTION_FIELD, HTTP_CONNECTION_FIELD_LEN );
    header.fieldLen = HTTP_CONNECTION_FIELD_LEN;
    memcpy( header.value, HTTP_TEST_HEADER_VALUE, HTTP_TEST_HEADER_VALUE_LEN );
    header.valueLen = HTTP_TEST_HEADER_VALUE_LEN;
    reqHeaders.flags = HTTP_REQUEST_DISABLE_CONTENT_LENGTH_FLAG;
    reqHeaders.pBuffer = buffer;
    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     header.field, header.fieldLen,
                                     header.value, header.valueLen );
    ok( test_err == HTTP_INVALID_PARAMETER );

    /* Test "Host" header field. */
    reset();
    memcpy( header.field, HTTP_HOST_FIELD, HTTP_HOST_FIELD_LEN );
    header.fieldLen = HTTP_HOST_FIELD_LEN;
    memcpy( header.value, HTTP_TEST_HEADER_VALUE, HTTP_TEST_HEADER_VALUE_LEN );
    header.valueLen = HTTP_TEST_HEADER_VALUE_LEN;
    reqHeaders.pBuffer = buffer;
    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     header.field, header.fieldLen,
                                     header.value, header.valueLen );
    ok( test_err == HTTP_INVALID_PARAMETER );

    /* Test "User-Agent" header field. */
    reset();
    memcpy( header.field, HTTP_USER_AGENT_FIELD, HTTP_USER_AGENT_FIELD_LEN );
    header.fieldLen = HTTP_USER_AGENT_FIELD_LEN;
    memcpy( header.value, HTTP_TEST_HEADER_VALUE, HTTP_TEST_HEADER_VALUE_LEN );
    header.valueLen = HTTP_TEST_HEADER_VALUE_LEN;
    reqHeaders.pBuffer = buffer;
    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     header.field, header.fieldLen,
                                     header.value, header.valueLen );
    ok( test_err == HTTP_INVALID_PARAMETER );

    /* Test HTTP_INSUFFICIENT_MEMORY error from having buffer size less than
     * what is required to fit HTTP headers. */
    reset();
    fillTemplateHeaderStruct();
    memcpy( smallBuffer, HTTP_TEST_HEADER_REQUEST_LINE, HTTP_TEST_HEADER_REQUEST_LINE_LEN );
    reqHeaders.headersLen = HTTP_TEST_HEADER_REQUEST_LINE_LEN;
    reqHeaders.pBuffer = smallBuffer;
    reqHeaders.bufferLen = HTTP_TEST_SUFFICIENT_HEADER_LEN - 1;
    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     header.field, header.fieldLen,
                                     header.value, header.valueLen );
    ok( test_err == HTTP_INSUFFICIENT_MEMORY );

    return grade();
}

#include <string.h>

#include "common.h"

/* Functions are pulled out into their own C files to be tested as a unit. */
#include "_addHeader.c"
#include "HTTPClient_AddHeader.c"

/* Template HTTP header fields and values. */
#define HTTP_TEST_HEADER_FIELD               "Authorization"
#define HTTP_TEST_HEADER_FIELD_LEN           ( sizeof( HTTP_TEST_HEADER_FIELD ) - 1 )
#define HTTP_TEST_HEADER_VALUE               "None"
#define HTTP_TEST_HEADER_VALUE_LEN           ( sizeof( HTTP_TEST_HEADER_VALUE ) - 1 )
/* Template for first line of HTTP header. */
#define HTTP_TEST_HEADER_REQUEST_LINE        "GET / HTTP/1.1 \r\n"
#define HTTP_TEST_HEADER_REQUEST_LINE_LEN    ( sizeof( HTTP_TEST_HEADER_REQUEST_LINE ) - 1 )
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
        fillHeaderStructTemplate();                                  \
        reqHeaders.pBuffer = buffer;                                 \
    }                                                                \
    while( 0 )

    plan( 16 );

    /* Happy Path testing. Prefill the user buffer with HTTP_TEST_HEADER_REQUEST_LINE
     * and call HTTPClient_AddHeader using the field and value in the header struct. */
    reset();
    /* Add 1 because snprintf() writes a null byte at the end. */
    snprintf( correctHeader, HTTP_TEST_SUFFICIENT_HEADER_LEN + 1,
              "%s%s: %s\r\n\r\n",
              HTTP_TEST_HEADER_REQUEST_LINE,
              HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_VALUE );
    correctHeaderLen = HTTP_TEST_SUFFICIENT_HEADER_LEN;
    /* Set parameters for reqHeaders. */
    snprintf( ( char * ) reqHeaders.pBuffer,
              HTTP_TEST_HEADER_REQUEST_LINE_LEN + 1, HTTP_TEST_HEADER_REQUEST_LINE );
    reqHeaders.bufferLen = HTTP_TEST_BUFFER_SIZE;
    reqHeaders.headersLen = HTTP_TEST_HEADER_REQUEST_LINE_LEN;
    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     header.field, header.fieldLen,
                                     header.value, header.valueLen );
    ok( strncmp( ( char * ) reqHeaders.pBuffer,
                 correctHeader, correctHeaderLen ) == 0 );
    ok( reqHeaders.headersLen == correctHeaderLen );
    ok( test_err == HTTP_SUCCESS );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test adding extra header with insufficient memory. */
    snprintf( correctHeader, HTTP_TEST_SUFFICIENT_HEADER_LEN + 1,
              "%s%s: %s\r\n\r\n",
              HTTP_TEST_HEADER_REQUEST_LINE,
              HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_VALUE );
    correctHeaderLen = HTTP_TEST_SUFFICIENT_HEADER_LEN;
    /* Prefill the buffer with a request line and header. */
    snprintf( ( char * ) reqHeaders.pBuffer, HTTP_TEST_SUFFICIENT_HEADER_LEN + 1,
              "%s%s: %s\r\n\r\n",
              HTTP_TEST_HEADER_REQUEST_LINE,
              HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_VALUE );
    reqHeaders.headersLen = HTTP_TEST_SUFFICIENT_HEADER_LEN;
    reqHeaders.bufferLen = reqHeaders.headersLen;
    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     header.field, header.fieldLen,
                                     header.value, header.valueLen );
    ok( strncmp( ( char * ) reqHeaders.pBuffer,
                 correctHeader, correctHeaderLen ) == 0 );
    ok( reqHeaders.headersLen == correctHeaderLen );
    ok( test_err == HTTP_INSUFFICIENT_MEMORY );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test adding extra header with sufficient memory. */
    correctHeaderLen = HTTP_TEST_SUFFICIENT_HEADER_LEN +
                       HTTP_TEST_HEADER_FIELD_LEN + HTTP_TEST_HEADER_VALUE_LEN +
                       HTTP_HEADER_FIELD_SEPARATOR_LEN + HTTP_HEADER_LINE_SEPARATOR_LEN;
    snprintf( correctHeader, correctHeaderLen + 1,
              "%s%s: %s\r\n%s: %s\r\n\r\n",
              HTTP_TEST_HEADER_REQUEST_LINE,
              HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_VALUE,
              HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_VALUE );
    /* Prefill the buffer with a request line and header. */
    snprintf( ( char * ) reqHeaders.pBuffer, HTTP_TEST_SUFFICIENT_HEADER_LEN + 1,
              "%s%s: %s\r\n\r\n",
              HTTP_TEST_HEADER_REQUEST_LINE,
              HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_VALUE );
    reqHeaders.headersLen = HTTP_TEST_SUFFICIENT_HEADER_LEN;
    reqHeaders.bufferLen = correctHeaderLen;

    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     header.field, header.fieldLen,
                                     header.value, header.valueLen );
    ok( strncmp( ( char * ) reqHeaders.pBuffer,
                 correctHeader, correctHeaderLen ) == 0 );
    ok( reqHeaders.headersLen == correctHeaderLen );
    ok( test_err == HTTP_SUCCESS );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test a NULL request headers interface. */
    test_err = HTTPClient_AddHeader( NULL,
                                     header.field, header.fieldLen,
                                     header.value, header.valueLen );
    ok( test_err == HTTP_INVALID_PARAMETER );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test a NULL pBuffer member of request headers. */
    reqHeaders.pBuffer = NULL;
    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     header.field, header.fieldLen,
                                     header.value, header.valueLen );
    ok( test_err == HTTP_INVALID_PARAMETER );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test NULL header field. */
    reqHeaders.bufferLen = HTTP_TEST_BUFFER_SIZE;
    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     NULL, header.fieldLen,
                                     header.value, header.valueLen );
    ok( test_err == HTTP_INVALID_PARAMETER );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test NULL header value. */
    reqHeaders.bufferLen = HTTP_TEST_BUFFER_SIZE;
    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     header.field, header.fieldLen,
                                     NULL, header.valueLen );
    ok( test_err == HTTP_INVALID_PARAMETER );
    reset();

    /* -----------------------------------------------------------------------*/


    /* Test that fieldLen > 0. */
    reqHeaders.bufferLen = HTTP_TEST_BUFFER_SIZE;
    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     header.field, 0,
                                     header.value, header.valueLen );
    ok( test_err == HTTP_INVALID_PARAMETER );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test that valueLen > 0. */
    reqHeaders.bufferLen = HTTP_TEST_BUFFER_SIZE;
    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     header.field, header.fieldLen,
                                     header.value, 0 );
    ok( test_err == HTTP_INVALID_PARAMETER );
    reset();

    /* -----------------------------------------------------------------------*/

    /* Test HTTP_INSUFFICIENT_MEMORY error from having buffer size less than
     * what is required to fit HTTP headers. */
    memcpy( smallBuffer, HTTP_TEST_HEADER_REQUEST_LINE, HTTP_TEST_HEADER_REQUEST_LINE_LEN );
    reqHeaders.headersLen = HTTP_TEST_HEADER_REQUEST_LINE_LEN;
    reqHeaders.pBuffer = smallBuffer;
    reqHeaders.bufferLen = HTTP_TEST_SUFFICIENT_HEADER_LEN - 1;
    test_err = HTTPClient_AddHeader( &reqHeaders,
                                     header.field, header.fieldLen,
                                     header.value, header.valueLen );
    ok( test_err == HTTP_INSUFFICIENT_MEMORY );
    reset();

    /* -----------------------------------------------------------------------*/

    return grade();
}

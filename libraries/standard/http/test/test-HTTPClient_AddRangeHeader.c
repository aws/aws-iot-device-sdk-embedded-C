#include <string.h>

#include "common.h"

/* Functions are pulled out into their own C files to be tested as a unit. */
#include "_addHeader.c"
#include "HTTPClient_AddRangeHeader.c"

/* Template HTTP header fields and values. */
#define HTTP_TEST_HEADER_FIELD               "Authorization"
#define HTTP_TEST_HEADER_FIELD_LEN           ( sizeof( HTTP_TEST_HEADER_FIELD ) - 1 )
#define HTTP_TEST_HEADER_VALUE               "None"
#define HTTP_TEST_HEADER_VALUE_LEN           ( sizeof( HTTP_TEST_HEADER_VALUE ) - 1 )
/* Template for first line of HTTP header. */
#define HTTP_TEST_HEADER_REQUEST_LINE        "POST / HTTP/1.1 \r\n"
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


static int32_t _rangeStartPositive = 10;
static int32_t _rangeStartZero = 0;
static int32_t _rangeStartNegative = -100;

static int32_t _rangeEndPositive = 10;
static int32_t _rangeEndZero = 0;
static int32_t _rangeEndNegative = -100;

#define RANGE_WITH_DIFF_START_AND_END_BYTES    "0-10"
#define RANGE_WITH_SAME_START_AND_END_BYTES    "10-10"
#define RANGE_WITH_NEGATIVE_START_BYTE         "-100"
#define RANGE_WITH_ONLY_START_BYTE             "-100"


int main()
{
    HTTPRequestHeaders_t reqHeaders = HTTP_REQUEST_HEADERS_INITIALIZER;
    HTTPRequestHeaders_t reqHeadersDflt = HTTP_REQUEST_HEADERS_INITIALIZER;
    HTTPStatus_t retCode = HTTP_NOT_SUPPORTED;
    uint8_t buffer[ HTTP_TEST_BUFFER_SIZE ] = { 0 };
    uint8_t smallBuffer[ HTTP_TEST_SUFFICIENT_HEADER_LEN - 1 ] = { 0 };
    char correctHeader[ HTTP_TEST_BUFFER_SIZE ] = { 0 };
    size_t correctHeaderLen = HTTP_TEST_SUFFICIENT_HEADER_LEN;

#define reset()                                                      \
    do {                                                             \
        retCode = HTTP_NOT_SUPPORTED;                                \
        reqHeaders = reqHeadersDflt;                                 \
        memset( buffer, 0, HTTP_TEST_BUFFER_SIZE );                  \
        memset( correctHeader, 0, HTTP_TEST_SUFFICIENT_HEADER_LEN ); \
    }                                                                \
    while( 0 )

    plan( 16 );

    /* / * Test the happy path. * / */
    /* reset(); */
    /* fillHeaderStructTemplate(); */
    /* / * We add 1 because snprintf() writes a null byte at the end. * / */
    /* snprintf( correctHeader, HTTP_TEST_SUFFICIENT_HEADER_LEN + 1, */
    /*           "%s%s: %s\r\n\r\n", */
    /*           HTTP_TEST_HEADER_REQUEST_LINE, */
    /*           HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_VALUE ); */
    /* correctHeaderLen = HTTP_TEST_SUFFICIENT_HEADER_LEN; */
    /* / * Set parameters for reqHeaders. * / */
    /* memcpy( buffer, HTTP_TEST_HEADER_REQUEST_LINE, HTTP_TEST_HEADER_REQUEST_LINE_LEN ); */
    /* reqHeaders.pBuffer = buffer; */
    /* reqHeaders.bufferLen = HTTP_TEST_BUFFER_SIZE; */
    /* reqHeaders.headersLen = HTTP_TEST_HEADER_REQUEST_LINE_LEN; */
    /* retCode = HTTPClient_AddRangeHeader( &reqHeaders, */
    /*                                  header.field, header.fieldLen, */
    /*                                  header.value, header.valueLen ); */
    /* ok( strncmp( ( char * ) reqHeaders.pBuffer, */
    /*              correctHeader, correctHeaderLen ) == 0 ); */
    /* ok( reqHeaders.headersLen == correctHeaderLen ); */
    /* ok( retCode == HTTP_SUCCESS ); */
    /* / * Add extra header with insufficient memory. * / */
    /* reqHeaders.bufferLen = reqHeaders.headersLen; */
    /* retCode = HTTPClient_AddRangeHeader( &reqHeaders, */
    /*                                  header.field, header.fieldLen, */
    /*                                  header.value, header.valueLen ); */
    /* ok( strncmp( ( char * ) reqHeaders.pBuffer, */
    /*              correctHeader, correctHeaderLen ) == 0 ); */
    /* ok( reqHeaders.headersLen == correctHeaderLen ); */
    /* ok( retCode == HTTP_INSUFFICIENT_MEMORY ); */
    /* / * Add extra header with sufficient memory. * / */
    /* reqHeaders.bufferLen = HTTP_TEST_BUFFER_SIZE; */
    /* correctHeaderLen = HTTP_TEST_SUFFICIENT_HEADER_LEN + */
    /*                    HTTP_TEST_HEADER_FIELD_LEN + HTTP_TEST_HEADER_VALUE_LEN + */
    /*                    HTTP_HEADER_FIELD_SEPARATOR_LEN + HTTP_HEADER_LINE_SEPARATOR_LEN; */
    /* / * We add 1 because snprintf() writes a null byte at the end. * / */
    /* snprintf( correctHeader, correctHeaderLen + 1, */
    /*           "%s%s: %s\r\n%s: %s\r\n\r\n", */
    /*           HTTP_TEST_HEADER_REQUEST_LINE, */
    /*           HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_VALUE, */
    /*           HTTP_TEST_HEADER_FIELD, HTTP_TEST_HEADER_VALUE ); */
    /* retCode = HTTPClient_AddRangeHeader( &reqHeaders, */
    /*                                  header.field, header.fieldLen, */
    /*                                  header.value, header.valueLen ); */
    /* ok( strncmp( ( char * ) reqHeaders.pBuffer, */
    /*              correctHeader, correctHeaderLen ) == 0 ); */
    /* ok( reqHeaders.headersLen == correctHeaderLen ); */
    /* ok( retCode == HTTP_SUCCESS ); */

    /* Request header parameter is NULL. */
    reset();
    retCode = HTTPClient_AddRangeHeader( NULL,
                                         _rangeStartZero,
                                         _rangeEndZero );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* Underlying buffer is NULL in request headers. */
    reset();
    retCode = HTTPClient_AddRangeHeader( &reqHeaders,
                                         _rangeStartZero,
                                         _rangeEndZero );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* Request Header Size is zero. */
    reset();
    reqHeaders.pBuffer = &buffer[ 0 ];
    retCode = HTTPClient_AddRangeHeader( &reqHeaders,
                                         _rangeStartZero,
                                         _rangeEndZero );
    ok( retCode == HTTP_INSUFFICIENT_MEMORY );

    /* Test incorrect combinations of rangeStart and rangeEnd. */

    /* rangeStart > rangeEnd */
    reset();
    reqHeaders.pBuffer = buffer;
    retCode = HTTPClient_AddRangeHeader( &reqHeaders,
                                         _rangeEndPositive + 1,
                                         _rangeEndPositive );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* rangeStart is negative but rangeStart is non-zero. */
    reset();
    reqHeaders.pBuffer = buffer;
    retCode = HTTPClient_AddRangeHeader( &reqHeaders,
                                         _rangeStartNegative,
                                         _rangeEndPositive );
    ok( retCode == HTTP_INVALID_PARAMETER );
    reset();
    reqHeaders.pBuffer = buffer;
    retCode = HTTPClient_AddRangeHeader( &reqHeaders,
                                         _rangeStartNegative,
                                         _rangeEndNegative );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* Both range values are negative. */
    reset();
    reqHeaders.pBuffer = buffer;
    retCode = HTTPClient_AddRangeHeader( &reqHeaders,
                                         _rangeStartNegative,
                                         _rangeEndNegative );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* / * Test HTTP_INSUFFICIENT_MEMORY error from having buffer size less than */
    /*  * what is required to fit HTTP headers. * / */
    /* reset(); */
    /* fillHeaderStructTemplate(); */
    /* memcpy( smallBuffer, HTTP_TEST_HEADER_REQUEST_LINE, HTTP_TEST_HEADER_REQUEST_LINE_LEN ); */
    /* reqHeaders.headersLen = HTTP_TEST_HEADER_REQUEST_LINE_LEN; */
    /* reqHeaders.pBuffer = smallBuffer; */
    /* reqHeaders.bufferLen = HTTP_TEST_SUFFICIENT_HEADER_LEN - 1; */
    /* retCode = HTTPClient_AddRangeHeader( &reqHeaders, */
    /*                                  header.field, header.fieldLen, */
    /*                                  header.value, header.valueLen ); */
    /* ok( retCode == HTTP_INSUFFICIENT_MEMORY ); */

    return grade();
}

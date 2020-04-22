#include <string.h>

#include "common.h"
#include "_isNullParam.c"
#include "_addHeader.c"

struct Header
{
    char field[ 100 ];
    size_t fieldLen;
    char value[ 100 ];
    size_t valueLen;
}
header;

/* Functions are pulled out into their own C files to be tested as a unit. */
#include "HTTPClient_AddHeader.c"

#define xqcReset()                      \
    do {                                \
        memset( header.field, 0, 100 ); \
        header.fieldLen = 0;            \
        memset( header.value, 0, 100 ); \
        header.valueLen = 0;            \
    }                                   \
    while( 0 )

#define reset()     \
    do {            \
        xqcReset(); \
    }               \
    while( 0 )

int main()
{
    HTTPRequestHeaders_t reqHeaders, reqHeadersDflt = { &reqHeaders, &reqHeaders };
    HTTPStatus_t test_err = HTTP_NOT_SUPPORTED;
    char pBuffer[ HTTP_BUFFER_DEFAULT_SIZE ] = { 0 };

    char correctHeader[ HTTP_CORRECT_HEADER_STRING_SIZE ] = { 0 };

#define reset()                                                      \
    do {                                                             \
        xqcReset();                                                  \
        reqHeaders = reqHeadersDflt;                                 \
        memset( pBuffer, 0, HTTP_BUFFER_DEFAULT_SIZE );              \
        memset( correctHeader, 0, HTTP_CORRECT_HEADER_STRING_SIZE ); \
    }                                                                \
    while( 0 )

    plan( 1 );

    /* happy path */
    reset();
    snprintf( correctHeader, HTTP_CORRECT_HEADER_STRING_SIZE,
              "%s%s:%s\r\n\r\n",
              HTTP_HEADER_SAMPLE_FIRST_LINE, HTTP_HEADER_SAMPLE_FIELD, HTTP_HEADER_SAMPLE_VALUE );
    memcpy( pBuffer, HTTP_HEADER_SAMPLE_FIRST_LINE, HTTP_HEADER_SAMPLE_FIRST_LINE_LEN );
    reqHeaders.pBuffer = pBuffer;
    reqHeaders.headersLen += HTTP_HEADER_SAMPLE_FIRST_LINE_LEN;
    reqHeaders.bufferLen += HTTP_HEADER_SAMPLE_FIRST_LINE_LEN;
    memcpy( header.field, HTTP_HEADER_SAMPLE_FIELD, HTTP_HEADER_SAMPLE_FIELD_LEN );
    header.fieldLen = HTTP_HEADER_SAMPLE_FIELD_LEN;
    memcpy( header.value, HTTP_HEADER_SAMPLE_VALUE, HTTP_HEADER_SAMPLE_VALUE_LEN );
    header.valueLen = HTTP_HEADER_SAMPLE_VALUE_LEN;
    test_err = _addHeader( &reqHeaders,
                           header.field, header.fieldLen,
                           header.value, header.valueLen );
    ok( strncmp( reqHeaders.pBuffer, correctHeader, reqHeaders.bufferLen ) == true );
    ok( test_err == HTTP_SUCCESS );
    reset();


    return 0;
}

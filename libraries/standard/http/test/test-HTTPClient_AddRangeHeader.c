#include <string.h>
#include <stdbool.h>

#include "common.h"

/* Functions are pulled out into their own C files to be tested as a unit. */
#include "_addHeader.c"
#include "_convertInt32ToAscii.c"
#include "HTTPClient_AddRangeHeader.c"

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


/* Range Request data that is common for all range specification types. */
#define RANGE_REQUEST_HEADER_DATA_PREFIX        "Range: bytes="
#define RANGE_REQUEST_HEADER_DATA_PREFIX_LEN    ( sizeof( RANGE_REQUEST_HEADER_DATA_PREFIX ) - 1 )

/* The range end value for representing end of file byte. */
#define RANGE_REQUEST_END_OF_FILE               -1

/* Type to store expected headers data. */
typedef struct _headers
{
    uint8_t buffer[ HTTP_TEST_BUFFER_SIZE ];
    size_t dataLen;
} _headers_t;

#define setupBuffersWithPreexistingHeader( requestHeaders,                \
                                           testBuffer,                    \
                                           expectedHeaders,               \
                                           preexistingData )              \
    do {                                                                  \
        size_t dataLen = strlen( preexistingData );                       \
        requestHeaders.pBuffer = testBuffer;                              \
        requestHeaders.bufferLen = sizeof( testBuffer );                  \
        /* We add 1 bytes as snprintf() writes a null byte at the end. */ \
        int numBytes = snprintf( ( char * ) requestHeaders.pBuffer,       \
                                 dataLen + 1,                             \
                                 "%s",                                    \
                                 preexistingData );                       \
        ok( numBytes == ( int ) dataLen );                                \
        requestHeaders.headersLen = dataLen;                              \
        /* Fill the same data in the expected buffer as HTTPClient_AddRangeHeaders()
         * is not expected to change it. */                         \
        ok( memcpy( expectedHeaders.buffer, requestHeaders.pBuffer, \
                    requestHeaders.headersLen )                     \
            == expectedHeaders.buffer );                            \
        expectedHeaders.dataLen = requestHeaders.headersLen;        \
    } while( 0 )


#define addRangeToExpectedHeaders( expectedHeaders, expectedRange, terminatorExists )         \
    do {                                                                                      \
        size_t rangeRequestLen = RANGE_REQUEST_HEADER_DATA_PREFIX_LEN +                       \
                                 strlen( expectedRange ) +                                    \
                                 2 * HTTP_HEADER_LINE_SEPARATOR_LEN;                          \
        int numBytes =                                                                        \
            snprintf( ( char * ) expectedHeaders.buffer +                                     \
                      expectedHeaders.dataLen -                                               \
                      ( terminatorExists ? HTTP_HEADER_LINE_SEPARATOR_LEN : 0 ),              \
                      /* We add 1 bytes as snprintf() writes a null byte at the end. */       \
                      rangeRequestLen + 1,                                                    \
                      "%s%s\r\n\r\n",                                                         \
                      RANGE_REQUEST_HEADER_DATA_PREFIX,                                       \
                      expectedRange );                                                        \
        ok( ( size_t ) numBytes == rangeRequestLen );                                         \
        expectedHeaders.dataLen += rangeRequestLen -                                          \
                                   ( terminatorExists ? HTTP_HEADER_LINE_SEPARATOR_LEN : 0 ); \
    } while( 0 )


int main()
{
    HTTPRequestHeaders_t testHeaders = { 0 };
    HTTPStatus_t retCode = HTTP_NOT_SUPPORTED;
    uint8_t testBuffer[ HTTP_TEST_BUFFER_SIZE ] = { 0 };
    _headers_t expectedHeaders = { 0 };
    int testRangeStart = 0;
    int testRangeEnd = 0;

#define reset()                                                   \
    do {                                                          \
        retCode = HTTP_NOT_SUPPORTED;                             \
        memset( &testHeaders, 0, sizeof( testHeaders ) );         \
        memset( testBuffer, 0, sizeof( testBuffer ) );            \
        memset( &expectedHeaders, 0, sizeof( expectedHeaders ) ); \
    } while( 0 )

    plan( 62 );

    /*************************** Test happy path. *****************************/

    /* Case 1: Headers buffer contains header data ending with "\r\n\r\n". */

    /* Range specification of the form [rangeStart, rangeEnd]. */
    /* Test with 0 as the range values */
    reset();
    setupBuffersWithPreexistingHeader( testHeaders, testBuffer,
                                       expectedHeaders,
                                       PREEXISTING_HEADER_DATA );
    testRangeStart = 0;
    testRangeEnd = 0;
    addRangeToExpectedHeaders( expectedHeaders,
                               "0-0" /*expected range*/,
                               true );
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         testRangeStart,
                                         testRangeEnd );
    ok( retCode == HTTP_SUCCESS );
    /* Verify the the Range Request header data. */
    ok( testHeaders.headersLen == expectedHeaders.dataLen );
    ok( memcmp( testHeaders.pBuffer, expectedHeaders.buffer, expectedHeaders.dataLen )
        == 0 );
    /* Verify that the bufferLen data was not tampered with. */
    ok( testHeaders.bufferLen == sizeof( testBuffer ) );

    /* Test for [0, eof) range */
    reset();
    setupBuffersWithPreexistingHeader( testHeaders, testBuffer,
                                       expectedHeaders,
                                       PREEXISTING_HEADER_DATA );
    testRangeStart = 0;
    testRangeEnd = RANGE_REQUEST_END_OF_FILE;
    addRangeToExpectedHeaders( expectedHeaders,
                               "0-" /*expected range*/,
                               true );
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         testRangeStart,
                                         testRangeEnd );
    ok( retCode == HTTP_SUCCESS );
    /* Verify the the Range Request header data. */
    ok( testHeaders.headersLen == expectedHeaders.dataLen );
    ok( memcmp( testHeaders.pBuffer, expectedHeaders.buffer, expectedHeaders.dataLen )
        == 0 );
    /* Verify that the bufferLen data was not tampered with. */
    ok( testHeaders.bufferLen == sizeof( testBuffer ) );

    reset();
    setupBuffersWithPreexistingHeader( testHeaders, testBuffer,
                                       expectedHeaders,
                                       PREEXISTING_HEADER_DATA );
    testRangeStart = 10;
    testRangeEnd = 100;
    addRangeToExpectedHeaders( expectedHeaders,
                               "10-100" /*expected range*/,
                               true );
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         testRangeStart,
                                         testRangeEnd );
    ok( retCode == HTTP_SUCCESS );
    /* Verify the the Range Request header data. */
    ok( testHeaders.headersLen == expectedHeaders.dataLen );
    ok( memcmp( testHeaders.pBuffer, expectedHeaders.buffer, expectedHeaders.dataLen )
        == 0 );
    /* Verify that the bufferLen data was not tampered with. */
    ok( testHeaders.bufferLen == sizeof( testBuffer ) );

    /* Range specification of the form [rangeStart,)
     * i.e. for all bytes >= rangeStart. */
    reset();
    setupBuffersWithPreexistingHeader( testHeaders, testBuffer,
                                       expectedHeaders,
                                       PREEXISTING_HEADER_DATA );
    testRangeStart = 100;
    testRangeEnd = RANGE_REQUEST_END_OF_FILE;
    addRangeToExpectedHeaders( expectedHeaders,
                               "100-" /*expected range*/,
                               true );
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         testRangeStart,
                                         testRangeEnd );
    ok( retCode == HTTP_SUCCESS );
    /* Verify the the Range Request header data. */
    ok( testHeaders.headersLen == expectedHeaders.dataLen );
    ok( memcmp( testHeaders.pBuffer, expectedHeaders.buffer, expectedHeaders.dataLen )
        == 0 );
    /* Verify that the bufferLen data was not tampered with. */
    ok( testHeaders.bufferLen == sizeof( testBuffer ) );

    /* Range specification for the last N bytes. */
    reset();
    setupBuffersWithPreexistingHeader( testHeaders, testBuffer,
                                       expectedHeaders,
                                       PREEXISTING_HEADER_DATA );
    testRangeStart = -50;
    testRangeEnd = RANGE_REQUEST_END_OF_FILE;
    addRangeToExpectedHeaders( expectedHeaders,
                               "-50" /*expected range*/,
                               true );
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         testRangeStart,
                                         testRangeEnd );
    ok( retCode == HTTP_SUCCESS );
    /* Verify the the Range Request header data. */
    ok( testHeaders.headersLen == expectedHeaders.dataLen );
    ok( memcmp( testHeaders.pBuffer, expectedHeaders.buffer, expectedHeaders.dataLen )
        == 0 );
    /* Verify that the bufferLen data was not tampered with. */
    ok( testHeaders.bufferLen == sizeof( testBuffer ) );

    /* Test with LARGE range values. */
    reset();
    setupBuffersWithPreexistingHeader( testHeaders, testBuffer,
                                       expectedHeaders,
                                       PREEXISTING_HEADER_DATA );
    testRangeStart = INT32_MAX;
    testRangeEnd = INT32_MAX;
    addRangeToExpectedHeaders( expectedHeaders,
                               "2147483647-2147483647" /*expected range*/,
                               true );
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         testRangeStart,
                                         testRangeEnd );
    ok( retCode == HTTP_SUCCESS );
    /* Verify the the Range Request header data. */
    ok( testHeaders.headersLen == expectedHeaders.dataLen );
    ok( memcmp( testHeaders.pBuffer, expectedHeaders.buffer, expectedHeaders.dataLen )
        == 0 );
    /* Verify that the bufferLen data was not tampered with. */
    ok( testHeaders.bufferLen == sizeof( testBuffer ) );

    /* Case 2: Headers buffer does not contain data with trailing "\r\n\r\n". */

    /* Range specification of the form [rangeStart, rangeEnd]. */
    /* Test with 0 as the range values */
    reset();
    setupBuffersWithPreexistingHeader( testHeaders, testBuffer,
                                       expectedHeaders,
                                       PREEXISTING_REQUEST_LINE );
    testRangeStart = 0;
    testRangeEnd = 0;
    addRangeToExpectedHeaders( expectedHeaders,
                               "0-0" /*expected range*/,
                               false );
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         testRangeStart,
                                         testRangeEnd );
    ok( retCode == HTTP_SUCCESS );
    /* Verify the the Range Request header data. */
    ok( testHeaders.headersLen == expectedHeaders.dataLen );
    ok( memcmp( testHeaders.pBuffer, expectedHeaders.buffer, expectedHeaders.dataLen )
        == 0 );
    /* Verify that the bufferLen data was not tampered with. */
    ok( testHeaders.bufferLen == sizeof( testBuffer ) );

    /*************************** Test Failure Cases *****************************/

    /* Request header parameter is NULL. */
    reset();
    retCode = HTTPClient_AddRangeHeader( NULL,
                                         0 /* rangeStart */,
                                         0 /* rageEnd */ );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* Underlying buffer is NULL in request headers. */
    reset();
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         0 /* rangeStart */,
                                         0 /* rageEnd */ );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* Request Header Size is zero. */
    reset();
    testHeaders.pBuffer = &testBuffer[ 0 ];
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         0 /* rangeStart */,
                                         0 /* rageEnd */ );
    ok( retCode == HTTP_INSUFFICIENT_MEMORY );

    /* Test incorrect combinations of rangeStart and rangeEnd. */

    /* rangeStart > rangeEnd */
    reset();
    testHeaders.pBuffer = &testBuffer[ 0 ];
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         10 /* rangeStart */,
                                         5 /* rageEnd */ );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* rangeStart is negative but rangeStart is non-End of File. */
    reset();
    testHeaders.pBuffer = &testBuffer[ 0 ];
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         -10 /* rangeStart */,
                                         RANGE_REQUEST_END_OF_FILE + 1 /* rageEnd */ );
    ok( retCode == HTTP_INVALID_PARAMETER );
    reset();
    testHeaders.pBuffer = &testBuffer[ 0 ];
    retCode = HTTPClient_AddRangeHeader( &testHeaders,
                                         -50 /* rangeStart */,
                                         -10 /* rageEnd */ );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* Test Insufficient memory failure when the buffer has one less byte than required. */
    reset();
    setupBuffersWithPreexistingHeader( testHeaders, testBuffer,
                                       expectedHeaders,
                                       PREEXISTING_HEADER_DATA );
    size_t preHeadersLen = testHeaders.headersLen;
    testRangeStart = 5;
    testRangeEnd = 10;
    addRangeToExpectedHeaders( expectedHeaders,
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
    ok( retCode == HTTP_INSUFFICIENT_MEMORY );
    /* Verify the headers input parameter is unaltered. */
    ok( testHeaders.headersLen == preHeadersLen );
    ok( testHeaders.bufferLen == expectedHeaders.dataLen - 1 );
    ok( memcmp( testHeaders.pBuffer, expectedHeaders.buffer, testHeaders.bufferLen )
        == 0 );

    return grade();
}

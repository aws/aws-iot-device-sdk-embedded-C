#include <string.h>

#include "common.h"

/* Mirror of internal type used by HTTPClient_ReadHeader function. */
typedef struct readHeaderContext
{
    const char * pHeaderName;
    size_t headerNameLen;
    const char ** pHeaderValueLoc;
    size_t * pHeaderValueLen;
} readHeaderContext_t;

/* Functions are pulled out into their own C files to be tested as a unit. */
#include "readHeaderParsingCallback.c"
#include "HTTPClient_ReadHeader.c"

/* Template HTTP request for a PUT request. */
#define HTTP_TEST_RESPONSE          \
    "HTTP/1.1 200 OK"               \
    "test-header0: test-value0\r\n" \
    "test-header1: test-value1\r\n" \
    "test-header2: test-value2\r\n" \
    "\r\n"

#define HEADER_NAME_0_IN_BUFFER      "test-header0"
#define HEADER_NAME_1_IN_BUFFER      "test-header1"
#define HEADER_NAME_NOT_IN_BUFFER    "header-not-in-buffer"
#define TEST_BUFFER_SIZE             100

/* Mocked out implementations of parser function dependencies. */
static HTTPStatus_t initializeParsingContextRetCode = HTTP_SUCCESS;
HTTPStatus_t HTTPClient_InitializeParsingContext( HTTPParsingContext_t * pParsingContext,
                                                  HTTPClient_HeaderParsingCallback_t * pHeaderParsingCallback )
{
    ( void ) pParsingContext;
    ( void ) pHeaderParsingCallback;

    return initializeParsingContextRetCode;
}

static HTTPStatus_t parseResponseRetCode = HTTP_SUCCESS;
HTTPStatus_t HTTPClient_ParseResponse( HTTPParsingContext_t * pParsingContext,
                                       const uint8_t * pBuffer,
                                       size_t bufferLen )
{
    ( void ) pParsingContext;

    ( void ) pBuffer;
    ( void ) bufferLen;

    return parseResponseRetCode;
}

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

int main()
{
    HTTPResponse_t testResponse = { 0 };
    uint8_t testBuffer[ TEST_BUFFER_SIZE ] = { 0u };
    HTTPStatus_t retCode = HTTP_NOT_SUPPORTED;
    const char * pValueLoc = NULL;
    size_t valueLen = 0u;

#define reset()                                             \
    do {                                                    \
        retCode = HTTP_NOT_SUPPORTED;                       \
        memset( &testResponse, 0, sizeof( testResponse ) ); \
        memset( &testBuffer, 0, sizeof( testBuffer ) );     \
        pValueLoc = NULL;                                   \
        valueLen = 0u;                                      \
        initializeParsingContextRetCode = HTTP_SUCCESS;     \
        parseResponseRetCode = HTTP_SUCCESS;                \
    } while( 0 )

    plan( 62 );

    /*************************** Test Failure Cases *****************************/

    /* Response parameter is NULL. */
    reset();
    retCode = HTTPClient_ReadHeader( NULL,
                                     "Header",
                                     strlen( "Header" ),
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* Underlying buffer is NULL in the response parameter. */
    reset();
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     "Header",
                                     strlen( "Header" ),
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* Response buffer size is zero. */
    reset();
    testResponse.pBuffer = &testBuffer[ 0 ];
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     "Header",
                                     strlen( "Header" ),
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* Header field name is NULL. */
    reset();
    testResponse.pBuffer = &testBuffer[ 0 ];
    testResponse.bufferLen = sizeof( testBuffer );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     NULL,
                                     strlen( "Header" ),
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* Header field length is 0. */
    reset();
    testResponse.pBuffer = &testBuffer[ 0 ];
    testResponse.bufferLen = sizeof( testBuffer );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     "Header",
                                     0u,
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* Invalid output parameters. */
    reset();
    testResponse.pBuffer = &testBuffer[ 0 ];
    testResponse.bufferLen = sizeof( testBuffer );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     "Header",
                                     strlen( "Header" ),
                                     NULL,
                                     &valueLen );
    ok( retCode == HTTP_INVALID_PARAMETER );
    reset();
    testResponse.pBuffer = &testBuffer[ 0 ];
    testResponse.bufferLen = sizeof( testBuffer );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     "Header",
                                     strlen( "Header" ),
                                     &pValueLoc,
                                     NULL );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* Test when HTTPClient_InitializeParsingContext returns failure. */
    reset();
    initializeParsingContextRetCode = HTTP_INTERNAL_ERROR;
    testResponse.pBuffer = &testBuffer[ 0 ];
    testResponse.bufferLen = sizeof( testBuffer );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     "Header",
                                     strlen( "Header" ),
                                     &pValueLoc,
                                     NULL );
    ok( retCode == HTTP_INTERNAL_ERROR );

    /* Test when HTTPClient_ParseResponse returns failure. */
    reset();
    parseResponseRetCode = HTTP_HEADER_NOT_FOUND;
    testResponse.pBuffer = &testBuffer[ 0 ];
    testResponse.bufferLen = sizeof( testBuffer );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     "Header",
                                     strlen( "Header" ),
                                     &pValueLoc,
                                     NULL );
    ok( retCode == HTTP_HEADER_NOT_FOUND );
    reset();
    parseResponseRetCode = HTTP_INTERNAL_ERROR;
    testResponse.pBuffer = &testBuffer[ 0 ];
    testResponse.bufferLen = sizeof( testBuffer );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     "Header",
                                     strlen( "Header" ),
                                     &pValueLoc,
                                     NULL );
    ok( retCode == HTTP_INTERNAL_ERROR );


    /* Test when requested header is not present in response. */



    /*************************** Test Happy-Path Cases *****************************/



    return grade();
}

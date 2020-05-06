#include <string.h>
#include <stdbool.h>

#include "common.h"

/* Mirror of internal type used by HTTPClient_ReadHeader function. */
typedef struct readHeaderContext
{
    const char * pHeaderName;
    size_t headerNameLen;
    const char ** pHeaderValueLoc;
    size_t * pHeaderValueLen;
    uint8_t headerFound;
} readHeaderContext_t;

/* Functions are pulled out into their own C files to be tested as a unit. */
#include "readHeaderParsingCallback.c"
#include "HTTPClient_ReadHeader.c"

/* Template HTTP request for a PUT request. */
static const char * pTestResponse = "HTTP/1.1 200 OK"
                                    "test-header0: test-value0\r\n"
                                    "test-header1: test-value1\r\n"
                                    "test-header2: test-value2\r\n"
                                    "\r\n";
static const size_t headerFieldInRespLoc = 15;
static const size_t headerFieldInRespLen = strlen( "test-header0" );
static const size_t headerValInRespLoc = 29;
static const size_t headerValInRespLen = strlen( "test-value0" );

#define HEADER_IN_BUFFER        "test-header0"
#define HEADER_NOT_IN_BUFFER    "header-not-in-buffer"
#define TEST_BUFFER_SIZE        100

/* Mocked out implementations of parser function dependencies. */
static HTTPStatus_t initializeParsingContextRetCode = HTTP_SUCCESS;
HTTPStatus_t HTTPClient_InitializeParsingContext( HTTPParsingContext_t * pParsingContext,
                                                  HTTPClient_HeaderParsingCallback_t * pHeaderParsingCallback )
{
    /* Verify the input arguments. */
    ok( pParsingContext != NULL );
    ok( pHeaderParsingCallback != NULL );

    /* Side-effect of mock'd function. */
    pParsingContext->pHeaderParsingCallback = pHeaderParsingCallback;

    return initializeParsingContextRetCode;
}

static HTTPStatus_t parseResponseRetCode = HTTP_SUCCESS;
static bool invokeParsingCallback = false;
HTTPStatus_t HTTPClient_ParseResponse( HTTPParsingContext_t * pParsingContext,
                                       const uint8_t * pBuffer,
                                       size_t bufferLen )
{
    ( void ) pBuffer;
    ( void ) bufferLen;

    /* Verify the input arguments. */
    ok( pParsingContext != NULL );
    ok( pParsingContext->pHeaderParsingCallback->onHeaderCallback != NULL );
    ok( pParsingContext->pHeaderParsingCallback->pContext != NULL );
    ok( pParsingContext->pHeaderParsingCallback->onHeaderCallback == readHeaderParsingCallback );
    /*ok( pBuffer == ( const Uint8_t * ) pTestResponse ); */
    ok( bufferLen == strlen( pTestResponse ) );

    if( invokeParsingCallback )
    {
        pParsingContext->pHeaderParsingCallback->onHeaderCallback(
            pParsingContext->pHeaderParsingCallback->pContext,
            &pTestResponse[ headerFieldInRespLoc ],
            headerFieldInRespLen,
            &pTestResponse[ headerValInRespLoc ],
            headerValInRespLen,
            200 /* status code */ );
    }

    return parseResponseRetCode;
}

int main()
{
    HTTPResponse_t testResponse = { 0 };
    HTTPStatus_t retCode = HTTP_NOT_SUPPORTED;
    const char * pValueLoc = NULL;
    size_t valueLen = 0u;

#define reset()                                             \
    do {                                                    \
        retCode = HTTP_NOT_SUPPORTED;                       \
        memset( &testResponse, 0, sizeof( testResponse ) ); \
        pValueLoc = NULL;                                   \
        valueLen = 0u;                                      \
        initializeParsingContextRetCode = HTTP_SUCCESS;     \
        parseResponseRetCode = HTTP_SUCCESS;                \
        invokeParsingCallback = false;                      \
    } while( 0 )

    plan( 58 );

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
    testResponse.pBuffer = ( uint8_t * ) &pTestResponse[ 0 ];
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     "Header",
                                     strlen( "Header" ),
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* Header field name is NULL. */
    reset();
    testResponse.pBuffer = ( uint8_t * ) &pTestResponse[ 0 ];
    testResponse.bufferLen = strlen( pTestResponse );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     NULL,
                                     strlen( "Header" ),
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* Header field length is 0. */
    reset();
    testResponse.pBuffer = ( uint8_t * ) &pTestResponse[ 0 ];
    testResponse.bufferLen = strlen( pTestResponse );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     "Header",
                                     0u,
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* Invalid output parameters. */
    reset();
    testResponse.pBuffer = ( uint8_t * ) &pTestResponse[ 0 ];
    testResponse.bufferLen = strlen( pTestResponse );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     "Header",
                                     strlen( "Header" ),
                                     NULL,
                                     &valueLen );
    ok( retCode == HTTP_INVALID_PARAMETER );
    reset();
    testResponse.pBuffer = ( uint8_t * ) &pTestResponse[ 0 ];
    testResponse.bufferLen = strlen( pTestResponse );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     "Header",
                                     strlen( "Header" ),
                                     &pValueLoc,
                                     NULL );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* Test when HTTPClient_InitializeParsingContext returns failure. */
    reset();
    initializeParsingContextRetCode = HTTP_INTERNAL_ERROR;
    testResponse.pBuffer = ( uint8_t * ) &pTestResponse[ 0 ];
    testResponse.bufferLen = strlen( pTestResponse );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     "Header",
                                     strlen( "Header" ),
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_INTERNAL_ERROR );

    /* Test when HTTPClient_ParseResponse returns failure. */
    reset();
    parseResponseRetCode = HTTP_INTERNAL_ERROR;
    testResponse.pBuffer = ( uint8_t * ) &pTestResponse[ 0 ];
    testResponse.bufferLen = strlen( pTestResponse );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     "Header",
                                     strlen( "Header" ),
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_INTERNAL_ERROR );

    /*************************** Test Happy-Path Cases *****************************/

    /* Test when requested header in present response. */
    reset();
    invokeParsingCallback = true;
    testResponse.pBuffer = ( uint8_t * ) &pTestResponse[ 0 ];
    testResponse.bufferLen = strlen( pTestResponse );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     HEADER_IN_BUFFER,
                                     strlen( HEADER_IN_BUFFER ),
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_SUCCESS );
    ok( pValueLoc == &pTestResponse[ headerValInRespLoc ] );
    ok( valueLen == headerValInRespLen );

    /* Test when requested header is not present in response. */
    reset();
    invokeParsingCallback = true;
    testResponse.pBuffer = ( uint8_t * ) &pTestResponse[ 0 ];
    testResponse.bufferLen = strlen( pTestResponse );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     HEADER_NOT_IN_BUFFER,
                                     strlen( HEADER_NOT_IN_BUFFER ),
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_HEADER_NOT_FOUND );
    /* Make sure that the output parameters were not updated. */
    ok( pValueLoc == NULL );
    ok( valueLen == 0u );

    return grade();
}

#include <string.h>
#include <stdbool.h>

#include "common.h"

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

/* Mocked out implementations of parser function dependencies. */
static HTTPStatus_t initializeParsingContextRetCode = HTTP_SUCCESS;
HTTPStatus_t HTTPClient_InitializeParsingContext( HTTPParsingContext_t * pParsingContext,
                                                  HTTPClient_HeaderParsingCallback_t * pHeaderParsingCallback )
{
    ( void ) pHeaderParsingCallback;

    /* Verify the input arguments. */
    ok( pParsingContext != NULL );

    return initializeParsingContextRetCode;
}

static HTTPStatus_t findHeaderInRespRetCode = HTTP_SUCCESS;
static const uint8_t * pExpectedField = NULL;
static size_t expectedFieldSize = 0u;
static const uint8_t * pValLocToReturn = NULL;
static size_t valLenToReturn = 0u;
HTTPStatus_t HTTPClient_FindHeaderInResponse( HTTPParsingContext_t * pParsingContext,
                                              const uint8_t * pBuffer,
                                              size_t bufferLen,
                                              const uint8_t * pField,
                                              size_t fieldLen,
                                              const uint8_t ** pValue,
                                              size_t * pValueLen )
{
    /* Verify the input arguments. */
    ok( pParsingContext != NULL );
    ok( pBuffer == ( const uint8_t * ) pTestResponse );
    ok( bufferLen == strlen( pTestResponse ) );
    ok( bufferLen != 0u );
    ok( pField != NULL );
    ok( fieldLen == expectedFieldSize );
    ok( 0u == memcmp( pField, pExpectedField, fieldLen ) );
    ok( pValue != NULL );
    ok( pValueLen != NULL );

    /* Side-effects of mock'd implementation. */
    *pValue = pValLocToReturn;
    *pValueLen = valLenToReturn;

    return findHeaderInRespRetCode;
}

int main()
{
    HTTPResponse_t testResponse = { 0 };
    HTTPStatus_t retCode = HTTP_NOT_SUPPORTED;
    const uint8_t * pValueLoc = NULL;
    size_t valueLen = 0u;

#define reset()                                             \
    do {                                                    \
        retCode = HTTP_NOT_SUPPORTED;                       \
        memset( &testResponse, 0, sizeof( testResponse ) ); \
        pValueLoc = NULL;                                   \
        valueLen = 0u;                                      \
        initializeParsingContextRetCode = HTTP_SUCCESS;     \
        findHeaderInRespRetCode = HTTP_SUCCESS;             \
        pExpectedField = NULL;                              \
        expectedFieldSize = 0u;                             \
        pValLocToReturn = NULL;                             \
        valLenToReturn = 0u;                                \
    } while( 0 )

    plan( 44 );

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
    /* Configure the HTTPClient_FindResponseInHeader mock. */
    findHeaderInRespRetCode = HTTP_INTERNAL_ERROR;
    pExpectedField = HEADER_IN_BUFFER;
    expectedFieldSize = strlen( HEADER_IN_BUFFER );
    /* Call the function under test. */
    testResponse.pBuffer = ( uint8_t * ) &pTestResponse[ 0 ];
    testResponse.bufferLen = strlen( pTestResponse );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     HEADER_IN_BUFFER,
                                     strlen( HEADER_IN_BUFFER ),
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_INTERNAL_ERROR );

    /* Test when requested header is not present in response. */

    reset();
    /* Configure the HTTPClient_FindResponseInHeader mock. */
    findHeaderInRespRetCode = HTTP_HEADER_NOT_FOUND;
    pExpectedField = HEADER_NOT_IN_BUFFER;
    expectedFieldSize = strlen( HEADER_NOT_IN_BUFFER );
    /* Call the function under test. */
    testResponse.pBuffer = ( uint8_t * ) &pTestResponse[ 0 ];
    testResponse.bufferLen = strlen( pTestResponse );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     HEADER_NOT_IN_BUFFER,
                                     strlen( HEADER_NOT_IN_BUFFER ),
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_HEADER_NOT_FOUND );

    /*************************** Test Happy-Path Cases *****************************/

    /* Test when requested header in present response. */

    reset();
    /* Configure the HTTPClient_FindResponseInHeader mock. */
    pExpectedField = HEADER_IN_BUFFER;
    expectedFieldSize = strlen( HEADER_IN_BUFFER );
    pValLocToReturn = &pTestResponse[ headerValInRespLoc ];
    valLenToReturn = headerValInRespLen;
    /* Call the function under test. */
    testResponse.pBuffer = ( uint8_t * ) &pTestResponse[ 0 ];
    testResponse.bufferLen = strlen( pTestResponse );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     HEADER_IN_BUFFER,
                                     strlen( HEADER_IN_BUFFER ),
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_SUCCESS );
    ok( pValueLoc == ( const uint8_t * ) &pTestResponse[ headerValInRespLoc ] );
    ok( valueLen == headerValInRespLen );

    return grade();
}

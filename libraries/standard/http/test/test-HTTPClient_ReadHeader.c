#include <string.h>
#include <stdbool.h>

#include "common.h"
#include "http_parser/http_parser.h"

/* Mirror of the context type used to pass to http_parser. */
typedef struct findHeaderContext
{
    const uint8_t * pField;
    size_t fieldLen;
    const uint8_t ** pValueLoc;
    size_t * pValueLen;
    uint8_t fieldFound : 1;
    uint8_t valueFound : 1;
} findHeaderContext_t;

/* Functions are pulled out into their own C files to be tested as a unit. */
#include "HTTPClient_strerror.c"
#include "findHeaderFieldParserCallback.c"
#include "findHeaderValueParserCallback.c"
#include "findHeaderOnHeaderCompleteCallback.c"
#include "findHeaderInResponse.c"
#include "HTTPClient_ReadHeader.c"

/* Template HTTP request for a PUT request. */
static const char * pTestResponse = "HTTP/1.1 200 OK\r\n"
                                    "test-header0: test-value0\r\n"
                                    "test-header1: test-value1\r\n"
                                    "test-header2: test-value2\r\n"
                                    "\r\n";
static const size_t headerFieldInRespLoc = 44;
static const size_t headerFieldInRespLen = sizeof( "test-header1" ) - 1u;
static const size_t headerValInRespLoc = 58;
static const size_t headerValInRespLen = sizeof( "test-value1" ) - 1u;

#define HEADER_IN_BUFFER        "test-header1"
#define HEADER_NOT_IN_BUFFER    "header-not-in-buffer"

/* -------------------- Mock'd implementations of http_parser function dependencies. ------------------ */

void http_parser_init( http_parser * parser,
                       enum http_parser_type type )
{
    ok( parser != NULL );
    ok( type == HTTP_RESPONSE );
}

void http_parser_settings_init( http_parser_settings * settings )
{
    ok( settings != NULL );
}
/* Variables for controlling behavior of the http_parser_execute() mock. */
static const char * pExpectedBuffer = NULL;
static size_t expectedBufferSize = 0u;
bool invokeHeaderFieldCallback = false;
const char * pFieldLocToReturn = NULL;
size_t fieldLenToReturn = 0u;
bool invokeHeaderValueCallback = false;
const char * pValueLocToReturn = NULL;
static int expectedValCbRetVal = 0;
size_t valueLenToReturn = 0u;
bool invokeHeaderCompleteCallback = false;
unsigned int parserErrNo = 0;
size_t http_parser_execute( http_parser * parser,
                            const http_parser_settings * settings,
                            const char * data,
                            size_t len )
{
    ok( parser != NULL );
    ok( settings != NULL );
    ok( len == expectedBufferSize );
    ok( data == pExpectedBuffer );

    ok( settings->on_header_field != NULL );
    ok( settings->on_header_value != NULL );
    ok( settings->on_headers_complete != NULL );

    if( invokeHeaderFieldCallback == true )
    {
        ok( HTTP_PARSER_CONTINUE_PARSING ==
            settings->on_header_field( parser,
                                       pFieldLocToReturn,
                                       fieldLenToReturn ) );
    }

    if( invokeHeaderValueCallback == true )
    {
        ok( expectedValCbRetVal ==
            settings->on_header_value( parser,
                                       pValueLocToReturn,
                                       valueLenToReturn ) );
    }

    if( invokeHeaderCompleteCallback == true )
    {
        ok( HTTP_PARSER_STOP_PARSING ==
            settings->on_headers_complete( parser ) );
    }

    /* Set the error value in the parser. */
    parser->http_errno = parserErrNo;

    return len;
}

const char * http_errno_description( enum http_errno err )
{
    ( void ) err;
    return "test-error";
}

/* -------------------- End of http_parser function mocks. ------------------ */

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
        pExpectedBuffer = &pTestResponse[ 0 ];              \
        expectedBufferSize = strlen( pTestResponse );       \
        invokeHeaderFieldCallback = false;                  \
        pFieldLocToReturn = NULL;                           \
        fieldLenToReturn = 0u;                              \
        invokeHeaderValueCallback = false;                  \
        pValueLocToReturn = NULL;                           \
        expectedValCbRetVal = 0;                            \
        valueLenToReturn = 0u;                              \
        invokeHeaderCompleteCallback = false;               \
    } while( 0 )

    plan( 69 );

    /*************************** Test Failure Cases *****************************/

    /* Response parameter is NULL. */
    reset();
    retCode = HTTPClient_ReadHeader( NULL,
                                     ( const uint8_t * ) "Header",
                                     strlen( "Header" ),
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* Underlying buffer is NULL in the response parameter. */
    reset();
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     ( const uint8_t * ) "Header",
                                     strlen( "Header" ),
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* Response buffer size is zero. */
    reset();
    testResponse.pBuffer = ( uint8_t * ) &pTestResponse[ 0 ];
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     ( const uint8_t * ) "Header",
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
                                     ( const uint8_t * ) "Header",
                                     0u,
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* Invalid output parameters. */
    reset();
    testResponse.pBuffer = ( uint8_t * ) &pTestResponse[ 0 ];
    testResponse.bufferLen = strlen( pTestResponse );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     ( const uint8_t * ) "Header",
                                     strlen( "Header" ),
                                     NULL,
                                     &valueLen );
    ok( retCode == HTTP_INVALID_PARAMETER );
    reset();
    testResponse.pBuffer = ( uint8_t * ) &pTestResponse[ 0 ];
    testResponse.bufferLen = strlen( pTestResponse );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     ( const uint8_t * ) "Header",
                                     strlen( "Header" ),
                                     &pValueLoc,
                                     NULL );
    ok( retCode == HTTP_INVALID_PARAMETER );

    /* Test when the header is present in response but http_parser_execute()
     * does not set the expected errno value (of "CB_header_value")
     * due to an internal error. */
    reset();
    /* Configure the http_parser_execute mock. */
    invokeHeaderFieldCallback = true;
    invokeHeaderValueCallback = true;
    pFieldLocToReturn = &pTestResponse[ headerFieldInRespLoc ];
    fieldLenToReturn = headerFieldInRespLen;
    pValueLocToReturn = &pTestResponse[ headerValInRespLoc ];
    valueLenToReturn = headerValInRespLen;
    expectedValCbRetVal = HTTP_PARSER_STOP_PARSING;
    parserErrNo = HPE_CB_chunk_complete;
    /* Call the function under test. */
    testResponse.pBuffer = ( uint8_t * ) &pTestResponse[ 0 ];
    testResponse.bufferLen = strlen( pTestResponse );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     ( const uint8_t * ) HEADER_IN_BUFFER,
                                     strlen( HEADER_IN_BUFFER ),
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_INTERNAL_ERROR );

    /* Test when requested header is not present in response. */

    reset();
    /* Configure the http_parser_execute mock. */
    invokeHeaderCompleteCallback = false;
    parserErrNo = HPE_OK;
    /* Call the function under test. */
    testResponse.pBuffer = ( uint8_t * ) &pTestResponse[ 0 ];
    testResponse.bufferLen = strlen( pTestResponse );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     ( const uint8_t * ) HEADER_NOT_IN_BUFFER,
                                     strlen( HEADER_NOT_IN_BUFFER ),
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_HEADER_NOT_FOUND );

    /* Test with invalid HTTP responses. */

    /* Test when invalid response only contains the header field for the requested header. */
    const char * pResponseWithoutValue = "HTTP/1.1 200 OK\r\n"
                                         "test-header0: test-value0\r\n"
                                         "test-header1:";
    reset();
    /* Configure the http_parser_execute mock. */
    pExpectedBuffer = pResponseWithoutValue;
    expectedBufferSize = strlen( pResponseWithoutValue );
    invokeHeaderFieldCallback = true;
    pFieldLocToReturn = &pTestResponse[ headerFieldInRespLoc ];
    fieldLenToReturn = headerFieldInRespLen;
    /* Call the function under test. */
    testResponse.pBuffer = ( uint8_t * ) &pResponseWithoutValue[ 0 ];
    testResponse.bufferLen = strlen( pResponseWithoutValue );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     ( const uint8_t * ) HEADER_IN_BUFFER,
                                     strlen( HEADER_IN_BUFFER ),
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_INVALID_RESPONSE );

    /* Test when the invalid response does not contain the requested header.
     * (Response is invalid as it doesn't end with "\r\n\r\n".) */
    reset();
    const char * pResponseWithoutHeaders = "HTTP/1.1 200 OK\r\n"
                                           "test-header0:test-value0";
    /* Configure the http_parser_execute mock. */
    pExpectedBuffer = &pResponseWithoutHeaders[ 0 ];
    expectedBufferSize = strlen( pResponseWithoutHeaders );
    parserErrNo = HPE_UNKNOWN;
    /* Call the function under test. */
    testResponse.pBuffer = ( uint8_t * ) &pResponseWithoutHeaders[ 0 ];
    testResponse.bufferLen = strlen( pResponseWithoutHeaders );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     ( const uint8_t * ) HEADER_NOT_IN_BUFFER,
                                     strlen( HEADER_NOT_IN_BUFFER ),
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_INVALID_RESPONSE );

    /*************************** Test Happy-Path Cases *****************************/

    /* Test when requested header in present response. */

    reset();
    /* Configure the http_parser_execute mock. */
    expectedValCbRetVal = HTTP_PARSER_STOP_PARSING;
    pFieldLocToReturn = &pTestResponse[ headerFieldInRespLoc ];
    fieldLenToReturn = headerFieldInRespLen;
    pValueLocToReturn = &pTestResponse[ headerValInRespLoc ];
    valueLenToReturn = headerValInRespLen;
    invokeHeaderFieldCallback = true;
    invokeHeaderValueCallback = true;
    parserErrNo = HPE_CB_header_value;
    /* Call the function under test. */
    testResponse.pBuffer = ( uint8_t * ) &pTestResponse[ 0 ];
    testResponse.bufferLen = strlen( pTestResponse );
    retCode = HTTPClient_ReadHeader( &testResponse,
                                     ( const uint8_t * ) HEADER_IN_BUFFER,
                                     strlen( HEADER_IN_BUFFER ),
                                     &pValueLoc,
                                     &valueLen );
    ok( retCode == HTTP_SUCCESS );
    ok( pValueLoc == ( const uint8_t * ) &pTestResponse[ headerValInRespLoc ] );
    ok( valueLen == headerValInRespLen );

    return grade();
}

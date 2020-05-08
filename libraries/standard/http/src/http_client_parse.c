#include <assert.h>
#include <string.h>

#include "private/http_client_parse.h"
#include "private/http_client_internal.h"
#include "http_parser/http_parser.h"

HTTPStatus_t HTTPClient_InitializeParsingContext( HTTPParsingContext_t * pParsingContext,
                                                  HTTPClient_HeaderParsingCallback_t * pHeaderParsingCallback )
{
    /* Disable unused parameter warnings. */
    ( void ) pParsingContext;
    ( void ) pHeaderParsingCallback;
    /* This function is to be implenmented. */
    return HTTP_SUCCESS;
}

HTTPStatus_t HTTPClient_ParseResponse( HTTPParsingContext_t * pParsingContext,
                                       const uint8_t * pBuffer,
                                       size_t bufferLen )
{
    /* Disable unused parameter warnings. */
    ( void ) pBuffer;
    ( void ) bufferLen;

    /* This function is to be implemented. For now we return success. */
    pParsingContext->state = HTTP_PARSING_COMPLETE;
    return HTTP_SUCCESS;
}

/*-----------------------------------------------------------*/

static const int HTTP_PARSER_STOP_PARSING = 1;
static const int HTTP_PARSER_CONTINUE_PARSING = 0;

/**
 * @brief An aggregator that represents the user-provided parameters to the
 * #HTTPClient_ReadHeader API function, to be used as context parameter
 * to the parsing callback used by the API function.
 */
typedef struct findHeaderContext
{
    const uint8_t * pField;
    size_t fieldLen;
    const uint8_t ** pValueLoc;
    size_t * pValueLen;
    uint8_t fieldFound : 1;
    uint8_t valueFound : 1;
} findHeaderContext_t;

static int findHeaderHeaderParsedCallback( http_parser * pHttpParser,
                                           const char * pFieldLoc,
                                           size_t fieldLen )
{
    findHeaderContext_t * pContext = ( findHeaderContext_t * ) pHttpParser->data;

    assert( pHttpParser != NULL );
    assert( pFieldLoc != NULL );
    assert( fieldLen > 0u );

    assert( pContext->pField != NULL );
    assert( pContext->fieldLen > 0u );

    /* The header found flags should not be set. */
    assert( pContext->fieldFound == 0u );
    assert( pContext->valueFound == 0u );

    /* Check whether the parsed header matches the header we are looking for. */
    if( ( fieldLen == pContext->fieldLen ) && ( memcmp( pContext->pField, pFieldLoc, fieldLen ) == 0 ) )
    {
        IotLogDebugWithArgs( "Found header field in response: "
                             "HeaderName=%.*s, HeaderLocation=0x%d",
                             fieldLen, pContext->pField );

        /* Set the flag to indicate that header has been found in response. */
        pContext->fieldFound = 1u;
    }
    else
    {
        /* Empty else for MISRA 15.7 compliance. */
    }

    return HTTP_PARSER_CONTINUE_PARSING;
}

static int findHeaderValueParsedCallback( http_parser * pHttpParser,
                                          const char * pVaLueLoc,
                                          size_t valueLen )
{
    findHeaderContext_t * pContext = ( findHeaderContext_t * ) pHttpParser->data;
    int retCode = HTTP_PARSER_CONTINUE_PARSING;

    assert( pHttpParser != NULL );
    assert( pVaLueLoc != NULL );
    assert( valueLen > 0u );

    assert( pContext->pField != NULL );
    assert( pContext->fieldLen > 0u );
    assert( pContext->pValueLoc != NULL );
    assert( pContext->pValueLen != NULL );

    /* The header value found flag should not be set. */
    assert( pContext->valueFound == 0u );

    if( pContext->fieldFound == 1u )
    {
        IotLogDebugWithArgs( "Found header value in response: "
                             "RequestedField=%.*s, ValueLocation=0x%d",
                             pContext->fieldLen, pContext->pField, pVaLueLoc );

        /* Populate the output parameters with the location of the header value in the response buffer. */
        *pContext->pValueLoc = ( const uint8_t * ) pVaLueLoc;
        *pContext->pValueLen = valueLen;

        /* As we have found the value associated with the header, we don't need
         * to parse the response any further. */
        retCode = HTTP_PARSER_STOP_PARSING;
    }
    else
    {
        /* Empty else for MISRA 15.7 compliance. */
    }

    return retCode;
}


static int findHeaderOnHeaderCompleteCallback( http_parser * pHttpParser )
{
    /* Disable unused parameter warning. */
    ( void ) pHttpParser;

    assert( pHttpParser != NULL );

    /* If we have reached here, all headers in the response have been parsed but the requested
     * header has not been found in the response buffer. */
    IotLogDebugWithArgs( "Reached end of header parsing: Requested header not found in response:"
                         "HeaderField=%.*s",
                         ( ( findHeaderContext_t * ) pHttpParser->data )->fieldLen,
                         ( ( findHeaderContext_t * ) pHttpParser->data )->pField );

    /* No further parsing is required; thus, indicate the parser to stop parsing. */
    return HTTP_PARSER_STOP_PARSING;
}

HTTPStatus_t HTTPClient_FindHeaderInResponse( const uint8_t * pBuffer,
                                              size_t bufferLen,
                                              const uint8_t * pField,
                                              size_t fieldLen,
                                              const uint8_t ** pValueLoc,
                                              size_t * pValueLen )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;
    http_parser parser = { 0 };
    http_parser_settings parserSettings = { 0 };
    findHeaderContext_t context =
    {
        .pField     = pField,
        .fieldLen   = fieldLen,
        .pValueLoc  = pValueLoc,
        .pValueLen  = pValueLen,
        .fieldFound = 0u,
        .valueFound = 0u
    };
    size_t numOfBytesParsed = 0u;

    http_parser_init( &parser, HTTP_RESPONSE );

    /* Set the context for the parser. */
    parser.data = &context;

    /* The intention here to define callbacks just for searching the headers. We will
     * need to create a private context in httpParser->data that has the field and
     * value to update and pass back. */
    http_parser_settings_init( &parserSettings );
    parserSettings.on_header_field = findHeaderHeaderParsedCallback;
    parserSettings.on_header_value = findHeaderValueParsedCallback;
    parserSettings.on_headers_complete = findHeaderOnHeaderCompleteCallback;

    /* Start parsing for the header! */
    numOfBytesParsed = http_parser_execute( &parser, &parserSettings, ( char * ) pBuffer, bufferLen );

    IotLogDebugWithArgs( "Parsed response for header search: NumBytesParsed=%d",
                         numOfBytesParsed );

    if( parser.http_errno != 0 )
    {
        IotLogErrorWithArgs( "Failed to find header in response: http-parser returned error: ParserError=%s",
                             http_errno_description( HTTP_PARSER_ERRNO( &( parser ) ) ) );
        returnStatus = HTTP_INTERNAL_ERROR;
    }
    else if( context.fieldFound == 0u )
    {
        /* If header field is not found, then both the flags should be zero. */
        assert( context.valueFound == 0u );

        /* Header is not present in buffer. */
        IotLogWarnWithArgs( "Header not found in response buffer: "
                            "RequestedHeader=%.*s", fieldLen, pField );

        returnStatus = HTTP_HEADER_NOT_FOUND;
    }
    else if( context.valueFound == 0u )
    {
        /* The response buffer is invalid as only the header field was found
         * in the "<field>: <value>\r\n" format of an HTTP header. */
        IotLogErrorWithArgs( "Unable to find header value in response: "
                             "Response is invalid: RequestedHeader=%.*s",
                             fieldLen, pField );
        returnStatus = HTTP_INVALID_RESPONSE;
    }
    else
    {
        /* Header is found. */
        assert( ( context.fieldFound == 1u ) && ( context.valueFound == 1u ) );

        IotLogDebugWithArgs( "Found requested header in response: "
                             "HeaderName=%.*s, HeaderValue=%.*s",
                             fieldLen, pField,
                             *pValueLen, *pValueLoc );
    }

    return returnStatus;
}

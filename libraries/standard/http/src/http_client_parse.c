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

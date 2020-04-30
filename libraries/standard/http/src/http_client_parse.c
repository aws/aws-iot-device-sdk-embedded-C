#include "private/http_client_parse.h"

HTTPStatus_t _HTTPClient_InitializeParsingContext( HTTPParsingContext_t * pParsingContext,
                                                   HTTPClient_HeaderParsingCallback_t * pHeaderParsingCallback )
{
    /* This function is to be implenmented. */
    return HTTP_SUCCESS;
}

HTTPStatus_t _HTTPClient_ParseResponse( HTTPParsingContext_t * pParsingContext,
                                        const uint8_t * pBuffer,
                                        size_t bufferLen )
{
    /* This function is to be implemented. For now we return success. */
    pParsingContext->state = HTTP_PARSING_COMPLETE;
    return HTTP_SUCCESS;
}

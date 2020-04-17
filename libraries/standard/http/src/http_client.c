#include "http_client.h"
#include "private/http_client.h"

HTTPStatus_t _addHeaderLine( HTTPRequestHeaders_t * pRequestHeaders,
                             const char * pLine,
                             size_t lineLen )
{
    HTTPStatus_t status = HTTP_SUCCESS;

    /* Check if there is enough space in buffer for additional header pair.
     * The last HTTP_HEADER_LINE_END is used for error checking but must
     * be added before sending the request. */
    size_t toAddLen = lineLen + HTTP_HEADER_LINE_END_LEN;

    if( pRequestHeaders->headersLen
        + toAddLen > pRequestHeaders->bufferLen )
    {
        return HTTP_INSUFFICIENT_MEMORY;
    }

    /* Write to the buffer. */
    uint8_t * cur = pRequestHeaders->pBuffer;
    memcpy( cur, pLine, lineLen );
    cur += lineLen;
    memcpy( cur, HTTP_HEADER_LINE_END_LEN,
            HTTP_HEADER_LINE_END_LEN );
    /* Subtract HTTP_HEADER_LINE_END_LEN because it is only added later. */
    pRequestHeaders->headersLen += toAddLen;
    return status;
}

HTTPStatus_t _addHeaderPair( HTTPRequestHeaders_t * pRequestHeaders,
                             const char * pField,
                             size_t fieldLen,
                             const char * pValue,
                             size_t valueLen )
{
    HTTPStatus_t status = HTTP_SUCCESS;

    /* Check if there is enough space in buffer for additional header pair.
     * The last HTTP_HEADER_LINE_END is used for error checking but must
     * be added before sending the request. */
    size_t toAddLen = fieldLen + HTTP_HEADER_FIELD_SEPARATOR_LEN + \
                      valueLen + HTTP_HEADER_LINE_END_LEN +        \
                      HTTP_HEADER_LINE_END_LEN;

    if( pRequestHeaders->headersLen
        + toAddLen > pRequestHeaders->bufferLen )
    {
        return HTTP_INSUFFICIENT_MEMORY;
    }

    /* Write to the buffer. */
    uint8_t * cur = pRequestHeaders->pBuffer;
    memcpy( cur, pField, fieldLen );
    cur += fieldLen;
    memcpy( cur, HTTP_HEADER_FIELD_SEPARATOR,
            HTTP_HEADER_FIELD_SEPARATOR_LEN );
    cur += HTTP_HEADER_FIELD_SEPARATOR_LEN;
    memcpy( cur, pValue, valueLen );
    cur += valueLen;
    memcpy( cur, HTTP_HEADER_LINE_END, HTTP_HEADER_LINE_END_LEN );
    /* Subtract HTTP_HEADER_LINE_END_LEN because it is only added later. */
    pRequestHeaders->headersLen += toAddLen - HTTP_HEADER_LINE_END_LEN;

    return status;
}


HTTPStatus_t HTTPClient_InitializeRequestHeaders( HTTPRequestHeaders_t * pRequestHeaders,
                                                  const HTTPRequestInfo_t * pRequestInfo )
{
    size_t httpsProtocolVersionLen = STRLEN_LITERAL( HTTP_PROTOCOL_VERSION );
    HTTPStatus_t status = HTTP_SUCCESS;

    /* Check for null parameters. */
    if( ( pRequestHeaders == NULL ) || ( pRequestInfo == NULL ) ||
        ( pRequestHeaders->pBuffer == NULL ) || ( pRequestInfo->method == NULL ) ||
        ( pRequestInfo->pHost == NULL ) || ( pRequestInfo->pPath == NULL ) )
    {
        status = HTTP_INVALID_PARAMETER;
    }

    /* Check if user-provided buffer is large enough for headers. */
    pRequestInfo->methodLen + STRLEN_LITERAL( HTTP_PROTOCOL_VERSION );

    pRequestHeaders->headersLen

    if( status == HTTP_SUCCESS )
    {
        /* Clear user-provided buffer. */
        memset( pRequestHeaders->pBuffer, 0, pRequestHeaders->bufferLen );
        /* Write header data to the buffer. */
    }
}

HTTPStatus_t HTTPClient_AddHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                   const char * pName,
                                   size_t nameLen,
                                   const char * pValue,
                                   size_t valueLen )
{
    return HTTP_NOT_SUPPORTED;
}

HTTPStatus_t HTTPClient_AddRangeHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                        int32_t rangeStart,
                                        int32_t rangeEnd )
{
    return HTTP_NOT_SUPPORTED;
}

HTTPStatus_t HTTPClient_Send( const HTTPTransportInterface_t * pTransport,
                              const HTTPRequestHeaders_t * pRequestHeaders,
                              const uint8_t * pRequestBodyBuf, /* For a PUT or POST request. */
                              size_t reqBodyBufLen,
                              httpResponse_t * pResponse )
{
    return HTTP_NOT_SUPPORTED;
}

HTTPStatus_t HTTPClient_ReadHeader( httpResponse_t * pResponse,
                                    const char * pName,
                                    size_t nameLen,
                                    char ** pValue,
                                    size_t * valueLen )
{
    return HTTP_NOT_SUPPORTED;
}

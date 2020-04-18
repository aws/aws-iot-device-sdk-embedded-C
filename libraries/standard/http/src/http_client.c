#include "http_client.h"
#include "private/http_client.h"

uint8_t * _writeToBuffer( const uint8_t * pBuffer,
                          const void * source,
                          size_t len )
{
    memcpy( pBuffer, source, len );
    return pBuffer + len;
}

HTTPStatus_t _addHeaderLine( HTTPRequestHeaders_t * pRequestHeaders,
                             const char * pLine,
                             size_t lineLen )
{
    HTTPStatus_t status = HTTP_SUCCESS;
    uint8_t * pBufferCur = pRequestHeaders->pBuffer;

    /* Check if there is enough space in buffer for additional header pair.
     * Also count "\r\n" at the end of line.  */
    size_t toAddLen = lineLen + HTTP_HEADER_LINE_END_LEN;

    if( pRequestHeaders->headersLen
        + toAddLen > pRequestHeaders->bufferLen )
    {
        /* TODO: Add log. */
        return HTTP_INSUFFICIENT_MEMORY;
    }

    /* Write line to buffer. */
    pBufferCur = _writeToBuffer( pBufferCur, pLine, lineLen );
    /* Write "\r\n" to end the line */
    pBufferCur = _writeToBuffer( pBufferCur, HTTP_HEADER_LINE_END_LEN, HTTP_HEADER_LINE_END_LEN );
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
    uint8_t * pBufferCur = pRequestHeaders->pBuffer;

    /* Check if there is enough space in buffer for additional header pair.
     * The last HTTP_HEADER_LINE_END_LEN is used for error checking but must
     * be added separately after this method returns. */
    size_t toAddLen = fieldLen + HTTP_HEADER_FIELD_SEPARATOR_LEN + \
                      valueLen + HTTP_HEADER_LINE_END_LEN +        \
                      HTTP_HEADER_LINE_END_LEN;

    if( pRequestHeaders->headersLen
        + toAddLen > pRequestHeaders->bufferLen )
    {
        /* TODO: Add log. */
        return HTTP_INSUFFICIENT_MEMORY;
    }

    /* Append "Field: Value \r\n" to headers */
    pBufferCur = _writeToBuffer( pBufferCur, pField, fieldLen );
    pBufferCur = _writeToBuffer( pBufferCur, HTTP_HEADER_FIELD_SEPARATOR,
                                 HTTP_HEADER_FIELD_SEPARATOR_LEN );
    pBufferCur = _writeToBuffer( pBufferCur, pValue, valueLen );
    pBufferCur = _writeToBuffer( pBufferCur, HTTP_HEADER_LINE_END, HTTP_HEADER_LINE_END_LEN );

    /* Subtract HTTP_HEADER_LINE_END_LEN because it is not actually written
     * and only used for error checking as mentioned above. */
    pRequestHeaders->headersLen += toAddLen - HTTP_HEADER_LINE_END_LEN;

    return status;
}


HTTPStatus_t HTTPClient_InitializeRequestHeaders( HTTPRequestHeaders_t * pRequestHeaders,
                                                  const HTTPRequestInfo_t * pRequestInfo )
{
    HTTPStatus_t status = HTTP_SUCCESS;
    size_t toAddLen = 0;
    uint8_t * pBufferCur = pRequestHeaders->pBuffer;

    pRequestHeaders->headersLen = 0;

    /* Check for null parameters. */
    if( ( pRequestHeaders == NULL ) || ( pRequestInfo == NULL ) ||
        ( pRequestHeaders->pBuffer == NULL ) || ( pRequestInfo->method == NULL ) ||
        ( pRequestInfo->pHost == NULL ) || ( pRequestInfo->pPath == NULL ) )
    {
        status = HTTP_INVALID_PARAMETER;
    }

    /* Check if user-provided buffer is large enough for first line. */
    toAddLen = pRequestInfo->methodLen +                 \
               SPACE_CHARACTER_LEN +                     \
               pRequestInfo->pathLen +                   \
               SPACE_CHARACTER_LEN +                     \
               STRLEN_LITERAL( HTTP_PROTOCOL_VERSION ) + \
               HTTP_HEADER_LINE_END_LEN;

    if( toAddLen + pRequestHeaders->headersLen > pRequestHeaders->bufferLen )
    {
        /* TODO: Add log. */
        status = HTTP_INVALID_PARAMETER;
    }

    /* Write "<METHOD> <PATH> HTTP/1.1\r\n" to start of buffer. */
    pBufferCur = _writeToBuffer( pBufferCur, pRequestInfo->method, pRequestInfo->methodLen );
    pBufferCur += pRequestInfo->methodLen;
    pBufferCur = _writeToBuffer( pBufferCur, SPACE_CHARACTER, SPACE_CHARACTER_LEN );
    pBufferCur +=

        if( STRLEN_LITERAL( HTTP_USER_AGENT_VALUE ) )
    {
        toAddLen += HTTP_USER_AGENT_HEADER +
    }

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

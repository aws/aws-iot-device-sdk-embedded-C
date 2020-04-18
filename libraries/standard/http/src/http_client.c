#include "http_client.h"
#include "private/http_client.h"

HTTPStatus_t _addHeaderLine( HTTPRequestHeaders_t * pRequestHeaders,
                             const char * pLine,
                             size_t lineLen )
{
    HTTPStatus_t status = HTTP_SUCCESS;
    uint8_t * pBufferCur = pRequestHeaders->pBuffer;

    /* Check if there is enough space in buffer for additional header.
     * Also count "\r\n" at the end of line. */
    size_t toAddLen = lineLen + HTTP_HEADER_LINE_END_LEN;

    if( pRequestHeaders->headersLen
        + toAddLen > pRequestHeaders->bufferLen )
    {
        /* TODO: Add log. */
        return HTTP_INSUFFICIENT_MEMORY;
    }

    /* Write line to buffer. */
    memcpy( pBufferCur, pLine, lineLen );
    pBufferCur += lineLen;
    /* Write "\r\n" to end the line. */
    memcpy( pBufferCur, HTTP_HEADER_LINE_END_LEN, HTTP_HEADER_LINE_END_LEN );
    pRequestHeaders->headersLen += toAddLen;
    return status;
}

HTTPStatus_t _addHeader( HTTPRequestHeaders_t * pRequestHeaders,
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

    /* Write "Field: Value \r\n" to headers. */
    memcpy( pBufferCur, pField, fieldLen );
    pBufferCur += fieldLen;
    memcpy( pBufferCur, HTTP_HEADER_FIELD_SEPARATOR,
            HTTP_HEADER_FIELD_SEPARATOR_LEN );
    pBufferCur += HTTP_HEADER_FIELD_SEPARATOR_LEN;
    memcpy( pBufferCur, pValue, valueLen );
    pBufferCur += valueLen;
    memcpy( pBufferCur, HTTP_HEADER_LINE_END, HTTP_HEADER_LINE_END_LEN );

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
    size_t httpsProtocolVersionLen = STRLEN_LITERAL( HTTP_PROTOCOL_VERSION );

    pRequestHeaders->headersLen = 0;
    /* Clear user-provided buffer. */
    memset( pRequestHeaders->pBuffer, 0, pRequestHeaders->bufferLen );

    /* Check for null parameters. */
    if( ( pRequestHeaders == NULL ) || ( pRequestInfo == NULL ) ||
        ( pRequestHeaders->pBuffer == NULL ) ||
        ( pRequestInfo->method == NULL ) ||
        ( pRequestInfo->pHost == NULL ) ||
        ( pRequestInfo->pPath == NULL ) )
    {
        status = HTTP_INSUFFICIENT_MEMORY;
    }

    /* Check if buffer is large enough for "<METHOD> <PATH> HTTP/1.1\r\n". */
    toAddLen = pRequestInfo->methodLen +                 \
               SPACE_CHARACTER_LEN +                     \
               pRequestInfo->pathLen +                   \
               SPACE_CHARACTER_LEN +                     \
               STRLEN_LITERAL( HTTP_PROTOCOL_VERSION ) + \
               HTTP_HEADER_LINE_END_LEN;

    if( toAddLen + pRequestHeaders->headersLen > pRequestHeaders->bufferLen )
    {
        /* TODO: Add log. */
        status = HTTP_INSUFFICIENT_MEMORY;
    }

    if( HTTP_SUCCEEDED( status ) )
    {
        /* Write "<METHOD> <PATH> HTTP/1.1\r\n" to start the HTTP header. */
        memcpy( pBufferCur, pRequestInfo->method, pRequestInfo->methodLen );

        pBufferCur += pRequestInfo->methodLen;
        memcpy( pBufferCur, SPACE_CHARACTER, SPACE_CHARACTER_LEN );
        pBufferCur += SPACE_CHARACTER_LEN;

        /* Use "/" as default value if <PATH> is NULL. */
        if( ( pRequestInfo->pPath == NULL ) || ( pRequestInfo->pathLen == 0 ) )
        {
            memcpy( pBufferCur, HTTP_EMPTY_PATH, HTTP_EMPTY_PATH_LEN );
            pBufferCur += SPACE_CHARACTER_LEN;
        }
        else
        {
            memcpy( pBufferCur, pRequestInfo->pPath, pRequestInfo->pathLen );
            pBufferCur += pRequestInfo->pathLen;
        }

        memcpy( pBufferCur, SPACE_CHARACTER, SPACE_CHARACTER_LEN );
        pBufferCur += SPACE_CHARACTER_LEN;

        memcpy( pBufferCur, HTTP_PROTOCOL_VERSION, httpsProtocolVersionLen );
        pBufferCur += httpsProtocolVersionLen;
        memcpy( pBufferCur, HTTP_HEADER_LINE_END, HTTP_HEADER_LINE_END_LEN );
        pBufferCur += HTTP_HEADER_LINE_END_LEN;
        /* Finished "<METHOD> <PATH> HTTP/1.1\r\n". */
    }

    /* Write "User-Agent: <Value>". */
    status = _addHeader( pRequestHeaders,
                         HTTP_USER_AGENT_HEADER,
                         STRLEN_LITERAL( HTTP_USER_AGENT_HEADER ),
                         HTTP_USER_AGENT_VALUE,
                         STRLEN_LITERAL( HTTP_USER_AGENT_VALUE ) );

    if( HTTP_FAILED( status ) )
    {
        /* TODO: Add log. */
    }

    /* Write "Host: <Value>". */
    status = _addHeader( pRequestHeaders,
                         HTTP_HOST_HEADER,
                         STRLEN_LITERAL( HTTP_HOST_HEADER ),
                         pRequestInfo->pHost,
                         pRequestInfo->hostLen );

    if( HTTP_FAILED( status ) )
    {
        /* TODO: Add log. */
    }

    /* Write "\r\n" line to end the HTTP header. */
    if( ( HTTP_HEADER_LINE_END_LEN + pRequestHeaders->headersLen )
        > pRequestHeaders->bufferLen )
    {
        status = HTTP_INSUFFICIENT_MEMORY;
    }

    if( HTTP_SUCCEEDED( status ) )
    {
        memcpy( pBufferCur, HTTP_HEADER_LINE_END, HTTP_HEADER_LINE_END_LEN );
    }

    return status;
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

#include "http_client.h"
#include "private/http_client_internal.h"

bool _isNullParam( const void * ptr )
{
    /* TODO: Add log. */
    return ptr == NULL;
}

HTTPStatus_t _addHeaderLine( HTTPRequestHeaders_t * pRequestHeaders,
                             const char * pLine,
                             size_t lineLen )
{
    HTTPStatus_t status = HTTP_INTERNAL_ERROR;
    uint8_t * pBufferCur = pRequestHeaders->pBuffer;

    /* Check if there is enough space in buffer for additional header.
     * Also count "\r\n" at the end of line. */
    size_t toAddLen = lineLen + HTTP_HEADER_LINE_SEPARATOR_LEN;

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
    memcpy( pBufferCur, HTTP_HEADER_LINE_SEPARATOR_LEN, HTTP_HEADER_LINE_SEPARATOR_LEN );
    pRequestHeaders->headersLen += toAddLen;

    return status;
}

HTTPStatus_t _addHeader( HTTPRequestHeaders_t * pRequestHeaders,
                         const char * pField,
                         size_t fieldLen,
                         const char * pValue,
                         size_t valueLen )
{
    HTTPStatus_t status = HTTP_INTERNAL_ERROR;
    uint8_t * pBufferCur = pRequestHeaders->pBuffer;

    /* (a) Check if there is enough space in buffer for additional header.
     *     The additional "\r\n" at the end is used for checking that there
     *     is a enough space for the last line of an HTTP header.
     *     This last line must be added separately after this method returns. */
    size_t toAddLen = fieldLen + HTTP_HEADER_FIELD_SEPARATOR_LEN + \
                      valueLen + HTTP_HEADER_LINE_SEPARATOR_LEN +  \
                      HTTP_HEADER_LINE_SEPARATOR_LEN;

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
    memcpy( pBufferCur, HTTP_HEADER_LINE_SEPARATOR, HTTP_HEADER_LINE_SEPARATOR_LEN );

    /* Subtract HTTP_HEADER_LINE_SEPARATOR_LEN because it is not actually written
     * and only used for error checking as mentioned above in (a). */
    pRequestHeaders->headersLen += toAddLen - HTTP_HEADER_LINE_SEPARATOR_LEN;

    return status;
}


HTTPStatus_t HTTPClient_InitializeRequestHeaders( HTTPRequestHeaders_t * pRequestHeaders,
                                                  const HTTPRequestInfo_t * pRequestInfo )
{
    HTTPStatus_t status = HTTP_INTERNAL_ERROR;
    size_t toAddLen = 0;
    uint8_t * pBufferCur = pRequestHeaders->pBuffer;
    size_t httpsProtocolVersionLen = STRLEN_LITERAL( HTTP_PROTOCOL_VERSION );

    pRequestHeaders->headersLen = 0;
    /* Clear user-provided buffer. */
    memset( pRequestHeaders->pBuffer, 0, pRequestHeaders->bufferLen );

    /* Check for null parameters. */
    if( _isNullParam( pRequestHeaders ) || _isNullParam( pRequestInfo ) ||
        _isNullParam( pRequestHeaders->pBuffer ) ||
        _isNullParam( pRequestInfo->method ) ||
        _isNullParam( pRequestInfo->pHost ) ||
        _isNullParam( pRequestInfo->pPath ) )
    {
        status = HTTP_INVALID_PARAMETER;
    }

    /* Check if buffer can fit "<METHOD> <PATH> HTTP/1.1\r\n". */
    toAddLen = pRequestInfo->methodLen +                 \
               SPACE_CHARACTER_LEN +                     \
               pRequestInfo->pathLen +                   \
               SPACE_CHARACTER_LEN +                     \
               STRLEN_LITERAL( HTTP_PROTOCOL_VERSION ) + \
               HTTP_HEADER_LINE_SEPARATOR_LEN;

    if( toAddLen + pRequestHeaders->headersLen > pRequestHeaders->bufferLen )
    {
        status = HTTP_INSUFFICIENT_MEMORY;
    }
    else
    {
        /* TODO: Add log. */
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
            pBufferCur += HTTP_EMPTY_PATH_LEN;
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
        memcpy( pBufferCur, HTTP_HEADER_LINE_SEPARATOR, HTTP_HEADER_LINE_SEPARATOR_LEN );
        pBufferCur += HTTP_HEADER_LINE_SEPARATOR_LEN;

        /* Write "User-Agent: <Value>". */
        status = _addHeader( pRequestHeaders,
                             HTTP_USER_AGENT_FIELD,
                             HTTP_USER_AGENT_FIELD_LEN,
                             HTTP_USER_AGENT_VALUE,
                             STRLEN_LITERAL( HTTP_USER_AGENT_VALUE ) );
    }

    if( HTTP_SUCCEEDED( status ) )
    {
        pRequestHeaders->pBuffer += toAddLen;
        /* Write "Host: <Value>". */
        status = _addHeader( pRequestHeaders,
                             HTTP_HOST_FIELD,
                             HTTP_HOST_FIELD_LEN,
                             pRequestInfo->pHost,
                             pRequestInfo->hostLen );
    }

    if( HTTP_SUCCEEDED( status ) )
    {
        if( HTTP_REQUEST_KEEP_ALIVE_FLAG & pRequestInfo->flags )
        {
            /* Write "Connection: keep-alive" */
            status = _addHeader( pRequestHeaders,
                                 HTTP_CONNECTION_FIELD,
                                 HTTP_CONNECTION_FIELD_LEN,
                                 HTTP_CONNECTION_KEEP_ALIVE_VALUE,
                                 HTTP_CONNECTION_KEEP_ALIVE_VALUE_LEN );
        }
        else
        {
            /* Write "Connection: close" */
            status = _addHeader( pRequestHeaders,
                                 HTTP_CONNECTION_FIELD,
                                 HTTP_CONNECTION_FIELD_LEN,
                                 HTTP_CONNECTION_CLOSE_VALUE,
                                 HTTP_CONNECTION_CLOSE_VALUE_LEN );
        }
    }

    if( HTTP_SUCCEEDED( status ) )
    {
        /* Write "\r\n" line to end the HTTP header. */
        if( ( HTTP_HEADER_LINE_SEPARATOR_LEN + pRequestHeaders->headersLen )
            > pRequestHeaders->bufferLen )
        {
            status = HTTP_INSUFFICIENT_MEMORY;
        }
        else
        {
            /* TODO: Add log. */
        }
    }

    if( HTTP_SUCCEEDED( status ) )
    {
        memcpy( pBufferCur,
                HTTP_HEADER_LINE_SEPARATOR,
                HTTP_HEADER_LINE_SEPARATOR_LEN );
        pRequestHeaders->headersLen += HTTP_HEADER_LINE_SEPARATOR_LEN;
    }

    return status;
}

HTTPStatus_t HTTPClient_AddHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                   const char * pField,
                                   size_t fieldLen,
                                   const char * pValue,
                                   size_t valueLen )
{
    HTTPStatus_t status = HTTP_INTERNAL_ERROR;

    /* Check if header field is long enough for length to overflow. */
    if( fieldLen > ( UINT32_MAX >> 2 ) )
    {
        /* TODO: Add log. */
        status = HTTP_INVALID_PARAMETER;
    }

    /* Check if header value is long enough for length to overflow. */
    if( valueLen > ( UINT32_MAX >> 2 ) )
    {
        /* TODO: Add log. */
        status = HTTP_INVALID_PARAMETER;
    }

    /* "Content-Length" header must not be set by user if
     * HTTP_REQUEST_DISABLE_CONTENT_LENGTH_FLAG is deactivated. */
    if( !( HTTP_REQUEST_DISABLE_CONTENT_LENGTH_FLAG & pRequestInfo->flags ) &&
        strncmp( pField,
                 HTTP_CONTENT_LENGTH_FIELD, HTTP_CONTENT_LENGTH_FIELD_LEN ) )
    {
        /* TODO: Add log. */
        status = HTTP_INVALID_PARAMETER;
    }

    /* User must not set "Connection" header through this method. */
    if( strncmp( pField,
                 HTTP_CONNECTION_FIELD, HTTP_CONNECTION_FIELD_LEN ) )
    {
        /* TODO: Add log. */
        status = HTTP_INVALID_PARAMETER;
    }

    /* User must not set "Host" header through this method. */
    if( strncmp( pField,
                 HTTP_HOST_FIELD, HTTP_HOST_FIELD_LEN ) )
    {
        /* TODO: Add log. */
        status = HTTP_INVALID_PARAMETER;
    }

    /* User must not set "User-Agent" header through this method. */
    if( strncmp( pField,
                 HTTP_USER_AGENT_FIELD, HTTP_USER_AGENT_FIELD_LEN ) )
    {
        /* TODO: Add log. */
        status = HTTP_INVALID_PARAMETER;
    }

    if( HTTP_SUCCEEDED( status ) )
    {
        status = _addHeader( pRequestHeaders,
                             pField, fieldLen, pValue, valueLen );
    }

    return status;
}

HTTPStatus_t HTTPClient_AddRangeHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                        int32_t rangeStart,
                                        int32_t rangeEnd )
{
    /* Create buffer to fit max possible length for "bytes=<start>-<end>".
     * This is the value of the Range header. */
    char rangeValueStr[ HTTP_RANGE_BYTES_VALUE_MAX_LEN ] = { 0 };
    char * pRangeValueCur = &rangeValueStr;
    /* Excluding all the remaining null bytes. */
    size_t rangeValueStrActualLength = 0;

    /* Write "bytes=<start>:<end>" for Range header value. */
    memcpy( rangeValueStr,
            HTTP_RANGE_BYTES_PREFIX_VALUE, HTTP_RANGE_BYTES_PREFIX_VALUE_LEN );
    pRangeValueCur += HTTP_RANGE_BYTES_PREFIX_VALUE_LEN;
    rangeValueStrActualLength += HTTP_RANGE_BYTES_PREFIX_VALUE_LEN;
    memcpy( rangeValueStr, EQUAL_CHARACTER, EQUAL_CHARACTER_LEN );
    pRangeValueCur += EQUAL_CHARACTER_LEN;
    rangeValueStrActualLength += EQUAL_CHARACTER_LEN;
    memcpy( rangeValueStr, itoa( rangeStart ), itoaLength( rangeStart ) );
    pRangeValueCur += itoaLength( rangeStart );
    rangeValueStrActualLength += itoaLength( rangeStart );
    memcpy( rangeValueStr, DASH_CHARACTER, DASH_CHARACTER_LEN );
    pRangeValueCur += DASH_CHARACTER_LEN;
    rangeValueStrActualLength += DASH_CHARACTER_LEN;
    memcpy( rangeValueStr, itoa( rangeEnd ), itoaLength( rangeEnd ) );
    pRangeValueCur += itoaLength( rangeEnd );
    rangeValueStrActualLength += itoaLength( rangeEnd );

    return HTTPClient_AddHeader( pRequestHeaders,
                                 HTTP_RANGE_FIELD, HTTP_RANGE_FIELD_LEN,
                                 rangeValueStr, rangeValueStrActualLength );
}

HTTPStatus_t HTTPClient_Send( const HTTPTransportInterface_t * pTransport,
                              const HTTPRequestHeaders_t * pRequestHeaders,
                              const uint8_t * pRequestBodyBuf, /* For a PUT or POST request. */
                              size_t reqBodyBufLen,
                              const HTTPResponse_t * pResponse )
{
    return HTTP_NOT_SUPPORTED;
}

HTTPStatus_t HTTPClient_ReadHeader( const HTTPResponse_t * pResponse,
                                    const char * pName,
                                    size_t nameLen,
                                    char ** pValue,
                                    size_t * valueLen )
{
    return HTTP_NOT_SUPPORTED;
}

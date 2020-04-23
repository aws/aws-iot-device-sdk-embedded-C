/* Standard Includes. */
#include <string.h>
#include <stdlib.h>
#include <stdio.h>

#include "http_client.h"
#include "private/http_client_internal.h"

/*-----------------------------------------------------------*/

/**
 * @brief Send the HTTP headers over the transport send interface.
 *
 * @param pTransport Transport interface.
 * @param pRequestHeaders Request headers to send, it includes the buffer and length.
 *
 * @return #HTTP_SUCCESS if successful. If there was a network error or less
 * bytes than what was specified were sent, then #HTTP_NETWORK_ERROR is returned.
 */
static HTTPStatus_t _sendHttpHeaders( const HTTPTransportInterface_t * pTransport,
                                      const HTTPRequestHeaders_t * pRequestHeaders );

/**
 * @brief Send the HTTP body over the transport send interface.
 *
 * @param pTransport Transport interface.
 * @param pRequestBodyBuf Request body buffer.
 * @param reqBodyLen Length of the request body buffer.
 *
 * @return #HTTP_SUCCESS if successful. If there was a network error or less
 * bytes than what was specified were sent, then #HTTP_NETWORK_ERROR is returned.
 */
static HTTPStatus_t _sendHttpBody( const HTTPTransportInterface_t * pTransport,
                                   const uint8_t * pRequestBodyBuf,
                                   size_t reqBodyBufLen );

/*-----------------------------------------------------------*/

static HTTPStatus_t _addHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                const char * pField,
                                size_t fieldLen,
                                const char * pValue,
                                size_t valueLen );

static HTTPStatus_t _addHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                const char * pField,
                                size_t fieldLen,
                                const char * pValue,
                                size_t valueLen )
{
    HTTPStatus_t returnStatus = HTTP_INTERNAL_ERROR;
    uint8_t * pBufferCur = pRequestHeaders->pBuffer + pRequestHeaders->headersLen;
    size_t toAddLen = 0;
    uint8_t hasTrailingLine = 0;

    if( returnStatus != HTTP_INVALID_PARAMETER )
    {
        /* Backtrack before trailing "\r\n" (HTTP header end) if it's already written.
         * Note that this method also writes trailing "\r\n" before returning. */
        if( strncmp( ( char * ) pBufferCur - 2 * HTTP_HEADER_LINE_SEPARATOR_LEN,
                     "\r\n\r\n", 2 * HTTP_HEADER_LINE_SEPARATOR_LEN ) == 0 )
        {
            /* Set this flag to backtrack in case of HTTP_INSUFFICIENT_MEMORY. */
            hasTrailingLine = 1;
            pBufferCur -= HTTP_HEADER_LINE_SEPARATOR_LEN;
            pRequestHeaders->headersLen -= HTTP_HEADER_LINE_SEPARATOR_LEN;
        }

        /* Check if there is enough space in buffer for additional header. */
        toAddLen = fieldLen + HTTP_HEADER_FIELD_SEPARATOR_LEN + valueLen + \
                   HTTP_HEADER_LINE_SEPARATOR_LEN +                        \
                   HTTP_HEADER_LINE_SEPARATOR_LEN;

        if( ( pRequestHeaders->headersLen + toAddLen ) > pRequestHeaders->bufferLen )
        {
            IotLogError( "Insufficient memory: Provided buffer size too small " \
                         "to add new header." );
            returnStatus = HTTP_INSUFFICIENT_MEMORY;
        }
    }

    /* Set header length to original if previously backtracked. */
    if( ( returnStatus == HTTP_INSUFFICIENT_MEMORY ) && hasTrailingLine )
    {
        pRequestHeaders->headersLen += HTTP_HEADER_LINE_SEPARATOR_LEN;
    }

    if( returnStatus != HTTP_INSUFFICIENT_MEMORY )
    {
        /* Write "Field: Value \r\n\r\n" to headers. */
        memcpy( pBufferCur, pField, fieldLen );
        pBufferCur += fieldLen;
        memcpy( pBufferCur, HTTP_HEADER_FIELD_SEPARATOR,
                HTTP_HEADER_FIELD_SEPARATOR_LEN );
        pBufferCur += HTTP_HEADER_FIELD_SEPARATOR_LEN;
        memcpy( pBufferCur, pValue, valueLen );
        pBufferCur += valueLen;
        memcpy( pBufferCur, HTTP_HEADER_LINE_SEPARATOR, HTTP_HEADER_LINE_SEPARATOR_LEN );
        pBufferCur += HTTP_HEADER_LINE_SEPARATOR_LEN;
        memcpy( pBufferCur, HTTP_HEADER_LINE_SEPARATOR, HTTP_HEADER_LINE_SEPARATOR_LEN );
        pRequestHeaders->headersLen += toAddLen;
        returnStatus = HTTP_SUCCESS;
    }

    return returnStatus;
}

HTTPStatus_t HTTPClient_InitializeRequestHeaders( HTTPRequestHeaders_t * pRequestHeaders,
                                                  const HTTPRequestInfo_t * pRequestInfo )
{
    return HTTP_NOT_SUPPORTED;
}

HTTPStatus_t HTTPClient_AddHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                   const char * pField,
                                   size_t fieldLen,
                                   const char * pValue,
                                   size_t valueLen )
{
    HTTPStatus_t returnStatus = HTTP_INTERNAL_ERROR;
    uint8_t disabledContentLength = false;

    /* Check for NULL parameters. */
    if( pRequestHeaders == NULL )
    {
        IotLogError( "Parameter check failed: pRequestHeaders interface is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pRequestHeaders->pBuffer == NULL )
    {
        IotLogError( "Parameter check failed: pRequestHeaders->pBuffer is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( ( pField == NULL ) )
    {
        IotLogError( "Parameter check failed: pField is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( ( pValue == NULL ) )
    {
        IotLogError( "Parameter check failed: pValue is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else
    {
        /* Empty else MISRA 15.7 */
    }

    /* Check if header field is long enough for length to overflow. */
    if( fieldLen > ( UINT32_MAX >> 2 ) )
    {
        IotLogErrorWithArgs( "Parameter check failed: fieldLen must be less than %d.",
                             ( UINT32_MAX >> 2 ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( fieldLen == 0 )
    {
        IotLogError( "Parameter check failed: fieldLen must be greater than 0." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else
    {
        /* Empty else MISRA 15.7 */
    }

    /* Check if header value is long enough for length to overflow. */
    if( valueLen > ( UINT32_MAX >> 2 ) )
    {
        IotLogErrorWithArgs( "Parameter check failed: valueLen must be less than %d.",
                             ( UINT32_MAX >> 2 ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( valueLen == 0 )
    {
        IotLogError( "Parameter check failed: valueLen must be greater than 0." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else
    {
        /* Empty else MISRA 15.7 */
    }

    if( returnStatus != HTTP_INVALID_PARAMETER )
    {
        disabledContentLength = HTTP_REQUEST_DISABLE_CONTENT_LENGTH_FLAG &
                                pRequestHeaders->flags;

        /* "Content-Length" header must not be set by user if
         * HTTP_REQUEST_DISABLE_CONTENT_LENGTH_FLAG is deactivated. */
        if( !disabledContentLength &&
            ( strncmp( pField,
                       HTTP_CONTENT_LENGTH_FIELD, HTTP_CONTENT_LENGTH_FIELD_LEN ) == 0 ) )
        {
            IotLogError( "Parameter check failed: "                         \
                         "Adding Content-Length header disallowed because " \
                         "HTTP_REQUEST_DISABLE_CONTENT_LENGTH_FLAG is not set." );
            returnStatus = HTTP_INVALID_PARAMETER;
        }

        /* User must not set "Connection" header through this method. */
        if( strncmp( pField,
                     HTTP_CONNECTION_FIELD, fieldLen ) == 0 )
        {
            IotLogError( "Parameter check failed: "                  \
                         "Connection header can only be set during " \
                         "HTTPClient_InitializeRequestHeaders() "    \
                         "through HTTPRequestInfo_t.flags." );
            returnStatus = HTTP_INVALID_PARAMETER;
        }

        /* User must not set "Host" header through this method. */
        if( strncmp( pField,
                     HTTP_HOST_FIELD, fieldLen ) == 0 )
        {
            IotLogError( "Parameter check failed: "               \
                         "Host header can only be set during "    \
                         "HTTPClient_InitializeRequestHeaders() " \
                         "through HTTPRequestInfo_t.pHost." );
            returnStatus = HTTP_INVALID_PARAMETER;
        }

        /* User must not set "User-Agent" header through this method. */
        if( strncmp( pField,
                     HTTP_USER_AGENT_FIELD, fieldLen ) == 0 )
        {
            IotLogError( "Parameter check failed: "                  \
                         "User-Agent header can only be set during " \
                         "HTTPClient_InitializeRequestHeaders() "    \
                         "by defining HTTP_USER_AGENT_VALUE." );
            returnStatus = HTTP_INVALID_PARAMETER;
        }
    }

    if( returnStatus != HTTP_INVALID_PARAMETER )
    {
        returnStatus = _addHeader( pRequestHeaders,
                                   pField, fieldLen, pValue, valueLen );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t HTTPClient_AddRangeHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                        int32_t rangeStart,
                                        int32_t rangeEnd )
{
    return HTTP_NOT_SUPPORTED;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t _sendHttpHeaders( const HTTPTransportInterface_t * pTransport,
                                      const HTTPRequestHeaders_t * pRequestHeaders )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;
    int32_t transportStatus = 0;

    /* Send the HTTP headers over the network. */
    transportStatus = pTransport->send( pTransport->pContext,
                                        pRequestHeaders->pBuffer,
                                        pRequestHeaders->headersLen );

    if( transportStatus < 0 )
    {
        IotLogErrorWithArgs( "Error in sending the HTTP headers over the transport "
                             "interface: Transport returnStatus %d.",
                             transportStatus );
        returnStatus = HTTP_NETWORK_ERROR;
    }
    else if( transportStatus != pRequestHeaders->headersLen )
    {
        IotLogErrorWithArgs( "Failure in sending HTTP headers: Transport layer "
                             "did not send the required bytes: Required Bytes=%d"
                             ", Sent Bytes=%d.",
                             transportStatus );
        returnStatus = HTTP_NETWORK_ERROR;
    }
    else
    {
        /* Empty else MISRA 15.7 */
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t _sendHttpBody( const HTTPTransportInterface_t * pTransport,
                                   const uint8_t * pRequestBodyBuf,
                                   size_t reqBodyBufLen )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;
    int32_t transportStatus = 0;

    /* Send the HTTP body over the network. */
    if( pRequestBodyBuf != NULL )
    {
        transportStatus = pTransport->send( pTransport->pContext,
                                            pRequestBodyBuf,
                                            reqBodyBufLen );

        if( transportStatus < 0 )
        {
            IotLogErrorWithArgs( "Error in sending the HTTP body over the "
                                 "transport interface. Transport returnStatus %d.",
                                 transportStatus );
            returnStatus = HTTP_NETWORK_ERROR;
        }
        else if( transportStatus != reqBodyBufLen )
        {
            IotLogErrorWithArgs( "Failure in sending HTTP headers: Transport layer "
                                 "did not send the required bytes: Required Bytes=%d"
                                 ", Sent Bytes=%d.",
                                 transportStatus );
            returnStatus = HTTP_NETWORK_ERROR;
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t _receiveHttpResponse( const HTTPTransportInterface_t * pTransport,
                                          HTTPResponse_t * pResponse )
{
    /* TODO: Receive the HTTP response with parsing. */
    return HTTP_SUCCESS;
}

/*-----------------------------------------------------------*/

HTTPStatus_t HTTPClient_Send( const HTTPTransportInterface_t * pTransport,
                              const HTTPRequestHeaders_t * pRequestHeaders,
                              const uint8_t * pRequestBodyBuf,
                              size_t reqBodyBufLen,
                              HTTPResponse_t * pResponse )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    if( pTransport == NULL )
    {
        IotLogError( "Parameter check failed: pTransport interface is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pTransport->send == NULL )
    {
        IotLogError( "Parameter check failed: pTransport->send is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pTransport->recv == NULL )
    {
        IotLogError( "Parameter check failed: pTransport->recv is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pRequestHeaders == NULL )
    {
        IotLogError( "Parameter check failed: pRequestHeaders is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pRequestHeaders->pBuffer == NULL )
    {
        IotLogError( "Parameter check failed: pRequestHeaders->pBuffer is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else
    {
        /* Empty else MISRA 15.7 */
    }

    /* Send the headers, which are at one location in memory. */
    if( returnStatus == HTTP_SUCCESS )
    {
        returnStatus = _sendHttpHeaders( pTransport,
                                         pRequestHeaders );
    }

    /* Send the body, which is at another location in memory. */
    if( returnStatus == HTTP_SUCCESS )
    {
        returnStatus = _sendHttpBody( pTransport,
                                      pRequestBodyBuf,
                                      reqBodyBufLen );
    }

    if( returnStatus == HTTP_SUCCESS )
    {
        returnStatus = _receiveHttpResponse( pTransport,
                                             pResponse );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t HTTPClient_ReadHeader( HTTPResponse_t * pResponse,
                                    const char * pName,
                                    size_t nameLen,
                                    char ** pValue,
                                    size_t * valueLen )
{
    return HTTP_NOT_SUPPORTED;
}

/*-----------------------------------------------------------*/

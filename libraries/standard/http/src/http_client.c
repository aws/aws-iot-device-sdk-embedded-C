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

/*-----------------------------------------------------------*/

HTTPStatus_t HTTPClient_AddHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                   const char * pName,
                                   size_t nameLen,
                                   const char * pValue,
                                   size_t valueLen )
{
    return HTTP_NOT_SUPPORTED;
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
                             "interface: Transport status %d.",
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
                                 "transport interface. Transport status %d.",
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

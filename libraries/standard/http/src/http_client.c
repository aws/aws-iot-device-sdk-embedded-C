#include <assert.h>
#include <string.h>
#include <stdio.h>

#include "http_client.h"
#include "private/http_client_internal.h"
#include "private/http_client_parse.h"

/*-----------------------------------------------------------*/

/**
 * @brief Send the HTTP headers over the transport send interface.
 *
 * @param[in] pTransport Transport interface.
 * @param[in] pRequestHeaders Request headers to send, it includes the buffer
 * and length.
 *
 * @return #HTTP_SUCCESS if successful. If there was a network error or less
 * bytes than what was specified were sent, then #HTTP_NETWORK_ERROR is returned.
 */
static HTTPStatus_t _sendHttpHeaders( const HTTPTransportInterface_t * pTransport,
                                      const HTTPRequestHeaders_t * pRequestHeaders );

/**
 * @brief Send the HTTP body over the transport send interface.
 *
 * @param[in] pTransport Transport interface.
 * @param[in] pRequestBodyBuf Request body buffer.
 * @param[in] reqBodyLen Length of the request body buffer.
 *
 * @return #HTTP_SUCCESS if successful. If there was a network error or less
 * bytes than what was specified were sent, then #HTTP_NETWORK_ERROR is returned.
 */
static HTTPStatus_t _sendHttpBody( const HTTPTransportInterface_t * pTransport,
                                   const uint8_t * pRequestBodyBuf,
                                   size_t reqBodyBufLen );

/**
 * @brief Write header based on parameters. This method also adds a trailing "\r\n".
 * If a trailing "\r\n" already exists in the HTTP header, this method backtracks
 * in order to write over it and updates the length accordingly.
 *
 * @param pRequestHeaders Request header buffer information.
 * @param pField The header field name to write.
 * @param fieldLen The byte length of the header field name.
 * @param pValue The header value to write.
 * @param valueLen The byte length of the header field value.
 *
 * @return #HTTP_SUCCESS if successful. If there was insufficient memory in the
 * application buffer, then #HTTP_INSUFFICIENT_MEMORY is returned.
 */
static HTTPStatus_t _addHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                const char * pField,
                                size_t fieldLen,
                                const char * pValue,
                                size_t valueLen );

/**
 * @brief Receive HTTP response from the transport recv interface.
 *
 * @param[in] pTransport Transport interface.
 * @param[in] pResponse Response buffer.
 * @param[in] bufferLen Length of the response buffer.
 *
 * @return Returns #HTTP_SUCCESS if successful. If there was a network error or
 * more bytes than what was specified were read, then #HTTP_NETWORK_ERROR is
 * returned.
 */
HTTPStatus_t _receiveHttpResponse( const HTTPTransportInterface_t * pTransport,
                                   uint8_t * pBuffer,
                                   size_t bufferLen,
                                   size_t * pBytesReceived );

/**
 * @brief Get the status of the HTTP response given the parsing state and how
 * much data is in the response buffer.
 *
 * @param[in] parsingState State of the parsing on the HTTP response.
 * @param[in] totalReceived The amount of network data received in the response
 * buffer.
 * @param[in] responseBufferLen The length of the response buffer.
 *
 * @return Returns #HTTP_SUCCESS if the parsing state is complete. If
 * the parsing state denotes it never started, then return #HTTP_NO_RESPONSE. If
 * the parsing state is incomplete, then if the response buffer is not full
 * #HTTP_PARTIAL_RESPONSE is returned. If the parsing state is incomplete, then
 * if the response buffer is full #HTTP_INSUFFICIENT_MEMORY is returned.
 */
static HTTPStatus_t _getFinalResponseStatus( HTTPParsingState_t parsingState,
                                             size_t totalReceived,
                                             size_t responseBufferLen );

/**
 * @brief Receive the HTTP response from the network and parse it.
 *
 * @param[in] pTransport Transport interface.
 * @param[in] pResponse Response message to receive data from the network.
 *
 * @return Returns #HTTP_SUCCESS if successful. If there was an issue with receiving
 * the response over the network interface, then #HTTP_NETWORK_ERROR is returned,
 * please see #_receiveHttpResponse. If there was an issue with parsing, then the
 * parsing error that occurred will be returned, please see
 * #_HTTPClient_InitializeParsingContext and #_HTTPClient_ParseResponse. Please
 * see #_getFinalResponseStatus for the status returned when there were no
 * network or parsing errors.
 */
static HTTPStatus_t _receiveAndParseHttpResponse( const HTTPTransportInterface_t * pTransport,
                                                  HTTPResponse_t * pResponse );

/*-----------------------------------------------------------*/

static HTTPStatus_t _addHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                const char * pField,
                                size_t fieldLen,
                                const char * pValue,
                                size_t valueLen )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;
    uint8_t * pBufferCur = pRequestHeaders->pBuffer + pRequestHeaders->headersLen;
    size_t toAddLen = 0;
    size_t backtrackHeaderLen = pRequestHeaders->headersLen;
    int32_t bytesWritten = 0;

    assert( pRequestHeaders != NULL );
    assert( pRequestHeaders->pBuffer != NULL );
    assert( pField != NULL );
    assert( pValue != NULL );
    assert( fieldLen != 0u );
    assert( valueLen != 0u );

    /* Backtrack before trailing "\r\n" (HTTP header end) if it's already written.
     * Note that this method also writes trailing "\r\n" before returning.
     * The first condition prevents reading before start of the header. */
    if( ( HTTP_HEADER_END_INDICATOR_LEN <= pRequestHeaders->headersLen ) &&
        ( strncmp( ( char * ) pBufferCur - HTTP_HEADER_END_INDICATOR_LEN,
                   HTTP_HEADER_END_INDICATOR, HTTP_HEADER_END_INDICATOR_LEN ) == 0 ) )
    {
        backtrackHeaderLen -= HTTP_HEADER_LINE_SEPARATOR_LEN;
        pBufferCur -= HTTP_HEADER_LINE_SEPARATOR_LEN;
    }

    /* Check if there is enough space in buffer for additional header. */
    toAddLen = fieldLen + HTTP_HEADER_FIELD_SEPARATOR_LEN + valueLen +
               HTTP_HEADER_LINE_SEPARATOR_LEN +
               HTTP_HEADER_LINE_SEPARATOR_LEN;

    /* If we have enough room for the new header line, then write it to the header buffer. */
    if( ( backtrackHeaderLen + toAddLen ) <= pRequestHeaders->bufferLen )
    {
        /* Write "Field: Value \r\n" to headers. */
        bytesWritten = snprintf( ( char * ) pBufferCur,
                                 toAddLen,
                                 HTTP_HEADER_ADD_FORMAT,
                                 ( int32_t ) fieldLen, pField,
                                 ( int32_t ) valueLen, pValue );

        if( ( bytesWritten + HTTP_HEADER_LINE_SEPARATOR_LEN ) != toAddLen )
        {
            IotLogErrorWithArgs( "Internal error in snprintf() in _addHeader(). "
                                 "Bytes written: %d.", bytesWritten );
        }
        else
        {
            pBufferCur += bytesWritten;

            /* HTTP_HEADER_LINE_SEPARATOR cannot be written above because snprintf
             * writes an extra null byte at the end. */
            memcpy( pBufferCur, HTTP_HEADER_LINE_SEPARATOR, HTTP_HEADER_LINE_SEPARATOR_LEN );
            pRequestHeaders->headersLen = backtrackHeaderLen + toAddLen;
            returnStatus = HTTP_SUCCESS;
        }
    }
    else
    {
        IotLogErrorWithArgs( "Unable to add header in buffer: "
                             "Buffer has insufficient memory: "
                             "RequiredBytes=%d, RemainingBufferSize=%d",
                             toAddLen,
                             ( pRequestHeaders->bufferLen - pRequestHeaders->headersLen ) );
        returnStatus = HTTP_INSUFFICIENT_MEMORY;
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t HTTPClient_InitializeRequestHeaders( HTTPRequestHeaders_t * pRequestHeaders,
                                                  const HTTPRequestInfo_t * pRequestInfo )
{
    return HTTP_NOT_SUPPORTED;
}

/*-----------------------------------------------------------*/

HTTPStatus_t HTTPClient_AddHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                   const char * pField,
                                   size_t fieldLen,
                                   const char * pValue,
                                   size_t valueLen )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    /* Check for NULL parameters. */
    if( pRequestHeaders == NULL )
    {
        IotLogError( "Parameter check failed: pRequestHeaders is NULL." );
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
    else if( fieldLen == 0u )
    {
        IotLogError( "Parameter check failed: fieldLen must be greater than 0." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( valueLen == 0u )
    {
        IotLogError( "Parameter check failed: valueLen must be greater than 0." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else
    {
        /* Empty else MISRA 15.7 */
    }

    if( returnStatus == HTTP_SUCCESS )
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

    assert( pTransport != NULL );
    assert( pTransport->send != NULL );
    assert( pRequestHeaders != NULL );

    /* Send the HTTP headers over the network. */
    transportStatus = pTransport->send( pTransport->pContext,
                                        pRequestHeaders->pBuffer,
                                        pRequestHeaders->headersLen );

    if( transportStatus < 0 )
    {
        IotLogErrorWithArgs( "Failed to send HTTP headers: Transport send()"
                             " returned error: Transport Status=%d",
                             transportStatus );
        returnStatus = HTTP_NETWORK_ERROR;
    }
    else if( (size_t)transportStatus != pRequestHeaders->headersLen )
    {
        IotLogErrorWithArgs( "Failed to send HTTP headers: Transport layer "
                             "did not send the required bytes: Required bytes=%d"
                             ", Sent bytes=%d.",
                             pRequestHeaders->headersLen,
                             transportStatus );
        returnStatus = HTTP_NETWORK_ERROR;
    }
    else
    {
        IotLogDebugWithArgs( "Sent HTTP headers over the transport: Bytes sent "
                             "= %d.",
                             transportStatus );
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

    assert( pTransport != NULL );
    assert( pTransport->send != NULL );
    assert( pRequestBodyBuf != NULL );

    transportStatus = pTransport->send( pTransport->pContext,
                                        pRequestBodyBuf,
                                        reqBodyBufLen );

    if( transportStatus < 0 )
    {
        IotLogErrorWithArgs( "Failed to send HTTP body: Transport send() "
                             " returned error: Transport Status=%d",
                             transportStatus );
        returnStatus = HTTP_NETWORK_ERROR;
    }
    else if( ( size_t )transportStatus != reqBodyBufLen )
    {
        IotLogErrorWithArgs( "Failed to send HTTP body: Transport send() "
                             "did not send the required bytes: Required bytes=%d"
                             ", Sent bytes=%d.",
                             reqBodyBufLen,
                             transportStatus );
        returnStatus = HTTP_NETWORK_ERROR;
    }
    else
    {
        IotLogDebugWithArgs( "Sent HTTP body over the transport: Bytes sent=%d.",
                             transportStatus );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t _receiveHttpResponse( const HTTPTransportInterface_t * pTransport,
                                   uint8_t * pBuffer,
                                   size_t bufferLen,
                                   size_t * pBytesReceived )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    assert( pTransport != NULL );
    assert( pTransport->recv != NULL );
    assert( pBuffer != NULL );
    assert( pBytesReceived != NULL );

    int32_t transportStatus = pTransport->recv( pTransport->pContext,
                                                pBuffer,
                                                bufferLen );

    /* A transport status of less than zero is an error. */
    if( transportStatus < 0 )
    {
        IotLogErrorWithArgs( "Failed to receive HTTP response: Transport recv() "
                             "returned error: Transport status=%d.",
                             transportStatus );
        returnStatus = HTTP_NETWORK_ERROR;
    }
    else if( (size_t)transportStatus > bufferLen )
    {
        /* There is a bug in the transport recv if more bytes are reported
         * to have been read than the bytes asked for. */
        IotLogErrorWithArgs( "Failed to receive HTTP response: Transport recv() "
                             " read more bytes than expected: Bytes read=%d",
                             transportStatus );
        returnStatus = HTTP_NETWORK_ERROR;
    }
    else if( transportStatus > 0 )
    {
        /* Some or all of the specified data was received. */
        *pBytesReceived = ( size_t ) ( transportStatus );
        IotLogDebugWithArgs( "Received data from the transport: Bytes "
                             "received=%d.",
                             transportStatus );
    }
    else
    {
        /* When a zero is returned from the transport recv it will not be
         * invoked again. */
        IotLogDebug( "Transport recv() returned 0. Receiving transport data"
                     "is complete." );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t _getFinalResponseStatus( HTTPParsingState_t parsingState,
                                             size_t totalReceived,
                                             size_t responseBufferLen )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    assert( parsingState >= HTTP_PARSING_NONE &&
            parsingState <= HTTP_PARSING_COMPLETE );
    assert( totalReceived <= responseBufferLen );

    /* If no parsing occurred, that means network data was never received. */
    if( parsingState == HTTP_PARSING_NONE )
    {
        IotLogErrorWithArgs( "Response not received: Zero returned from "
                             "transport recv: Total received=%d",
                             totalReceived );
        returnStatus = HTTP_NO_RESPONSE;
    }
    else if( parsingState == HTTP_PARSING_INCOMPLETE )
    {
        if( totalReceived == responseBufferLen )
        {
            IotLogErrorWithArgs( "Response is too large for the response buffer"
                                 ": Response buffer size in bytes=%d",
                                 responseBufferLen );
            returnStatus = HTTP_INSUFFICIENT_MEMORY;
        }
        else
        {
            IotLogErrorWithArgs( "Partial response received: Transport recv "
                                 "returned zero before the complete response: "
                                 "Partial size=%d, Response buffer space "
                                 "left=%d",
                                 totalReceived,
                                 responseBufferLen - totalReceived );
            returnStatus = HTTP_PARTIAL_RESPONSE;
        }
    }
    else
    {
        /* Empty else for MISRA 15.7 compliance. */
    }

    return returnStatus;
}

static HTTPStatus_t _receiveAndParseHttpResponse( const HTTPTransportInterface_t * pTransport,
                                                  HTTPResponse_t * pResponse )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;
    size_t totalReceived = 0;
    size_t currentReceived = 0;
    HTTPParsingContext_t parsingContext = { 0 };

    if( pResponse->pBuffer == NULL )
    {
        IotLogError( "Parameter check failed: pResponse->pBuffer is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }

    if( returnStatus == HTTP_SUCCESS )
    {
        /* Initialize the parsing context. */
        returnStatus = _HTTPClient_InitializeParsingContext( &parsingContext,
                                                             pResponse->pHeaderParsingCallback );
    }

    /* While there are no errors in the transport recv or parsing, the response
     * message is not finished, and there is room in the response buffer. */
    while( ( returnStatus == HTTP_SUCCESS ) &&
           ( parsingContext.state != HTTP_PARSING_COMPLETE ) &&
           ( totalReceived < pResponse->bufferLen ) )
    {
        /* Receive the HTTP response data into the pResponse->pBuffer. */
        returnStatus = _receiveHttpResponse( pTransport,
                                             pResponse->pBuffer + totalReceived,
                                             pResponse->bufferLen - totalReceived,
                                             &currentReceived );

        if( returnStatus == HTTP_SUCCESS )
        {
            if( currentReceived > 0 )
            {
                totalReceived += currentReceived;
                /* Data is received into the buffer and must be parsed. */
                returnStatus = _HTTPClient_ParseResponse( &parsingContext,
                                                          pResponse->pBuffer + totalReceived,
                                                          currentReceived );
            }
            else
            {
                /* If there was no data received, then end receiving and parsing
                 * the response. */
                break;
            }
        }
    }

    if( returnStatus == HTTP_SUCCESS )
    {
        /* For no network or parsing errors, the final status of the response
         * message is derived from the state of the parsing and how much data
         * is in the buffer. */
        returnStatus = _getFinalResponseStatus( parsingContext.state,
                                                totalReceived,
                                                pResponse->bufferLen );
    }

    return returnStatus;
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
        /* Empty else for MISRA 15.7 compliance. */
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
        if( pRequestBodyBuf != NULL )
        {
            returnStatus = _sendHttpBody( pTransport,
                                          pRequestBodyBuf,
                                          reqBodyBufLen );
        }
        else
        {
            IotLogDebug( "A request body was not sent: pRequestBodyBuf is NULL." );
        }
    }

    if( returnStatus == HTTP_SUCCESS )
    {
        /* If the application chooses to receive a response, then pResponse
         * will not be NULL. */
        if( pResponse != NULL )
        {
            returnStatus = _receiveAndParseHttpResponse( pTransport,
                                                         pResponse );
        }
        else
        {
            IotLogWarn( "A response was not received: pResponse is NULL. " );
        }
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

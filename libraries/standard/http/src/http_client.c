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
     * Note that this method also writes trailing "\r\n" before returning. */
    if( strncmp( ( char * ) pBufferCur - ( 2 * HTTP_HEADER_LINE_SEPARATOR_LEN ),
                 "\r\n\r\n", 2 * HTTP_HEADER_LINE_SEPARATOR_LEN ) == 0 )
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
        /* Write "Field: Value \r\n\r\n" to headers. */
        bytesWritten = snprintf( ( char * ) pBufferCur,
                                 toAddLen,
                                 "%.*s%s%.*s%s",
                                 ( int32_t ) fieldLen, pField,
                                 HTTP_HEADER_FIELD_SEPARATOR,
                                 ( int32_t ) valueLen, pValue,
                                 HTTP_HEADER_LINE_SEPARATOR );

        if( ( bytesWritten + HTTP_HEADER_LINE_SEPARATOR_LEN ) != toAddLen )
        {
            IotLogErrorWithArgs( "Internal error in snprintf() in _addHeader(). "
                                 "Bytes written: %d.", bytesWritten );
        }
        else
        {
            pBufferCur += bytesWritten;
        }

        /* HTTP_HEADER_LINE_SEPARATOR cannot be written above because snprintf
         * writes an extra null byte at the end. */
        memcpy( pBufferCur, HTTP_HEADER_LINE_SEPARATOR, HTTP_HEADER_LINE_SEPARATOR_LEN );
        pRequestHeaders->headersLen = backtrackHeaderLen + toAddLen;
        returnStatus = HTTP_SUCCESS;
    }
    else
    {
        IotLogErrorWithArgs( "Unable to add header in buffer: ",
                             "Buffer has insufficient memory: ",
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
    HTTPStatus_t returnStatus = HTTP_SUCCESS;
    size_t requiredBytes = 0;
    char rangeStartStrBuffer[ MAX_INT32_NO_OF_DIGITS ] = { 0 };
    size_t rangeStartStrLen = 0;
    char rangeEndStrBuffer[ MAX_INT32_NO_OF_DIGITS ] = { 0 };
    size_t rangeEndStrLen = 0;
    uint8_t hasTrailingSeparator = 0u;

    if( pRequestHeaders == NULL )
    {
        IotLogError( "Parameter check failed: pRequestHeaders is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( rangeEnd < 0 )
    {
        IotLogErrorWithArgs( "Parameter check failed: rangeEnd is negative: "
                             "rangeEnd should be >=0: RangeEnd=%d", rangeEnd );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( ( rangeEnd != 0 ) && ( rangeStart > rangeEnd ) )
    {
        IotLogErrorWithArgs( "Parameter check failed: Invalid range values: "
                             "rangeStart should be > rangeEnd when both are > 0: "
                             "RangeStart=%d, RangeEnd=%d", rangeStart, rangeEnd );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else
    {
        /* Empty else MISRA 15.7 */
    }

    requiredBytes = RANGE_REQUEST_HEADER_FIELD_LEN +
                    HTTP_HEADER_LINE_SEPARATOR_LEN +
                    RANGE_REQUEST_HEADER_VALUE_PREFIX_LEN;

    /* Add byte count for ASCII representation of rangeStart value. */
    ( void ) itoa( rangeStart, rangeStartStrBuffer, 10 );
    requiredBytes += strlen( rangeStartStrBuffer );

    /* Scenario when both range parameters are part of the request. */
    if( rangeEnd != 0 )
    {
        /* Add byte count for ASCII representation of rangeEnd value. */
        ( void ) itoa( rangeEnd, rangeEndStrBuffer, 10 );
        requiredBytes += strlen( rangeEndStrBuffer );
    }
    /* Case when request is for all bytes >= rangeStart. */
    else if( rangeStart > 0 )
    {
        /* Add byte count for "-" character. */
        requiredBytes += DASH_CHARACTER_LEN;
    }

    /* Add byte counts for appending "\r\n" twice at the end. */
    requiredBytes += 2 * HTTP_HEADER_LINE_SEPARATOR_LEN;

    /* Backtrack before trailing "\r\n" (HTTP header end) if it's already written.
     * Note that this method also writes trailing "\r\n" before returning. */
    if( memcmp( pRequestHeaders->pBuffer +  -( 2 * HTTP_HEADER_LINE_SEPARATOR_LEN ),
                "\r\n\r\n", 2 * HTTP_HEADER_LINE_SEPARATOR_LEN ) == 0 )
    {
        hasTrailingSeparator = 1u;
    }

    /* Check if the passed header buffer contains enough remaining memory for
     * adding the Range Request header. */
    if( ( pRequestHeaders->bufferLen - pRequestHeaders->headersLen -
          HTTP_HEADER_LINE_SEPARATOR_LEN )
        >= requiredBytes )
    {
        /* Add the range request header field and rangeStart value of the form
         * "Range: bytes=<rangeStart>" to the buffer. */
        sprintf( pRequestHeaders->pBuffer + pRequestHeaders->headersLen
                 - HTTP_HEADER_LINE_SEPARATOR_LEN,
                 "%s%s%s%s",
                 RANGE_REQUEST_HEADER_FIELD,
                 HTTP_HEADER_FIELD_SEPARATOR
                 RANGE_REQUEST_HEADER_VALUE_PREFIX,
                 rangeStartStrBuffer );

        pRequestHeaders->headersLen += RANGE_REQUEST_HEADER_FIELD_LEN +
                                       HTTP_HEADER_LINE_SEPARATOR_LEN +
                                       RANGE_REQUEST_HEADER_VALUE_PREFIX_LEN +
                                       rangeStartStrLen;

        /* Add remaining value data depending on the range specification type . */

        /* Add rangeEnd value if it is valid. */
        if( rangeEnd != 0 )
        {
            /* Add the rangeEnd value to the request range .*/
            sprintf( pRequestHeaders->pBuffer + pRequestHeaders->headersLen,
                     "%s%s"
                     DASH_CHARACTER,
                     rangeEndStrBuffer );
            pRequestHeaders->headersLen += DASH_CHARACTER_LEN + rangeEndStrLen;
        }
        /* Case when request is for all bytes >= rangeStart. */
        else if( rangeStart > 0 )
        {
            /* Add the "-" character.*/
            sprintf( pRequestHeaders->pBuffer + pRequestHeaders->headersLen,
                     "%s"
                     DASH_CHARACTER );
            pRequestHeaders->headersLen += DASH_CHARACTER_LEN;
        }

        /* Add the termination "\r\n\r\n" characters. */
        /*Note: memcpy() is used here to avoid adding NULL character in the buffer. */
        memcpy( pRequestHeaders->pBuffer + pRequestHeaders->headersLen,
                HTTP_HEADER_LINE_SEPARATOR,
                HTTP_HEADER_LINE_SEPARATOR_LEN );
        memcpy( pRequestHeaders->pBuffer + pRequestHeaders->headersLen,
                HTTP_HEADER_LINE_SEPARATOR,
                HTTP_HEADER_LINE_SEPARATOR_LEN );
        pRequestHeaders->headersLen += 2 * HTTP_HEADER_LINE_SEPARATOR_LEN;
    }
    else
    {
        IotLogErrorWithArgs( "Unable to add Range Request in buffer: "
                             "Buffer has insufficient space: "
                             "RequiredBytes=%d, BufferSpace=%d",
                             requiredBytes,
                             ( pRequestHeaders->bufferLen - pRequestHeaders->headersLen ) );
        returnStatus = HTTP_INSUFFICIENT_MEMORY;
    }

    return returnStatus;
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
                             "interface : TransportStatus = % d.",
                             transportStatus );
        returnStatus = HTTP_NETWORK_ERROR;
    }
    else if( transportStatus != pRequestHeaders->headersLen )
    {
        IotLogErrorWithArgs( "Failure in sending HTTP headers:Transport layer "
                             "did not send the required bytes:RequiredBytes = % d "
                             ", SentBytes = % d.",
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
                                 "transport interface.TransportStatus = % d.",
                                 transportStatus );
            returnStatus = HTTP_NETWORK_ERROR;
        }
        else if( transportStatus != reqBodyBufLen )
        {
            IotLogErrorWithArgs( "Failure in sending HTTP headers:      Transport layer "
                                 "did not send the required bytes:      RequiredBytes = % d "
                                 ", SentBytes = % d.",
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
        IotLogError( "Parameter check failed:   pTransport interface is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pTransport->send == NULL )
    {
        IotLogError( "Parameter check failed:   pTransport->send is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pTransport->recv == NULL )
    {
        IotLogError( "Parameter check failed:   pTransport->recv is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pRequestHeaders == NULL )
    {
        IotLogError( "Parameter check failed:   pRequestHeaders is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pRequestHeaders->pBuffer == NULL )
    {
        IotLogError( "Parameter check failed:   pRequestHeaders->pBuffer is NULL." );
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

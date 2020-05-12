#include <assert.h>
#include <string.h>

#include "http_client.h"
#include "private/http_client_internal.h"
#include "private/http_client_parse.h"
#include "http_parser/http_parser.h"

/*-----------------------------------------------------------*/

/**
 * @brief An aggregator that represents the user-provided parameters to the
 * #HTTPClient_ReadHeader API function. This will be used as context parameter
 * for the parsing callbacks used by the API function.
 */
typedef struct findHeaderContext
{
    const uint8_t * pField;
    size_t fieldLen;
    const uint8_t ** pValueLoc;
    size_t * pValueLen;
    uint8_t fieldFound : 1;
    uint8_t valueFound : 1;
} findHeaderContext_t;

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
static HTTPStatus_t sendHttpHeaders( const HTTPTransportInterface_t * pTransport,
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
static HTTPStatus_t sendHttpBody( const HTTPTransportInterface_t * pTransport,
                                  const uint8_t * pRequestBodyBuf,
                                  size_t reqBodyBufLen );

/**
 * @brief Write header based on parameters. This method also adds a trailing "\r\n".
 * If a trailing "\r\n" already exists in the HTTP header, this method backtracks
 * in order to write over it and updates the length accordingly.
 *
 * @param[in] pRequestHeaders Request header buffer information.
 * @param[in] pField The ISO 8859-1 encoded header field name to write.
 * @param[in] fieldLen The byte length of the header field name.
 * @param[in] pValue The ISO 8859-1 encoded header value to write.
 * @param[in] valueLen The byte length of the header field value.
 *
 * @return #HTTP_SUCCESS if successful. If there was insufficient memory in the
 * application buffer, then #HTTP_INSUFFICIENT_MEMORY is returned.
 */
static HTTPStatus_t addHeader( HTTPRequestHeaders_t * pRequestHeaders,
                               const uint8_t * pField,
                               size_t fieldLen,
                               const uint8_t * pValue,
                               size_t valueLen );

/**
 * @brief Receive HTTP response from the transport recv interface.
 *
 * @param[in] pTransport Transport interface.
 * @param[in] pResponse Response buffer.
 * @param[in] bufferLen Length of the response buffer.
 * @param[out] Bytes received from the transport interface.
 *
 * @return Returns #HTTP_SUCCESS if successful. If there was a network error or
 * more bytes than what was specified were read, then #HTTP_NETWORK_ERROR is
 * returned.
 */
HTTPStatus_t receiveHttpResponse( const HTTPTransportInterface_t * pTransport,
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
static HTTPStatus_t getFinalResponseStatus( HTTPParsingState_t parsingState,
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
 * please see #receiveHttpResponse. If there was an issue with parsing, then the
 * parsing error that occurred will be returned, please see
 * #HTTPClient_InitializeParsingContext and HTTPClient_ParseResponse. Please
 * see #getFinalResponseStatus for the status returned when there were no
 * network or parsing errors.
 */
static HTTPStatus_t receiveAndParseHttpResponse( const HTTPTransportInterface_t * pTransport,
                                                 HTTPResponse_t * pResponse );

/**
 * @brief Converts an integer value to its ASCII representation in the passed buffer.
 *
 * @param[in] value The value to convert to ASCII.
 * @param[out] pBuffer The buffer to store the ASCII representation of the integer.
 *
 * @return Returns the number of bytes written to @p pBuffer.
 */
static uint8_t convertInt32ToAscii( int32_t value,
                                    uint8_t * pBuffer,
                                    size_t bufferLength );

/**
 * @brief This method writes the request line (first line) of the HTTP Header
 * into #HTTPRequestHeaders_t.pBuffer and updates length accordingly.
 *
 * @param pRequestHeaders Request header buffer information.
 * @param pMethod The HTTP request method e.g. "GET", "POST", "PUT", or "HEAD".
 * @param methodLen The byte length of the request method.
 * @param pPath The Request-URI to the objects of interest, e.g. "/path/to/item.txt".
 * @param pathLen The byte length of the request path.
 *
 * @return #HTTP_SUCCESS if successful. If there was insufficient memory in the
 * application buffer, then #HTTP_INSUFFICIENT_MEMORY is returned.
 */
static HTTPStatus_t writeRequestLine( HTTPRequestHeaders_t * pRequestHeaders,
                                      const char * pMethod,
                                      size_t methodLen,
                                      const char * pPath,
                                      size_t pathLen );

/**
 * @brief Find the specified header field in the response buffer.
 *
 * @param[in] pBuffer The response buffer to parse.
 * @param[in] bufferLen The length of the response buffer to parse.
 * @param[in] pField The header field to search for.
 * @param[in] fieldLen The length of pField.
 * @param[out] pValue The location of the the header value found in pBuffer.
 * @param[out] pValueLen The length of pValue.
 *
 * @return One of the following:
 * - #HTTP_SUCCESS when header is found in the response.
 * - #HTTP_HEADER_NOT_FOUND if requested header is not found in response.
 * - #HTTP_INVALID_RESPONSE if passed response is invalid for parsing.
 * - #HTTP_INTERNAL_ERROR for any parsing errors.
 */
static HTTPStatus_t findHeaderInResponse( const uint8_t * pBuffer,
                                          size_t bufferLen,
                                          const uint8_t * pField,
                                          size_t fieldLen,
                                          const uint8_t ** pValue,
                                          size_t * pValueLen );

/**
 * @brief The "on_header_field" callback for the HTTP parser used by the
 * #findHeaderInResponse function. The callback checks whether the parser
 * header field matched the header being searched for, and sets a flag to
 * represent reception of the header accordingly.
 *
 * @param[in] pHttpParser The parser object to which this callback is registered.
 * @param[in] pFieldLoc The location of the parsed header field in the response buffer.
 * @param[in] fieldLen The length of the header field.
 *
 * @return Returns #HTTP_PARSER_CONTINUE_PARSING to indicate continuation with parsing.
 */
static int findHeaderFieldParserCallback( http_parser * pHttpParser,
                                          const char * pFieldLoc,
                                          size_t fieldLen );

/**
 * @brief The "on_header_value" callback for the HTTP parser used by the
 * #findHeaderInResponse function. The callback sets the user-provided output parameters
 * for header value if the requested header's field was found in the
 * @ref findHeaderFieldParserCallback function.
 *
 * @param[in] pHttpParser The parser object to which this callback is registered.
 * @param[in] pVaLueLoc The location of the parsed header value in the response buffer.
 * @param[in] valueLen The length of the header value.
 *
 * @return Returns #HTTP_PARSER_STOP_PARSING if the header field/value pair are found; otherwise,
 * #HTTP_PARSING_CONTINUE_PARSING.
 */
static int findHeaderValueParserCallback( http_parser * pHttpParser,
                                          const char * pVaLueLoc,
                                          size_t valueLen );

/**
 * @brief The "on_header_complete" callback for the HTTP parser used by the
 * #findHeaderInResponse function.
 *
 * This callback will only be invoked if the requested header is not found in
 * the response. This callback is used to signal the parser to halt execution
 * if the requested header is not found.
 *
 * @param[in] pHttpParser The parser object to which this callback is registered.
 *
 * @return Returns #HTTP_PARSER_STOP_PARSING for the parser to halt further execution,
 * as all headers have been parsed in the response.
 */
static int findHeaderOnHeaderCompleteCallback( http_parser * pHttpParser );

/*-----------------------------------------------------------*/

static uint8_t convertInt32ToAscii( int32_t value,
                                    uint8_t * pBuffer,
                                    size_t bufferLength )
{
    /* As input value may be altered and MISRA C 2012 rule 17.8 prevents modification
     * of parameter, a local copy of the parameter is stored. */
    uint32_t absoluteValue = 0u;
    uint8_t numOfDigits = 0u;
    uint8_t index = 0u;
    uint8_t isNegative = 0u;

    assert( pBuffer != NULL );
    assert( bufferLength >= MAX_INT32_NO_OF_DECIMAL_DIGITS );
    ( void ) bufferLength;

    /* If the value is negative, write the '-' (minus) character to the buffer. */
    if( value < 0 )
    {
        isNegative = 1u;

        *pBuffer = ( uint8_t ) '-';

        /* Convert the value to its absolute representation. */
        absoluteValue = ( uint32_t ) ( value * -1 );
    }
    else
    {
        /* As the input integer value is positive, store is as it-is. */
        absoluteValue = ( uint32_t ) value;
    }

    /* Write the absolute integer value in reverse ASCII representation. */
    do
    {
        pBuffer[ isNegative + numOfDigits ] = ( uint8_t ) ( absoluteValue % 10u ) + ( uint8_t ) '0';
        numOfDigits++;
        absoluteValue /= 10u;
    } while( absoluteValue != 0u );

    /* Reverse the digits in the buffer to store the correct ASCII representation
     * of the value. */
    for( index = 0u; index < ( numOfDigits / 2u ); index++ )
    {
        pBuffer[ isNegative + index ] ^= pBuffer[ isNegative + numOfDigits - index - 1u ];
        pBuffer[ isNegative + numOfDigits - index - 1u ] ^= pBuffer[ isNegative + index ];
        pBuffer[ isNegative + index ] ^= pBuffer[ isNegative + numOfDigits - index - 1u ];
    }

    return( isNegative + numOfDigits );
}

/*-----------------------------------------------------------*/

static HTTPStatus_t addHeader( HTTPRequestHeaders_t * pRequestHeaders,
                               const uint8_t * pField,
                               size_t fieldLen,
                               const uint8_t * pValue,
                               size_t valueLen )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;
    uint8_t * pBufferCur = pRequestHeaders->pBuffer + pRequestHeaders->headersLen;
    size_t toAddLen = 0u;
    size_t backtrackHeaderLen = pRequestHeaders->headersLen;

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
        /* Write "<Field>: <Value> \r\n" to the headers buffer. */

        /* Copy the header name into the buffer. */
        memcpy( pBufferCur, pField, fieldLen );
        pBufferCur += fieldLen;

        /* Copy the field separator, ": ", into the buffer. */
        memcpy( pBufferCur,
                ( const uint8_t * ) HTTP_HEADER_FIELD_SEPARATOR,
                HTTP_HEADER_FIELD_SEPARATOR_LEN );
        pBufferCur += HTTP_HEADER_FIELD_SEPARATOR_LEN;

        /* Copy the header value into the buffer. */
        memcpy( pBufferCur, pValue, valueLen );
        pBufferCur += valueLen;

        /* Copy the header end indicator, "\r\n\r\n" into the buffer. */
        memcpy( pBufferCur,
                ( const uint8_t * ) HTTP_HEADER_END_INDICATOR,
                HTTP_HEADER_END_INDICATOR_LEN );

        /* Update the headers length value. */
        pRequestHeaders->headersLen = backtrackHeaderLen + toAddLen;
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

static HTTPStatus_t writeRequestLine( HTTPRequestHeaders_t * pRequestHeaders,
                                      const char * pMethod,
                                      size_t methodLen,
                                      const char * pPath,
                                      size_t pathLen )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;
    uint8_t * pBufferCur = pRequestHeaders->pBuffer;
    size_t toAddLen = methodLen +                 \
                      SPACE_CHARACTER_LEN +       \
                      SPACE_CHARACTER_LEN +       \
                      HTTP_PROTOCOL_VERSION_LEN + \
                      HTTP_HEADER_LINE_SEPARATOR_LEN;

    assert( pRequestHeaders != NULL );
    assert( pRequestHeaders->pBuffer != NULL );
    assert( pMethod != NULL );
    assert( methodLen != 0u );

    toAddLen += ( pPath == NULL || pathLen == 0 ) ? HTTP_EMPTY_PATH_LEN : pathLen;

    if( ( toAddLen + pRequestHeaders->headersLen ) > pRequestHeaders->bufferLen )
    {
        returnStatus = HTTP_INSUFFICIENT_MEMORY;
    }

    if( returnStatus == HTTP_SUCCESS )
    {
        /* Write "<METHOD> <PATH> HTTP/1.1\r\n" to start the HTTP header. */
        memcpy( pBufferCur, pMethod, methodLen );
        pBufferCur += methodLen;
        memcpy( pBufferCur, SPACE_CHARACTER, SPACE_CHARACTER_LEN );

        pBufferCur += SPACE_CHARACTER_LEN;

        /* Use "/" as default value if <PATH> is NULL. */
        if( ( pPath == NULL ) || ( pathLen == 0 ) )
        {
            memcpy( pBufferCur, HTTP_EMPTY_PATH, HTTP_EMPTY_PATH_LEN );
            pBufferCur += HTTP_EMPTY_PATH_LEN;
        }
        else
        {
            memcpy( pBufferCur, pPath, pathLen );
            pBufferCur += pathLen;
        }

        memcpy( pBufferCur, SPACE_CHARACTER, SPACE_CHARACTER_LEN );
        pBufferCur += SPACE_CHARACTER_LEN;

        memcpy( pBufferCur,
                HTTP_PROTOCOL_VERSION, HTTP_PROTOCOL_VERSION_LEN );
        pBufferCur += HTTP_PROTOCOL_VERSION_LEN;
        memcpy( pBufferCur,
                HTTP_HEADER_LINE_SEPARATOR, HTTP_HEADER_LINE_SEPARATOR_LEN );
        pRequestHeaders->headersLen = toAddLen;
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t HTTPClient_InitializeRequestHeaders( HTTPRequestHeaders_t * pRequestHeaders,
                                                  const HTTPRequestInfo_t * pRequestInfo )
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
    else if( ( pRequestInfo == NULL ) )
    {
        IotLogError( "Parameter check failed: pRequestInfo is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( ( pRequestInfo->method == NULL ) )
    {
        IotLogError( "Parameter check failed: pRequestInfo->method is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pRequestInfo->pHost == NULL )
    {
        IotLogError( "Parameter check failed: pRequestInfo->pHost is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pRequestInfo->methodLen == 0 )
    {
        IotLogError( "Parameter check failed: pRequestInfo->methodLen must be greater than 0." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pRequestInfo->hostLen == 0 )
    {
        IotLogError( "Parameter check failed: pRequestInfo->hostLen must be greater than 0." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else
    {
        /* Empty else MISRA 15.7 */
    }

    if( returnStatus == HTTP_SUCCESS )
    {
        /* Reset application-provided parameters. */
        pRequestHeaders->headersLen = 0;

        /* Write "<METHOD> <PATH> HTTP/1.1\r\n" to start the HTTP header. */
        returnStatus = writeRequestLine( pRequestHeaders,
                                         pRequestInfo->method,
                                         pRequestInfo->methodLen,
                                         pRequestInfo->pPath,
                                         pRequestInfo->pathLen );
    }

    if( returnStatus == HTTP_SUCCESS )
    {
        /* Write "User-Agent: <Value>". */
        returnStatus = addHeader( pRequestHeaders,
                                  ( const uint8_t * ) HTTP_USER_AGENT_FIELD,
                                  HTTP_USER_AGENT_FIELD_LEN,
                                  ( const uint8_t * ) HTTP_USER_AGENT_VALUE,
                                  HTTP_USER_AGENT_VALUE_LEN );
    }

    if( returnStatus == HTTP_SUCCESS )
    {
        /* Write "Host: <Value>". */
        returnStatus = addHeader( pRequestHeaders,
                                  ( const uint8_t * ) HTTP_HOST_FIELD,
                                  HTTP_HOST_FIELD_LEN,
                                  ( const uint8_t * ) pRequestInfo->pHost,
                                  pRequestInfo->hostLen );
    }

    if( returnStatus == HTTP_SUCCESS )
    {
        if( HTTP_REQUEST_KEEP_ALIVE_FLAG & pRequestInfo->flags )
        {
            /* Write "Connection: keep-alive". */
            returnStatus = addHeader( pRequestHeaders,
                                      ( const uint8_t * ) HTTP_CONNECTION_FIELD,
                                      HTTP_CONNECTION_FIELD_LEN,
                                      ( const uint8_t * ) HTTP_CONNECTION_KEEP_ALIVE_VALUE,
                                      HTTP_CONNECTION_KEEP_ALIVE_VALUE_LEN );
        }
        else
        {
            /* Write "Connection: close". */
            returnStatus = addHeader( pRequestHeaders,
                                      ( const uint8_t * ) HTTP_CONNECTION_FIELD,
                                      HTTP_CONNECTION_FIELD_LEN,
                                      ( const uint8_t * ) HTTP_CONNECTION_CLOSE_VALUE,
                                      HTTP_CONNECTION_CLOSE_VALUE_LEN );
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t HTTPClient_AddHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                   const uint8_t * pField,
                                   size_t fieldLen,
                                   const uint8_t * pValue,
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
        returnStatus = addHeader( pRequestHeaders,
                                  pField, fieldLen, pValue, valueLen );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t HTTPClient_AddRangeHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                        int32_t rangeStartOrlastNbytes,
                                        int32_t rangeEnd )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;
    uint8_t rangeValueBuffer[ MAX_RANGE_REQUEST_VALUE_LEN ] = { 0 };
    size_t rangeValueLength = 0u;

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
    else if( rangeEnd < HTTP_RANGE_REQUEST_END_OF_FILE )
    {
        IotLogErrorWithArgs( "Parameter check failed: rangeEnd is invalid: "
                             "rangeEnd should be >=-1: RangeEnd=%d", rangeEnd );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( ( rangeStartOrlastNbytes < 0 ) &&
             ( rangeEnd != HTTP_RANGE_REQUEST_END_OF_FILE ) )
    {
        IotLogErrorWithArgs( "Parameter check failed: Invalid range values: "
                             "rangeEnd should be -1 when rangeStart < 0: "
                             "RangeStart=%d, RangeEnd=%d",
                             rangeStartOrlastNbytes, rangeEnd );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( ( rangeEnd != HTTP_RANGE_REQUEST_END_OF_FILE ) &&
             ( rangeStartOrlastNbytes > rangeEnd ) )
    {
        IotLogErrorWithArgs( "Parameter check failed: Invalid range values: "
                             "rangeStart should be < rangeEnd when both are >= 0: "
                             "RangeStart=%d, RangeEnd=%d",
                             rangeStartOrlastNbytes, rangeEnd );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else
    {
        /* Generate the value data for the Range Request header.*/

        /* Write the range value prefix in the buffer. */
        memcpy( rangeValueBuffer,
                RANGE_REQUEST_HEADER_VALUE_PREFIX,
                RANGE_REQUEST_HEADER_VALUE_PREFIX_LEN );
        rangeValueLength += RANGE_REQUEST_HEADER_VALUE_PREFIX_LEN;

        /* Write the range start value in the buffer. */
        rangeValueLength += convertInt32ToAscii( rangeStartOrlastNbytes,
                                                 rangeValueBuffer + rangeValueLength,
                                                 sizeof( rangeValueBuffer ) - rangeValueLength );

        /* Add remaining value data depending on the range specification type. */

        /* Add rangeEnd value if request is for [rangeStart, rangeEnd] byte range */
        if( rangeEnd != HTTP_RANGE_REQUEST_END_OF_FILE )
        {
            /* Write the "-" character to the buffer.*/
            memcpy( rangeValueBuffer + rangeValueLength,
                    DASH_CHARACTER,
                    DASH_CHARACTER_LEN );
            rangeValueLength += DASH_CHARACTER_LEN;

            /* Write the rangeEnd value of the request range to the buffer .*/
            rangeValueLength += convertInt32ToAscii( rangeEnd,
                                                     rangeValueBuffer + rangeValueLength,
                                                     sizeof( rangeValueBuffer ) - rangeValueLength );
        }
        /* Case when request is for bytes in the range [rangeStart, EoF). */
        else if( rangeStartOrlastNbytes >= 0 )
        {
            /* Write the "-" character to the buffer.*/
            memcpy( rangeValueBuffer + rangeValueLength,
                    DASH_CHARACTER,
                    DASH_CHARACTER_LEN );
            rangeValueLength += DASH_CHARACTER_LEN;
        }
        else
        {
            /* Empty else MISRA 15.7 */
        }

        /* Add the Range Request header field and value to the buffer. */
        returnStatus = addHeader( pRequestHeaders,
                                  ( const uint8_t * ) RANGE_REQUEST_HEADER_FIELD,
                                  RANGE_REQUEST_HEADER_FIELD_LEN,
                                  rangeValueBuffer,
                                  rangeValueLength );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t sendHttpHeaders( const HTTPTransportInterface_t * pTransport,
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
                             " returned error: TransportStatus=%d",
                             transportStatus );
        returnStatus = HTTP_NETWORK_ERROR;
    }
    else if( ( size_t ) transportStatus != pRequestHeaders->headersLen )
    {
        IotLogErrorWithArgs( "Failed to send HTTP headers: Transport layer "
                             "did not send the required bytes: RequiredBytes=%d"
                             ", SentBytes=%d.",
                             pRequestHeaders->headersLen,
                             transportStatus );
        returnStatus = HTTP_NETWORK_ERROR;
    }
    else
    {
        IotLogDebugWithArgs( "Sent HTTP headers over the transport: BytesSent "
                             "=%d.",
                             transportStatus );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t sendHttpBody( const HTTPTransportInterface_t * pTransport,
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
                             " returned error: TransportStatus=%d",
                             transportStatus );
        returnStatus = HTTP_NETWORK_ERROR;
    }
    else if( ( size_t ) transportStatus != reqBodyBufLen )
    {
        IotLogErrorWithArgs( "Failed to send HTTP body: Transport send() "
                             "did not send the required bytes: RequiredBytes=%d"
                             ", Sent bytes=%d.",
                             reqBodyBufLen,
                             transportStatus );
        returnStatus = HTTP_NETWORK_ERROR;
    }
    else
    {
        IotLogDebugWithArgs( "Sent HTTP body over the transport: BytesSent=%d.",
                             transportStatus );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t receiveHttpResponse( const HTTPTransportInterface_t * pTransport,
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
                             "returned error: TransportStatus=%d.",
                             transportStatus );
        returnStatus = HTTP_NETWORK_ERROR;
    }
    else if( ( size_t ) transportStatus > bufferLen )
    {
        /* There is a bug in the transport recv if more bytes are reported
         * to have been read than the bytes asked for. */
        IotLogErrorWithArgs( "Failed to receive HTTP response: Transport recv() "
                             " read more bytes than requested: BytesRead=%d, "
                             "RequestedBytes=%d",
                             transportStatus,
                             bufferLen );
        returnStatus = HTTP_NETWORK_ERROR;
    }
    else if( transportStatus > 0 )
    {
        /* Some or all of the specified data was received. */
        *pBytesReceived = ( size_t ) ( transportStatus );
        IotLogDebugWithArgs( "Received data from the transport: BytesReceived=%d.",
                             transportStatus );
    }
    else
    {
        /* When a zero is returned from the transport recv it will not be
         * invoked again. */
        IotLogDebug( "Received zero bytes from trasnport recv(). Receiving "
                     "transport data is complete." );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t getFinalResponseStatus( HTTPParsingState_t parsingState,
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
                             "transport recv: totalReceived=%d",
                             totalReceived );
        returnStatus = HTTP_NO_RESPONSE;
    }
    else if( parsingState == HTTP_PARSING_INCOMPLETE )
    {
        if( totalReceived == responseBufferLen )
        {
            IotLogErrorWithArgs( "Cannot receive complete response from tansport"
                                 " interface: Response buffer has insufficient "
                                 "space: responseBufferLen=%d",
                                 responseBufferLen );
            returnStatus = HTTP_INSUFFICIENT_MEMORY;
        }
        else
        {
            IotLogErrorWithArgs( "Received partial response from transport ",
                                 "recv(): ResponseSize=%d, TotalBufferSize=%d",
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

static HTTPStatus_t receiveAndParseHttpResponse( const HTTPTransportInterface_t * pTransport,
                                                 HTTPResponse_t * pResponse )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;
    size_t totalReceived = 0u;
    size_t currentReceived = 0u;
    HTTPParsingContext_t parsingContext = { 0 };
    uint8_t shouldRecv = 0u;

    assert( pTransport != NULL );
    assert( pTransport->recv != NULL );
    assert( pResponse != NULL );

    /* Initialize the parsing context. */
    returnStatus = HTTPClient_InitializeParsingContext( &parsingContext,
                                                        pResponse->pHeaderParsingCallback );

    if( returnStatus == HTTP_SUCCESS )
    {
        shouldRecv = 1u;
    }

    while( shouldRecv == 1u )
    {
        /* Receive the HTTP response data into the pResponse->pBuffer. */
        returnStatus = receiveHttpResponse( pTransport,
                                            pResponse->pBuffer + totalReceived,
                                            pResponse->bufferLen - totalReceived,
                                            &currentReceived );

        if( returnStatus == HTTP_SUCCESS )
        {
            if( currentReceived > 0u )
            {
                totalReceived += currentReceived;
                /* Data is received into the buffer and must be parsed. */
                returnStatus = HTTPClient_ParseResponse( &parsingContext,
                                                         pResponse->pBuffer + totalReceived,
                                                         currentReceived );
            }
        }

        /* While there are no errors in the transport recv or parsing, we received
         * data over the transport, the response message is not finished, and
         * there is room in the response buffer. */
        shouldRecv = ( ( returnStatus == HTTP_SUCCESS ) &&
                       ( currentReceived > 0u ) &&
                       ( parsingContext.state != HTTP_PARSING_COMPLETE ) &&
                       ( totalReceived < pResponse->bufferLen ) ) ? 1u : 0u;
    }

    if( returnStatus == HTTP_SUCCESS )
    {
        /* For no network or parsing errors, the final status of the response
         * message is derived from the state of the parsing and how much data
         * is in the buffer. */
        returnStatus = getFinalResponseStatus( parsingContext.state,
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
    else if( ( pResponse != NULL ) && ( pResponse->pBuffer == NULL ) )
    {
        IotLogError( "Parameter check failed: pResponse->pBuffer is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else
    {
        /* Empty else for MISRA 15.7 compliance. */
    }

    /* Send the headers, which are at one location in memory. */
    if( returnStatus == HTTP_SUCCESS )
    {
        returnStatus = sendHttpHeaders( pTransport,
                                        pRequestHeaders );
    }

    /* Send the body, which is at another location in memory. */
    if( returnStatus == HTTP_SUCCESS )
    {
        if( pRequestBodyBuf != NULL )
        {
            returnStatus = sendHttpBody( pTransport,
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
            returnStatus = receiveAndParseHttpResponse( pTransport,
                                                        pResponse );
        }
        else
        {
            IotLogDebug( "Response ignored: pResponse is NULL." );
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

/* The coverity violation is for using a non-const type for the "pHttpParser" parser
 * instead of a const-type as the pointed to object is not modified by the function.
 * We suppress this violations this violation as this function follows the function
 * function signature of the "on_header_field" callback specified by the http-parser
 * library. */
/* coverity[misra_c_2012_rule_8_13_violation] */
static int findHeaderFieldParserCallback( http_parser * pHttpParser,
                                          const char * pFieldLoc,
                                          size_t fieldLen )
{
    findHeaderContext_t * pContext = ( findHeaderContext_t * ) pHttpParser->data;

    assert( pHttpParser != NULL );
    assert( pFieldLoc != NULL );
    assert( fieldLen > 0u );

    assert( pContext->pField != NULL );
    assert( pContext->fieldLen > 0u );

    /* The header found flags should not be set. */
    assert( pContext->fieldFound == 0u );
    assert( pContext->valueFound == 0u );

    /* Check whether the parsed header matches the header we are looking for. */
    if( ( fieldLen == pContext->fieldLen ) && ( memcmp( pContext->pField, pFieldLoc, fieldLen ) == 0 ) )
    {
        IotLogDebugWithArgs( "Found header field in response: "
                             "HeaderName=%.*s, HeaderLocation=0x%d",
                             fieldLen, pContext->pField );

        /* Set the flag to indicate that header has been found in response. */
        pContext->fieldFound = 1u;
    }
    else
    {
        /* Empty else for MISRA 15.7 compliance. */
    }

    return HTTP_PARSER_CONTINUE_PARSING;
}

/*-----------------------------------------------------------*/

/* The coverity violation is for using a non-const type for the "pHttpParser" parser
 * instead of a const-type as the pointed to object is not modified by the function.
 * We suppress this violations this violation as this function follows the function
 * function signature of the "on_header_value" callback specified by the http-parser
 * library. */
/* coverity[misra_c_2012_rule_8_13_violation] */
static int findHeaderValueParserCallback( http_parser * pHttpParser,
                                          const char * pVaLueLoc,
                                          size_t valueLen )
{
    findHeaderContext_t * pContext = ( findHeaderContext_t * ) pHttpParser->data;

    /* The coverity violation is for using "int" instead of a type that specifies size
     * and signedness information. We suppress this violation as this variable represents
     * the return value type of this callback function, whose return type is defined by
     * http-parser. */
    /* coverity[misra_c_2012_directive_4_6_violation] */
    int retCode = HTTP_PARSER_CONTINUE_PARSING;

    assert( pHttpParser != NULL );
    assert( pVaLueLoc != NULL );
    assert( valueLen > 0u );

    assert( pContext->pField != NULL );
    assert( pContext->fieldLen > 0u );
    assert( pContext->pValueLoc != NULL );
    assert( pContext->pValueLen != NULL );

    /* The header value found flag should not be set. */
    assert( pContext->valueFound == 0u );

    if( pContext->fieldFound == 1u )
    {
        IotLogDebugWithArgs( "Found header value in response: "
                             "RequestedField=%.*s, ValueLocation=0x%d",
                             pContext->fieldLen, pContext->pField, pVaLueLoc );

        /* Populate the output parameters with the location of the header value in the response buffer. */
        *pContext->pValueLoc = ( const uint8_t * ) pVaLueLoc;
        *pContext->pValueLen = valueLen;

        /* Set the header value found flag. */
        pContext->valueFound = 1u;

        /* As we have found the value associated with the header, we don't need
         * to parse the response any further. */
        retCode = HTTP_PARSER_STOP_PARSING;
    }
    else
    {
        /* Empty else for MISRA 15.7 compliance. */
    }

    return retCode;
}

/*-----------------------------------------------------------*/

/* The coverity violation is for using a non-const type for the "pHttpParser" parser
 * instead of a const-type as the pointed to object is not modified by the function.
 * We suppress this violations this violation as this function follows the function
 * function signature of the "on_headers_complete" callback specified by the http-parser
 * library. */
/* coverity[misra_c_2012_rule_8_13_violation] */
static int findHeaderOnHeaderCompleteCallback( http_parser * pHttpParser )
{
    /* Disable unused parameter warning. */
    ( void ) pHttpParser;

    assert( pHttpParser != NULL );

    /* If we have reached here, all headers in the response have been parsed but the requested
     * header has not been found in the response buffer. */
    IotLogDebugWithArgs( "Reached end of header parsing: Header not found in response: "
                         "RequestedHeader=%.*s",
                         ( ( findHeaderContext_t * ) pHttpParser->data )->fieldLen,
                         ( ( findHeaderContext_t * ) pHttpParser->data )->pField );

    /* No further parsing is required; thus, indicate the parser to stop parsing. */
    return HTTP_PARSER_STOP_PARSING;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t findHeaderInResponse( const uint8_t * pBuffer,
                                          size_t bufferLen,
                                          const uint8_t * pField,
                                          size_t fieldLen,
                                          const uint8_t ** pValueLoc,
                                          size_t * pValueLen )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;
    http_parser parser = { 0 };
    http_parser_settings parserSettings = { 0 };
    findHeaderContext_t context =
    {
        .pField     = pField,
        .fieldLen   = fieldLen,
        .pValueLoc  = pValueLoc,
        .pValueLen  = pValueLen,
        .fieldFound = 0u,
        .valueFound = 0u
    };
    size_t numOfBytesParsed = 0u;

    /* Disable unused variable warning. */
    ( void ) numOfBytesParsed;

    http_parser_init( &parser, HTTP_RESPONSE );

    /* Set the context for the parser. */
    parser.data = &context;

    /* The intention here to define callbacks just for searching the headers. We will
     * need to create a private context in httpParser->data that has the field and
     * value to update and pass back. */
    http_parser_settings_init( &parserSettings );
    parserSettings.on_header_field = findHeaderFieldParserCallback;
    parserSettings.on_header_value = findHeaderValueParserCallback;
    parserSettings.on_headers_complete = findHeaderOnHeaderCompleteCallback;

    /* Start parsing for the header! */
    numOfBytesParsed = http_parser_execute( &parser,
                                            &parserSettings,
                                            ( const char * ) pBuffer,
                                            bufferLen );

    IotLogDebugWithArgs( "Parsed response for header search: NumBytesParsed=%d",
                         numOfBytesParsed );

    if( context.fieldFound == 0u )
    {
        /* If header field is not found, then both the flags should be zero. */
        assert( context.valueFound == 0u );

        /* Header is not present in buffer. */
        IotLogWarnWithArgs( "Header not found in response buffer: "
                            "RequestedHeader=%.*s", fieldLen, pField );

        returnStatus = HTTP_HEADER_NOT_FOUND;
    }
    else if( context.valueFound == 0u )
    {
        /* The response buffer is invalid as only the header field was found
         * in the "<field>: <value>\r\n" format of an HTTP header. */
        IotLogErrorWithArgs( "Unable to find header value in response: "
                             "Response data is invalid: "
                             "RequestedHeader=%.*s, ParserError=%s",
                             fieldLen, pField,
                             http_errno_description( HTTP_PARSER_ERRNO( &( parser ) ) ) );
        returnStatus = HTTP_INVALID_RESPONSE;
    }
    else
    {
        /* Empty else (when assert and logging is disabled) for MISRA 15.7 compliance. */

        /* Header is found. */
        assert( ( context.fieldFound == 1u ) && ( context.valueFound == 1u ) );

        IotLogDebugWithArgs( "Found requested header in response: "
                             "HeaderName=%.*s, HeaderValue=%.*s",
                             fieldLen, pField,
                             *pValueLen, *pValueLoc );
    }

    /* If the header field-value pair is found in response, then the return value of "on_header_value"
     * callback (related to the header value) should cause the http_parser.http_errno to be "CB_header_value". */
    if( ( returnStatus == HTTP_SUCCESS ) &&
        ( ( parser.http_errno != HPE_CB_header_value ) ) )
    {
        IotLogErrorWithArgs( "Header found in response but http-parser returned error: ParserError=%s",
                             http_errno_description( HTTP_PARSER_ERRNO( &( parser ) ) ) );
        returnStatus = HTTP_INTERNAL_ERROR;
    }

    /* If header was not found, then the "on_header_complete" callback is expected to be called which should
     * cause the http_parser.http_errno to be "OK" */
    else if( ( returnStatus == HTTP_HEADER_NOT_FOUND ) &&
             ( ( parser.http_errno != HPE_OK ) ) )
    {
        IotLogErrorWithArgs( "Header not found in response: http-parser returned error: ParserError=%s",
                             http_errno_description( HTTP_PARSER_ERRNO( &( parser ) ) ) );
        returnStatus = HTTP_INVALID_RESPONSE;
    }
    else
    {
        /* Empty else for MISRA 15.7 compliance. */
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t HTTPClient_ReadHeader( const HTTPResponse_t * pResponse,
                                    const uint8_t * pHeaderName,
                                    size_t headerNameLen,
                                    const uint8_t ** pHeaderValueLoc,
                                    size_t * pHeaderValueLen )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    if( pResponse == NULL )
    {
        IotLogError( "Parameter check failed: pResponse is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pResponse->pBuffer == NULL )
    {
        IotLogError( "Parameter check failed: pResponse->pBuffer is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pResponse->bufferLen == 0u )
    {
        IotLogError( "Parameter check failed: pResponse->bufferLen is 0: "
                     "Buffer len should be > 0." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pHeaderName == NULL )
    {
        IotLogError( "Parameter check failed: Input header name is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( headerNameLen == 0u )
    {
        IotLogError( "Parameter check failed: Input header name length is 0: "
                     "headerNameLen should be > 0." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pHeaderValueLoc == NULL )
    {
        IotLogError( "Parameter check failed: Output parameter for header value location is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pHeaderValueLen == NULL )
    {
        IotLogError( "Parameter check failed: Output parameter for header value length is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else
    {
        /* Empty else for MISRA 15.7 compliance. */
    }

    if( returnStatus == HTTP_SUCCESS )
    {
        returnStatus = findHeaderInResponse( pResponse->pBuffer,
                                             pResponse->bufferLen,
                                             pHeaderName,
                                             headerNameLen,
                                             pHeaderValueLoc,
                                             pHeaderValueLen );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

const char * HTTPClient_strerror( HTTPStatus_t status )
{
    const char * str = NULL;

    switch( status )
    {
        case HTTP_SUCCESS:
            str = "HTTP_SUCCESS";
            break;

        case HTTP_INVALID_PARAMETER:
            str = "HTTP_INVALID_PARAMETER";
            break;

        case HTTP_NETWORK_ERROR:
            str = "HTTP_NETWORK_ERROR";
            break;

        case HTTP_PARTIAL_RESPONSE:
            str = "HTTP_PARTIAL_RESPONSE";
            break;

        case HTTP_NO_RESPONSE:
            str = "HTTP_NO_RESPONSE";
            break;

        case HTTP_INSUFFICIENT_MEMORY:
            str = "HTTP_INSUFFICIENT_MEMORY";
            break;

        case HTTP_INTERNAL_ERROR:
            str = "HTTP_INTERNAL_ERROR";
            break;

        case HTTP_SECURITY_ALERT_RESPONSE_HEADERS_SIZE_LIMIT_EXCEEDED:
            str = "HTTP_SECURITY_ALERT_RESPONSE_HEADERS_SIZE_LIMIT_EXCEEDED";
            break;

        case HTTP_SECURITY_ALERT_PARSER_INVALID_CHARACTER:
            str = "HTTP_SECURITY_ALERT_PARSER_INVALID_CHARACTER";
            break;

        case HTTP_SECURITY_ALERT_INVALID_CONTENT_LENGTH:
            str = "HTTP_SECURITY_ALERT_INVALID_CONTENT_LENGTH";
            break;

        case HTTP_HEADER_NOT_FOUND:
            str = "HTTP_HEADER_NOT_FOUND";
            break;

        case HTTP_INVALID_RESPONSE:
            str = "HTTP_INVALID_RESPONSE";
            break;

        case HTTP_NOT_SUPPORTED:
            str = "HTTP_NOT_SUPPORTED";
            break;

        default:
            IotLogWarnWithArgs( "Invalid status code received for string conversion: "
                                "StatusCode=%d", status );
            break;
    }

    return str;
}

/*-----------------------------------------------------------*/

#include <assert.h>
#include <string.h>

#include "http_client.h"
#include "private/http_client_internal.h"

/*-----------------------------------------------------------*/

/**
 * @brief Send HTTP bytes over the transport send interface.
 *
 * @param[in] pTransport Transport interface.
 * @param[in] pDataHTTP request data to send.
 * @param[in] dataLen HTTP request data length.
 *
 * @return #HTTP_SUCCESS if successful. If there was a network error or less
 * bytes than what were specified were sent, then #HTTP_NETWORK_ERROR is
 * returned.
 */
static HTTPStatus_t sendHttpData( const HTTPTransportInterface_t * pTransport,
                                  const uint8_t * pData,
                                  size_t dataLen );

/**
 * @brief Send the HTTP headers over the transport send interface.
 *
 * @param[in] pTransport Transport interface.
 * @param[in] pRequestHeaders Request headers to send, it includes the buffer
 * and length.
 * @param[in] reqBodyLen The length of the request body to be sent. This is
 * used to generated a Content-Length header.
 * @param[in] flags Application provided flags to #HTTPClient_Send.
 *
 * @return #HTTP_SUCCESS if successful. If there was a network error or less
 * bytes than what were specified were sent, then #HTTP_NETWORK_ERROR is
 * returned.
 */
static HTTPStatus_t sendHttpHeaders( const HTTPTransportInterface_t * pTransport,
                                     HTTPRequestHeaders_t * pRequestHeaders,
                                     size_t reqBodyLen,
                                     uint32_t flags );

/**
 * @brief Adds the Content-Length header field and value to the
 * @p pRequestHeaders.
 *
 * @param[in] pRequestHeaders Request header buffer information.
 * @param[in] contentLength The Content-Length header value to write.
 *
 * @return #HTTP_SUCCESS if successful. If there was insufficient memory in the
 * application buffer, then #HTTP_INSUFFICIENT_MEMORY is returned.
 */
static HTTPStatus_t addContentLengthHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                            size_t contentLength );

/**
 * @brief Send the HTTP body over the transport send interface.
 *
 * @param[in] pTransport Transport interface.
 * @param[in] pRequestBodyBuf Request body buffer.
 * @param[in] reqBodyBufLen Length of the request body buffer.
 *
 * @return #HTTP_SUCCESS if successful. If there was a network error or less
 * bytes than what was specified were sent, then #HTTP_NETWORK_ERROR is
 * returned.
 */
static HTTPStatus_t sendHttpBody( const HTTPTransportInterface_t * pTransport,
                                  const uint8_t * pRequestBodyBuf,
                                  size_t reqBodyBufLen );

/**
 * @brief Write header based on parameters. This method also adds a trailing
 * "\r\n". If a trailing "\r\n" already exists in the HTTP header, this method
 * backtracks in order to write over it and updates the length accordingly.
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
 * @brief Receive HTTP response from the transport receive interface.
 *
 * @param[in] pTransport Transport interface.
 * @param[in] pBuffer Response buffer.
 * @param[in] bufferLen Length of the response buffer.
 * @param[out] pBytesReceived Bytes received from the transport interface.
 *
 * @return Returns #HTTP_SUCCESS if successful. If there was a network error or
 * more bytes than what was specified were read, then #HTTP_NETWORK_ERROR is
 * returned.
 */
HTTPStatus_t receiveHttpData( const HTTPTransportInterface_t * pTransport,
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
 * @param[in] pRequestHeaders Request headers for the corresponding HTTP request.
 *
 * @return Returns #HTTP_SUCCESS if successful. Please see #receiveHttpData,
 * #parseHttpResponse, and #getFinalResponseStatus for other statuses returned.
 */
static HTTPStatus_t receiveAndParseHttpResponse( const HTTPTransportInterface_t * pTransport,
                                                 HTTPResponse_t * pResponse,
                                                 const HTTPRequestHeaders_t * pRequestHeaders );

/**
 * @brief Converts an integer value to its ASCII representation in the passed
 * buffer.
 *
 * @param[in] value The value to convert to ASCII.
 * @param[out] pBuffer The buffer to store the ASCII representation of the
 * integer.
 *
 * @return Returns the number of bytes written to @p pBuffer.
 */
static uint8_t convertInt32ToAscii( int32_t value,
                                    char * pBuffer,
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
 * @param[out] pValueLoc The location of the the header value found in pBuffer.
 * @param[out] pValueLen The length of pValue.
 *
 * @return One of the following:
 * - #HTTP_SUCCESS when header is found in the response.
 * - #HTTP_HEADER_NOT_FOUND if requested header is not found in response.
 * - #HTTP_INVALID_RESPONSE if passed response is invalid for parsing.
 * - #HTTP_PARSER_INTERNAL_ERROR for any parsing errors.
 */
static HTTPStatus_t findHeaderInResponse( const uint8_t * pBuffer,
                                          size_t bufferLen,
                                          const uint8_t * pField,
                                          size_t fieldLen,
                                          const uint8_t ** pValueLoc,
                                          size_t * pValueLen );

/**
 * @brief The "on_header_field" callback for the HTTP parser used by the
 * #findHeaderInResponse function. The callback checks whether the parser
 * header field matched the header being searched for, and sets a flag to
 * represent reception of the header accordingly.
 *
 * @param[in] pHttpParser Parsing object containing state and callback context.
 * @param[in] pFieldLoc The location of the parsed header field in the response
 * buffer.
 * @param[in] fieldLen The length of the header field.
 *
 * @return Returns #HTTP_PARSER_CONTINUE_PARSING to indicate continuation with
 * parsing.
 */
static int findHeaderFieldParserCallback( http_parser * pHttpParser,
                                          const char * pFieldLoc,
                                          size_t fieldLen );

/**
 * @brief The "on_header_value" callback for the HTTP parser used by the
 * #findHeaderInResponse function. The callback sets the user-provided output
 * parameters for header value if the requested header's field was found in the
 * @ref findHeaderFieldParserCallback function.
 *
 * @param[in] pHttpParser Parsing object containing state and callback context.
 * @param[in] pVaLueLoc The location of the parsed header value in the response
 * buffer.
 * @param[in] valueLen The length of the header value.
 *
 * @return Returns #HTTP_PARSER_STOP_PARSING, if the header field/value pair are
 * found, otherwise #HTTP_PARSING_CONTINUE_PARSING is returned.
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
 * @param[in] pHttpParser Parsing object containing state and callback context.
 *
 * @return Returns #HTTP_PARSER_STOP_PARSING for the parser to halt further
 * execution, as all headers have been parsed in the response.
 */
static int findHeaderOnHeaderCompleteCallback( http_parser * pHttpParser );


/**
 * @brief Initialize the parsing context for parsing a response fresh from the
 * server.
 *
 * @param[in] pParsingContext The parsing context to initialize.
 */
static void initializeParsingContextForFirstResponse( HTTPParsingContext_t * pParsingContext );

/**
 * @brief Parses the response buffer in @p pResponse.
 *
 * This function may be invoked multiple times for different parts of the the
 * HTTP response. The state of what was last parsed in the response is kept in
 * @p pParsingContext.
 *
 * @param[in,out] pParsingState The response parsing state.
 * @param[in,out] pResponse The response information to be updated.
 * @param[in] parseLen The next length to parse in pResponse->pBuffer.
 * @param[in] isHeaderResponse If the response is to a HEAD request this is set
 * to 1, otherwise this is set to 0.
 *
 * @return One of the following:
 * - #HTTP_SUCCESS
 * - #HTTP_INVALID_PARAMETER
 * - Please see #processHttpParserError for parsing errors returned.
 */
static HTTPStatus_t parseHttpResponse( HTTPParsingContext_t * pParsingContext,
                                       HTTPResponse_t * pResponse,
                                       size_t parseLen,
                                       uint8_t isHeadResponse );

/**
 * @brief Callback invoked during http_parser_execute() to indicate the start of
 * the HTTP response message.
 *
 * This callback is invoked when an "H" in the "HTTP/1.1" that starts a response
 * is found.
 *
 * @param[in] pHttpParser Parsing object containing state and callback context.
 *
 * @return #HTTP_PARSER_CONTINUE_PARSING to continue parsing.
 */
static int httpParserOnMessageBeginCallback( http_parser * pHttpParser );

/**
 * @brief Callback invoked during http_parser_execute() when the HTTP response
 * status-code and its associated reason-phrase are found.
 *
 * @param[in] pHttpParser Parsing object containing state and callback context.
 * @param[in] pLoc Location of the HTTP response reason-phrase string in the
 * response message buffer.
 * @param[in] length Length of the HTTP response status code string.
 *
 * @return #HTTP_PARSER_CONTINUE_PARSING to continue parsing.
 */
static int httpParserOnStatusCallback( http_parser * pHttpParser,
                                       const char * pLoc,
                                       size_t length );

/**
 * @brief Callback invoked during http_parser_execute() when an HTTP response
 * header field is found.
 *
 * If only part of the header field was found, then parsing of the next part of
 * the response message will invoke this callback in succession.
 *
 * @param[in] pHttpParser Parsing object containing state and callback context.
 * @param[in] pLoc Location of the header field string in the response
 * message buffer.
 * @param[in] length Length of the header field.
 *
 * @return #HTTP_PARSER_CONTINUE_PARSING to continue parsing.
 */
static int httpParserOnHeaderFieldCallback( http_parser * pHttpParser,
                                            const char * pLoc,
                                            size_t length );

/**
 * @brief Callback invoked during http_parser_execute() when an HTTP response
 * header value is found.
 *
 * This header value corresponds to the header field that was found in the
 * immediately preceeding httpParserOnHeaderFieldCallback().
 *
 * If only part of the header value was found, then parsing of the next part of
 * the response message will invoke this callback in succession.
 *
 * @param[in] pHttpParser Parsing object containing state and callback context.
 * @param[in] pLoc Location of the header value in the response message buffer.
 * @param[in] length Length of the header value.
 *
 * @return #HTTP_PARSER_CONTINUE_PARSING to continue parsing.
 */
static int httpParserOnHeaderValueCallback( http_parser * pHttpParser,
                                            const char * pLoc,
                                            size_t length );

/**
 * @brief Callback invoked during http_parser_execute() when the end of the
 * headers are found.
 *
 * The end of the headers is signaled in a HTTP response message by another
 * "\r\n" after the final header line.
 *
 * @param[in] pHttpParser Parsing object containing state and callback context.
 *
 * @return #HTTP_PARSER_CONTINUE_PARSING to continue parsing.
 * #HTTP_PARSER_STOP_PARSING is returned if the response is for a HEAD request.
 */
static int httpParserOnHeadersCompleteCallback( http_parser * pHttpParser );

/**
 * @brief Callback invoked during http_parser_execute() when the HTTP response
 * body is found.
 *
 * If only part of the response body was found, then parsing of the next part of
 * the response message will invoke this callback in succession.
 *
 * This callback will be also invoked in succession if the response body is of
 * type "Transfer-Encoding: chunked". This callback will be invoked after each
 * chunk header.
 *
 * The follow is an example of a Transfer-Encoding chunked response:
 *
 * HTTP/1.1 200 OK\r\n
 * Content-Type: text/plain\r\n
 * Transfer-Encoding: chunked\r\n
 * \r\n
 * d\r\n
 * Hello World! \r\n
 * 7\r\n
 * I am a \r\n
 * a\r\n
 * developer.\r\n
 * 0\r\n
 * \r\n
 *
 * The first invocation of this callback will contain @p pLoc = "Hello World!"
 * and @p length = 13.
 * The second invocation of this callback will contain @p pLoc = "I am a " and
 * @p length = 7.
 * The third invocation of this callback will contain @p pLoc = "developer." and
 * @p length = 10.
 *
 * @param[in] pHttpParser Parsing object containing state and callback context.
 * @param[in] pLoc - Pointer to the body string in the response message buffer.
 * @param[in] length - The length of the body found.
 *
 * @return Zero to continue parsing. All other return values will stop parsing
 * and http_parser_execute() will return with status HPE_CB_body.
 */
static int httpParserOnBodyCallback( http_parser * pHttpParser,
                                     const char * pLoc,
                                     size_t length );

/**
 * @brief Callback invoked during http_parser_execute() to indicate the the
 * completion of an HTTP response message.
 *
 * When there is no response body, the end of the response message is when the
 * headers end. This is indicated by another "\r\n" after the final header line.
 *
 * When there is response body, the end of the response message is when the
 * full "Content-Length" value is parsed following the end of the headers. If
 * there is no Content-Length header, then http_parser_execute() expects a
 * zero length-ed parsing data to indicate the end of the response.
 *
 * For a "Transfer-Encoding: chunked" type of response message, the complete
 * response message is signalled by a terminating chunk header with length zero.
 *
 * See https://github.com/nodejs/http-parser for more information.
 *
 * @param[in] pHttpParser Parsing object containing state and callback context.
 *
 * @return Zero to continue parsing. All other return values will stop parsing
 * and http_parser_execute() will return with status HPE_CB_message_complete.
 */
static int httpParserOnMessageCompleteCallback( http_parser * pHttpParser );

/**
 * @brief When a complete header is found the HTTP response header count
 * increases and the application is notified.
 *
 * This function is invoked only in callbacks that could follow
 * #httpParserOnHeaderValueCallback. These callbacks are
 * #httpParserOnHeaderFieldCallback and #httpParserOnHeadersCompleteCallback.
 * A header field and value is not is not known to be complete until 
 * #httpParserOnHeaderValueCallback is not called in succession.
 *
 * @param[in] pParsingContext Parsing state containing information to notify
 * the application of a complete header.
 */
static void processCompleteHeader( HTTPParsingContext_t * pParsingContext );

/**
 * @brief When parsing is complete an error could be indicated in
 * pHttpParser->http_errno. This function translates that error into a library
 * specific error code.
 *
 * @param[in] pHttpParser Third-party HTTP parsing context.
 *
 * @return One of the following:
 * - #HTTP_SUCCESS
 * - #HTTP_SECURITY_ALERT_RESPONSE_HEADERS_SIZE_LIMIT_EXCEEDED
 * - #HTTP_SECURITY_ALERT_EXTRANEOUS_RESPONSE_DATA
 * - #HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_CHUNK_HEADER
 * - #HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_PROTOCOL_VERSION
 * - #HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_STATUS_CODE
 * - #HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_CHARACTER
 * - #HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_CONTENT_LENGTH
 * - #HTTP_PARSER_INTERNAL_ERROR
 */
static HTTPStatus_t processHttpParserError( http_parser * pHttpParser );

/*-----------------------------------------------------------*/

static void processCompleteHeader( HTTPParsingContext_t * pParsingContext )
{
    HTTPResponse_t * pResponse = NULL;

    assert( pParsingContext != NULL );
    assert( pParsingContext->pResponse != NULL );

    pResponse = pParsingContext->pResponse;

    /* A header is complete when both the last header field and value have been
     * filled in. */
    if( ( pParsingContext->pLastHeaderField != NULL ) &&
        ( pParsingContext->pLastHeaderValue != NULL ) )
    {
        /* Increase the header count. */
        pResponse->headerCount++;

        LogDebug( ( "Response parsing: Found complete header: "
                    "HeaderField=%.*s, HeaderValue=%.*s",
                    pParsingContext->lastHeaderFieldLen,
                    pParsingContext->pLastHeaderField,
                    pParsingContext->lastHeaderValueLen,
                    pParsingContext->pLastHeaderValue ) );

        /* If the application registered a callback, then it must be notified. */
        if( pResponse->pHeaderParsingCallback != NULL )
        {
            pResponse->pHeaderParsingCallback->onHeaderCallback(
                pResponse->pHeaderParsingCallback->pContext,
                ( const uint8_t * ) pParsingContext->pLastHeaderField,
                pParsingContext->lastHeaderFieldLen,
                ( const uint8_t * ) pParsingContext->pLastHeaderValue,
                pParsingContext->lastHeaderValueLen,
                pResponse->statusCode );
        }

        /* Prepare the next header field and value for the first invocation of
         * httpParserOnHeaderFieldCallback() and
         * httpParserOnHeaderValueCallback(). */
        pParsingContext->pLastHeaderField = NULL;
        pParsingContext->lastHeaderFieldLen = 0u;
        pParsingContext->pLastHeaderValue = NULL;
        pParsingContext->lastHeaderValueLen = 0u;
    }
}

/*-----------------------------------------------------------*/

/* MISRA directive 4.6 violation is for using primitive type int, instead of
 * a typedef which denotes the signedness and size of the type. This violation
 * is suppressed because this callback follows the function signature for the
 * http_cb type in http-parser. */

/* MISRA directive 8.13 flags that pHttpParser should be a const parameter since
 * it does not change. This rule is suppressed because http-parser defines
 * their callback function signatures without the const. */
/* coverity[misra_c_2012_directive_4_6_violation] */
/* coverity[misra_c_2012_rule_8_13_violation] */
static int httpParserOnMessageBeginCallback( http_parser * pHttpParser )
{
    HTTPParsingContext_t * pParsingContext = NULL;
    HTTPResponse_t * pResponse = NULL;

    assert( pHttpParser != NULL );
    assert( pHttpParser->data != NULL );

    /* The MISRA rule 11.5 violation flags casting a void pointer to another
     * type. This rule is suppressed here because the http-parser library
     * requires that private context into callbacks must be set to a void
     * pointer variable. */
    /* coverity[misra_c_2012_rule_11_5_violation] */
    pParsingContext = ( HTTPParsingContext_t * ) ( pHttpParser->data );
    pResponse = pParsingContext->pResponse;

    assert( pResponse != NULL );

    /* Parsing has initiated. */
    pParsingContext->state = HTTP_PARSING_INCOMPLETE;

    LogDebug( ( "Response parsing: Found the start of the response message." ) );

    /* The MISRA directive 4.6 violation is for using primitive type int, instead of
     * a typedef which denotes the signedness and size of the type. This violation
     * is suppressed because http-parser requires this callback to return an integer. */
    /* coverity[misra_c_2012_directive_4_6_violation] */
    return HTTP_PARSER_CONTINUE_PARSING;
}

/*-----------------------------------------------------------*/

/* The MISRA directive 4.6 violation is for using primitive type int, instead of
 * a typedef which denotes the signedness and size of the type. This violation
 * is suppressed because this callback follows the function signature for the
 * http_data_cb type in http-parser. */

/* MISRA directive 8.13 flags that pHttpParser should be a const parameter since
 * it does not change. This rule is suppressed because http-parser defines
 * their callback function signatures without the const. */
/* coverity[misra_c_2012_directive_4_6_violation] */
/* coverity[misra_c_2012_rule_8_13_violation] */
static int httpParserOnStatusCallback( http_parser * pHttpParser,
                                       const char * pLoc,
                                       size_t length )
{
    HTTPParsingContext_t * pParsingContext = NULL;
    HTTPResponse_t * pResponse = NULL;

    assert( pHttpParser != NULL );
    assert( pHttpParser->data != NULL );
    assert( pLoc != NULL );

    /* The MISRA rule 11.5 violation flags casting a void pointer to another
     * type. This rule is suppressed here because the http-parser library
     * requires that private context into callbacks must be set to a void
     * pointer variable. */
    /* coverity[misra_c_2012_rule_11_5_violation] */
    pParsingContext = ( HTTPParsingContext_t * ) ( pHttpParser->data );
    pResponse = pParsingContext->pResponse;

    assert( pResponse != NULL );

    /* Set the location of what to parse next. */
    pParsingContext->pBufferCur = pLoc + length;

    /* Initialize the first header field and value to be passed to the user
     * callback. */
    pParsingContext->pLastHeaderField = NULL;
    pParsingContext->lastHeaderFieldLen = 0u;
    pParsingContext->pLastHeaderValue = NULL;
    pParsingContext->lastHeaderValueLen = 0u;

    /* httpParserOnStatusCallback() is reached because http_parser_execute() has
     * successfully read the HTTP response status code. */
    pResponse->statusCode = ( uint16_t ) ( pHttpParser->status_code );

    LogDebug( ( "Response parsing: Found the Reason-Phrase: "
                "StatusCode=%d, ReasonPhrase=%.*s",
                pResponse->statusCode,
                length,
                pLoc ) );

    /* The MISRA directive 4.6 violation is for using primitive type int, instead of
     * a typedef which denotes the signedness and size of the type. This violation
     * is suppressed because http-parser requires this callback to return an integer. */
    /* coverity[misra_c_2012_directive_4_6_violation] */
    return HTTP_PARSER_CONTINUE_PARSING;
}

/*-----------------------------------------------------------*/

/* The MISRA directive 4.6 violation is for using primitive type int, instead of
 * a typedef which denotes the signedness and size of the type. This violation
 * is suppressed because this callback follows the function signature for the
 * http_data_cb type in http-parser. */

/* MISRA directive 8.13 flags that pHttpParser should be a const parameter since
 * it does not change. This rule is suppressed because http-parser defines
 * their callback function signatures without the const. */
/* coverity[misra_c_2012_directive_4_6_violation] */
/* coverity[misra_c_2012_rule_8_13_violation] */
static int httpParserOnHeaderFieldCallback( http_parser * pHttpParser,
                                            const char * pLoc,
                                            size_t length )
{
    HTTPParsingContext_t * pParsingContext = NULL;
    HTTPResponse_t * pResponse = NULL;

    assert( pHttpParser != NULL );
    assert( pHttpParser->data != NULL );
    assert( pLoc != NULL );

    /* The MISRA rule 11.5 violation flags casting a void pointer to another
     * type. This rule is suppressed here because the http-parser library
     * requires that private context into callbacks must be set to a void
     * pointer variable. */
    /* coverity[misra_c_2012_rule_11_5_violation] */
    pParsingContext = ( HTTPParsingContext_t * ) ( pHttpParser->data );
    pResponse = pParsingContext->pResponse;

    assert( pResponse != NULL );

    /* If this is the first time httpParserOnHeaderFieldCallback() has been
     * invoked on a response, then the headers location in the response was set
     * to NULL in the preceding httpParseOnStatusFieldCallback(). */
    if( pResponse->pHeaders == NULL )
    {
        pResponse->pHeaders = ( const uint8_t * ) pLoc;
    }

    /* Set the location of what to parse next. */
    pParsingContext->pBufferCur = pLoc + length;

    /* The httpParserOnHeaderFieldCallback() always follows the
     * httpParserOnHeaderValueCallback() if there is another header field. When
     * httpParserOnHeaderValueCallback() is not called in succession, then a
     * complete header has been found. */
    processCompleteHeader( pParsingContext );

    /* If httpParserOnHeaderFieldCallback() is invoked in succession, then the
     * last time http_parser_execute() was called only part of the header field
     * was parsed. The indication of successive invocations is a non-NULL
     * pParsingContext->pLastHeaderField. */
    if( pParsingContext->pLastHeaderField == NULL )
    {
        pParsingContext->pLastHeaderField = pLoc;
        pParsingContext->lastHeaderFieldLen = length;
    }
    else
    {
        pParsingContext->lastHeaderFieldLen += length;
    }

    LogDebug( ( "Response parsing: Found a header field: "
                "HeaderField=%.*s",
                length,
                pLoc ) );

    /* The MISRA directive 4.6 violation is for using primitive type int, instead of
     * a typedef which denotes the signedness and size of the type. This violation
     * is suppressed because http-parser requires this callback to return an integer. */
    /* coverity[misra_c_2012_directive_4_6_violation] */
    return HTTP_PARSER_CONTINUE_PARSING;
}

/*-----------------------------------------------------------*/

/* The MISRA directive 4.6 violation is for using primitive type int, instead of
 * a typedef which denotes the signedness and size of the type. This violation
 * is suppressed because this callback follows the function signature for the
 * http_data_cb type in http-parser. */

/* MISRA directive 8.13 flags that pHttpParser should be a const parameter since
 * it does not change. This rule is suppressed because http-parser defines
 * their callback function signatures without the const. */
/* coverity[misra_c_2012_directive_4_6_violation] */
/* coverity[misra_c_2012_rule_8_13_violation] */
static int httpParserOnHeaderValueCallback( http_parser * pHttpParser,
                                            const char * pLoc,
                                            size_t length )
{
    HTTPParsingContext_t * pParsingContext = NULL;
    HTTPResponse_t * pResponse = NULL;

    assert( pHttpParser != NULL );
    assert( pHttpParser->data != NULL );
    assert( pLoc != NULL );

    /* The MISRA rule 11.5 violation flags casting a void pointer to another
     * type. This rule is suppressed here because the http-parser library
     * requires that private context into callbacks must be set to a void
     * pointer variable. */
    /* coverity[misra_c_2012_rule_11_5_violation] */
    pParsingContext = ( HTTPParsingContext_t * ) ( pHttpParser->data );
    pResponse = pParsingContext->pResponse;

    assert( pResponse != NULL );

    /* Set the location of what to parse next. */
    pParsingContext->pBufferCur = pLoc + length;

    /* If httpParserOnHeaderValueCallback() is invoked in succession, then the
     * last time http_parser_execute() was called only part of the header field
     * was parsed. The indication of successive invocations is a non-NULL
     * pParsingContext->pLastHeaderField. */
    if( pParsingContext->pLastHeaderValue == NULL )
    {
        pParsingContext->pLastHeaderValue = pLoc;
        pParsingContext->lastHeaderValueLen = length;
    }
    else
    {
        pParsingContext->lastHeaderValueLen += length;
    }

    /* Given that httpParserOnHeaderFieldCallback() is ALWAYS invoked before
     * httpParserOnHeaderValueCallback() is invoked, then the last header field
     * should never be NULL. This would indicate a bug in the http-parser
     * library. */
    assert( pParsingContext->pLastHeaderField != NULL );

    LogDebug( ( "Response parsing: Found a header value: "
                "HeaderValue=%.*s",
                length,
                pLoc ) );

    /* The MISRA directive 4.6 violation is for using primitive type int, instead of
     * a typedef which denotes the signedness and size of the type. This violation
     * is suppressed because http-parser requires this callback to return an integer. */
    /* coverity[misra_c_2012_directive_4_6_violation] */
    return HTTP_PARSER_CONTINUE_PARSING;
}

/*-----------------------------------------------------------*/

/* The MISRA directive 4.6 violation is for using primitive type int, instead of
 * a typedef which denotes the signedness and size of the type. This violation
 * is suppressed because this callback follows the function signature for the
 * http_data_cb type in http-parser. */

/* MISRA directive 8.13 flags that pHttpParser should be a const parameter since
 * it does not change. This rule is suppressed because http-parser defines
 * their callback function signatures without the const. */
/* coverity[misra_c_2012_directive_4_6_violation] */
/* coverity[misra_c_2012_rule_8_13_violation] */
static int httpParserOnHeadersCompleteCallback( http_parser * pHttpParser )
{
    /* The MISRA directive 4.6 violation is for using primitive type int,
     * instead of a typedef which denotes the signedness and size of the type.
     * This violation is suppressed because this variable stores the return
     * value of this callback, which follows the function signature for the
     * http_data_cb type in http-parser. */
    /* coverity[misra_c_2012_directive_4_6_violation] */
    int shouldContinueParse = HTTP_PARSER_CONTINUE_PARSING;
    HTTPParsingContext_t * pParsingContext = NULL;
    HTTPResponse_t * pResponse = NULL;

    assert( pHttpParser != NULL );
    assert( pHttpParser->data != NULL );

    /* The MISRA rule 11.5 violation flags casting a void pointer to another
     * type. This rule is suppressed here because the http-parser library
     * requires that private context into callbacks must be set to a void
     * pointer variable. */
    /* coverity[misra_c_2012_rule_11_5_violation] */
    pParsingContext = ( HTTPParsingContext_t * ) ( pHttpParser->data );
    pResponse = pParsingContext->pResponse;

    assert( pResponse != NULL );

    /* Set the location of what to parse next. */
    pParsingContext->pBufferCur += HTTP_HEADER_END_INDICATOR_LEN;

    /* If headers existed, then pResponse->pHeaders was set during the first
     * call to httpParserOnHeaderFieldCallback(). */
    if( pResponse->pHeaders != NULL )
    {
        /* The start of the headers ALWAYS come before the the end of the headers. */
        assert( ( const char * ) ( pResponse->pHeaders ) < pParsingContext->pBufferCur );

        /* MISRA Rule 10.8 flags the following line for casting from a signed
         * pointer difference to a size_t. This rule us suppressed because in
         * in the previous statement it is asserted that the pointer difference
         * will never be negative. */
        /* coverity[misra_c_2012_rule_10_8_violation] */
        pResponse->headersLen = ( size_t ) ( pParsingContext->pBufferCur - ( const char * ) ( pResponse->pHeaders ) );
    }
    else
    {
        pResponse->headersLen = 0u;
    }

    /* If the Content-Length header was found, then pHttpParser->content_length
     * will not be equal to the maximum 64 bit integer. */

    /* MISRA rule 14.3 flags the following line as invaraint. http-parser library
     * sets pHttpParser->content_length intentionally to the maximum 64 bit
     * integer to note a non-existent Content-Length header. */
    /* coverity[misra_c_2012_rule_14_3_violation] */
    if( pHttpParser->content_length != ( ( uint64_t ) -1 ) )
    {
        pResponse->contentLength = ( size_t ) ( pHttpParser->content_length );
    }
    else
    {
        pResponse->contentLength = 0u;
    }

    /* If the Connection: close header was found this flag will be set. */

    /* The MISRA directive 4.6 violation is for using primitive type unsigned
     * int, instead of a typedef which denotes the signedness and size of the
     * type. This violation is suppressed because http-parser defines these
     * variables as an unsigned int. */
    /* coverity[misra_c_2012_directive_4_6_violation] */
    if( ( pHttpParser->flags & ( unsigned int ) ( F_CONNECTION_CLOSE ) ) != 0u )
    {
        pResponse->flags |= HTTP_RESPONSE_CONNECTION_CLOSE_FLAG;
    }

    /* If the Connection: keep-alive header was found this flag will be set. */

    /* The MISRA directive 4.6 violation is for using primitive type unsigned
     * int, instead of a typedef which denotes the signedness and size of the
     * type. This violation is suppressed because http-parser defines these
     * variables as an unsigned int. */
    /* coverity[misra_c_2012_directive_4_6_violation] */
    if( ( pHttpParser->flags & ( unsigned int ) ( F_CONNECTION_KEEP_ALIVE ) ) != 0u )
    {
        pResponse->flags |= HTTP_RESPONSE_CONNECTION_KEEP_ALIVE_FLAG;
    }

    /* http_parser_execute() requires that callback implementations must
     * indicate that parsing stops on headers complete, if response is to a HEAD
     * request. A HEAD response will contain Content-Length, but no body. If
     * the parser is not stopped here, then it will try to keep parsing past the
     * end of the headers up to the Content-Length found. */
    if( pParsingContext->isHeadResponse == 1u )
    {
        /* The MISRA directive 4.6 violation is for using primitive type int, instead of
         * a typedef which denotes the signedness and size of the type. This violation
         * is suppressed because http-parser requires this callback to return an integer. */
        /* coverity[misra_c_2012_directive_4_6_violation] */
        shouldContinueParse = HTTP_PARSER_STOP_PARSING;
    }

    /* If headers are present in the response, then
     * httpParserOnHeadersCompleteCallback() always follows
     * the httpParserOnHeaderValueCallback(). When
     * httpParserOnHeaderValueCallback() is not called in succession, then a
     * complete header has been found. */
    processCompleteHeader( pParsingContext );

    LogDebug( ( "Response parsing: Found the end of the headers." ) );

    return shouldContinueParse;
}

/*-----------------------------------------------------------*/

/* The MISRA directive 4.6 violation is for using primitive type int, instead of
 * a typedef which denotes the signedness and size of the type. This violation
 * is suppressed because this callback follows the function signature for the
 * http_data_cb type in http-parser. */

/* MISRA directive 8.13 flags that pHttpParser should be a const parameter since
 * it does not change. This rule is suppressed because http-parser defines
 * their callback function signatures without the const. */
/* coverity[misra_c_2012_directive_4_6_violation] */
/* coverity[misra_c_2012_rule_8_13_violation] */
static int httpParserOnBodyCallback( http_parser * pHttpParser,
                                     const char * pLoc,
                                     size_t length )
{
    /* The MISRA directive 4.6 violation is for using primitive type int,
     * instead of a typedef which denotes the signedness and size of the type.
     * This violation is suppressed because this variable stores the return
     * value of this callback, which follows the function signature for the
     * http_data_cb type in http-parser. */
    /* coverity[misra_c_2012_directive_4_6_violation] */
    int shouldContinueParse = HTTP_PARSER_CONTINUE_PARSING;
    HTTPParsingContext_t * pParsingContext = NULL;
    HTTPResponse_t * pResponse = NULL;
    uint8_t * pNextWriteLoc = NULL;

    assert( pHttpParser != NULL );
    assert( pHttpParser->data != NULL );
    assert( pLoc != NULL );

    /* The MISRA rule 11.5 violation flags casting a void pointer to another
     * type. This rule is suppressed here because the http-parser library
     * requires that private context into callbacks must be set to a void
     * pointer variable. */
    /* coverity[misra_c_2012_rule_11_5_violation] */
    pParsingContext = ( HTTPParsingContext_t * ) ( pHttpParser->data );
    pResponse = pParsingContext->pResponse;

    assert( pResponse != NULL );
    assert( pResponse->pBuffer != NULL );
    assert( pLoc > ( const char * ) ( pResponse->pBuffer ) );
    assert( pLoc < ( const char * ) ( pResponse->pBuffer + pResponse->bufferLen ) );

    /* If this is the first time httpParserOnBodyCallback() has been invoked,
     * then the start of the response body is NULL. */
    if( pResponse->pBody == NULL )
    {
        pResponse->pBody = ( const uint8_t * ) ( pParsingContext->pBufferCur );
        pResponse->bodyLen = 0u;
    }

    /* The next location to write. */

    /* MISRA Rule 11.8 flags casting away the const qualifier in the pointer
     * type. This rule is suppressed because when the body is of transfer
     * encoding chunked, the body must be copied over the chunk headers that
     * preceed it. This is done to have a contigous response body. This does
     * affect future parsing as the changed segment will always be before the
     * next place to parse. */
    /* coverity[misra_c_2012_rule_11_8_violation] */
    pNextWriteLoc = ( uint8_t * ) ( pResponse->pBody + pResponse->bodyLen );

    /* If the response is of type Transfer-Encoding: chunked, then actual body
     * will follow the the chunked header. This body data is in a later location
     * and must be moved up in the buffer. When pLoc is greater than the current
     * end of the body, that signals the parser found a chunk header. */

    /* MISRA rule 18.3 glags the following as pLoc not pointing to the same
     * object as pNextWriteLoc. This rule is suppressed because http-parser will
     * always return a pLoc within the response buffer limit. */
    /* coverity[misra_c_2012_rule_18_3_violation] */
    if( pLoc > ( const char * ) pNextWriteLoc )
    {
        ( void ) memcpy( pNextWriteLoc, ( const uint8_t * ) pLoc, length );
    }

    /* Increase the length of the body found. */
    pResponse->bodyLen += length;

    /* Set the next location of parsing. */
    pParsingContext->pBufferCur = pLoc + length;

    LogDebug( ( "Response parsing: Found the response body. "
                "BodyLength=%d",
                length,
                pLoc ) );

    return shouldContinueParse;
}

/*-----------------------------------------------------------*/

/* The MISRA directive 4.6 violation is for using primitive type int, instead of
 * a typedef which denotes the signedness and size of the type. This violation
 * is suppressed because this callback follows the function signature for the
 * http_cb type in http-parser. */

/* MISRA directive 8.13 flags that pHttpParser should be a const parameter since
 * it does not change. This rule is suppressed because http-parser defines
 * their callback function signatures without the const. */
/* coverity[misra_c_2012_directive_4_6_violation] */
/* coverity[misra_c_2012_rule_8_13_violation] */
static int httpParserOnMessageCompleteCallback( http_parser * pHttpParser )
{
    HTTPParsingContext_t * pParsingContext = NULL;

    assert( pHttpParser != NULL );
    assert( pHttpParser->data != NULL );

    /* The MISRA rule 11.5 violation flags casting a void pointer to another
     * type. This rule is suppressed here because the http-parser library
     * requires that private context into callbacks must be set to a void
     * pointer variable. */
    /* coverity[misra_c_2012_rule_11_5_violation] */
    pParsingContext = ( HTTPParsingContext_t * ) ( pHttpParser->data );

    /* The response message is complete. */
    pParsingContext->state = HTTP_PARSING_COMPLETE;

    LogDebug( ( "Response parsing: Response message complete." ) );

    return HTTP_PARSER_CONTINUE_PARSING;
}

/*-----------------------------------------------------------*/

static void initializeParsingContextForFirstResponse( HTTPParsingContext_t * pParsingContext )
{
    assert( pParsingContext != NULL );

    /* Initialize the third-party HTTP parser to parse responses. */
    http_parser_init( &( pParsingContext->httpParser ), HTTP_RESPONSE );

    http_parser_set_max_header_size( HTTP_MAX_RESPONSE_HEADERS_SIZE_BYTES );

    /* No response has been parsed yet. */
    pParsingContext->state = HTTP_PARSING_NONE;

    /* No response to update is associated with this parsing context yet. */
    pParsingContext->pResponse = NULL;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t processHttpParserError( http_parser * pHttpParser )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    assert( pHttpParser != NULL );

    /* MISRA rule 10.5 notes casting an unsigned integer to an enum type. This
     * violation is suppressed because the http-parser library directly sets
     * and maps http_parser.http_errno to the enum http_errno. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    switch( ( enum http_errno ) ( pHttpParser->http_errno ) )
    {
        case HPE_OK:
            /* There were no errors. */
            break;

        case HPE_INVALID_EOF_STATE:

            /* In this case the parser was passed a length of zero, which indicates
             * an EOF from the server, in the middle of parsing the response.
             * This case is already handled by checking HTTPParsingContext_t.state. */
            break;

        case HPE_HEADER_OVERFLOW:
            LogError( ( "Response parsing error: Header byte limit "
                        "exceeded: HeaderByteLimit=%d.",
                        HTTP_MAX_RESPONSE_HEADERS_SIZE_BYTES ) );
            returnStatus = HTTP_SECURITY_ALERT_RESPONSE_HEADERS_SIZE_LIMIT_EXCEEDED;
            break;

        case HPE_CLOSED_CONNECTION:
            LogError( ( "Response parsing error: Data received past complete "
                        "response with \"Connection: close\" header present." ) );
            returnStatus = HTTP_SECURITY_ALERT_EXTRANEOUS_RESPONSE_DATA;
            break;

        case HPE_INVALID_CHUNK_SIZE:

            /* http_parser_execute() does not give feedback on the exact failing
             * character and location. */
            LogError( ( "Response parsing error: Invalid character found in "
                        "chunk header." ) );
            returnStatus = HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_CHUNK_HEADER;
            break;

        case HPE_INVALID_VERSION:

            /* http_parser_execute() does not give feedback on the exact failing
             * character and location. */
            LogError( ( "Response parsing error: Invalid character found in "
                        "HTTP protocol version." ) );
            returnStatus = HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_PROTOCOL_VERSION;
            break;

        case HPE_INVALID_STATUS:

            /* There could be an invalid character or the status code number
             * could be out of range. This feedback is not given back by the
             * http-parser library. */
            LogError( ( "Response parsing error: Invalid Status code." ) );
            returnStatus = HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_STATUS_CODE;
            break;

        case HPE_STRICT:
        case HPE_INVALID_CONSTANT:
            LogError( ( "Response parsing error: Invalid character found in "
                        "Status-Line or header delimitters." ) );
            returnStatus = HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_CHARACTER;
            break;

        case HPE_LF_EXPECTED:
            LogError( ( "Response parsing error: Expected line-feed in header "
                        "not found." ) );
            returnStatus = HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_CHARACTER;
            break;

        case HPE_INVALID_HEADER_TOKEN:

            /* http_parser_execute() does not give feedback on the exact failing
             * character and location. */
            LogError( ( "Response parsing error: Invalid character found in "
                        "headers." ) );
            returnStatus = HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_CHARACTER;
            break;

        case HPE_INVALID_CONTENT_LENGTH:

            /* http_parser_execute() does not give feedback on the exact failing
             * character and location. */
            LogError( ( "Response parsing error: Invalid character found in "
                        "content-length headers." ) );
            returnStatus = HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_CONTENT_LENGTH;
            break;

        case HPE_UNEXPECTED_CONTENT_LENGTH:
            LogError( ( "Response parsing error: A Content-Length header was "
                        "found when it shouldn't have been." ) );
            returnStatus = HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_CONTENT_LENGTH;
            break;

        /* All other error cases cannot be triggered and indicate an error in the
         * third-party parsing library if found. */
        default:
            LogError( ( "Error in third-party http-parser library." ) );
            returnStatus = HTTP_PARSER_INTERNAL_ERROR;
            break;
    }

    /* Errors with CB_ prepending are manual returns of non-zero in the
     * response parsing callbacked. */

    /* MISRA rule 10.5 notes casting an unsigned integer to an enum type. This
     * violation is suppressed because the http-parser library directly sets
     * and maps http_parser.http_errno to the enum http_errno. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    LogDebug( ( "http-parser errno description: %s",
                http_errno_description( HTTP_PARSER_ERRNO( pHttpParser ) ) ) );

    return returnStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t parseHttpResponse( HTTPParsingContext_t * pParsingContext,
                                HTTPResponse_t * pResponse,
                                size_t parseLen,
                                uint8_t isHeadResponse )
{
    HTTPStatus_t returnStatus;
    http_parser_settings parserSettings = { 0 };
    size_t bytesParsed = 0u;

    assert( pParsingContext != NULL );
    assert( pResponse != NULL );
    assert( isHeadResponse <= 1 );

    /* If this is the first time this parsing context is used, then set the
     * response input. */
    if( pParsingContext->pResponse == NULL )
    {
        pParsingContext->pResponse = pResponse;
        pParsingContext->pBufferCur = ( const char * ) pResponse->pBuffer;
        /* Set if this response is for a HEAD request. */
        pParsingContext->isHeadResponse = isHeadResponse;

        /* Initialize the status-code returned in the response. */
        pResponse->statusCode = 0u;
        /* Initialize the start of the response body and length. */
        pResponse->pBody = NULL;
        pResponse->bodyLen = 0u;

        /* Initialize the start of the headers, its length, and the count for
         * the parsing that follows the status. */
        pResponse->pHeaders = NULL;
        pResponse->headersLen = 0u;
        pResponse->headerCount = 0u;
        /* Initialize the response flags. */
        pResponse->flags = 0u;
    }
    else
    {
        /* This function is currently private to the HTTP Client library. It is
         * therefore a development bug to have this function invoked in
         * succession without the same response. */
        assert( pParsingContext->pResponse == pResponse );
    }

    /* Initialize the callbacks that http_parser_execute will invoke. */
    http_parser_settings_init( &parserSettings );
    parserSettings.on_message_begin = httpParserOnMessageBeginCallback;
    parserSettings.on_status = httpParserOnStatusCallback;
    parserSettings.on_header_field = httpParserOnHeaderFieldCallback;
    parserSettings.on_header_value = httpParserOnHeaderValueCallback;
    parserSettings.on_headers_complete = httpParserOnHeadersCompleteCallback;
    parserSettings.on_body = httpParserOnBodyCallback;
    parserSettings.on_message_complete = httpParserOnMessageCompleteCallback;

    /* Setting this allows the parsing context and response to be carried to
     * each of the callbacks that http_parser_execute() will invoke. */
    pParsingContext->httpParser.data = pParsingContext;

    /* This will begin the parsing. Each of the callbacks set in
     * parserSettings will be invoked as parts of the HTTP response are
     * reached. */
    bytesParsed = http_parser_execute( &( pParsingContext->httpParser ),
                                       &parserSettings,
                                       pParsingContext->pBufferCur,
                                       parseLen );

    LogDebug( ( "Parsed HTTP Response buffer: BytesParsed=%d, ",
                "ExpectedBytesParsed=%d",
                bytesParsed,
                parseLen ) );

    returnStatus = processHttpParserError( &( pParsingContext->httpParser ) );

    return returnStatus;
}

/*-----------------------------------------------------------*/

static uint8_t convertInt32ToAscii( int32_t value,
                                    char * pBuffer,
                                    size_t bufferLength )
{
    /* As input value may be altered and MISRA C 2012 rule 17.8 prevents
     * modification of parameter, a local copy of the parameter is stored.
     * absoluteValue stores the positive version of the input value. Its type
     * remains the same type as the input value to avoid unnecessary casting on
     * a privately used variable. This variable's size will always be less
     * than INT32_MAX. */
    int32_t absoluteValue = value;
    uint8_t numOfDigits = 0u;
    uint8_t index = 0u;
    uint8_t isNegative = 0u;
    char temp = '\0';

    assert( pBuffer != NULL );
    assert( bufferLength >= MAX_INT32_NO_OF_DECIMAL_DIGITS );
    ( void ) bufferLength;

    /* If the value is negative, write the '-' (minus) character to the buffer. */
    if( value < 0 )
    {
        isNegative = 1u;

        *pBuffer = '-';

        /* Convert the value to its absolute representation. */
        absoluteValue = value * -1;
    }

    /* Write the absolute integer value in reverse ASCII representation. */
    do
    {
        pBuffer[ isNegative + numOfDigits ] = ( char ) ( ( absoluteValue % 10 ) + '0' );
        numOfDigits++;
        absoluteValue /= 10;
    } while( absoluteValue != 0 );

    /* Reverse the digits in the buffer to store the correct ASCII representation
     * of the value. */
    for( index = 0u; index < ( numOfDigits / 2u ); index++ )
    {
        temp = pBuffer[ isNegative + index ];
        pBuffer[ isNegative + index ] = pBuffer[ isNegative + numOfDigits - index - 1u ];
        pBuffer[ isNegative + numOfDigits - index - 1u ] = temp;
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

    /* If we have enough room for the new header line, then write it to the
     * header buffer. */
    if( ( backtrackHeaderLen + toAddLen ) <= pRequestHeaders->bufferLen )
    {
        /* Write "<Field>: <Value> \r\n" to the headers buffer. */

        /* Copy the header name into the buffer. */
        ( void ) memcpy( pBufferCur, pField, fieldLen );
        pBufferCur += fieldLen;

        /* Copy the field separator, ": ", into the buffer. */

        /* MISRA rule 21.15 flags the memcpy of two different types, const uint8_t*
         * and const char*. These types are the same size, so this comparision is
         * acceptable. */
        /* coverity[misra_c_2012_rule_21_15_violation] */
        ( void ) memcpy( pBufferCur,
                         HTTP_HEADER_FIELD_SEPARATOR,
                         HTTP_HEADER_FIELD_SEPARATOR_LEN );
        pBufferCur += HTTP_HEADER_FIELD_SEPARATOR_LEN;

        /* Copy the header value into the buffer. */
        ( void ) memcpy( pBufferCur, pValue, valueLen );
        pBufferCur += valueLen;

        /* Copy the header end indicator, "\r\n\r\n" into the buffer. */

        /* MISRA rule 21.15 flags the memcpy of two different types, const uint8_t*
         * and const char*. These types are the same size, so this comparision is
         * acceptable. */
        /* coverity[misra_c_2012_rule_21_15_violation] */
        ( void ) memcpy( pBufferCur,
                         HTTP_HEADER_END_INDICATOR,
                         HTTP_HEADER_END_INDICATOR_LEN );

        /* Update the headers length value. */
        pRequestHeaders->headersLen = backtrackHeaderLen + toAddLen;
    }
    else
    {
        LogError( ( "Unable to add header in buffer: "
                    "Buffer has insufficient memory: "
                    "RequiredBytes=%lu, RemainingBufferSize=%lu",
                    ( unsigned long ) toAddLen,
                    ( unsigned long ) ( pRequestHeaders->bufferLen - pRequestHeaders->headersLen ) ) );
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

    toAddLen += ( ( pPath == NULL ) || ( pathLen == 0u ) ) ? HTTP_EMPTY_PATH_LEN : pathLen;

    if( ( toAddLen + pRequestHeaders->headersLen ) > pRequestHeaders->bufferLen )
    {
        returnStatus = HTTP_INSUFFICIENT_MEMORY;
    }

    if( returnStatus == HTTP_SUCCESS )
    {
        /* Write "<METHOD> <PATH> HTTP/1.1\r\n" to start the HTTP header. */

        /* MISRA rule 21.15 flags the memcpy of two different types, const uint8_t*
         * and const char*. These types are the same size, so this comparision is
         * acceptable. */
        /* coverity[misra_c_2012_rule_21_15_violation] */
        ( void ) memcpy( pBufferCur, pMethod, methodLen );
        pBufferCur += methodLen;

        /* MISRA rule 21.15 flags the memcpy of two different types, const uint8_t*
         * and const char*. These types are the same size, so this comparision is
         * acceptable. */
        /* coverity[misra_c_2012_rule_21_15_violation] */
        ( void ) memcpy( pBufferCur, SPACE_CHARACTER, SPACE_CHARACTER_LEN );

        pBufferCur += SPACE_CHARACTER_LEN;

        /* Use "/" as default value if <PATH> is NULL. */
        if( ( pPath == NULL ) || ( pathLen == 0u ) )
        {
            /* MISRA rule 21.15 flags the memcpy of two different types, const uint8_t*
             * and const char*. These types are the same size, so this comparision is
             * acceptable. */
            /* coverity[misra_c_2012_rule_21_15_violation] */
            ( void ) memcpy( pBufferCur,
                             HTTP_EMPTY_PATH,
                             HTTP_EMPTY_PATH_LEN );
            pBufferCur += HTTP_EMPTY_PATH_LEN;
        }
        else
        {
            /* MISRA rule 21.15 flags the memcpy of two different types, const uint8_t*
             * and const char*. These types are the same size, so this comparision is
             * acceptable. */
            /* coverity[misra_c_2012_rule_21_15_violation] */
            ( void ) memcpy( pBufferCur, pPath, pathLen );
            pBufferCur += pathLen;
        }

        /* MISRA rule 21.15 flags the memcpy of two different types, const uint8_t*
         * and const char*. These types are the same size, so this comparision is
         * acceptable. */
        /* coverity[misra_c_2012_rule_21_15_violation] */
        ( void ) memcpy( pBufferCur,
                         SPACE_CHARACTER,
                         SPACE_CHARACTER_LEN );
        pBufferCur += SPACE_CHARACTER_LEN;

        /* MISRA rule 21.15 flags the memcpy of two different types, const uint8_t*
         * and const char*. These types are the same size, so this comparision is
         * acceptable. */
        /* coverity[misra_c_2012_rule_21_15_violation] */
        ( void ) memcpy( pBufferCur,
                         HTTP_PROTOCOL_VERSION,
                         HTTP_PROTOCOL_VERSION_LEN );
        pBufferCur += HTTP_PROTOCOL_VERSION_LEN;

        /* MISRA rule 21.15 flags the memcpy of two different types, const uint8_t*
         * and const char*. These types are the same size, so this comparision is
         * acceptable. */
        /* coverity[misra_c_2012_rule_21_15_violation] */
        ( void ) memcpy( pBufferCur,
                         HTTP_HEADER_LINE_SEPARATOR,
                         HTTP_HEADER_LINE_SEPARATOR_LEN );
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
        LogError( ( "Parameter check failed: pRequestHeaders is NULL." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pRequestHeaders->pBuffer == NULL )
    {
        LogError( ( "Parameter check failed: pRequestHeaders->pBuffer is NULL." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( ( pRequestInfo == NULL ) )
    {
        LogError( ( "Parameter check failed: pRequestInfo is NULL." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( ( pRequestInfo->method == NULL ) )
    {
        LogError( ( "Parameter check failed: pRequestInfo->method is NULL." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pRequestInfo->pHost == NULL )
    {
        LogError( ( "Parameter check failed: pRequestInfo->pHost is NULL." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pRequestInfo->methodLen == 0u )
    {
        LogError( ( "Parameter check failed: pRequestInfo->methodLen must be greater than 0." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pRequestInfo->hostLen == 0u )
    {
        LogError( ( "Parameter check failed: pRequestInfo->hostLen must be greater than 0." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else
    {
        /* Empty else MISRA 15.7 */
    }

    if( returnStatus == HTTP_SUCCESS )
    {
        /* Reset application-provided parameters. */
        pRequestHeaders->headersLen = 0u;

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
        if( ( HTTP_REQUEST_KEEP_ALIVE_FLAG & pRequestInfo->flags ) != 0u )
        {
            /* Write "Connection: keep-alive". */
            returnStatus = addHeader( pRequestHeaders,
                                      ( const uint8_t * ) HTTP_CONNECTION_FIELD,
                                      HTTP_CONNECTION_FIELD_LEN,
                                      ( const uint8_t * ) HTTP_CONNECTION_KEEP_ALIVE_VALUE,
                                      HTTP_CONNECTION_KEEP_ALIVE_VALUE_LEN );
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
        LogError( ( "Parameter check failed: pRequestHeaders is NULL." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pRequestHeaders->pBuffer == NULL )
    {
        LogError( ( "Parameter check failed: pRequestHeaders->pBuffer is NULL." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( ( pField == NULL ) )
    {
        LogError( ( "Parameter check failed: pField is NULL." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( ( pValue == NULL ) )
    {
        LogError( ( "Parameter check failed: pValue is NULL." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( fieldLen == 0u )
    {
        LogError( ( "Parameter check failed: fieldLen must be greater than 0." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( valueLen == 0u )
    {
        LogError( ( "Parameter check failed: valueLen must be greater than 0." ) );
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

    /* This buffer uses a char type instead of the general purpose uint8_t because
    * the range value expected to be written is within the ASCII character set. */
    char rangeValueBuffer[ HTTP_MAX_RANGE_REQUEST_VALUE_LEN ] = { '\0' };
    size_t rangeValueLength = 0u;

    if( pRequestHeaders == NULL )
    {
        LogError( ( "Parameter check failed: pRequestHeaders is NULL." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pRequestHeaders->pBuffer == NULL )
    {
        LogError( ( "Parameter check failed: pRequestHeaders->pBuffer is NULL." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( rangeEnd < HTTP_RANGE_REQUEST_END_OF_FILE )
    {
        LogError( ( "Parameter check failed: rangeEnd is invalid: "
                    "rangeEnd should be >=-1: RangeEnd=%d", rangeEnd ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( ( rangeStartOrlastNbytes < 0 ) &&
             ( rangeEnd != HTTP_RANGE_REQUEST_END_OF_FILE ) )
    {
        LogError( ( "Parameter check failed: Invalid range values: "
                    "rangeEnd should be -1 when rangeStart < 0: "
                    "RangeStart=%d, RangeEnd=%d",
                    rangeStartOrlastNbytes, rangeEnd ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( ( rangeEnd != HTTP_RANGE_REQUEST_END_OF_FILE ) &&
             ( rangeStartOrlastNbytes > rangeEnd ) )
    {
        LogError( ( "Parameter check failed: Invalid range values: "
                    "rangeStart should be < rangeEnd when both are >= 0: "
                    "RangeStart=%d, RangeEnd=%d",
                    rangeStartOrlastNbytes, rangeEnd ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else
    {
        /* Generate the value data for the Range Request header.*/

        /* Write the range value prefix in the buffer. */
        ( void ) memcpy( rangeValueBuffer,
                         HTTP_RANGE_REQUEST_HEADER_VALUE_PREFIX,
                         HTTP_RANGE_REQUEST_HEADER_VALUE_PREFIX_LEN );
        rangeValueLength += HTTP_RANGE_REQUEST_HEADER_VALUE_PREFIX_LEN;

        /* Write the range start value in the buffer. */
        rangeValueLength += convertInt32ToAscii( rangeStartOrlastNbytes,
                                                 rangeValueBuffer + rangeValueLength,
                                                 sizeof( rangeValueBuffer ) - rangeValueLength );

        /* Add remaining value data depending on the range specification type. */

        /* Add rangeEnd value if request is for [rangeStart, rangeEnd] byte range */
        if( rangeEnd != HTTP_RANGE_REQUEST_END_OF_FILE )
        {
            /* Write the "-" character to the buffer.*/
            ( void ) memcpy( rangeValueBuffer + rangeValueLength,
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
            ( void ) memcpy( rangeValueBuffer + rangeValueLength,
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
                                  ( const uint8_t * ) HTTP_RANGE_REQUEST_HEADER_FIELD,
                                  HTTP_RANGE_REQUEST_HEADER_FIELD_LEN,
                                  ( const uint8_t * ) rangeValueBuffer,
                                  rangeValueLength );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t sendHttpData( const HTTPTransportInterface_t * pTransport,
                                  const uint8_t * pData,
                                  size_t dataLen )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;
    int32_t transportStatus = 0;

    assert( pTransport != NULL );
    assert( pTransport->send != NULL );
    assert( pData != NULL );

    transportStatus = pTransport->send( pTransport->pContext,
                                        pData,
                                        dataLen );

    if( transportStatus < 0 )
    {
        LogError( ( "Failed to send HTTP data: Transport send()"
                    " returned error: TransportStatus=%d",
                    transportStatus ) );
        returnStatus = HTTP_NETWORK_ERROR;
    }
    else if( ( size_t ) transportStatus != dataLen )
    {
        LogError( ( "Failed to send HTTP data: Transport layer "
                    "did not send the required bytes: RequiredBytes=%lu"
                    ", SentBytes=%d.",
                    ( unsigned long ) dataLen,
                    transportStatus ) );
        returnStatus = HTTP_NETWORK_ERROR;
    }
    else
    {
        LogDebug( ( "Sent HTTP data over the transport: BytesSent "
                    "=%d.",
                    transportStatus ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t addContentLengthHeader( HTTPRequestHeaders_t * pRequestHeaders,
                                            size_t contentLength )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;
    char pContentLengthValue[ MAX_INT32_NO_OF_DECIMAL_DIGITS ] = { '\0' };
    uint8_t contentLengthValueNumBytes = 0u;
    size_t headerLength = 0u;

    assert( pRequestHeaders != NULL );
    assert( contentLength > 0u );

    contentLengthValueNumBytes = convertInt32ToAscii( ( int32_t ) contentLength,
                                                      pContentLengthValue,
                                                      sizeof( pContentLengthValue ) );

    returnStatus = addHeader( pRequestHeaders,
                              ( const uint8_t * ) HTTP_CONTENT_LENGTH_FIELD,
                              HTTP_CONTENT_LENGTH_FIELD_LEN,
                              ( const uint8_t * ) pContentLengthValue,
                              contentLengthValueNumBytes );

    if( returnStatus != HTTP_SUCCESS )
    {
        LogError( ( "Failed to write Content-Length header to the request "
                    "header buffer: ContentLengthValue: %lu",
                    ( unsigned long ) contentLength ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t sendHttpHeaders( const HTTPTransportInterface_t * pTransport,
                                     HTTPRequestHeaders_t * pRequestHeaders,
                                     size_t reqBodyLen,
                                     uint32_t flags )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;
    size_t numBytesToSend = 0u;
    uint8_t shouldSendContentLength = 0u;

    assert( pTransport != NULL );
    assert( pTransport->send != NULL );
    assert( pRequestHeaders != NULL );

    /* Send the content length header if the flag to disable is not set and the
     * body length is greater than zero. */
    shouldSendContentLength = ( ( ( flags & HTTP_SEND_DISABLE_CONTENT_LENGTH_FLAG ) == 0u ) &&
                                ( reqBodyLen > 0u ) ) ? 1u : 0u;

    if( shouldSendContentLength == 1u )
    {
        returnStatus = addContentLengthHeader( pRequestHeaders, reqBodyLen );
    }

    if( returnStatus == HTTP_SUCCESS )
    {
        LogDebug( ( "Sending HTTP request headers: HeaderBytes=%d",
                    numBytesToSend ) );

        /* Send the HTTP headers over the network. */
        returnStatus = sendHttpData( pTransport, pRequestHeaders->pBuffer, pRequestHeaders->headersLen );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t sendHttpBody( const HTTPTransportInterface_t * pTransport,
                                  const uint8_t * pRequestBodyBuf,
                                  size_t reqBodyBufLen )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    assert( pTransport != NULL );
    assert( pTransport->send != NULL );
    assert( pRequestBodyBuf != NULL );

    /* Send the request body. */
    LogDebug( ( "Sending the HTTP request body: BodyBytes=%d",
                reqBodyBufLen ) );
    returnStatus = sendHttpData( pTransport, pRequestBodyBuf, reqBodyBufLen );

    return returnStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t receiveHttpData( const HTTPTransportInterface_t * pTransport,
                              uint8_t * pBuffer,
                              size_t bufferLen,
                              size_t * pBytesReceived )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;
    int32_t transportStatus = 0;

    assert( pTransport != NULL );
    assert( pTransport->recv != NULL );
    assert( pBuffer != NULL );
    assert( pBytesReceived != NULL );

    transportStatus = pTransport->recv( pTransport->pContext,
                                        pBuffer,
                                        bufferLen );

    /* A transport status of less than zero is an error. */
    if( transportStatus < 0 )
    {
        LogError( ( "Failed to receive HTTP data: Transport recv() "
                    "returned error: TransportStatus=%d.",
                    transportStatus ) );
        returnStatus = HTTP_NETWORK_ERROR;
    }
    else if( ( size_t ) transportStatus > bufferLen )
    {
        /* There is a bug in the transport recv if more bytes are reported
         * to have been read than the bytes asked for. */
        LogError( ( "Failed to receive HTTP data: Transport recv() "
                    " read more bytes than requested: BytesRead=%d, "
                    "RequestedBytes=%lu",
                    transportStatus,
                    ( unsigned long ) bufferLen ) );
        returnStatus = HTTP_NETWORK_ERROR;
    }
    else if( transportStatus > 0 )
    {
        /* Some or all of the specified data was received. */
        *pBytesReceived = ( size_t ) ( transportStatus );
        LogDebug( ( "Received data from the transport: BytesReceived=%d.",
                    transportStatus ) );
    }
    else
    {
        /* When a zero is returned from the transport recv it will not be
         * invoked again. */
        *pBytesReceived = 0;
        LogDebug( ( "Received zero bytes from transport recv(). Receiving "
                    "transport data is complete." ) );
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
        LogError( ( "Response not received: Zero returned from "
                    "transport recv: totalReceived=%lu",
                    ( unsigned long ) totalReceived ) );
        returnStatus = HTTP_NO_RESPONSE;
    }
    else if( parsingState == HTTP_PARSING_INCOMPLETE )
    {
        if( totalReceived == responseBufferLen )
        {
            LogError( ( "Cannot receive complete response from tansport"
                        " interface: Response buffer has insufficient "
                        "space: responseBufferLen=%lu",
                        ( unsigned long ) responseBufferLen ) );
            returnStatus = HTTP_INSUFFICIENT_MEMORY;
        }
        else
        {
            LogError( ( "Received partial response from transport "
                        "receive(): ResponseSize=%lu, TotalBufferSize=%lu",
                        ( unsigned long ) totalReceived,
                        ( unsigned long ) ( responseBufferLen - totalReceived ) ) );
            returnStatus = HTTP_PARTIAL_RESPONSE;
        }
    }
    else
    {
        /* Empty else for MISRA 15.7 compliance. */
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static HTTPStatus_t receiveAndParseHttpResponse( const HTTPTransportInterface_t * pTransport,
                                                 HTTPResponse_t * pResponse,
                                                 const HTTPRequestHeaders_t * pRequestHeaders )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;
    size_t totalReceived = 0u;
    size_t currentReceived = 0u;
    HTTPParsingContext_t parsingContext = { 0 };
    uint8_t shouldRecv = 1u;
    uint8_t isHeadResponse = 0u;

    assert( pTransport != NULL );
    assert( pTransport->recv != NULL );
    assert( pResponse != NULL );
    assert( pRequestHeaders != NULL );
    assert( pRequestHeaders->headersLen >= HTTP_MINIMUM_REQUEST_LINE_LENGTH );

    /* The parsing context needs to know if the response is for a HEAD request.
     * The third-party parser requires parsing is manually indicated to stop
     * in the httpParserOnHeadersCompleteCallback() for a HEAD response,
     * otherwise the parser will not indicate the message was complete. */
    if( strncmp( ( const char * ) ( pRequestHeaders->pBuffer ),
                 HTTP_METHOD_HEAD,
                 sizeof( HTTP_METHOD_HEAD ) - 1u ) == 0 )
    {
        isHeadResponse = 1u;
    }

    /* Initialize the parsing context for parsing the response received from the
     * network. */
    initializeParsingContextForFirstResponse( &parsingContext );

    while( shouldRecv == 1u )
    {
        /* Receive the HTTP response data into the pResponse->pBuffer. */
        returnStatus = receiveHttpData( pTransport,
                                        pResponse->pBuffer + totalReceived,
                                        pResponse->bufferLen - totalReceived,
                                        &currentReceived );

        if( returnStatus == HTTP_SUCCESS )
        {
            /* Data is received into the buffer and must be parsed. Parsing is
             * invoked even with a length of zero. A length of zero indicates to
             * the parser that there is no more data from the server (EOF). */
            returnStatus = parseHttpResponse( &parsingContext,
                                              pResponse,
                                              currentReceived,
                                              isHeadResponse );
            totalReceived += currentReceived;
        }

        /* Reading should continue if there are no errors in the transport recv
         * or parsing, non-zero data was received from the network,
         * the parser indicated the response message is not finished, and there
         * is room in the response buffer. */
        shouldRecv = ( ( returnStatus == HTTP_SUCCESS ) &&
                       ( currentReceived > 0u ) &&
                       ( parsingContext.state != HTTP_PARSING_COMPLETE ) &&
                       ( totalReceived < pResponse->bufferLen ) ) ? 1u : 0u;
    }

    if( returnStatus == HTTP_SUCCESS )
    {
        /* If there are errors in receiving from the network or during parsing,
         * the final status of the response message is derived from the state of
         * the parsing and how much data is in the buffer. */
        returnStatus = getFinalResponseStatus( parsingContext.state,
                                               totalReceived,
                                               pResponse->bufferLen );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

HTTPStatus_t HTTPClient_Send( const HTTPTransportInterface_t * pTransport,
                              HTTPRequestHeaders_t * pRequestHeaders,
                              const uint8_t * pRequestBodyBuf,
                              size_t reqBodyBufLen,
                              HTTPResponse_t * pResponse,
                              uint32_t flags )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    if( pTransport == NULL )
    {
        LogError( ( "Parameter check failed: pTransport interface is NULL." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pTransport->send == NULL )
    {
        LogError( ( "Parameter check failed: pTransport->send is NULL." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pTransport->recv == NULL )
    {
        LogError( ( "Parameter check failed: pTransport->recv is NULL." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pRequestHeaders == NULL )
    {
        LogError( ( "Parameter check failed: pRequestHeaders is NULL." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pRequestHeaders->pBuffer == NULL )
    {
        LogError( ( "Parameter check failed: pRequestHeaders->pBuffer is NULL." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pRequestHeaders->headersLen < HTTP_MINIMUM_REQUEST_LINE_LENGTH )
    {
        LogError( ( "Parameter check failed: pRequestHeaders->headersLen "
                    "does not meet minimum the required length. "
                    "MinimumRequiredLength=%u, HeadersLength =%lu",
                    HTTP_MINIMUM_REQUEST_LINE_LENGTH,
                    ( unsigned long ) ( pRequestHeaders->headersLen ) ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( ( pResponse != NULL ) && ( pResponse->pBuffer == NULL ) )
    {
        LogError( ( "Parameter check failed: pResponse->pBuffer is NULL." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( ( pRequestBodyBuf == NULL ) && ( reqBodyBufLen > 0u ) )
    {
        LogError( ( "Parameter check failed: pRequestBodyBuf is NULL, but "
                    "reqBodyBufLen is greater than zero." ) );
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
                                        pRequestHeaders,
                                        reqBodyBufLen,
                                        flags );
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
            LogDebug( ( "A request body was not sent: pRequestBodyBuf is NULL." ) );
        }
    }

    if( returnStatus == HTTP_SUCCESS )
    {
        /* If the application chooses to receive a response, then pResponse
         * will not be NULL. */
        if( pResponse != NULL )
        {
            returnStatus = receiveAndParseHttpResponse( pTransport,
                                                        pResponse,
                                                        pRequestHeaders );
        }
        else
        {
            LogDebug( ( "Response ignored: pResponse is NULL." ) );
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

/* The MISRA rule 8.13 violation is for using a non-const type for the
 * "pHttpParser" parser instead of a const-type, because the pointed to object
 * is not modified by the function. This violations is suppressed because this
 * function follows the function signature of the "on_header_field" callback
 * specified by the http-parser library.
 * /* The MISRA directive 4.6 violation is for using primitive type int, instead of
 * a typedef which denotes the signedness and size of the type. This violation
 * is suppressed because this callback follows the function signature for the
 * http_data_cb type in http-parser. */
/* coverity[misra_c_2012_rule_8_13_violation] */
/* coverity[misra_c_2012_directive_4_6_violation] */
static int findHeaderFieldParserCallback( http_parser * pHttpParser,
                                          const char * pFieldLoc,
                                          size_t fieldLen )
{
    findHeaderContext_t * pContext = NULL;

    assert( pHttpParser != NULL );
    assert( pFieldLoc != NULL );
    assert( fieldLen > 0u );

    assert( pContext->pField != NULL );
    assert( pContext->fieldLen > 0u );

    /* The header found flags should not be set. */
    assert( pContext->fieldFound == 0u );
    assert( pContext->valueFound == 0u );

    /* The MISRA rule 11.5 violation flags casting a void pointer to another
     * type. This rule is suppressed here because the http-parser library
     * requires that private context into callbacks must be set to a void
     * pointer variable. */
    /* coverity[misra_c_2012_rule_11_5_violation] */
    pContext = ( findHeaderContext_t * ) pHttpParser->data;

    /* Check whether the parsed header matches the header we are looking for. */

    /* MISRA rule 21.15 flags the memcmp of two different types, const uint8_t*
     * and const char*. These types are the same size, so this comparision is
     * acceptable. */
    /* coverity[misra_c_2012_rule_21_15_violation] */
    if( ( fieldLen == pContext->fieldLen ) &&
        ( memcmp( pContext->pField, pFieldLoc, fieldLen ) == 0 ) )
    {
        LogDebug( ( "Found header field in response: "
                    "HeaderName=%.*s, HeaderLocation=0x%x",
                    fieldLen, pContext->pField, pFieldLoc ) );

        /* Set the flag to indicate that header has been found in response. */
        pContext->fieldFound = 1u;
    }
    else
    {
        /* Empty else for MISRA 15.7 compliance. */
    }

    /* The MISRA directive 4.6 violation is for using primitive type int, instead of
     * a typedef which denotes the signedness and size of the type. This violation
     * is suppressed because http-parser requires this callback to return an integer. */
    /* coverity[misra_c_2012_directive_4_6_violation] */
    return HTTP_PARSER_CONTINUE_PARSING;
}

/*-----------------------------------------------------------*/

/* The coverity violation is for using a non-const type for the "pHttpParser" parser
 * instead of a const-type as the pointed to object is not modified by the function.
 * We suppress this violations this violation as this function follows the function
 * function signature of the "on_header_value" callback specified by the http-parser
 * library. */

/* The MISRA directive 4.6 violation is for using primitive type int, instead of
 * a typedef which denotes the signedness and size of the type. This violation
 * is suppressed because this callback follows the function signature for the
 * http_data_cb type in http-parser. */
/* coverity[misra_c_2012_rule_8_13_violation] */
/* coverity[misra_c_2012_directive_4_6_violation] */
static int findHeaderValueParserCallback( http_parser * pHttpParser,
                                          const char * pVaLueLoc,
                                          size_t valueLen )
{
    /* The coverity violation is for using "int" instead of a type that specifies size
     * and signedness information. We suppress this violation as this variable represents
     * the return value type of this callback function, whose return type is defined by
     * http-parser. */
    /* coverity[misra_c_2012_directive_4_6_violation] */
    int retCode = HTTP_PARSER_CONTINUE_PARSING;
    findHeaderContext_t * pContext = NULL;

    assert( pHttpParser != NULL );
    assert( pVaLueLoc != NULL );
    assert( valueLen > 0u );

    assert( pContext->pField != NULL );
    assert( pContext->fieldLen > 0u );
    assert( pContext->pValueLoc != NULL );
    assert( pContext->pValueLen != NULL );

    /* The MISRA rule 11.5 violation flags casting a void pointer to another
     * type. This rule is suppressed here because the http-parser library
     * requires that private context into callbacks must be set to a void
     * pointer variable. */
    /* coverity[misra_c_2012_rule_11_5_violation] */
    pContext = ( findHeaderContext_t * ) pHttpParser->data;

    /* The header value found flag should not be set. */
    assert( pContext->valueFound == 0u );

    if( pContext->fieldFound == 1u )
    {
        LogDebug( ( "Found header value in response: "
                    "RequestedField=%.*s, ValueLocation=0x%x",
                    pContext->fieldLen, pContext->pField, pVaLueLoc ) );

        /* Populate the output parameters with the location of the header value in the response buffer. */
        *pContext->pValueLoc = ( const uint8_t * ) pVaLueLoc;
        *pContext->pValueLen = valueLen;

        /* Set the header value found flag. */
        pContext->valueFound = 1u;

        /* As we have found the value associated with the header, we don't need
         * to parse the response any further. */

        /* The MISRA directive 4.6 violation is for using primitive type int, instead of
         * a typedef which denotes the signedness and size of the type. This violation
         * is suppressed because http-parser requires this callback to return an integer. */
        /* coverity[misra_c_2012_directive_4_6_violation] */
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

/* The MISRA directive 4.6 violation is for using primitive type int, instead of
 * a typedef which denotes the signedness and size of the type. This violation
 * is suppressed because this callback follows the function signature for the
 * http_cb type in http-parser. */
/* coverity[misra_c_2012_rule_8_13_violation] */
/* coverity[misra_c_2012_directive_4_6_violation] */
static int findHeaderOnHeaderCompleteCallback( http_parser * pHttpParser )
{
    findHeaderContext_t * pContext = NULL;

    /* Disable unused parameter warning. */
    ( void ) pHttpParser;

    assert( pHttpParser != NULL );

    /* The MISRA rule 11.5 violation flags casting a void pointer to another
     * type. This rule is suppressed here because the http-parser library
     * requires that private context into callbacks must be set to a void
     * pointer variable. */
    /* coverity[misra_c_2012_rule_11_5_violation] */
    pContext = ( findHeaderContext_t * ) pHttpParser->data;

    /* If we have reached here, all headers in the response have been parsed but the requested
     * header has not been found in the response buffer. */
    LogDebug( ( "Reached end of header parsing: Header not found in response: "
                "RequestedHeader=%.*s",
                pContext->fieldLen,
                pContext->pField ) );

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
    findHeaderContext_t context = { 0 };
    size_t numOfBytesParsed = 0u;

    context.pField = pField;
    context.fieldLen = fieldLen;
    context.pValueLoc = pValueLoc;
    context.pValueLen = pValueLen;
    context.fieldFound = 0u;
    context.valueFound = 0u;

    /* Disable unused variable warning. This variable is used only in logging. */
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

    LogDebug( ( "Parsed response for header search: NumBytesParsed=%u",
                numOfBytesParsed ) );

    if( context.fieldFound == 0u )
    {
        /* If header field is not found, then both the flags should be zero. */
        assert( context.valueFound == 0u );

        /* Header is not present in buffer. */
        LogWarn( ( "Header not found in response buffer: "
                   "RequestedHeader=%.*s",
                   ( int ) fieldLen,
                   pField ) );

        returnStatus = HTTP_HEADER_NOT_FOUND;
    }
    else if( context.valueFound == 0u )
    {
        /* The response buffer is invalid as only the header field was found
         * in the "<field>: <value>\r\n" format of an HTTP header. */

        /* MISRA rule 10.5 notes casting an unsigned integer to an enum type. This
         * violation is suppressed because the http-parser library directly sets
         * and maps http_parser.http_errno to the enum http_errno. */
        /* coverity[misra_c_2012_rule_10_5_violation] */
        LogError( ( "Unable to find header value in response: "
                    "Response data is invalid: "
                    "RequestedHeader=%.*s, ParserError=%s",
                    ( int ) fieldLen,
                    pField,
                    http_errno_description( HTTP_PARSER_ERRNO( &( parser ) ) ) ) );
        returnStatus = HTTP_INVALID_RESPONSE;
    }
    else
    {
        /* Empty else (when assert and logging is disabled) for MISRA 15.7
         * compliance. */

        /* Header is found. */
        assert( ( context.fieldFound == 1u ) && ( context.valueFound == 1u ) );

        LogDebug( ( "Found requested header in response: "
                    "HeaderName=%.*s, HeaderValue=%.*s",
                    ( int ) fieldLen,
                    pField,
                    ( int ) ( *pValueLen ),
                    *pValueLoc ) );
    }

    /* If the header field-value pair is found in response, then the return
     * value of "on_header_value" callback (related to the header value) should
     * cause the http_parser.http_errno to be "CB_header_value". */

    /* MISRA rule 10.5 notes casting an unsigned integer to an enum type. This
     * violation is suppressed because the http-parser library directly sets
     * and maps http_parser.http_errno to the enum http_errno. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    if( ( returnStatus == HTTP_SUCCESS ) &&
        ( parser.http_errno != HPE_CB_header_value ) )
    {
        /* MISRA rule 10.5 notes casting an unsigned integer to an enum type. This
         * violation is suppressed because the http-parser library directly sets
         * and maps http_parser.http_errno to the enum http_errno. */
        /* coverity[misra_c_2012_rule_10_5_violation] */
        LogError( ( "Header found in response but http-parser returned error: "
                    "ParserError=%s",
                    http_errno_description( HTTP_PARSER_ERRNO( &( parser ) ) ) ) );
        returnStatus = HTTP_PARSER_INTERNAL_ERROR;
    }

    /* If header was not found, then the "on_header_complete" callback is
     * expected to be called which should cause the http_parser.http_errno to be
     * "OK" */

    /* MISRA rule 10.5 notes casting an unsigned integer to an enum type. This
     * violation is suppressed because the http-parser library directly sets
     * and maps http_parser.http_errno to the enum http_errno. */
    /* coverity[misra_c_2012_rule_10_5_violation] */
    else if( ( returnStatus == HTTP_HEADER_NOT_FOUND ) &&
             ( parser.http_errno != HPE_OK ) )
    {
        /* MISRA rule 10.5 notes casting an unsigned integer to an enum type. This
         * violation is suppressed because the http-parser library directly sets
         * and maps http_parser.http_errno to the enum http_errno. */
        /* coverity[misra_c_2012_rule_10_5_violation] */
        LogError( ( "Header not found in response: http-parser returned error: "
                    "ParserError=%s",
                    http_errno_description( HTTP_PARSER_ERRNO( &( parser ) ) ) ) );
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
        LogError( ( "Parameter check failed: pResponse is NULL." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pResponse->pBuffer == NULL )
    {
        LogError( ( "Parameter check failed: pResponse->pBuffer is NULL." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pResponse->bufferLen == 0u )
    {
        LogError( ( "Parameter check failed: pResponse->bufferLen is 0: "
                    "Buffer len should be > 0." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pHeaderName == NULL )
    {
        LogError( ( "Parameter check failed: Input header name is NULL." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( headerNameLen == 0u )
    {
        LogError( ( "Parameter check failed: Input header name length is 0: "
                    "headerNameLen should be > 0." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pHeaderValueLoc == NULL )
    {
        LogError( ( "Parameter check failed: Output parameter for header value location is NULL." ) );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pHeaderValueLen == NULL )
    {
        LogError( ( "Parameter check failed: Output parameter for header value length is NULL." ) );
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

        case HTTP_SECURITY_ALERT_RESPONSE_HEADERS_SIZE_LIMIT_EXCEEDED:
            str = "HTTP_SECURITY_ALERT_RESPONSE_HEADERS_SIZE_LIMIT_EXCEEDED";
            break;

        case HTTP_SECURITY_ALERT_EXTRANEOUS_RESPONSE_DATA:
            str = "HTTP_SECURITY_ALERT_EXTRANEOUS_RESPONSE_DATA";
            break;

        case HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_CHUNK_HEADER:
            str = "HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_CHUNK_HEADER";
            break;

        case HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_PROTOCOL_VERSION:
            str = "HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_PROTOCOL_VERSION";
            break;

        case HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_STATUS_CODE:
            str = "HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_STATUS_CODE";
            break;

        case HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_CHARACTER:
            str = "HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_CHARACTER";
            break;

        case HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_CONTENT_LENGTH:
            str = "HTTP_SECURITY_ALERT_MALFORMED_RESPONSE_INVALID_CONTENT_LENGTH";
            break;

        case HTTP_PARSER_INTERNAL_ERROR:
            str = "HTTP_PARSER_INTERNAL_ERROR";
            break;

        case HTTP_HEADER_NOT_FOUND:
            str = "HTTP_HEADER_NOT_FOUND";
            break;

        case HTTP_INVALID_RESPONSE:
            str = "HTTP_INVALID_RESPONSE";
            break;

        default:
            LogWarn( ( "Invalid status code received for string conversion: "
                       "StatusCode=%d", status ) );
            break;
    }

    return str;
}

/*-----------------------------------------------------------*/

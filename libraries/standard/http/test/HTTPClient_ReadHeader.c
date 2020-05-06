HTTPStatus_t HTTPClient_ReadHeader( const HTTPResponse_t * pResponse,
                                    const uint8_t * pHeaderName,
                                    size_t headerNameLen,
                                    const uint8_t ** pHeaderValueLoc,
                                    size_t * pHeaderValueLen )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;
    HTTPParsingContext_t parsingContext;
    readHeaderContext_t context =
    {
        .pHeaderName     = pHeaderName,
        .headerNameLen   = headerNameLen,
        .pHeaderValueLoc = pHeaderValueLoc,
        .pHeaderValueLen = pHeaderValueLen,
        .headerFound     = 0u
    };

    HTTPClient_HeaderParsingCallback_t parsingCallback =
    {
        .onHeaderCallback = readHeaderParsingCallback,
        .pContext         = &context
    };

    memset( &parsingContext, 0, sizeof( HTTPParsingContext_t ) );

    if( pResponse == NULL )
    {
        IotLogError( "Parameter check failed: pResponse is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pResponse->pBuffer == NULL )
    {
        IotLogError( "Parameter check failed: pRequestHeaders->pBuffer is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pResponse->bufferLen == 0u )
    {
        IotLogError( "Parameter check failed: pRequestHeaders->bufferLen is 0: Buffer len should be > 0." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pHeaderName == NULL )
    {
        IotLogError( "Parameter check failed: Input header name is NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( headerNameLen == 0u )
    {
        IotLogError( "Parameter check failed: Input header name length is 0: pHeaderName should be > 0." );
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
        /* Initialize Parsing context with our callback. */
        returnStatus = HTTPClient_InitializeParsingContext( &parsingContext,
                                                            &parsingCallback );
    }

    if( returnStatus == HTTP_SUCCESS )
    {
        returnStatus = HTTPClient_ParseResponse( &parsingContext,
                                                 pResponse->pBuffer,
                                                 pResponse->bufferLen );

        if( returnStatus != HTTP_SUCCESS )
        {
            IotLogErrorWithArgs( "Unable to read header from response: "
                                 "Failure in parsing response for header field: "
                                 "HeaderName=%.*s", pHeaderName, headerNameLen );
        }
        else if( context.headerFound == 0u )
        {
            /* Header is not present in buffer. */
            IotLogWarnWithArgs( "Unable to read header from response: "
                                "Header field not found in response buffer: "
                                "HeaderName=%.*s", pHeaderName, headerNameLen );
            returnStatus = HTTP_HEADER_NOT_FOUND;
        }
        else
        {
            /* Header value found present in buffer. */
            IotLogDebugWithArgs( "Found requested header in response: "
                                 "HeaderName=%.*s, ValueLoc=%.*s",
                                 headerNameLen, pHeaderName,
                                 *pHeaderValueLen, *pHeaderValueLoc );
        }
    }
    else
    {
        IotLogErrorWithArgs( "Failed to read header from response: "
                             "Unable to initialize parsing context: "
                             "HeaderName=%.*s", pHeaderName, headerNameLen );
    }

    return returnStatus;
}

#include "http_client.h"
#include "stdio.h"

HTTPStatus_t HTTPClient_InitializeRequestHeaders( HTTPRequestHeaders_t * pRequestHeaders,
                                                  const HTTPRequestInfo_t * pRequestInfo )
{
    return HTTP_NOT_SUPPORTED;
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

static HTTPStatus_t _sendHttpHeaders( const HTTPTransportInterface_t* pTransport,
                                      const HTTPRequestHeaders_t* pRequestHeaders,
                                      const uint8_t* pRequestBodyBuf )
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
                    "interface. Transport status %d.", 
                    transportStatus );
        returnStatus = HTTP_NETWORK_ERROR;
    }
    else if( transportStatus != pRequestHeaders->headersLen )
    {
        IotLogErrorWithArgs( "Attempted to send %d, transport reported it sent %d.",
                    pRequestHeaders->headersLen,
                    transportStatus );
        returnStatus = HTTP_NETWORK_ERROR;
    }

    return returnStatus;
}

static HTTPStatus_t _sendHttpBody( const HTTPTransportInterface_t* pTransport,
                                   const uint8_t* pRequestBodyBuf,
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
            IotLogErrorWithArgs( "Attempted to send %d, transport reported it sent %d.",
                        reqBodyBufLen,
                        transportStatus );
            returnStatus = HTTP_NETWORK_ERROR;
        }
    }

    return returnStatus;
}

static HTTPStatus_t _receiveHttpResponse( const HTTPTransportInterface_t* pTransport,
                                          HTTPResponse_t* pResponse )
{
    #if 0
    HTTPStatus_t returnStatus = HTTP_SUCCESS;
    HTTPStatus_t parsingStatus = HTTP_SUCCESS;
    int32_t transportStatus = 0;
    size_t currentReceived = 0;

    /* If the application chooses not to receive a response then pResponse will
     * be NULL. */
    if( pResponse != NULL )
    {
        for( ;; )
        {
            transportStatus = pTransport->recv( pTransport->pContext,
                                                pResponse->pBuffer,
                                                pResponse->bodyLen );

            /* A transport status of less than zero is an error. */
            if( transportStatus < 0 )
            {
                IotLogErrorWithArgs( "Error in sending the HTTP body over the "
                                    "transport interface. Transport status %d.",
                                    transportStatus );
                returnStatus = HTTP_NETWORK_ERROR;
                break;
            }

            /* A zero is considered a timeout and the HTTP client library should
             * stop trying to recv. */
            if( transportStatus == 0 )
            {
                IotLogDebug( "Transport recv returned 0. Receiving response "
                             "is complete." );
                break;
            }

            /* Parsing state is local so that if the transport->recv loop is
             * invoked again with more data, then the parsing starts where it
             * left off. */

            /* Data is received into the buffer and must be parsed. */
            parsingStatus = HTTPClient_ParseResponse( pResponse, 
                                                      ( size_t )( transportStatus ) );

            if( parsingStatus == HTTP_MESSAGE_COMPLETE )
            {
                break;
            }

            if( parsingStatus != HTTP_MESSAGE_INCOMPLETE )
            {

            }
        }
    }
    #endif
    return HTTP_SUCCESS;
}

HTTPStatus_t HTTPClient_Send( const HTTPTransportInterface_t* pTransport,
                              const HTTPRequestHeaders_t* pRequestHeaders,
                              const uint8_t* pRequestBodyBuf,
                              size_t reqBodyBufLen,
                              HTTPResponse_t* pResponse )
{
    HTTPStatus_t returnStatus = HTTP_SUCCESS;

    if( pTransport == NULL )
    {
        IotLogError("The transport interface cannot be NULL.");
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pRequestHeaders == NULL )
    {
        IotLogError( "The request headers cannot be NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pTransport->send == NULL )
    {
        IotLogError( "The transport interface send cannot be NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }
    else if( pTransport->recv == NULL )
    {
        IotLogError( "The transport interface recv cannot be NULL." );
        returnStatus = HTTP_INVALID_PARAMETER;
    }

    /* Send the headers, which are at one location in memory. */
    if( returnStatus == HTTP_SUCCESS )
    {
        returnStatus = _sendHttpHeaders( pTransport,
                                         pRequestHeaders,
                                         pRequestBodyBuf );
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

HTTPStatus_t HTTPClient_ReadHeader( HTTPResponse_t * pResponse,
                                    const char * pName,
                                    size_t nameLen,
                                    char ** pValue,
                                    size_t * valueLen )
{
    return HTTP_NOT_SUPPORTED;
}

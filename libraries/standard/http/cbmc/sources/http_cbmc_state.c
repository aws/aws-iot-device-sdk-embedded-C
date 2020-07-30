#include <stdlib.h>

#include "http_cbmc_state.h"

void * mallocCanFail( size_t size )
{
    __CPROVER_assert( size < CBMC_MAX_OBJECT_SIZE, "mallocCanFail size is too big" );
    return nondet_bool() ? NULL : malloc( size );
}

HTTPRequestHeaders_t * allocateHttpRequestHeaders( HTTPRequestHeaders_t * pRequestHeaders )
{
    if( pRequestHeaders == NULL )
    {
        pRequestHeaders = mallocCanFail( sizeof( HTTPRequestHeaders_t ) );
    }

    if( pRequestHeaders != NULL )
    {
        __CPROVER_assume( pRequestHeaders->bufferLen < CBMC_MAX_OBJECT_SIZE );
        pRequestHeaders->pBuffer = mallocCanFail( pRequestHeaders->bufferLen );
    }

    return pRequestHeaders;
}

bool isValidHttpRequestHeaders( const HTTPRequestHeaders_t * pRequestHeaders )
{
    bool isValid = true;

    if( pRequestHeaders )
    {
        isValid = pRequestHeaders->bufferLen < CBMC_MAX_OBJECT_SIZE &&
                  pRequestHeaders->headersLen < CBMC_MAX_OBJECT_SIZE;
    }

    return isValid;
}

HTTPRequestInfo_t * allocateHttpRequestInfo( HTTPRequestInfo_t * pRequestInfo )
{
    if( pRequestInfo == NULL )
    {
        pRequestInfo = mallocCanFail( sizeof( HTTPRequestInfo_t ) );
    }

    if( pRequestInfo != NULL )
    {
        __CPROVER_assume( pRequestInfo->methodLen < CBMC_MAX_OBJECT_SIZE );
        pRequestInfo->method = mallocCanFail( pRequestInfo->methodLen );

        __CPROVER_assume( pRequestInfo->hostLen < CBMC_MAX_OBJECT_SIZE );
        pRequestInfo->pHost = mallocCanFail( pRequestInfo->hostLen );

        __CPROVER_assume( pRequestInfo->pathLen < CBMC_MAX_OBJECT_SIZE );
        pRequestInfo->pPath = mallocCanFail( pRequestInfo->pathLen );
    }

    return pRequestInfo;
}

bool isValidHttpRequestInfo( const HTTPRequestInfo_t * pRequestInfo )
{
    bool isValid = true;

    if( pRequestInfo )
    {
        isValid = ( pRequestInfo->methodLen < CBMC_MAX_OBJECT_SIZE ) &&
                  ( pRequestInfo->hostLen < CBMC_MAX_OBJECT_SIZE ) &&
                  ( pRequestInfo->pathLen < CBMC_MAX_OBJECT_SIZE );
    }

    return isValid;
}

HTTPResponse_t * allocateHttpResponse( HTTPResponse_t * pResponse )
{
    if( pResponse == NULL )
    {
        pResponse = mallocCanFail( sizeof( HTTPResponse_t ) );
    }

    if( pResponse != NULL )
    {
        __CPROVER_assume( pResponse->bufferLen < CBMC_MAX_OBJECT_SIZE );
        pResponse->pBuffer = mallocCanFail( pResponse->bufferLen );
        __CPROVER_assume( pResponse->bodyLen < CBMC_MAX_OBJECT_SIZE );
        pResponse->pBody = mallocCanFail( pResponse->bodyLen );
    }

    return pResponse;
}

bool isValidHttpResponse( const HTTPResponse_t * pResponse )
{
    bool isValid = true;

    if( pResponse )
    {
        isValid = ( pResponse->bufferLen < CBMC_MAX_OBJECT_SIZE ) &&
                  ( pResponse->bodyLen < CBMC_MAX_OBJECT_SIZE );
    }

    return isValid;
}

TransportInterface_t * allocateTransportInterface( TransportInterface_t * pTransport )
{
    if( pTransport == NULL )
    {
        pTransport = mallocCanFail( sizeof( TransportInterface_t ) );
    }

    if( pTransport != NULL )
    {
        pTransport->pNetworkContext = mallocCanFail( sizeof( NetworkContext_t ) );
    }

    return pTransport;
}

http_parser * allocateHttpParser( http_parser * pHttpParser )
{
    size_t dataLen;
    size_t responseLen;
    HTTPParsingContext_t * pHttpParsingContext;

    if( pHttpParser == NULL )
    {
        pHttpParser = malloc( sizeof( http_parser ) );
        pHttpParsingContext = allocateHttpParsingContext( pHttpParsingContext );
        pHttpParser->data = ( void * ) pHttpParsingContext;
    }

    return pHttpParser;
}

HTTPParsingContext_t * allocateHttpParsingContext( HTTPParsingContext_t * pHttpParsingContext )
{
    HTTPResponse_t * pHttpResponse = malloc( sizeof( HTTPResponse_t ) );

    if( pHttpParsingContext == NULL )
    {
        pHttpParsingContext = malloc( sizeof( HTTPParsingContext_t ) );
    }

    if( pHttpParsingContext != NULL )
    {
        pHttpParsingContext->pResponse = allocateHttpResponse( pHttpResponse );
        pHttpParsingContext->pBufferCur = pHttpResponse->pBuffer;
    }

    return pHttpParsingContext;
}

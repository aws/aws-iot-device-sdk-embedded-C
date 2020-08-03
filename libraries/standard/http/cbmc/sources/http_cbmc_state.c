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
    size_t headerOffset, bodyOffset;

    if( pResponse == NULL )
    {
        pResponse = mallocCanFail( sizeof( HTTPResponse_t ) );
    }

    if( pResponse != NULL )
    {
        __CPROVER_assume( pResponse->bufferLen < CBMC_MAX_OBJECT_SIZE );
        __CPROVER_assume( pResponse->bodyLen <= pResponse->bufferLen );
        __CPROVER_assume( pResponse->headersLen <= pResponse->bufferLen );

        pResponse->pBuffer = mallocCanFail( pResponse->bufferLen );

        __CPROVER_assume( headerOffset <= pResponse->headersLen );
        pResponse->pHeaders = nondet_bool() ? NULL :
                              pResponse->pBuffer + headerOffset;

        if( pResponse->bufferLen == 0 )
        {
            bodyOffset = 0;
        }
        else
        {
            __CPROVER_assume( pResponse->headersLen < bodyOffset &&
                              bodyOffset <= pResponse->bufferLen );
        }

        pResponse->pBody = nondet_bool() ? NULL :
                           pResponse->pBuffer + bodyOffset;
    }

    return pResponse;
}

bool isValidHttpResponse( const HTTPResponse_t * pResponse )
{
    bool isValid = true;

    if( pResponse )
    {
        isValid = ( pResponse->bufferLen < CBMC_MAX_OBJECT_SIZE ) &&
                  ( pResponse->bodyLen < pResponse->bufferLen ) &&
                  ( pResponse->headersLen < pResponse->bufferLen );
        isValid = isValid || pResponse->pBody == NULL;
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

bool isValidTransportInterface( TransportInterface_t * pTransportInterface )
{
    bool isValid = true;

    if( pTransportInterface )
    {
        isValid = isValid && ( pTransportInterface->send == TransportInterfaceSendStub ||
                               pTransportInterface->send == NULL );
        isValid = isValid && ( pTransportInterface->recv == TransportInterfaceReceiveStub ||
                               pTransportInterface->recv == NULL );
    }
}

http_parser * allocateHttpSendParser( http_parser * pHttpParser )
{
    HTTPParsingContext_t * pHttpParsingContext;

    if( pHttpParser == NULL )
    {
        pHttpParser = malloc( sizeof( http_parser ) );
    }

    pHttpParsingContext = allocateHttpSendParsingContext( NULL );
    __CPROVER_assume( isValidHttpSendParsingContext( pHttpParsingContext ) );
    pHttpParser->data = ( void * ) pHttpParsingContext;

    return pHttpParser;
}

HTTPParsingContext_t * allocateHttpSendParsingContext( HTTPParsingContext_t * pHttpParsingContext )
{
    HTTPResponse_t * pResponse;
    size_t bufferOffset;

    if( pHttpParsingContext == NULL )
    {
        pHttpParsingContext = malloc( sizeof( HTTPParsingContext_t ) );
    }

    if( pHttpParsingContext != NULL )
    {
        pResponse = allocateHttpResponse( NULL );
        __CPROVER_assume( isValidHttpResponse( pResponse ) &&
                          pResponse != NULL &&
                          pResponse->pBuffer != NULL &&
                          pResponse->bufferLen > 0 );
        pHttpParsingContext->pResponse = pResponse;

        __CPROVER_assume( bufferOffset <= pResponse->bufferLen );
        pHttpParsingContext->pBufferCur = pResponse->pBuffer + bufferOffset;
    }

    return pHttpParsingContext;
}

bool isValidHttpSendParsingContext( const HTTPParsingContext_t * pHttpParsingContext )
{
    bool isValid = true;

    isValid = isValid && ( pHttpParsingContext->lastHeaderFieldLen ) <= ( SIZE_MAX - CBMC_MAX_OBJECT_SIZE );
    isValid = isValid && ( pHttpParsingContext->lastHeaderValueLen ) <= ( SIZE_MAX - CBMC_MAX_OBJECT_SIZE );

    return isValid;
}

http_parser * allocateHttpReadHeaderParser( http_parser * pHttpParser )
{
    HTTPParsingContext_t * pFindHeaderContext;

    if( pHttpParser == NULL )
    {
        pHttpParser = malloc( sizeof( http_parser ) );
    }

    pFindHeaderContext = allocateFindHeaderContext( NULL );
    pHttpParser->data = ( void * ) pFindHeaderContext;

    return pHttpParser;
}

findHeaderContext_t * allocateFindHeaderContext( findHeaderContext_t * pFindHeaderContext )
{
    if( pFindHeaderContext == NULL )
    {
        pFindHeaderContext = malloc( sizeof( findHeaderContext_t ) );
    }

    return pFindHeaderContext;
}

#include <stdlib.h>

#include "http_cbmc_state.h"

#include "transport_interface_stubs.h"

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


#ifndef MAX_TRIES
    #define MAX_TRIES    2
#endif

int32_t TransportInterfaceSendStub( NetworkContext_t pContext,
                                    void * pBuffer,
                                    size_t bytesToSend )
{
    __CPROVER_assert( pBuffer != NULL,
                      "TransportInterfaceSendStub pBuffer is NULL" );

    /****************************************************************
    * The send method sends some portion of the message and returns the
    * total number of bytes in the prefix sent so far.  The send method
    * is used in a loop of the form
    *
    *   while ( send( conn, msg, len )  < len ) { ... }
    *
    * We need to bound the number of loop iterations, so we need to
    * bound the number of times it takes for send to finish sending the
    * message.  We use a static variable 'tries' to count the number of
    * times send has tried to send the message, and we force send to
    * finish the message after MAX_TRIES tries.
    ****************************************************************/

    /* The number of tries to send the message before this invocation */
    static int32_t tries;

    /* The number of bytes considered sent after this invocation */
    int32_t size;

    if( tries >= MAX_TRIES )
    {
        tries = 0;
        return bytesToSend;
    }

    tries++;
    return size;
}

int32_t TransportInterfaceReceiveStub( NetworkContext_t context,
                                       void * pBuffer,
                                       size_t bytesToRecv )
{
    __CPROVER_assert( pBuffer != NULL,
                      "TransportInterfaceSendStub pBuffer is NULL" );

    /****************************************************************
    * The send method sends some portion of the message and returns the
    * total number of bytes in the prefix sent so far.  The send method
    * is used in a loop of the form
    *
    *   while ( send( conn, msg, len )  < len ) { ... }
    *
    * We need to bound the number of loop iterations, so we need to
    * bound the number of times it takes for send to finish sending the
    * message.  We use a static variable 'tries' to count the number of
    * times send has tried to send the message, and we force send to
    * finish the message after MAX_TRIES tries.
    ****************************************************************/

    /* The number of tries to send the message before this invocation */
    static int32_t tries;

    /* The number of bytes considered sent after this invocation */
    int32_t size;

    if( tries >= MAX_TRIES )
    {
        tries = 0;
        return bytesToRecv;
    }

    tries++;
    return size;
}

HTTPTransportInterface_t * allocateTransportInterface( HTTPTransportInterface_t * pTransport )
{
    if( pTransport == NULL )
    {
        pTransport = mallocCanFail( sizeof( HTTPTransportInterface_t ) );
    }

    if( pTransport != NULL )
    {
        pTransport->pContext = mallocCanFail( sizeof( struct NetworkContext ) );
    }

    return pTransport;
}

bool isValidTransportInterface( HTTPTransportInterface_t * pTransport )
{
    bool isValid = true;

    if( pTransport != NULL )
    {
        isValid = ( pTransport->send == NULL ||
                    pTransport->send == TransportInterfaceSendStub ) &&
                  ( pTransport->recv == NULL ||
                    pTransport->recv == TransportInterfaceReceiveStub );
    }

    return isValid;
}

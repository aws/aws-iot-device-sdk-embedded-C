#include <stdlib.h>

#include "http_cbmc_state.h"

void * safeMalloc( size_t xWantedSize )
{
    return nondet_bool() ? malloc( xWantedSize ) : NULL;
}

HTTPRequestHeaders_t * allocateHTTPRequestHeaders()
{
    HTTPRequestHeaders_t * pRequestHeaders = NULL;

    pRequestHeaders = safeMalloc( sizeof( HTTPRequestHeaders_t ) );

    if( pRequestHeaders )
    {
        pRequestHeaders->pBuffer = safeMalloc( pRequestHeaders->bufferLen );
    }

    return pRequestHeaders;
}

int isValidHTTPRequestHeaders( const HTTPRequestHeaders_t * pRequestHeaders )
{
    return pRequestHeaders->bufferLen < CBMC_MAX_OBJECT_SIZE &&
           pRequestHeaders->headersLen < CBMC_MAX_OBJECT_SIZE &&
           pRequestHeaders->headersLen < pRequestHeaders->bufferLen &&
           __CPROVER_POINTER_OFFSET( pRequestHeaders->pBuffer ) <=
           pRequestHeaders->bufferLen;
}

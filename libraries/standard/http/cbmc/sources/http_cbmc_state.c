#include <stdlib.h>

#include "http_cbmc_state.h"

extern _Bool nondet_bool();

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
    int validBuffer = 1;

    if( pRequestHeaders->pBuffer )
    {
        validBuffer = __CPROVER_r_ok( pRequestHeaders->pBuffer, pRequestHeaders->bufferLen );
    }

    return pRequestHeaders->bufferLen < CBMC_MAX_OBJECT_SIZE &&
           pRequestHeaders->headersLen <= pRequestHeaders->bufferLen &&
           validBuffer;
}

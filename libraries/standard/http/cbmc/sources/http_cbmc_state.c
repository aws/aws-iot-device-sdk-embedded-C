#include "http_cbmc_state.h"

HTTPRequestHeaders_t allocate_HTTPRequestHeaders()
{
    HTTPRequestHeaders_t * pRequestHeaders = NULL;

    pRequestHeaders = safeMalloc( sizeof( HTTPRequestHeaders_t ) );

    if( pRequestHeaders )
    {
        pRequestHeaders->pBuffer = safeMalloc( pRequestHeaders->bufferLen );
    }

    return pRequestHeaders;
}

bool is_valid_HTTPRequestHeaders( const HTTPRequestHeaders_t * pRequestHeaders )
{
    return pRequestHeaders->bufferLen < CBMC_MAX_OBJECT_SIZE &&
           pRequestHeaders->headersLen < CBMC_MAX_OBJECT_SIZE &&
           pRequestHeaders->headersLen < pRequestHeaders->bufferLen &&
           __CPROVER_POINTER_OFFSET( pRequestHeaders->pBuffer ) <=
           pRequestHeaders->bufferLen;
}

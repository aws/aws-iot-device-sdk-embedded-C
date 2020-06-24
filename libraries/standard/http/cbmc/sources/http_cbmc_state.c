#include <stdlib.h>

#include "http_cbmc_state.h"

extern _Bool nondet_bool();

void * mallocCanFail( size_t size )
{
    __CPROVER_assert( size < CBMC_MAX_OBJECT_SIZE, "mallocCanFail size is too big" );
    return nondet_bool() ? NULL : malloc( size );
}

void allocateHttpRequestHeaders( HTTPRequestHeaders_t * pRequestHeaders )
{
    if( pRequestHeaders == NULL )
    {
        pRequestHeaders = mallocCanFail( sizeof( HTTPRequestHeaders_t ) );
    }

    pRequestHeaders->pBuffer = mallocCanFail( pRequestHeaders->bufferLen );

    return pRequestHeaders;
}

int isValidHttpRequestHeaders( const HTTPRequestHeaders_t * pRequestHeaders )
{
    int isValid = 1;

    if( pRequestHeaders )
    {
        isValid = pRequestHeaders->bufferLen < CBMC_MAX_OBJECT_SIZE &&
                  pRequestHeaders->headersLen < CBMC_MAX_OBJECT_SIZE;
    }

    return isValid;
}

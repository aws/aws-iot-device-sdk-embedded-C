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

HTTPRequestInfo_t * allocateHttpRequestInfo()
{
    HTTPRequestInfo_t * pRequestInfo = NULL;

    pRequestInfo = safeMalloc( sizeof( HTTPRequestInfo_t ) );

    if( pRequestInfo )
    {
        pRequestInfo->method = safeMalloc( pRequestInfo->methodLen );
        pRequestInfo->pHost = safeMalloc( pRequestInfo->hostLen );
        pRequestInfo->pPath = safeMalloc( pRequestInfo->pathLen );
    }

    return pRequestInfo;
}

int isValidHttpRequestInfo( const HTTPRequestInfo_t * pRequestInfo )
{
    int validRequestInfoLengths = 1, validRequestInfoChars = 1;

    if( pRequestInfo )
    {
        validRequestInfoLengths = ( pRequestInfo->reqFlags < CBMC_MAX_OBJECT_SIZE ) &&
                                  ( pRequestInfo->methodLen < CBMC_MAX_OBJECT_SIZE ) &&
                                  ( pRequestInfo->hostLen < CBMC_MAX_OBJECT_SIZE ) &&
                                  ( pRequestInfo->pathLen < CBMC_MAX_OBJECT_SIZE );

        if( pRequestInfo->method )
        {
            validRequestInfoChars = __CPROVER_r_ok( pRequestInfo->method,
                                                    pRequestInfo->methodLen );
        }

        if( pRequestInfo->pHost )
        {
            validRequestInfoChars &= __CPROVER_r_ok( pRequestInfo->pHost,
                                                     pRequestInfo->hostLen );
        }

        if( pRequestInfo->pPath )
        {
            validRequestInfoChars &= __CPROVER_r_ok( pRequestInfo->pPath,
                                                     pRequestInfo->pathLen );
        }
    }

    return validRequestInfoLengths && validRequestInfoChars;
}

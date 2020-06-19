/*
 * Insert copyright notice
 */

/**
 * @file HTTPClient_AddHeader_harness.c
 * @brief Implements the proof harness for HTTPClient_AddHeader function.
 */

#include "http_client.h"

#include "http_cbmc_state.h"

void harness()
{
    /* Insert argument declarations */
    HTTPRequestHeaders_t * pRequestHeaders = allocate_HTTPRequestHeaders();

    if( pRequestHeaders )
    {
        __CPROVER_assume( is_valid_HTTPRequestHeaders( pRequestHeaders ) );
    }

    size_t fieldLen;
    size_t valueLen;
    __CPROVER_assume( fieldLen < CBMC_MAX_OBJECT_SIZE );
    __CPROVER_assume( valueLen < CBMC_MAX_OBJECT_SIZE );

    char * pField = safeMalloc( fieldLen + 1 );
    char * pValue = safeMalloc( valueLen + 1 );

    if( pField )
    {
        pField[ fieldLen ] = 0;
    }

    if( pValue )
    {
        pValue[ valueLen ] = 0;
    }

    HTTPClient_AddHeader( pRequestHeaders, pField, fieldLen, pValue, valueLen );
}

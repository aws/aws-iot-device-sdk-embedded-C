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
    HTTPRequestHeaders_t * pRequestHeaders = NULL;
    char * pField = NULL;
    char * pValue = NULL;
    size_t fieldLen;
    size_t valueLen;

    pRequestHeaders = allocateHTTPRequestHeaders();

    if( pRequestHeaders )
    {
        __CPROVER_assume( isValidHTTPRequestHeaders( pRequestHeaders ) );
    }

    __CPROVER_assume( fieldLen < CBMC_MAX_OBJECT_SIZE );
    __CPROVER_assume( valueLen < CBMC_MAX_OBJECT_SIZE );

    pField = safeMalloc( fieldLen );
    pValue = safeMalloc( valueLen );

    if( pField )
    {
        __CPROVER_assume( __CPROVER_r_ok( pField, fieldLen ) );
    }

    if( pValue )
    {
        __CPROVER_assume( __CPROVER_r_ok( pValue, valueLen ) );
    }

    HTTPClient_AddHeader( pRequestHeaders, pField, fieldLen, pValue, valueLen );
}

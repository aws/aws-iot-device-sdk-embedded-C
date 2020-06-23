/*
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

/**
 * @file HTTPClient_AddHeader_harness.c
 * @brief Implements the proof harness for HTTPClient_AddHeader function.
 */

#include "http_client.h"

#include "http_cbmc_state.h"

void harness()
{
    HTTPRequestHeaders_t * pRequestHeaders = NULL;
    char * pField = NULL;
    char * pValue = NULL;
    size_t fieldLen;
    size_t valueLen;

    /* Initialize and make assumptions for request headers. */
    pRequestHeaders = allocateHttpRequestHeaders();

    if( pRequestHeaders )
    {
        __CPROVER_assume( isValidHttpRequestHeaders( pRequestHeaders ) );
    }

    __CPROVER_assume( fieldLen < CBMC_MAX_OBJECT_SIZE );

    /* Initialize and make assumptions for header field. */
    pField = safeMalloc( fieldLen );

    if( pField )
    {
        __CPROVER_assume( __CPROVER_r_ok( pField, fieldLen ) );
    }

    /* Initialize and make assumptions for header value. */
    __CPROVER_assume( valueLen < CBMC_MAX_OBJECT_SIZE );

    pValue = safeMalloc( valueLen );

    if( pValue )
    {
        __CPROVER_assume( __CPROVER_r_ok( pValue, valueLen ) );
    }

    HTTPClient_AddHeader( pRequestHeaders, pField, fieldLen, pValue, valueLen );
}

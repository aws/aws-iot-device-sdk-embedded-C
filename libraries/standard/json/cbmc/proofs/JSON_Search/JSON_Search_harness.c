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
 * @file JSON_Search_harness.c
 * @brief Implements the proof harness for the JSON_Search function.
 */

#include <stdlib.h>
#include "json.h"

void harness()
{
    char * buf = NULL;
    size_t max;
    char * queryKey = NULL;
    size_t queryKeyLength;
    char separator;
    char * outValue;
    size_t outValueLength;
    JSONStatus_t ret;

    __CPROVER_assume( max < CBMC_MAX_BUFSIZE );

    if( nondet_bool() )
    {
        buf = malloc( max );
        __CPROVER_assume( __CPROVER_r_ok( buf, max ) );
    }

    __CPROVER_assume( queryKeyLength < CBMC_MAX_BUFSIZE );

    if( nondet_bool() )
    {
        queryKey = malloc( queryKeyLength );
        __CPROVER_assume( __CPROVER_r_ok( queryKey, queryKeyLength ) );
    }

    ret = JSON_Search( buf,
                       max,
                       queryKey,
                       queryKeyLength,
                       separator,
                       ( nondet_bool() ? &outValue : NULL ),
                       ( nondet_bool() ? &outValueLength : NULL ) );
}

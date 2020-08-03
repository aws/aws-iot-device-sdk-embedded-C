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
 * @file HTTPClient_Send_http_parser_execute.c
 * @brief Creates a stub for http_parser_execute for coverage of HTTPClient_Send.
 */

#include <stdbool.h>
#include <stdint.h>

#include "http_client.h"
#include "private/http_client_internal.h"
#include "http_parser.h"

/**
 * @brief Attains coverage when a variable needs to possibly contain two values.
 */
bool nondet_bool();

size_t http_parser_execute( http_parser * parser,
                            const http_parser_settings * settings,
                            const char * data,
                            size_t len )
{
    const char * pValue;
    size_t fieldLength;
    size_t valueLength;
    unsigned int http_errno;
    findHeaderContext_t * pParsingContext;

    __CPROVER_assert( parser != NULL,
                      "http_parser_execute parser is NULL" );
    __CPROVER_assert( settings != NULL,
                      "http_parser_execute settings is NULL" );
    __CPROVER_assert( data != NULL,
                      "http_parser_execute data is NULL" );
    __CPROVER_assert( len < CBMC_MAX_OBJECT_SIZE,
                      "http_parser_execute len >= CBMC_MAX_OBJECT_SIZE" );

    parser->http_errno = http_errno;

    __CPROVER_assume( fieldLength <= len );
    __CPROVER_assume( valueLength <= len );

    pParsingContext = ( findHeaderContext_t * ) ( parser->data );
    pParsingContext->pField = nondet_bool() ? NULL : malloc( fieldLength );
    pParsingContext->fieldLen = fieldLength;
    pParsingContext->pValueLoc = NULL;
    pParsingContext->pValueLen = 0;
    pParsingContext->fieldFound = nondet_bool() ? 0 : 1;

    if( pParsingContext->fieldFound )
    {
        pParsingContext->valueFound = nondet_bool() ? 0 : 1;
    }
    else
    {
        pParsingContext->valueFound = 0;
    }

    if( pParsingContext->valueFound )
    {
        pValue = malloc( valueLength );
        pParsingContext->pValueLen = &valueLength;
        pParsingContext->pValueLoc = &pValue;
    }

    return pParsingContext->fieldFound ? valueLength : 0;
}

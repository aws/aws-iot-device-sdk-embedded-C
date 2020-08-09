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
 * @file findHeaderValueParserCallback_harness.c
 * @brief Implements the proof harness for findHeaderValueParserCallback function.
 */

#include "http_cbmc_state.h"
#include "http_parser.h"
#include "http_client.h"


void harness()
{
    http_parser * pHttpParser;
    HTTPResponse_t * pResponse;
    findHeaderContext_t * pFindHeaderContext;
    size_t fieldLen, fieldOffset, valueLen, valueOffset;
    char * pValueLoc;

    pHttpParser = allocateHttpReadHeaderParser( NULL );
    pResponse = allocateHttpResponse( NULL );
    pFindHeaderContext = allocateFindHeaderContext( NULL );
    __CPROVER_assume( isValidHttpResponse( pResponse ) &&
                      pResponse != NULL &&
                      pResponse->pBuffer != NULL &&
                      pResponse->bufferLen > 0 );

    __CPROVER_assume( 0 < valueLen && valueLen <= pResponse->bufferLen );
    __CPROVER_assume( valueOffset < valueLen );
    pValueLoc = pResponse->pBuffer + valueOffset;

    __CPROVER_assume( 0 < fieldLen && fieldLen <= pResponse->bufferLen );
    __CPROVER_assume( fieldOffset < fieldLen );
    pFindHeaderContext->pField = pResponse->pBuffer + fieldOffset;
    pFindHeaderContext->fieldLen = fieldLen;
    pFindHeaderContext->pValueLen = &valueLen;
    pFindHeaderContext->pValueLoc = &pValueLoc;
    pFindHeaderContext->fieldFound = nondet_bool() ? 0 : 1;
    pFindHeaderContext->valueFound = 0;
    pHttpParser->data = ( void * ) pFindHeaderContext;

    __CPROVER_file_local_http_client_c_findHeaderValueParserCallback( pHttpParser, pValueLoc, valueLen );
}

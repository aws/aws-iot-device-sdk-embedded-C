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
 * @file findHeaderFieldParserCallback_harness.c
 * @brief Implements the proof harness for findHeaderFieldParserCallback function.
 */

#include "http_cbmc_state.h"
#include "http_parser.h"
#include "http_client.h"


void harness()
{
    http_parser * pHttpParser;
    HTTPResponse_t * pResponse;
    findHeaderContext_t * pFindHeaderContext;
    size_t fieldLen, fieldContextLen, fieldOffset, valueLen, valueOffset;
    char * pFieldLoc;

    pHttpParser = allocateHttpReadHeaderParser( NULL );
    pFindHeaderContext = allocateFindHeaderContext( NULL );
    pResponse = allocateHttpResponse( NULL );
    __CPROVER_assume( isValidHttpResponse( pResponse ) &&
                      pResponse != NULL &&
                      pResponse->pBuffer != NULL &&
                      pResponse->bufferLen > 0 );

    __CPROVER_assume( 0 < fieldLen && fieldLen <= MAX_HEADER_FIELD_LENGTH && fieldLen <= pResponse->bufferLen );
    __CPROVER_assume( fieldOffset <= fieldLen );
    pFieldLoc = pResponse->pBuffer + fieldOffset;
    __CPROVER_assume( pFieldLoc + fieldLen < pResponse->pBuffer + pResponse->bufferLen );

    __CPROVER_assume( 0 < fieldContextLen && fieldContextLen < CBMC_MAX_OBJECT_SIZE );
    pFindHeaderContext->pField = ( char * ) malloc( fieldContextLen );
    pFindHeaderContext->fieldLen = fieldContextLen;
    pFindHeaderContext->fieldFound = 0;
    pFindHeaderContext->valueFound = 0;
    pHttpParser->data = ( void * ) pFindHeaderContext;

    __CPROVER_file_local_http_client_c_findHeaderFieldParserCallback( pHttpParser, pFieldLoc, fieldLen );
}

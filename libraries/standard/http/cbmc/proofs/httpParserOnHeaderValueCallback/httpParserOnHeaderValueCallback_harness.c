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
 * @file httpParserOnHeaderValueCallback_harness.c
 * @brief Implements the proof harness for httpParserOnHeaderValueCallback function.
 */

#include "http_cbmc_state.h"
#include "http_parser.h"


void harness()
{
    http_parser * pHttpParser = NULL;
    HTTPParsingContext_t * pParsingContext = NULL;
    HTTPResponse_t * pResponse = NULL;
    size_t length;
    char * pLoc;

    pHttpParser = allocateHttpParser( NULL );

    pParsingContext = ( HTTPParsingContext_t * ) pHttpParser->data;
    __CPROVER_assume( pParsingContext->pLastHeaderField != NULL );

    pResponse = pParsingContext->pResponse;
    __CPROVER_assume( __CPROVER_same_object( pResponse->pBuffer,
                                             pLoc ) );
    __CPROVER_assume( __CPROVER_same_object( pResponse->pHeaders,
                                             pParsingContext->pBufferCur ) );
    __CPROVER_assume( ( const char * ) pResponse->pBuffer <= pLoc &&
                      pLoc < ( const char * ) ( pResponse->pBuffer + pResponse->bufferLen ) );

    __CPROVER_assume( length < CBMC_MAX_OBJECT_SIZE );

    __CPROVER_file_local_http_client_c_httpParserOnHeaderValueCallback( pHttpParser, pLoc, length );
}

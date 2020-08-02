/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved. */
/* SPDX-License-Identifier: Apache-2.0 */

/*
 * Insert copyright notice
 */

/**
 * @file httpParserOnStatusCallback_harness.c
 * @brief Implements the proof harness for httpParserOnStatusCallback function.
 */

#include "http_cbmc_state.h"
#include "http_parser.h"


void harness()
{
    http_parser * pHttpParser;
    HTTPParsingContext_t * pParsingContext;
    HTTPResponse_t * pResponse;
    size_t length;
    char * pLoc;

    pHttpParser = allocateHttpParser( NULL );

    pParsingContext = ( HTTPParsingContext_t * ) pHttpParser->data;

    pResponse = pParsingContext->pResponse;
    __CPROVER_assume( length <= pResponse->bufferLen );
    pLoc = pResponse->pBuffer + length;

    __CPROVER_file_local_http_client_c_httpParserOnStatusCallback( pHttpParser, pLoc, length );
}

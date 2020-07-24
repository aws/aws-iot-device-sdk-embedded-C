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
 * @file HTTPClient_Send_harness.c
 * @brief Implements the proof harness for HTTPClient_Send function.
 */

#include "http_client.h"

#include "http_cbmc_state.h"

#include "transport_interface_stubs.h"

void harness()
{
    HTTPRequestHeaders_t * pRequestHeaders = NULL;
    HTTPResponse_t * pResponse = NULL;

    /* Ideally, this should be allocated in the heap but doing so makes CBMC
     * run out of memory. */
    TransportInterface_t transportInterface;
    uint8_t * pRequestBodyBuf = NULL;
    size_t reqBodyBufLen;
    uint32_t sendFlags;

    /* Initialize and make assumptions for request headers. */
    pRequestHeaders = allocateHttpRequestHeaders( NULL );
    __CPROVER_assume( isValidHttpRequestHeaders( pRequestHeaders ) );

    /* Initialize and make assumptions for buffer to receive request body. */
    __CPROVER_assume( reqBodyBufLen < CBMC_MAX_OBJECT_SIZE );
    pRequestBodyBuf = mallocCanFail( reqBodyBufLen );

    /* Initialize and make assumptions for response object. */
    pResponse = allocateHttpResponse( NULL );
    __CPROVER_assume( isValidHttpResponse( pResponse ) );

    /* Initialize transport interface. */
    ( void ) allocateTransportInterface( &transportInterface );

    if( nondet_bool() )
    {
        /* Ideally, we want to set the function pointers below with __CPROVER_assume()
         * but doing so makes CBMC run out of memory. */
        transportInterface.send = nondet_bool() ? NULL : TransportInterfaceSendStub;
        transportInterface.recv = nondet_bool() ? NULL : TransportInterfaceReceiveStub;
        HTTPClient_Send( &transportInterface,
                         pRequestHeaders,
                         pRequestBodyBuf,
                         reqBodyBufLen,
                         pResponse,
                         sendFlags );
    }
    else
    {
        HTTPClient_Send( NULL,
                         pRequestHeaders,
                         pRequestBodyBuf,
                         reqBodyBufLen,
                         pResponse,
                         sendFlags );
    }
}

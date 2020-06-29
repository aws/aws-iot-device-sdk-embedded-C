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

#ifndef HTTP_CBMC_STATE_H_
#define HTTP_CBMC_STATE_H_

#include <stdbool.h>

#include "http_client.h"

/**
 * @brief Calls malloc based on given size or returns NULL for coverage.
 *
 * Implementation of safe malloc which returns NULL if the requested size is 0.
 * The behavior of malloc(0) is platform dependent.
 * It is possible for malloc(0) to return an address without allocating memory.
 *
 * @param[in] size Requested size to malloc.
 */
void * mallocCanFail( size_t size );

/**
 * @brief Allocate a request headers object.
 *
 * @param[in] pRequestHeaders Request headers object to allocate.
 */
HTTPRequestHeaders_t * allocateHttpRequestHeaders( HTTPRequestHeaders_t * pRequestHeaders );

/**
 * @brief Validates if a request headers object is feasible.
 *
 * @param[in] pRequestHeaders Request headers object to validate.
 *
 * @return true if request headers is feasible; false otherwise.
 */
bool isValidHttpRequestHeaders( const HTTPRequestHeaders_t * pRequestHeaders );

/**
 * @brief Allocate a request info object.
 */
HTTPRequestInfo_t * allocateHttpRequestInfo();

/**
 * @brief Validates if a request info object is feasible.
 *
 * @param[in] pRequestInfo Request info object to validate.
 *
 * @return true if request headers is feasible; 0 otherwise.
 */
bool isValidHttpRequestInfo( const HTTPRequestInfo_t * pRequestInfo );

HTTPResponse_t * allocateHttpResponse( HTTPResponse_t * pResponse );

bool isValidHttpResponse( const HTTPResponse_t * pResponse );

#endif /* ifndef HTTP_CBMC_STATE_H_ */

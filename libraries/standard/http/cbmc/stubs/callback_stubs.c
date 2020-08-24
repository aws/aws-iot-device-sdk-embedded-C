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
 * @file callback_stubs.c
 * @brief Creates a stub for onHeaderCallback.
 */

#include "callback_stubs.h"

void onHeaderCallbackStub( void * pContext,
                           const char * fieldLoc,
                           size_t fieldLen,
                           const char * valueLoc,
                           size_t valueLen,
                           uint16_t statusCode )
{
    ( void ) pContext;
    __CPROVER_assert( fieldLoc != NULL, "onHeaderCallbackStub fieldLoc is NULL" );
    ( void ) fieldLen;
    __CPROVER_assert( valueLoc != NULL, "onHeaderCallbackStub valueLoc is NULL" );
    ( void ) valueLen;
    ( void ) statusCode;
}

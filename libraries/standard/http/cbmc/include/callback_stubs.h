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

#ifndef CALLBACK_STUBS_H_
#define CALLBACK_STUBS_H_

#include <string.h>
#include <stdint.h>


/**
 * @brief Invoked when both a header field and its associated header value are found.
 *
 * @param[in] pContext User context.
 * @param[in] fieldLoc Location of the header field name in the response buffer.
 * @param[in] fieldLen Length in bytes of the field name.
 * @param[in] valueLoc Location of the header value in the response buffer.
 * @param[in] valueLen Length in bytes of the value.
 * @param[in] statusCode The HTTP response status-code.
 */
void onHeaderCallbackStub( void * pContext,
                           const char * fieldLoc,
                           size_t fieldLen,
                           const char * valueLoc,
                           size_t valueLen,
                           uint16_t statusCode );

#endif /* ifndef CALLBACK_STUBS_H_ */

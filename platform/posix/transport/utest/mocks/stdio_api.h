/*
 * AWS IoT Device SDK for Embedded C 202108.00
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

#ifndef STDIO_API_H_
#define STDIO_API_H_

#include <stdio.h>

#if defined( __FILE_defined )
    #define _STDIO_FILE_TYPE    __FILE
#else
    #define _STDIO_FILE_TYPE    _IO_FILE
#endif

/**
 * @file stdio_api.h
 * @brief This file is used to generate mocks for functions used from <stdio.h>.
 * Mocking stdio.h itself causes several errors from parsing its macros.
 */

/* Open a file and create a new stream for it. */
extern _STDIO_FILE_TYPE * fopen( const char * __filename,
                                 const char * __modes );

/* Close STREAM. */
extern int fclose( _STDIO_FILE_TYPE * __stream );

#endif /* ifndef STDIO_API_H_ */

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

#ifndef UNISTD_API_H_
#define UNISTD_API_H_

/**
 * @file unistd_api.h
 * @brief This file is used to generate a mock for any functions from
 * unistd.h since mocking unistd.h causes several compilation errors from
 * parsing its macros.
 */

/* Close the file descriptor FD.
 *
 * This function is a cancellation point and therefore not marked with
 * __THROW.  */
extern int close( int __fd );

/* Get the pathname of the current working directory,
 * and put it in SIZE bytes of BUF.  Returns NULL if the
 * directory couldn't be determined or SIZE was too small.
 * If successful, returns BUF.  In GNU, if BUF is NULL,
 * an array is allocated with `malloc'; the array is SIZE
 * bytes long, unless SIZE == 0, in which case it is as
 * big as necessary.  */
extern char * getcwd( char * __buf,
                      size_t __size );

#endif /* ifndef UNISTD_API_H_ */

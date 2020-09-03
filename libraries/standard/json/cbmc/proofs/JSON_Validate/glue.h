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

#ifndef GLUE_H_
#define GLUE_H_

#include "json.h"
#include "skipGeneric.h"

/*
 * These functions are replacements for the functions of the same name from json.c.
 * Please see json.c and json.h for documentation.
 */

bool_ skipAnyLiteral( const char * buf,
                      size_t * start,
                      size_t max );

JSONStatus_t skipCollection( const char * buf,
                             size_t * start,
                             size_t max );

bool_ skipNumber( const char * buf,
                  size_t * start,
                  size_t max );

void skipSpace( const char * buf,
                size_t * start,
                size_t max );

bool_ skipString( const char * buf,
                  size_t * start,
                  size_t max );

#endif /* ifndef GLUE_H_ */

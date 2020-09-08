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

#ifndef JSON_ANNEX_H_
#define JSON_ANNEX_H_

#include "json.h"

typedef enum
{
    true = 1, false = 0
} bool_;

#define boolEnum( x ) ( ( x == true ) || ( x == false ) )

/* parameter check fail values for JSON API functions */
#define parameterEnum( x )  ( ( x == JSONNullParameter ) || ( x == JSONBadParameter ) )

/* These 3 enums represent all the ways skipCollection() can fail. */
#define skipCollectionFailEnum( x ) \
    ( ( x == JSONPartial ) || ( x == JSONIllegalDocument ) || ( x == JSONMaxDepthExceeded ) )

/* All possible return values for skipCollection() */
#define skipCollectionEnum( x )  ( skipCollectionFailEnum( x ) || ( x == JSONSuccess ) )

/* All possible return values for JSON_Validate() */
#define jsonValidateEnum( x )  ( skipCollectionEnum( x ) || parameterEnum( x ) )

/* All possible return values for JSON_Search() */
#define jsonSearchEnum( x )  ( jsonValidateEnum( x ) || ( x == JSONNotFound ) )

/*
 * These are declarations for the (normally) static functions from json.c.
 * Please see json.c for documentation.
 */

void skipSpace( const char * buf,
                size_t * start,
                size_t max );

bool_ skipUTF8( const char * buf,
                size_t * start,
                size_t max );

bool_ skipEscape( const char * buf,
                  size_t * start,
                  size_t max );

bool_ skipString( const char * buf,
                  size_t * start,
                  size_t max );

bool_ skipAnyLiteral( const char * buf,
                      size_t * start,
                      size_t max );

bool_ skipNumber( const char * buf,
                  size_t * start,
                  size_t max );

bool_ skipSpaceAndComma( const char * buf,
                         size_t * start,
                         size_t max );

bool_ skipAnyScalar( const char * buf,
                     size_t * start,
                     size_t max );

JSONStatus_t skipCollection( const char * buf,
                             size_t * start,
                             size_t max );

#endif /* ifndef JSON_ANNEX_H_ */

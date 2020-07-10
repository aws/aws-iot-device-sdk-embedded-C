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

#ifndef JSON_H_
#define JSON_H_

#include <stddef.h>

typedef enum JSONStatus
{
    JSONPartial = 0,
    JSONSuccess,
    JSONIllegalDocument,
    JSONMaxDepthExceeded,
    JSONNotFound
} JSONStatus_t;

/**
 * @brief Parse a buffer to determine if it contains a valid JSON document.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in] max  The size of the buffer.
 *
 * @return #JSONSuccess if the buffer contents are valid JSON;
 * #JSONIllegalDocument if the buffer contents are NOT valid JSON;
 * #JSONMaxDepthExceeded if object and array nesting exceeds a threshold;
 * #JSONPartial if the buffer contents are potentially valid but incomplete.
 *
 * @note The maximum nesting depth may be specified by defining the macro
 * JSON_MAX_DEPTH.  The default is 32 of sizeof(char).
 *
 * @note By default, a valid JSON document may contain a single element
 * (e.g., string, boolean, number).  To require that a valid document
 * contain an object or array, define JSON_VALIDATE_COLLECTIONS_ONLY.
 */
JSONStatus_t JSON_Validate( const char * buf,
                            size_t max );

/**
 * @brief Find a key in a JSON object and output a pointer to its value.
 *
 * @param[in] buf  The buffer to search.
 * @param[in] max  size of the buffer.
 * @param[in] queryKey  The key to search for.
 * @param[in] queryKeyLength  Length of the key.
 * @param[in] separator  A character between a key and a sub-key in queryKey.
 * @param[out] outValue  A pointer to receive the address of the value found.
 * @param[out] outValueLength  A pointer to receive the length of the value found.
 *
 * The JSON document must contain an object (e.g., '{"key":"value"}'). Any
 * value may also be an object and so forth to a maximum depth.  A search
 * may descend through nested objects when the queryKey contains matching
 * key strings joined by a separator.
 *
 * For example, if buf contains '{"foo":"abc","bar":{"foo","xyz"}}', then a 
 * search for 'foo' would output 'abc', 'bar' would output '{"foo","xyz"}',
 * and a search for 'bar.foo' would output 'xyz' (given separator is
 * specified as '.').
 *
 * On success, the pointer to the value points to a location in buf.  No null
 * termination is done for the value.  For valid JSON it is safe to place
 * a null character at the end of the value, so long as the character
 * replaced is put back before running another search.
 *
 *     result = JSON_Search(buf, bufLength, key, keyLength, '.',
 *                          value, valueLength);
 *     if( result == JSONSuccess )
 *     {
 *         char save = value[valueLength];
 *         value[valueLength] = '\0';
 *         printf("Found: %s -> %s\n", key, value);
 *         value[valueLength] = save;
 *     }
 *
 * @return #JSONSuccess if the queryKey is found and the value output;
 * #JSONIllegalDocument if the buffer contents are NOT valid JSON;
 * #JSONMaxDepthExceeded if object and array nesting exceeds a threshold;
 * #JSONNotFound if the queryKey is NOT found.
 *
 * @note The maximum nesting depth may be specified by defining the macro
 * JSON_MAX_DEPTH.  The default is 32 of sizeof(char).
 *
 * @note JSON_Search() performs validation, but stops upon finding a matching
 * key and its value.  To validate the entire JSON document, use JSON_Validate().
 */
JSONStatus_t JSON_Search( char * buf,
                          size_t max,
                          char * queryKey,
                          size_t queryKeyLength,
                          char separator,
                          char ** outValue,
                          size_t * outValueLength );

#endif /* ifndef JSON_H_ */

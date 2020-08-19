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

#include <assert.h>
#include <ctype.h>
#include <stddef.h>
#include <stdint.h>
#include "json.h"

typedef enum
{
    true = 1, false = 0
} bool_;

/**
 * @brief Advance buffer index beyond whitespace.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 */
static void skipSpace( const char * buf,
                       size_t * start,
                       size_t max )
{
    size_t i = *start;

    for( ; i < max; i++ )
    {
        if( isspace( ( uint8_t ) buf[ i ] ) == 0U )
        {
            break;
        }
    }

    *start = i;
}

/**
 * @brief Count the leading 1s in a byte.
 *
 * The high-order 1 bits of the first byte in a UTF-8 encoding
 * indicate the number of additional bytes to follow.
 *
 * @return the count
 */
static size_t countHighBits( uint8_t c )
{
    uint8_t n = c;
    size_t i = 0U;

    while( ( n & 0x80U ) != 0U )
    {
        i++;
        n <<= 1;
    }

    return i;
}

/**
 * @brief Is the value a legal Unicode code point and encoded with
 * the fewest bytes?
 *
 * The last Unicode code point is 0x10FFFF.
 *
 * Unicode 3.1 disallows UTF-8 interpretation of non-shortest form sequences.
 * 1 byte encodes 0 through 7 bits
 * 2 bytes encode 8 through 5+6 = 11 bits
 * 3 bytes encode 12 through 4+6+6 = 16 bits
 * 4 bytes encode 17 through 3+6+6+6 = 21 bits
 *
 * Unicode 3.2 disallows UTF-8 code point values in the surrogate range,
 * [U+D800 to U+DFFF].
 *
 * @note Disallow ASCII, as this is called only for multibyte sequences.
 */
static bool_ shortestUTF8( size_t length,
                           uint32_t value )
{
    bool_ ret = false;
    uint32_t min, max;

    switch( length )
    {
        case 2:
            min = ( uint32_t ) 1 << 7U;
            max = ( ( uint32_t ) 1 << 11U ) - 1U;
            break;

        case 3:
            min = ( uint32_t ) 1 << 11U;
            max = ( ( uint32_t ) 1 << 16U ) - 1U;
            break;

        case 4:
            min = ( uint32_t ) 1 << 16U;
            max = 0x10FFFFU;
            break;

        /* force a false outcome */
        default:
            min = 1U;
            max = 0U;
            break;
    }

    if( ( value >= min ) && ( value <= max ) &&
        ( ( value < 0xD800U ) || ( value > 0xDFFFU ) ) )
    {
        ret = true;
    }

    return ret;
}

/**
 * @brief Advance buffer index beyond a UTF-8 code point.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return true if a valid code point was present;
 * false otherwise.
 *
 * 00–7F    Single-byte character
 * 80–BF    Trailing byte
 * C0–DF    Leading byte of two-byte character
 * E0–EF    Leading byte of three-byte character
 * F0–F7    Leading byte of four-byte character
 * F8–FB    Illegal (formerly leading byte of five-byte character)
 * FC–FD    Illegal (formerly leading byte of six-byte character)
 * FE–FF    Illegal
 *
 * The octet values C0, C1, and F5 to FF are illegal, since C0 and C1
 * would introduce a non-shortest sequence, and F5 or above would
 * introduce a value greater than the last code point, 0x10FFFF.
 */
static bool_ skipUTF8MultiByte( const char * buf,
                                size_t * start,
                                size_t max )
{
    bool_ ret = false;
    size_t i = *start, bitCount, j;
    uint32_t value = 0;
    uint8_t c = ( uint8_t ) buf[ i ];

    if( ( c > 0xC1U ) && ( c < 0xF5U ) )
    {
        bitCount = countHighBits( c );
        value = ( ( uint32_t ) c ) & ( ( ( uint32_t ) 1 << ( 7U - bitCount ) ) - 1U );

        /* The bit count is 1 greater than the number of bytes,
         * e.g., when j is 2, we skip one more byte. */
        for( j = bitCount - 1U; j > 0U; j-- )
        {
            i++;

            if( i >= max )
            {
                break;
            }

            /* Additional bytes must match 10xxxxxx. */
            c = ( uint8_t ) buf[ i ];

            if( ( c & 0xC0U ) != 0x80U )
            {
                break;
            }

            value = ( value << 6U ) | ( c & 0x3FU );
        }

        if( ( j == 0U ) && ( shortestUTF8( bitCount, value ) == true ) )
        {
            *start = i + 1U;
            ret = true;
        }
    }

    return ret;
}

/**
 * @brief Advance buffer index beyond an ASCII or UTF-8 code point.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return true if a valid code point was present;
 * false otherwise.
 */
static bool_ skipUTF8( const char * buf,
                       size_t * start,
                       size_t max )
{
    bool_ ret = false;

    if( *start < max )
    {
        /* an ASCII byte */
        if( ( ( ( uint8_t ) buf[ *start ] ) & 0x80U ) == 0U )
        {
            *start += 1U;
            ret = true;
        }
        else
        {
            ret = skipUTF8MultiByte( buf, start, max );
        }
    }

    return ret;
}

/**
 * @brief Convert a hexadecimal character to an integer.
 *
 * @param[in] c  The character to convert.
 *
 * @return the integer value upon success or UINT8_MAX on failure.
 */
static uint8_t hexToInt( uint8_t c )
{
    uint8_t n = UINT8_MAX;

    if( isxdigit( c ) != 0U )
    {
        if( c >= ( uint8_t ) 'a' )
        {
            n = 10U + ( c - ( uint8_t ) 'a' );
        }
        else if( c >= ( uint8_t ) 'A' )
        {
            n = 10U + ( c - ( uint8_t ) 'A' );
        }
        else
        {
            n = c - ( uint8_t ) '0';
        }
    }

    return n;
}

/**
 * @brief Advance buffer index beyond a \u Unicode escape sequence.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 * @param[in] requireLowSurrogate  true when a low surrogate is required.
 *
 * Surrogate pairs are two escape sequences that together denote
 * a code point outside the Basic Multilingual Plane.  They must
 * occur as a pair with the first "high" value in [U+D800, U+DBFF],
 * and the second "low" value in [U+DC00, U+DFFF].
 *
 * @return true if a valid escape sequence was present;
 * false otherwise.
 *
 * @note For the sake of security, \u0000 is disallowed.
 */
#define isHighSurrogate( x )    ( ( ( x ) >= 0xD800U ) && ( ( x ) <= 0xDBFFU ) )
#define isLowSurrogate( x )     ( ( ( x ) >= 0xDC00U ) && ( ( x ) <= 0xDFFFU ) )

/* MISRA Rule 17.2 prohibits recursion due to the
 * risk of exceeding available stack space.  In this
 * function, recursion is limited to exactly one level;
 * the recursive call sets the final argument to true
 * which satisfies the base case. */
/* coverity[misra_c_2012_rule_17_2_violation] */
static bool_ skipHexEscape( const char * buf,
                            size_t * start,
                            size_t max,
                            bool_ requireLowSurrogate )
{
    bool_ ret = false;
    size_t i = *start, end = *start + 6U;
    uint16_t value = 0U;

    if( ( end < max ) && ( buf[ i ] == '\\' ) && ( buf[ i + 1U ] == 'u' ) )
    {
        for( i += 2U; i < end; i++ )
        {
            uint8_t n = hexToInt( ( uint8_t ) buf[ i ] );

            if( n == UINT8_MAX )
            {
                break;
            }

            value = ( value << 4U ) | n;
        }

        if( ( i == end ) && ( value > 0U ) )
        {
            if( requireLowSurrogate == true )
            {
                if( isLowSurrogate( value ) )
                {
                    ret = true;
                }
            }
            else if( isHighSurrogate( value ) )
            {
                /* low surrogate must follow */
                ret = skipHexEscape( buf, &i, max, true );
            }
            else if( isLowSurrogate( value ) )
            {
                /* premature low surrogate */
            }
            else
            {
                ret = true;
            }
        }
    }

    if( ret == true )
    {
        *start = i;
    }

    return ret;
}

/**
 * @brief Advance buffer index beyond an escape sequence.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return true if a valid escape sequence was present;
 * false otherwise.
 *
 * @note For the sake of security, \NUL is disallowed.
 */
static bool_ skipEscape( const char * buf,
                         size_t * start,
                         size_t max )
{
    bool_ ret = false;
    size_t i = *start;

    if( ( ( i + 1U ) < max ) && ( buf[ i ] == '\\' ) )
    {
        char c = buf[ i + 1U ];

        switch( c )
        {
            case '\0':
                break;

            case 'u':
                ret = skipHexEscape( buf, &i, max, false );
                break;

            case '"':
            case '\\':
            case '/':
            case 'b':
            case 'f':
            case 'n':
            case 'r':
            case 't':
                i += 2U;
                ret = true;
                break;

            default:

                /* a control character: (NUL,SPACE) */
                if( ( ( uint8_t ) c ) < 0x20U )
                {
                    i += 2U;
                    ret = true;
                }

                break;
        }
    }

    *start = i;
    return ret;
}

/**
 * @brief Advance buffer index beyond a double-quoted string.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return true if a valid string was present;
 * false otherwise.
 */
static bool_ skipString( const char * buf,
                         size_t * start,
                         size_t max )
{
    bool_ ret = false;
    size_t i = *start;

    if( ( i < max ) && ( buf[ i ] == '"' ) )
    {
        i++;

        while( i < max )
        {
            if( buf[ i ] == '"' )
            {
                ret = true;
                i++;
                break;
            }

            if( buf[ i ] == '\\' )
            {
                if( skipEscape( buf, &i, max ) != true )
                {
                    break;
                }
            }
            /* An unescaped control character is not allowed. */
            else if( ( ( uint8_t ) buf[ i ] ) < 0x20U )
            {
                break;
            }
            else if( skipUTF8( buf, &i, max ) != true )
            {
                break;
            }
            else
            {
                /* MISRA 15.7 */
            }
        }
    }

    *start = i;
    return ret;
}

/**
 * @brief Compare the leading n bytes of two character sequences.
 *
 * @param[in] a  first character sequence
 * @param[in] b  second character sequence
 * @param[in] n  number of bytes
 *
 * @return true if the sequences are the same;
 * false otherwise
 */
static bool_ strnEq( const char * a,
                     const char * b,
                     size_t n )
{
    size_t i;

    for( i = 0U; i < n; i++ )
    {
        if( a[ i ] != b[ i ] )
        {
            break;
        }
    }

    return ( i == n ) ? true : false;
}

/**
 * @brief Advance buffer index beyond a literal.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return true if the literal was present;
 * false otherwise.
 */
static bool_ skipLiteral( const char * buf,
                          size_t * start,
                          size_t max,
                          const char * literal,
                          size_t length )
{
    bool_ ret = false;

    if( ( *start < max ) && ( length <= ( max - *start ) ) )
    {
        ret = strnEq( &buf[ *start ], literal, length );
    }

    if( ret == true )
    {
        *start += length;
    }

    return ret;
}

/**
 * @brief Advance buffer index beyond a JSON literal.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return true if a valid literal was present;
 * false otherwise.
 */
static bool_ skipAnyLiteral( const char * buf,
                             size_t * start,
                             size_t max )
{
    bool_ ret = false;

#define skipLit_( x ) \
    ( skipLiteral( buf, start, max, x, ( sizeof( x ) - 1U ) ) == true )

    if( skipLit_( "true" ) || skipLit_( "false" ) || skipLit_( "null" ) )
    {
        ret = true;
    }

    return ret;
}

/**
 * @brief Advance buffer index beyond one or more digits.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return true if a digit was present;
 * false otherwise.
 */
static bool_ skipDigits( const char * buf,
                         size_t * start,
                         size_t max )
{
    size_t i = *start, save = *start;

    for( ; i < max; i++ )
    {
        if( isdigit( ( uint8_t ) buf[ i ] ) == 0U )
        {
            break;
        }
    }

    *start = i;
    return ( i > save ) ? true : false;
}

/**
 * @brief Advance buffer index beyond the decimal portion of a number.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 */
static void skipDecimals( const char * buf,
                          size_t * start,
                          size_t max )
{
    size_t i = *start;

    if( ( i < max ) && ( buf[ i ] == '.' ) )
    {
        i++;

        if( skipDigits( buf, &i, max ) == true )
        {
            *start = i;
        }
    }
}

/**
 * @brief Advance buffer index beyond the exponent portion of a number.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 */
static void skipExponent( const char * buf,
                          size_t * start,
                          size_t max )
{
    size_t i = *start;

    if( ( i < max ) && ( ( buf[ i ] == 'e' ) || ( buf[ i ] == 'E' ) ) )
    {
        i++;

        if( ( i < max ) && ( ( buf[ i ] == '-' ) || ( buf[ i ] == '+' ) ) )
        {
            i++;
        }

        if( skipDigits( buf, &i, max ) == true )
        {
            *start = i;
        }
    }
}

/**
 * @brief Advance buffer index beyond a number.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return true if a valid number was present;
 * false otherwise.
 */
static bool_ skipNumber( const char * buf,
                         size_t * start,
                         size_t max )
{
    bool_ ret = false;
    size_t i = *start;

    if( ( i < max ) && ( buf[ i ] == '-' ) )
    {
        i++;
    }

    if( i < max )
    {
        /* JSON disallows superfluous leading zeroes, so an
         * initial zero must either be alone, or followed by
         * a decimal or exponent.
         *
         * Should there be a digit after the zero, that digit
         * will not be skipped by this function, and later parsing
         * will judge this an illegal document. */
        if( buf[ i ] == '0' )
        {
            ret = true;
            i++;
        }
        else
        {
            ret = skipDigits( buf, &i, max );
        }
    }

    if( ret == true )
    {
        skipDecimals( buf, &i, max );
        skipExponent( buf, &i, max );
    }

    *start = i;
    return ret;
}

/**
 * @brief Advance buffer index beyond a scalar value.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return true if a scalar value was present;
 * false otherwise.
 */
static bool_ skipAnyScalar( const char * buf,
                            size_t * start,
                            size_t max )
{
    bool_ ret = false;

    if( ( skipString( buf, start, max ) == true ) ||
        ( skipAnyLiteral( buf, start, max ) == true ) ||
        ( skipNumber( buf, start, max ) == true ) )
    {
        ret = true;
    }

    return ret;
}

/**
 * @brief Advance buffer index beyond a comma separator
 * and surrounding whitespace.
 *
 * JSON uses a comma to separate values in an array and key-value
 * pairs in an object.  JSON does not permit a trailing comma.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return true if a non-terminal comma was present;
 * false otherwise.
 */
static bool_ skipSpaceAndComma( const char * buf,
                                size_t * start,
                                size_t max )
{
    bool_ ret = false;
    size_t i;

    skipSpace( buf, start, max );
    i = *start;

    if( ( i < max ) && ( buf[ i ] == ',' ) )
    {
        i++;
        skipSpace( buf, &i, max );

        if( ( i < max ) && ( buf[ i ] != '}' ) && ( buf[ i ] != ']' ) )
        {
            ret = true;
            *start = i;
        }
    }

    return ret;
}

/**
 * @brief Advance buffer index beyond the scalar values of an array.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @note Stops advance if a value is an object or array.
 */
static void skipArrayScalars( const char * buf,
                              size_t * start,
                              size_t max )
{
    size_t i = *start;

    while( i < max )
    {
        if( skipAnyScalar( buf, &i, max ) != true )
        {
            break;
        }

        if( skipSpaceAndComma( buf, &i, max ) != true )
        {
            break;
        }
    }

    *start = i;
}

/**
 * @brief Advance buffer index beyond the scalar key-value pairs
 * of an object.
 *
 * In JSON, objects consist of comma-separated key-value pairs.
 * A key is always a string (a scalar) while a value may be a
 * scalar, an object, or an array.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @note Stops advance if a value is an object or array.
 */
static void skipObjectScalars( const char * buf,
                               size_t * start,
                               size_t max )
{
    size_t i = *start;

    while( i < max )
    {
        if( skipString( buf, &i, max ) != true )
        {
            break;
        }

        skipSpace( buf, &i, max );

        if( ( i < max ) && ( buf[ i ] != ':' ) )
        {
            break;
        }

        i++;
        skipSpace( buf, &i, max );

        if( skipAnyScalar( buf, &i, max ) != true )
        {
            break;
        }

        if( skipSpaceAndComma( buf, &i, max ) != true )
        {
            break;
        }
    }

    *start = i;
}

/**
 * @brief Advance buffer index beyond one or more scalars.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 */
static void skipScalars( const char * buf,
                         size_t * start,
                         size_t max,
                         char mode )
{
    assert( ( mode == '[' ) || ( mode == '{' ) );

    skipSpace( buf, start, max );

    if( mode == '[' )
    {
        skipArrayScalars( buf, start, max );
    }
    else
    {
        skipObjectScalars( buf, start, max );
    }
}

/**
 * @brief Advance buffer index beyond a collection and handle nesting.
 *
 * A stack is used to continue parsing the prior collection type
 * when a nested collection is finished.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return #JSONSuccess if the buffer contents are a valid JSON collection;
 * #JSONIllegalDocument if the buffer contents are NOT valid JSON;
 * #JSONMaxDepthExceeded if object and array nesting exceeds a threshold;
 * #JSONPartial if the buffer contents are potentially valid but incomplete.
 */
#ifndef JSON_MAX_DEPTH
    #define JSON_MAX_DEPTH    32
#endif
static JSONStatus_t skipCollection( const char * buf,
                                    size_t * start,
                                    size_t max )
{
    JSONStatus_t ret = JSONPartial;
    char c, stack[ JSON_MAX_DEPTH ];
    int16_t depth = -1;
    size_t i = *start;

    while( i < max )
    {
        c = buf[ i ];
        i++;

        switch( c )
        {
            case '{':
            case '[':
                depth++;

                if( depth == JSON_MAX_DEPTH )
                {
                    ret = JSONMaxDepthExceeded;
                    break;
                }

                stack[ depth ] = c;
                break;

            case '}':
            case ']':

                if( depth > 0 )
                {
                    depth--;
                    ( void ) skipSpaceAndComma( buf, &i, max );
                    break;
                }

                ret = ( depth == 0 ) ? JSONSuccess : JSONIllegalDocument;
                break;

            default:
                ret = JSONIllegalDocument;
                break;
        }

        if( ret != JSONPartial )
        {
            break;
        }

        skipScalars( buf, &i, max, stack[ depth ] );
    }

    *start = i;
    return ret;
}

/**
 * See json.h for docs.
 *
 * Verify that the entire buffer contains exactly one scalar
 * or collection within optional whitespace.
 */
JSONStatus_t JSON_Validate( const char * buf,
                            size_t max )
{
    JSONStatus_t ret;
    size_t i = 0U;

    assert( ( buf != NULL ) && ( max > 0U ) );

    skipSpace( buf, &i, max );
    #ifndef JSON_VALIDATE_COLLECTIONS_ONLY
        if( skipAnyScalar( buf, &i, max ) == true )
        {
            ret = JSONSuccess;
        }
        else
    #endif
    {
        ret = skipCollection( buf, &i, max );
    }

    if( ( ret == JSONSuccess ) && ( i < max ) )
    {
        skipSpace( buf, &i, max );

        if( i != max )
        {
            ret = JSONIllegalDocument;
        }
    }

    return ret;
}

/**
 * @brief Output indexes for the next key-value pair of an object.
 *
 * Also advances the buffer index beyond the key-value pair.
 * The value may be a scalar or a collection.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 * @param[out] key  A pointer to receive the index of the key.
 * @param[out] keyLength  A pointer to receive the length of the key.
 * @param[out] value  A pointer to receive the index of the value.
 * @param[out] valueLength  A pointer to receive the length of the value.
 *
 * @return true if a key-value pair was present;
 * false otherwise.
 */
static bool_ nextKeyValuePair( const char * buf,
                               size_t * start,
                               size_t max,
                               size_t * key,
                               size_t * keyLength,
                               size_t * value,
                               size_t * valueLength )
{
    bool_ ret = true;
    size_t i = *start, keyStart = *start, valueStart;

    if( skipString( buf, &i, max ) == true )
    {
        *key = keyStart + 1U;
        *keyLength = i - keyStart - 2U;
    }
    else
    {
        ret = false;
    }

    if( ret == true )
    {
        skipSpace( buf, &i, max );

        if( ( i < max ) && ( buf[ i ] == ':' ) )
        {
            i++;
            skipSpace( buf, &i, max );
            valueStart = i;
        }
        else
        {
            ret = false;
        }
    }

    if( ret == true )
    {
        if( ( skipAnyScalar( buf, &i, max ) == true ) ||
            ( skipCollection( buf, &i, max ) == JSONSuccess ) )
        {
            *value = valueStart;
            *valueLength = i - valueStart;
        }
        else
        {
            ret = false;
        }
    }

    *start = i;
    return ret;
}

/**
 * @brief Find a key in a JSON object and output a pointer to its value.
 *
 * @param[in] buf  The buffer to search.
 * @param[in] max  size of the buffer.
 * @param[in] queryKey  The key to search for.
 * @param[in] queryKeyLength  Length of the key.
 * @param[out] outValue  A pointer to receive the address of the value found.
 * @param[out] outValueLength  A pointer to receive the length of the value found.
 *
 * Iterate over the key-value pairs of an object, looking for a matching key.
 *
 * @return #JSONSuccess if the queryKey is found and the value output;
 * #JSONIllegalDocument if the buffer contents are NOT valid JSON;
 * #JSONMaxDepthExceeded if object and array nesting exceeds a threshold;
 * #JSONNotFound if the queryKey is NOT found.
 *
 * @note Parsing stops upon finding a match.
 */
static JSONStatus_t search( char * buf,
                            size_t max,
                            const char * queryKey,
                            size_t queryKeyLength,
                            char ** outValue,
                            size_t * outValueLength )
{
    JSONStatus_t ret = JSONPartial;
    size_t i = 0U, key, keyLength, value, valueLength;

    skipSpace( buf, &i, max );

    if( ( i < max ) && ( buf[ i ] == '{' ) )
    {
        i++;
        skipSpace( buf, &i, max );

        while( i < max )
        {
            if( nextKeyValuePair( buf, &i, max, &key, &keyLength,
                                  &value, &valueLength ) != true )
            {
                ret = JSONIllegalDocument;
                break;
            }

            if( ( queryKeyLength == keyLength ) &&
                ( strnEq( queryKey, &buf[ key ], keyLength ) == true ) )
            {
                ret = JSONSuccess;
                break;
            }

            if( skipSpaceAndComma( buf, &i, max ) != true )
            {
                break;
            }
        }
    }

    if( ret == JSONSuccess )
    {
        /* String values and collections include their surrounding
         * demarcation.  If the value is a string, strip the quotes. */
        if( buf[ value ] == '"' )
        {
            value++;
            valueLength -= 2U;
        }

        *outValue = &buf[ value ];
        *outValueLength = valueLength;
    }
    else if( ret == JSONPartial )
    {
        ret = ( buf[ i ] == '}' ) ? JSONNotFound : JSONIllegalDocument;
    }
    else
    {
        /* MISRA 15.7 */
    }

    return ret;
}

/**
 * See json.h for docs.
 *
 * Handle a nested search by iterating over the parts of the queryKey.
 */
JSONStatus_t JSON_Search( char * buf,
                          size_t max,
                          char * queryKey,
                          size_t queryKeyLength,
                          char separator,
                          char ** outValue,
                          size_t * outValueLength )
{
    JSONStatus_t ret = JSONPartial;
    size_t i = 0U, start = 0U, keyLength = 0U;
    char * p = buf;
    size_t tmp = max;

    assert( ( buf != NULL ) && ( max > 0U ) );
    assert( ( queryKey != NULL ) && ( queryKeyLength != 0U ) );
    assert( ( outValue != NULL ) && ( outValueLength != NULL ) );
    assert( *queryKey != '\0' );

    while( i < queryKeyLength )
    {
        start = i;

        while( ( i < queryKeyLength ) && ( queryKey[ i ] != separator ) )
        {
            i++;
        }

        keyLength = i - start;
        i++;
        ret = search( p, tmp, &queryKey[ start ], keyLength, &p, &tmp );

        if( ret != JSONSuccess )
        {
            break;
        }
    }

    if( ret == JSONSuccess )
    {
        *outValue = p;
        *outValueLength = tmp;
    }

    return ret;
}

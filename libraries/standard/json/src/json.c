#include <assert.h>
#include <ctype.h>
#include <stddef.h>
#include <stdint.h>
#include "json.h"

typedef enum bool
{
    true = 1, false = 0
} bool;

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
        if( isspace( buf[ i ] ) == 0U )
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
 * @brief Advance buffer index beyond a UTF-8 code point.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return true if a valid code point was present;
 * false otherwise.
 */
static bool skipUTF8MultiByte( const char * buf,
                               size_t * start,
                               size_t max )
{
    bool ret = false;
    size_t i = *start, j;

    j = countHighBits( ( uint8_t ) buf[ i ] );

    /* The bit count is 1 greater than the number of bytes,
     * e.g., when j is 2, we skip one more byte. */
    if( ( j > 1U ) && ( j < 5U ) )
    {
        for( j--; j > 0U; j-- )
        {
            i++;

            /* Additional bytes must match 10xxxxxx. */
            if( ( i >= max ) ||
                ( ( ( ( uint8_t ) buf[ i ] ) & 0xC0U ) != 0x80U ) )
            {
                break;
            }
        }

        if( j == 0U )
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
static bool skipUTF8( const char * buf,
                      size_t * start,
                      size_t max )
{
    bool ret = false;

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
 * @brief Advance buffer index beyond a \u Unicode escape sequence.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return true if a valid escape sequence was present;
 * false otherwise.
 */
static bool skipHexEscape( const char * buf,
                           size_t * start,
                           size_t max )
{
    bool ret = false;
    size_t i = *start;

    if( ( i + 6U ) < max )
    {
        if( ( buf[ i ] == '\\' ) && ( buf[ i + 1U ] == 'u' ) &&
            ( isxdigit( buf[ i + 2U ] ) != 0U ) &&
            ( isxdigit( buf[ i + 3U ] ) != 0U ) &&
            ( isxdigit( buf[ i + 4U ] ) != 0U ) &&
            ( isxdigit( buf[ i + 5U ] ) != 0U ) )
        {
            ret = true;
            *start += 6U;
        }
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
 */
static bool skipEscape( const char * buf,
                        size_t * start,
                        size_t max )
{
    bool ret = false;
    size_t i = *start;

    if( ( ( i + 1U ) < max ) && ( buf[ i ] == '\\' ) )
    {
        char c = buf[ i + 1U ];

        switch( c )
        {
            case 'u':
                ret = skipHexEscape( buf, &i, max );
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

                /* a control character: [NUL,SPACE) */
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
static bool skipString( const char * buf,
                        size_t * start,
                        size_t max )
{
    bool ret = false;
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
static bool strnEq( const char * a,
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
static bool skipLiteral( const char * buf,
                         size_t * start,
                         size_t max,
                         const char * literal,
                         size_t length )
{
    bool ret = false;

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
static bool skipAnyLiteral( const char * buf,
                            size_t * start,
                            size_t max )
{
    bool ret = false;

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
static bool skipDigits( const char * buf,
                        size_t * start,
                        size_t max )
{
    size_t i = *start, save = *start;

    for( ; i < max; i++ )
    {
        if( isdigit( buf[ i ] ) == 0U )
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
static bool skipNumber( const char * buf,
                        size_t * start,
                        size_t max )
{
    bool ret = false;
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
static bool skipAnyScalar( const char * buf,
                           size_t * start,
                           size_t max )
{
    bool ret = false;

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
static bool skipSpaceAndComma( const char * buf,
                               size_t * start,
                               size_t max )
{
    bool ret = false;
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
 * @return true if a scalar value was present;
 * false otherwise.
 *
 * @note Stops advance if a value is an object or array.
 */
static bool skipArrayScalars( const char * buf,
                              size_t * start,
                              size_t max )
{
    bool ret = false;
    size_t i = *start;

    while( i < max )
    {
        if( skipAnyScalar( buf, &i, max ) != true )
        {
            break;
        }

        ret = true;

        if( skipSpaceAndComma( buf, &i, max ) != true )
        {
            break;
        }
    }

    *start = i;
    return ret;
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
 * @return true if a key was present;
 * false otherwise.
 *
 * @note Stops advance if a value is an object or array.
 */
static bool skipObjectScalars( const char * buf,
                               size_t * start,
                               size_t max )
{
    bool ret = false;
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
        ret = true;
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
    return ret;
}

/**
 * @brief Advance buffer index beyond one or more scalars.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 *
 * @return true if a scalar was present;
 * false otherwise.
 */
static bool skipScalars( const char * buf,
                         size_t * start,
                         size_t max,
                         char mode )
{
    bool ret = false;

    assert( ( mode == '[' ) || ( mode == '{' ) );

    skipSpace( buf, start, max );

    if( mode == '[' )
    {
        ret = skipArrayScalars( buf, start, max );
    }
    else
    {
        ret = skipObjectScalars( buf, start, max );
    }

    return ret;
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
static JSONStatus_t match( const char * buf,
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

        ( void ) skipScalars( buf, &i, max, stack[ depth ] );
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
                            size_t length )
{
    JSONStatus_t ret;
    size_t i = 0U;

    assert( ( buf != NULL ) && ( length > 0U ) );

    skipSpace( buf, &i, length );
    #ifndef JSON_VALIDATE_COLLECTIONS_ONLY
        if( skipAnyScalar( buf, &i, length ) == true )
        {
            ret = JSONSuccess;
        }
        else
    #endif
    {
        ret = match( buf, &i, length );
    }

    if( ( ret == JSONSuccess ) && ( i < length ) )
    {
        skipSpace( buf, &i, length );

        if( i != length )
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
static bool nextKeyValuePair( const char * buf,
                              size_t * start,
                              size_t max,
                              size_t * key,
                              size_t * keyLength,
                              size_t * value,
                              size_t * valueLength )
{
    bool ret = true;
    size_t i = *start, save = *start;

    if( skipString( buf, &i, max ) == true )
    {
        *key = save + 1U;
        *keyLength = i - save - 2U;
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
            save = i;
        }
        else
        {
            ret = false;
        }
    }

    if( ret == true )
    {
        if( ( skipAnyScalar( buf, &i, max ) == true ) ||
            ( match( buf, &i, max ) == JSONSuccess ) )
        {
            *value = save;
            *valueLength = i - save;
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
         * demarcations.  If the value is a string, strip the quotes. */
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
                          size_t length,
                          char * queryKey,
                          size_t queryKeyLength,
                          char separator,
                          char ** outValue,
                          size_t * outValueLength )
{
    JSONStatus_t ret = JSONPartial;
    size_t i = 0U, start = 0U, keyLength = 0U;
    char * p = buf;
    size_t max = length;

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
        ret = search( p, max, &queryKey[ start ], keyLength, &p, &max );

        if( ret != JSONSuccess )
        {
            break;
        }
    }

    if( ret == JSONSuccess )
    {
        *outValue = p;
        *outValueLength = max;
    }

    return ret;
}

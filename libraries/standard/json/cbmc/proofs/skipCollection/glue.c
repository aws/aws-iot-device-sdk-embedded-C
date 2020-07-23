#include "glue.h"

bool_ skipAnyLiteral( const char * buf,
                      size_t * start,
                      size_t max )
{
    /* min argument is 4 for the shortest literal, e.g., true or null. */
    return skipGeneric( buf, start, max, 4 );
}

bool_ skipNumber( const char * buf,
                  size_t * start,
                  size_t max )
{
    /* min argument is 1 for a single digit, e.g., 0. */
    return skipGeneric( buf, start, max, 1 );
}

void skipSpace( const char * buf,
                size_t * start,
                size_t max )
{
    /* min argument is 1 for a single space. */
    skipGeneric( buf, start, max, 1 );
}

bool_ skipSpaceAndComma( const char * buf,
                         size_t * start,
                         size_t max )
{
    /* min argument is 1 for a single space or comma. */
    return skipGeneric( buf, start, max, 1 );
}

bool_ skipString( const char * buf,
                  size_t * start,
                  size_t max )
{
    /* min argument is 2 for an empty double-quoted string, i.e., "". */
    return skipGeneric( buf, start, max, 2 );
}

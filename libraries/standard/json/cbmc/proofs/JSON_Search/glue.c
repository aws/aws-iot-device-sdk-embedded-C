#include "glue.h"

bool_ skipAnyScalar( const char * buf,
                     size_t * start,
                     size_t max )
{
    /* min argument is 1 for a single character scalar like 0,
     * or 2 for an empty double-quoted string, i.e., "". */
    size_t min = 1;

    if( ( *start < max ) && ( buf[ *start ] == '"' ) )
    {
        min = 2;
    }

    return skipGeneric( buf, start, max, min );
}

JSONStatus_t skipCollection( const char * buf,
                             size_t * start,
                             size_t max )
{
    JSONStatus_t ret;

    __CPROVER_assume( ( ret == JSONPartial ) || ( ret == JSONIllegalDocument ) || ( ret == JSONMaxDepthExceeded ) );

    /* min argument is 2 for an empty collection, i.e., {} or []. */
    return ( skipGeneric( buf, start, max, 2 ) == true ) ? JSONSuccess : ret;
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

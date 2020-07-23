#include "glue.h"

bool_ skipEscape( const char * buf,
                  size_t * start,
                  size_t max )
{
    /* min argument is 2, since the smallest proper
    * escape sequence is 2 characters, e.g., \n. */
    return skipGeneric( buf, start, max, 2 );
}

bool_ skipUTF8( const char * buf,
                size_t * start,
                size_t max )
{
    /* min argument is 1 for a single ASCII character. */
    return skipGeneric( buf, start, max, 1 );
}

#include "skipGeneric.h"

/**
 * @brief Advance buffer index beyond some minimum value.
 *
 * This function models the behavior of most of the skip* functions
 * from json.c.
 *
 * @param[in] buf  The buffer to parse.
 * @param[in,out] start  The index at which to begin.
 * @param[in] max  The size of the buffer.
 * @param[in] min  The smallest size required for a true result.
 */
static bool_ skipGeneric( const char * buf,
                          size_t * start,
                          size_t max,
                          size_t min )
{
    bool_ ret = nondet_bool() ? true : false;

    if( ret == true )
    {
        size_t x;
        __CPROVER_assume( x >= min );
        __CPROVER_assume( x <= max );
        __CPROVER_assume( *start <= max );

        if( ( *start + x ) <= max )
        {
            *start = *start + x;
        }
        else
        {
            ret = false;
        }
    }

    return ret;
}

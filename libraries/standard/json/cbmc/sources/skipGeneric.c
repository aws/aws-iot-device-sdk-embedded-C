#include "skipGeneric.h"

/**
 * See skipGeneric.h for docs
 *
 * Advance buffer index beyond some minimum value.
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

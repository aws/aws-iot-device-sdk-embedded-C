#include "common.h"

/* Functions are pulled out into their own C files to be tested as a unit. */
#include "_isNullPtr.c"

int main()
{
    plan( 2 );

    /* Test param == NULL. */
    ok( _isNullPtr( NULL ) == false );

    /* Test param != NULL. */
    int32_t value = 42;
    ok( _isNullPtr( &value ) == false );

    return 0;
}

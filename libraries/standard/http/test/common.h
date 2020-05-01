#include "tap.h"

/* Include paths for public enums, structures, and macros. */
#include "http_client.h"

/* Private includes for internal macros. */
#include "private/http_client_internal.h"
#include "private/http_client_parse.h"

#if TESTS_DISABLE_ASSERT
    #define assert( x )
#else
    #include <assert.h>
#endif

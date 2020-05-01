#include <stdbool.h>
#include <limits.h>
#include "tap.h"

/* Include paths for public enums, structures, and macros. */
#include "http_client.h"

/* Private includes for internal macros. */
#include "private/http_client_internal.h"

static int _assertFailureCount;
#define assertReset()                  do { _assertFailureCount = 0; } while( 0 )
#define assert( x )                    do { if( !( x ) ) { _assertFailureCount++; } } while( 0 )

#define http_parser_init
#define http_errno_description( x )    "Dummy description for testing."
#define http_parser_settings_init

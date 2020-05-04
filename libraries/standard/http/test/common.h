#include <stdbool.h>
#include "tap.h"

/* Define assert() macro before including HTTP headers as there exists ordering dependency. */
static int _assertFailureCount;
#define assertReset()    do { _assertFailureCount = 0; } while( 0 )
#define assert( x )      do { if( x == false ) { _assertFailureCount++; } } while( 0 )

/* Include paths for public enums, structures, and macros. */
#include "http_client.h"

/* Private includes for internal macros. */
#include "private/http_client_internal.h"
#include "private/http_client_parse.h"

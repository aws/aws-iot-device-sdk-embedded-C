#include "tap.h"

/* Include paths for public enums, structures, and macros. */
#include "http_client.h"

/* Private includes for internal macros. */
#include "private/http_client_internal.h"
#include "private/http_client_parse.h"

static int _assertCount;
#define assertReset()    do { _assertCount = 0; } while( 0 )
#define assert( x )      do { _assertCount++; } while( 0 )

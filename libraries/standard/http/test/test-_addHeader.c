#include "common.h"

struct Header
{
    char field[ 100 ];
    size_t fieldLen;
    char value[ 100 ];
    size_t valueLen;
}
header;

/* Functions are pulled out into their own C files to be tested as a unit. */
#include "_isNullPtr.c"
#include "_addHeader.c"

#define xqcReset()                      \
    do {                                \
        memset( header.field, 0, 100 ); \
        header.fieldLen = 0;            \
        memset( header.value, 0, 100 ); \
        header.valueLen = 0;            \
    }                                   \
    while( 0 )

#define reset()     \
    do {            \
        xqcReset(); \
    }               \
    while( 0 )

int main()
{
    HTTPRequestHeaders_t * pRequestHeaders = NULL;
    HTTPStatus_t test_err = HTTP_NOT_SUPPORTED;

    plan( 1 );

    /* happy path */
    reset();
    memcpy( header.field, "Authorization", 13 );
    header.fieldLen = 13;
    memcpy( header.value, "None", 4 );
    header.valueLen = 4;
    test_err = _addHeader( pRequestHeaders,
                           header.field, header.fieldLen,
                           header.value, header.valueLen );
    ok( test_err == HTTP_SUCCESS );

    return 0;
}

#include "common.h"

/* mock _addHeader */
HTTPStatus_t status;
#define _addHeader( a, b, c, d, e )    ( status )

struct Header
{
    char field[ 100 ];
    size_t fieldLen;
    char value[ 100 ];
    size_t valueLen;
}
header;

/* Functions are pulled out into their own C files to be tested as a unit. */
#include "HTTPClient_AddHeader.c"

#define xqcReset()                      \
    do {                                \
        status = HTTP_SUCCESS;          \
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
    test_err = HTTPClient_AddHeader( pRequestHeaders,
                                     header.field, header.fieldLen,
                                     header.value, header.valueLen );
    ok( test_err == HTTP_SUCCESS );

    return 0;
}

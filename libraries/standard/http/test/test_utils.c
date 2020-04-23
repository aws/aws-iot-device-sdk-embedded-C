#include "http_client.h"
#include "../src/private/http_client_internal.h"

#define HTTP_REQUEST_HEADERS_INITIALIZER     { 0 }
#define HTTP_USER_BUFFER_SIZE                ( 100 )
#define HTTP_CORRECT_HEADER_STRING_SIZE   \
    ( HTTP_HEADER_SAMPLE_FIRST_LINE_LEN + \
      HTTP_HEADER_SAMPLE_FIELD_LEN +      \
      HTTP_HEADER_FIELD_SEPARATOR_LEN +   \
      HTTP_HEADER_SAMPLE_VALUE_LEN +      \
      HTTP_HEADER_LINE_SEPARATOR_LEN +    \
      HTTP_HEADER_LINE_SEPARATOR_LEN )
#define HTTP_HEADER_SAMPLE_FIELD             "Authorization"
#define HTTP_HEADER_SAMPLE_FIELD_LEN         ( uint8_t ) ( sizeof( HTTP_HEADER_SAMPLE_FIELD ) - 1 )
#define HTTP_HEADER_SAMPLE_VALUE             "None"
#define HTTP_HEADER_SAMPLE_VALUE_LEN         ( uint8_t ) ( sizeof( HTTP_HEADER_SAMPLE_VALUE ) - 1 )
#define HTTP_HEADER_SAMPLE_FIRST_LINE        "GET / HTTP/1.1 \r\n"
#define HTTP_HEADER_SAMPLE_FIRST_LINE_LEN    ( uint8_t ) ( sizeof( HTTP_HEADER_SAMPLE_FIRST_LINE ) - 1 )

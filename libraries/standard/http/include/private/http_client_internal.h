#ifndef HTTP_CLIENT_INTERNAL_H_
#define HTTP_CLIENT_INTERNAL_H_

#include "../http_client.h"

#define STRLEN_LITERAL( x )    ( ( sizeof( x ) / sizeof( char ) ) - 1 )
#define HTTP_SUCCEEDED( x )    ( ( x ) != HTTP_SUCCESS )
#define HTTP_FAILED( x )       ( ( x ) != HTTP_SUCCESS )

    HTTPStatus_t _addHeaderLine( HTTPRequestHeaders_t * pRequestHeaders,
                                 const char * pLine,
                                 size_t lineLen );
    HTTPStatus_t _addHeader( HTTPRequestHeaders_t * pRequestHeaders,
                             const char * pField,
                             size_t fieldLen,
                             const char * pValue,
                             size_t valueLen );

#endif /* ifndef HTTP_CLIENT_INTERNAL_H_ */

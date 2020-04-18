#ifndef HTTP_CLIENT_PRIVATE_H_
#define HTTP_CLIENT_PRIVATE_H_

#define STRLEN_LITERAL( x )    ( ( sizeof( x ) / sizeof( char ) ) - 1 )
    uint8_t * _writeToBuffer( const uint8_t * pBuffer,
                              const void * source,
                              size_t len );
    HTTPStatus_t _addHeaderLine( HTTPRequestHeaders_t * pRequestHeaders,
                                 const char * pLine,
                                 size_t lineLen );
    HTTPStatus_t _addHeaderPair( HTTPRequestHeaders_t * pRequestHeaders,
                                 const char * pField,
                                 size_t fieldLen,
                                 const char * pValue,
                                 size_t valueLen );

#endif /* ifndef HTTP_CLIENT_PRIVATE_H_ */

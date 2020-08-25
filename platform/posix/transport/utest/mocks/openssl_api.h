#ifndef OPENSSL_API_H_
#define OPENSSL_API_H_

#include <openssl/ssl.h>
#include <openssl/err.h>

/**
 * @file openssl_api.h
 * @brief This file is used to generate mocks for the OpenSSL API's used in
 * the abstraction layer. Mocking openssl/ssl.h itself causes several
 * errors from parsing its macros.
 */

struct ssl_st
{
    int filler;
};

struct x509_st
{
    int filler;
};

struct x509_store_st
{
    int filler;
};

struct ssl_ctx_st
{
    int filler;
};

struct ssl_method_st
{
    int filler;
};

#undef SSL_set_max_send_fragment
#undef SSL_set_tlsext_host_name
#undef SSL_CTX_set_mode

extern int X509_STORE_add_cert( X509_STORE * ctx,
                                X509 * x );

X509 * PEM_read_X509( FILE * fp,
                      X509 ** x,
                      pem_password_cb * cb,
                      void * u );

extern X509_STORE * SSL_CTX_get_cert_store( const SSL_CTX * ctx );

extern int SSL_CTX_use_certificate_chain_file( SSL_CTX * ctx,
                                               const char * file );

extern int SSL_CTX_use_PrivateKey_file( SSL_CTX * ctx,
                                        const char * file,
                                        int type );

extern int SSL_set_alpn_protos( SSL * ssl,
                                const unsigned char * protos,
                                unsigned int protos_len );

extern int SSL_set_max_send_fragment( SSL * ssl,
                                      long m );

extern void SSL_set_default_read_buffer_len( SSL * s,
                                             size_t len );

extern int SSL_set_tlsext_host_name( const SSL * s,
                                     const char * name );

extern SSL_CTX * SSL_CTX_new( const SSL_METHOD * meth );

extern const SSL_METHOD * TLS_client_method( void );

extern long SSL_CTX_set_mode( SSL_CTX * ctx,
                              long mode );

extern SSL * SSL_new( SSL_CTX * ctx );

extern void SSL_set_verify( SSL * s,
                            int mode,
                            SSL_verify_cb callback );

extern int SSL_set_fd( SSL * s,
                       int fd );

extern int SSL_connect( SSL * ssl );

extern long SSL_get_verify_result( const SSL * ssl );

extern void SSL_CTX_free( SSL_CTX * );

extern void SSL_free( SSL * ssl );

extern long SSL_CTX_ctrl( SSL_CTX * ctx,
                          int cmd,
                          long larg,
                          void * parg );

extern long SSL_ctrl( SSL * ssl,
                      int cmd,
                      long larg,
                      void * parg );

extern int SSL_shutdown( SSL * s );

extern int SSL_read( SSL * ssl,
                     void * buf,
                     int num );

extern int SSL_get_error( const SSL * s,
                          int ret_code );

extern int SSL_write( SSL * ssl,
                      const void * buf,
                      int num );

const char * ERR_reason_error_string( unsigned long e );

#endif /* ifndef OPENSSL_API_H_ */

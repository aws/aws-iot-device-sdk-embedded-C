#ifndef OPENSSL_API_H_
#define OPENSSL_API_H_

/**
 * @file openssl_api.h
 * @brief This file is used to generate mocks for the OpenSSL API's used in
 * the abstraction layer. Mocking openssl/ssl.h itself causes several
 * errors from parsing its macros.
 */


int X509_STORE_add_cert( X509_STORE * ctx,
                         X509 * x );

X509_STORE * SSL_CTX_get_cert_store( const SSL_CTX * );

int SSL_CTX_use_certificate_chain_file( SSL_CTX * ctx,
                                        const char * file );

int SSL_CTX_use_PrivateKey_file( SSL_CTX * ctx,
                                 const char * file,
                                 int type );

int SSL_set_alpn_protos( SSL * ssl,
                         const unsigned char * protos,
                         unsigned int protos_len );

long SSL_set_max_send_fragment( SSL * ssl,
                                long m );

void SSL_set_default_read_buffer_len( SSL * s,
                                      size_t len );

int SSL_set_tlsext_host_name( const SSL * s,
                              const char * name );

SSL_CTX * SSL_CTX_new( const SSL_METHOD * meth );

const SSL_METHOD * TLS_client_method( void );

long SSL_CTX_set_mode( SSL_CTX * ctx,
                       long mode );

SSL * SSL_new( SSL_CTX * ctx );

void SSL_set_verify( SSL * s,
                     int mode,
                     SSL_verify_cb callback );

int SSL_set_fd( SSL * s,
                int fd );

int SSL_connect( SSL * ssl );

long SSL_get_verify_result( const SSL * ssl );

void SSL_CTX_free( SSL_CTX * );

void SSL_free( SSL * ssl );

int SSL_shutdown( SSL * s );

int SSL_read( SSL * ssl,
              void * buf,
              int num );

int SSL_get_error( const SSL * s,
                   int ret_code );

int SSL_write( SSL * ssl,
               const void * buf,
               int num );

#endif /* ifndef OPENSSL_API_H_ */

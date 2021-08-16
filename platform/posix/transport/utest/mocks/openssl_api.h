/*
 * AWS IoT Device SDK for Embedded C 202108.00
 * Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of
 * this software and associated documentation files (the "Software"), to deal in
 * the Software without restriction, including without limitation the rights to
 * use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
 * the Software, and to permit persons to whom the Software is furnished to do so,
 * subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all
 * copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
 * FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
 * COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
 * IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

#ifndef OPENSSL_API_H_
#define OPENSSL_API_H_

#include <openssl/ssl.h>

/**
 * @file openssl_api.h
 * @brief This file is used to generate mocks for the OpenSSL API's used in
 * the abstraction layer. Mocking openssl/ssl.h itself causes several
 * errors from parsing its macros.
 */

/* These structs must be defined to avoid a build error because the
 * they are set as opaque types by the OpenSSL library. */
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

/* The functions prototypes below are used by CMock to generate mocks
 * for any OpenSSL API calls used by the OpenSSL transport wrapper.
 *
 * IMPORTANT: If a new function is added to the OpenSSL transport wrapper,
 * it MUST also be added here.*/

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

extern void SSL_set_default_read_buffer_len( SSL * s,
                                             size_t len );

extern SSL_CTX * SSL_CTX_new( const SSL_METHOD * meth );

extern const SSL_METHOD * TLS_client_method( void );

extern long SSL_CTX_ctrl( SSL_CTX * ctx,
                          int cmd,
                          long larg,
                          void * parg );

extern SSL * SSL_new( SSL_CTX * ctx );

extern void SSL_set_verify( SSL * s,
                            int mode,
                            SSL_verify_cb callback );

extern int SSL_set_fd( SSL * s,
                       int fd );

extern int SSL_set1_host( SSL * s,
                          const char * hostname );

extern int SSL_connect( SSL * ssl );

extern long SSL_get_verify_result( const SSL * ssl );

extern void SSL_CTX_free( SSL_CTX * );

extern void SSL_free( SSL * ssl );

/* Macro wrappers:
 * SSL_CTX_set_mode */
extern long SSL_CTX_ctrl( SSL_CTX * ctx,
                          int cmd,
                          long larg,
                          void * parg );

/* Macro wrappers:
 * SSL_set_tlsext_host_name
 * SSL_set_max_send_fragment */
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

extern int SSL_pending( const SSL * ssl );

const char * ERR_reason_error_string( unsigned long e );

void X509_free( X509 * a );

#endif /* ifndef OPENSSL_API_H_ */

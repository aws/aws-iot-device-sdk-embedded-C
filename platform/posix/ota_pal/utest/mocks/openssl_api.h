/*
 * OTA PAL V2.1.0 for POSIX
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

#ifndef OPENSSL_API_H
#define OPENSSL_API_H

#include <openssl/ssl.h>

/**
 * @file openssl_api.h
 * @brief This file is used to generate mocks for the OpenSSL API's used in
 * the abstraction layer. Mocking openssl/ssl.h itself causes several
 * errors from parsing its macros.
 */

/* These structs must be defined to avoid a build error because the
 * they are set as opaque types by the OpenSSL library. */
struct bio_st
{
    int filler;
};

struct bio_method_st
{
    int filler;
};

struct x509_st
{
    int filler;
};

struct evp_pkey_st
{
    int filler;
};

struct evp_md_ctx_st
{
    int filler;
};

struct evp_pkey_ctx_st
{
    int filler;
};

struct engine_st
{
    int filler;
};

struct evp_md_st
{
    int filler;
};

/* Function declarations for functions in the OpenSSL bio.h header file. */
extern const BIO_METHOD * BIO_s_file( void );

extern BIO * BIO_new( const BIO_METHOD * type );

extern const BIO_METHOD * BIO_s_mem( void );

extern int BIO_puts( BIO * bp,
                     const char * buf );

extern void BIO_free_all( BIO * a );

extern long BIO_ctrl( BIO * bp,
                      int cmd,
                      long larg,
                      void * parg );

/* Function declarations for functions in the OpenSSL pem.h header file. */
extern X509 * PEM_read_bio_X509( BIO * bp,
                                 X509 ** x,
                                 pem_password_cb * cb,
                                 void * u );

/* Function declarations for functions in the OpenSSL x509.h header file. */
EVP_PKEY * X509_get_pubkey( X509 * x );

extern void X509_free( X509 * a );

/* Function declarations for functions in the OpenSSL evp.h header file. */
extern EVP_MD_CTX * EVP_MD_CTX_new( void );

extern int EVP_DigestVerifyInit( EVP_MD_CTX * ctx,
                                 EVP_PKEY_CTX ** pctx,
                                 const EVP_MD * type,
                                 ENGINE * e,
                                 EVP_PKEY * pkey );

extern int EVP_DigestUpdate( EVP_MD_CTX * ctx,
                             const void * d,
                             size_t cnt );

extern int EVP_DigestVerifyFinal( EVP_MD_CTX * ctx,
                                  const unsigned char * sig,
                                  size_t siglen );

extern void EVP_MD_CTX_free( EVP_MD_CTX * ctx );

extern void EVP_PKEY_free( EVP_PKEY * pkey );

extern const EVP_MD * EVP_sha256( void );

/* Function declarations for functions in the OpenSSL crypto.h header file. */
extern void CRYPTO_free( void * ptr,
                         const char * file,
                         int line );

extern void * CRYPTO_malloc( size_t num,
                             const char * file,
                             int line );

#endif /* ifndef OPENSSL_API_H */

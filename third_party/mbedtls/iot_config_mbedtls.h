/*
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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

/* This file configures the mbed TLS library built with this SDK. */

#ifndef IOT_CONFIG_MBEDTLS_H_
#define IOT_CONFIG_MBEDTLS_H_

/* System support for assembly and time. */
#define MBEDTLS_HAVE_ASM
#define MBEDTLS_HAVE_TIME
#define MBEDTLS_HAVE_TIME_DATE

/* Remove deprecated functions to prevent their use. */
#define MBEDTLS_DEPRECATED_REMOVED

/* Enabled block cipher modes of operation. */
#define MBEDTLS_CIPHER_MODE_CBC
#define MBEDTLS_CIPHER_MODE_CFB
#define MBEDTLS_CIPHER_MODE_CTR
#define MBEDTLS_CIPHER_MODE_OFB
#define MBEDTLS_CIPHER_MODE_XTS

/* Enabled block cipher padding modes. */
#define MBEDTLS_CIPHER_PADDING_ONE_AND_ZEROS
#define MBEDTLS_CIPHER_PADDING_ZEROS_AND_LEN
#define MBEDTLS_CIPHER_PADDING_ZEROS

/* Disable weak cipher suites. */
#define MBEDTLS_REMOVE_ARC4_CIPHERSUITES
#define MBEDTLS_REMOVE_3DES_CIPHERSUITES

/* Enabled eliptic curves. */
#define MBEDTLS_ECP_DP_SECP192R1_ENABLED
#define MBEDTLS_ECP_DP_SECP224R1_ENABLED
#define MBEDTLS_ECP_DP_SECP256R1_ENABLED
#define MBEDTLS_ECP_DP_SECP384R1_ENABLED
#define MBEDTLS_ECP_DP_SECP521R1_ENABLED
#define MBEDTLS_ECP_DP_SECP192K1_ENABLED
#define MBEDTLS_ECP_DP_SECP224K1_ENABLED
#define MBEDTLS_ECP_DP_SECP256K1_ENABLED
#define MBEDTLS_ECP_DP_BP256R1_ENABLED
#define MBEDTLS_ECP_DP_BP384R1_ENABLED
#define MBEDTLS_ECP_DP_BP512R1_ENABLED
#define MBEDTLS_ECP_DP_CURVE25519_ENABLED
#define MBEDTLS_ECP_DP_CURVE448_ENABLED

/* Enable NIST curves optimization and deterministic ECDSA. */
#define MBEDTLS_ECP_NIST_OPTIM
#define MBEDTLS_ECDSA_DETERMINISTIC

/* Enable TLS cipher suites supported by AWS IoT. */
#define MBEDTLS_KEY_EXCHANGE_ECDHE_RSA_ENABLED
#define MBEDTLS_KEY_EXCHANGE_ECDHE_ECDSA_ENABLED

/* Enable use of the filesystem. */
#define MBEDTLS_FS_IO

/* Enable Encrypt-then-MAC and Extended Master Secret. */
#define MBEDTLS_SSL_ENCRYPT_THEN_MAC
#define MBEDTLS_SSL_EXTENDED_MASTER_SECRET

/* Enable hardware acceleration in the SSL module. */
#define MBEDTLS_SSL_HW_RECORD_ACCEL

/* Enable SSL max fragment length, ALPN, and SNI. */
#define MBEDTLS_SSL_MAX_FRAGMENT_LENGTH
#define MBEDTLS_SSL_ALPN
#define MBEDTLS_SSL_SERVER_NAME_INDICATION

/* Enable TLS v1.2 only. */
#define MBEDTLS_SSL_PROTO_TLS1_2

/* Enable verification of key usage and extended key usage. */
#define MBEDTLS_X509_CHECK_KEY_USAGE
#define MBEDTLS_X509_CHECK_EXTENDED_KEY_USAGE

/* Use x86 AES-NI instructions. */
#define MBEDTLS_AESNI_C

/* Enabled mbed TLS modules. */
#define MBEDTLS_ASN1_PARSE_C
#define MBEDTLS_ASN1_WRITE_C
#define MBEDTLS_AES_C
#define MBEDTLS_BASE64_C
#define MBEDTLS_BIGNUM_C
#define MBEDTLS_CIPHER_C
#define MBEDTLS_CTR_DRBG_C
#define MBEDTLS_ECDSA_C
#define MBEDTLS_ECDH_C
#define MBEDTLS_ECP_C
#define MBEDTLS_ENTROPY_C
#define MBEDTLS_ERROR_C
#define MBEDTLS_HMAC_DRBG_C
#define MBEDTLS_MD_C
#define MBEDTLS_NET_C
#define MBEDTLS_OID_C
#define MBEDTLS_PEM_PARSE_C
#define MBEDTLS_PK_C
#define MBEDTLS_PK_PARSE_C
#define MBEDTLS_PKCS1_V15
#define MBEDTLS_PLATFORM_C
#define MBEDTLS_RSA_C
#define MBEDTLS_SHA256_C
#define MBEDTLS_SHA512_C
#define MBEDTLS_SSL_CLI_C
#define MBEDTLS_SSL_TLS_C
#define MBEDTLS_TIMING_C
#define MBEDTLS_X509_USE_C
#define MBEDTLS_X509_CRT_PARSE_C

/* Use platform mutexes in mbed TLS. */
#define MBEDTLS_THREADING_C
#define MBEDTLS_THREADING_ALT

/* Validate mbed TLS configuration. */
#include "mbedtls/check_config.h"

#endif

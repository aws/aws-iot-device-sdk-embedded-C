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

/* This file declares mutex functions for mbed TLS using platform mutexes. */

#ifndef THREADING_ALT_H_
#define THREADING_ALT_H_

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <stdbool.h>

/* Platform threads include. */
#include "platform/iot_threads.h"

/* Represents a mutex used by mbed TLS. */
typedef struct mbedtls_threading_mutex
{
    /* Whether this mutex is valid. */
    bool valid;
    /* The wrapped platform mutex. */
    IotMutex_t mutex;
} mbedtls_threading_mutex_t;

/* Initializes a new mutex. Sets the valid member of mbedtls_threading_mutex_t. */
void mbedtlsMutex_Init( mbedtls_threading_mutex_t * pMutex );

/* Frees a mutex. */
void mbedtlsMutex_Free( mbedtls_threading_mutex_t * pMutex );

/* Locks a mutex. Returns 0 on success; one of MBEDTLS_ERR_THREADING_BAD_INPUT_DATA
 * or MBEDTLS_ERR_THREADING_MUTEX_ERROR on error. */
int mbedtlsMutex_Lock( mbedtls_threading_mutex_t * pMutex );

/* Unlocks a mutex. Returns 0 on success; one of MBEDTLS_ERR_THREADING_BAD_INPUT_DATA
 * or MBEDTLS_ERR_THREADING_MUTEX_ERROR on error. */
int mbedtlsMutex_Unlock( mbedtls_threading_mutex_t * pMutex );

#endif /* ifndef THREADING_ALT_H_ */

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

/* This file implements mutex functions for mbed TLS using platform mutexes. */

/* mbed TLS threading include. This includes the "threading_alt.h" header. */
#include <mbedtls/threading.h>

/*-----------------------------------------------------------*/

void mbedtlsMutex_Init( mbedtls_threading_mutex_t * pMutex )
{
    pMutex->valid = IotMutex_Create( &( pMutex->mutex ), false );
}

/*-----------------------------------------------------------*/

void mbedtlsMutex_Free( mbedtls_threading_mutex_t * pMutex )
{
    if( pMutex->valid == true )
    {
        IotMutex_Destroy( &( pMutex->mutex ) );
    }
}

/*-----------------------------------------------------------*/

int mbedtlsMutex_Lock( mbedtls_threading_mutex_t * pMutex )
{
    int status = 0;

    if( pMutex->valid == false )
    {
        status = MBEDTLS_ERR_THREADING_BAD_INPUT_DATA;
    }
    else
    {
        IotMutex_Lock( &( pMutex->mutex ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

int mbedtlsMutex_Unlock( mbedtls_threading_mutex_t * pMutex )
{
    int status = 0;

    if( pMutex->valid == false )
    {
        status = MBEDTLS_ERR_THREADING_BAD_INPUT_DATA;
    }
    else
    {
        IotMutex_Unlock( &( pMutex->mutex ) );
    }

    return status;
}

/*-----------------------------------------------------------*/

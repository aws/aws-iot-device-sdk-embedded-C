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

/**
 * @file iot_network_mbedtls.c
 * @brief Implementation of the network interface functions in iot_network.h
 * for mbed TLS.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* mbed TLS network include. */
#include "iot_network_mbedtls.h"

/* mbed TLS includes. */
#include <mbedtls/ctr_drbg.h>
#include <mbedtls/entropy.h>
#include <mbedtls/error.h>
#include <mbedtls/threading.h>

/* Configure logs for the functions in this file. */
#ifdef IOT_LOG_LEVEL_NETWORK
    #define LIBRARY_LOG_LEVEL        IOT_LOG_LEVEL_NETWORK
#else
    #ifdef IOT_LOG_LEVEL_GLOBAL
        #define LIBRARY_LOG_LEVEL    IOT_LOG_LEVEL_GLOBAL
    #else
        #define LIBRARY_LOG_LEVEL    IOT_LOG_NONE
    #endif
#endif

#define LIBRARY_LOG_NAME    ( "NET" )
#include "iot_logging_setup.h"

/* Logging macro for mbed TLS errors. */
#if LIBRARY_LOG_LEVEL > IOT_LOG_NONE
    #define _logMbedtlsError( error, message )        \
    {                                                 \
        char pErrorMessage[ 64 ] = { 0 };             \
        mbedtls_strerror( error, pErrorMessage, 64 ); \
        IotLogError( "%s error: %s. ",                \
                     message,                         \
                     pErrorMessage );                 \
    }
#else
    #define _logMbedtlsError( error, message )
#endif /* if LIBRARY_LOG_LEVEL > IOT_LOG_NONE */

/*-----------------------------------------------------------*/

/**
 * @brief mbed TLS entropy context for generation of random numbers.
 */
static mbedtls_entropy_context _entropyContext;

/**
 * @brief mbed TLS CTR DRBG context for generation of random numbers.
 */
static mbedtls_ctr_drbg_context _ctrDrbgContext;

/**
 * @brief An #IotNetworkInterface_t that uses the functions in this file.
 */
const IotNetworkInterface_t IotNetworkMbedtls =
{
    .create             = IotNetworkMbedtls_Create,
    .setReceiveCallback = IotNetworkMbedtls_SetReceiveCallback,
    .send               = IotNetworkMbedtls_Send,
    .receive            = IotNetworkMbedtls_Receive,
    .close              = IotNetworkMbedtls_Close,
    .destroy            = IotNetworkMbedtls_Destroy
};

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkMbedtls_Init( void )
{
    int mbedtlsError = 0;
    IotNetworkError_t status = IOT_NETWORK_SUCCESS;

    /* Set the mutex functions for mbed TLS thread safety. */
    mbedtls_threading_set_alt( mbedtlsMutex_Init,
                               mbedtlsMutex_Free,
                               mbedtlsMutex_Lock,
                               mbedtlsMutex_Unlock );

    /* Initialize contexts for random number generation. */
    mbedtls_entropy_init( &_entropyContext );
    mbedtls_ctr_drbg_init( &_ctrDrbgContext );

    /* Seed the random number generator. */
    mbedtlsError = mbedtls_ctr_drbg_seed( &_ctrDrbgContext,
                                          mbedtls_entropy_func,
                                          &_entropyContext,
                                          NULL,
                                          0 );

    if( mbedtlsError != 0 )
    {
        status = IOT_NETWORK_FAILURE;
        _logMbedtlsError( mbedtlsError, "Failed to seed PRNG in initialization." );

        IotNetworkMbedtls_Cleanup();
    }
    else
    {
        IotLogInfo( "Network library initialized." );
    }

    return status;
}

/*-----------------------------------------------------------*/

void IotNetworkMbedtls_Cleanup( void )
{
    /* Free the contexts for random number generation. */
    mbedtls_ctr_drbg_free( &_ctrDrbgContext );
    mbedtls_entropy_free( &_entropyContext );

    /* Clear the mutex functions for mbed TLS thread safety. */
    mbedtls_threading_free_alt();

    IotLogInfo( "Network library cleanup done." );
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkMbedtls_Create( void * pConnectionInfo,
                                            void * pCredentialInfo,
                                            void ** pConnection )
{
    return IOT_NETWORK_FAILURE;
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkMbedtls_SetReceiveCallback( void * pConnection,
                                                        IotNetworkReceiveCallback_t receiveCallback,
                                                        void * pContext )
{
    return IOT_NETWORK_FAILURE;
}

/*-----------------------------------------------------------*/

size_t IotNetworkMbedtls_Send( void * pConnection,
                               const uint8_t * pMessage,
                               size_t messageLength )
{
    return 0;
}

/*-----------------------------------------------------------*/

size_t IotNetworkMbedtls_Receive( void * pConnection,
                                  uint8_t * pBuffer,
                                  size_t bytesRequested )
{
    return 0;
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkMbedtls_Close( void * pConnection )
{
    return IOT_NETWORK_FAILURE;
}

/*-----------------------------------------------------------*/

IotNetworkError_t IotNetworkMbedtls_Destroy( void * pConnection )
{
    return IOT_NETWORK_FAILURE;
}

/*-----------------------------------------------------------*/

void IotNetworkMbedtls_GetServerInfo( void * pConnection,
                                      IotMetricsTcpConnection_t * pServerInfo )
{
}

/*-----------------------------------------------------------*/

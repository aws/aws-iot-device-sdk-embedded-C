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
 * @file iot_network_metrics.c
 * @brief Implementation of the functions in iot_metrics.h that wraps functions
 * from the networking abstraction.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* Standard includes. */
#include <string.h>

/* Platform threads include. */
#include "platform/iot_threads.h"

/* Metrics networking include. */
#include "iot_network_metrics.h"

/*
 * Provide default values for undefined memory allocation functions.
 */
#ifndef IotNetwork_Malloc
    #include <stdlib.h>

/**
 * @brief Memory allocation. This function should have the same signature
 * as [malloc](http://pubs.opengroup.org/onlinepubs/9699919799/functions/malloc.html).
 */
    #define IotNetwork_Malloc    malloc
#endif
#ifndef IotNetwork_Free
    #include <stdlib.h>

/**
 * @brief Free memory. This function should have the same signature as
 * [free](http://pubs.opengroup.org/onlinepubs/9699919799/functions/free.html).
 */
    #define IotNetwork_Free    free
#endif

/*-----------------------------------------------------------*/

/**
 * @brief Wraps the network connection creation function with metrics.
 */
static IotNetworkError_t _metricsNetworkCreate( void * pConnectionInfo,
                                                void * pCredentialInfo,
                                                void ** pConnection );

/**
 * @brief Wraps the network connection close function with metrics.
 */
static IotNetworkError_t _metricsNetworkClose( void * pConnection );

/**
 * @brief Used to match metrics connection records by network connection.
 *
 * @param[in] pConnectionLink Pointer to a metrics connection record's link element.
 * @param[in] pContext The network connection to match.
 *
 * @return `true` if the given metrics connection record matches the given
 * network connection; `false` otherwise.
 */
static bool _connectionMatch( const IotLink_t * pConnectionLink,
                              void * pContext );

/*-----------------------------------------------------------*/

/**
 * @brief Holds a list of active TCP connections.
 */
static IotListDouble_t _connectionList = IOT_LIST_DOUBLE_INITIALIZER;

/**
 * @brief Protects #_connectionList from concurrent access.
 */
static IotMutex_t _connectionListMutex;

/*-----------------------------------------------------------*/

/* Choose the appropriate network abstraction implementation. */
#if IOT_NETWORK_USE_OPENSSL == 1
    /* OpenSSL networking include. */
    #include "posix/iot_network_openssl.h"

    /**
     * @brief Pointer to the metrics-wrapped network creation function.
     */
    static IotNetworkError_t ( * _networkCreate )( void *, void *, void ** ) = IotNetworkOpenssl_Create;

    /**
     * @brief Pointer to the metrics-wrapped network close function.
     */
    static IotNetworkError_t ( * _networkClose )( void * ) = IotNetworkOpenssl_Close;

    /**
     * @brief Pointer to the function that retrieves the server info for a connection.
     */
    static void ( * _networkServerInfo )( void *,
                                        IotMetricsTcpConnection_t * ) = IotNetworkOpenssl_GetServerInfo;

    /**
     * @brief An #IotNetworkInterface_t that wraps network abstraction functions with
     * metrics.
     */
    const IotNetworkInterface_t IotNetworkMetrics =
    {
        .create             = _metricsNetworkCreate,
        .setReceiveCallback = IotNetworkOpenssl_SetReceiveCallback,
        .send               = IotNetworkOpenssl_Send,
        .receive            = IotNetworkOpenssl_Receive,
        .close              = _metricsNetworkClose,
        .destroy            = IotNetworkOpenssl_Destroy
    };
#else
    /* mbed TLS networking include. */
    #include "iot_network_mbedtls.h"

    /**
     * @brief Pointer to the metrics-wrapped network creation function.
     */
    static IotNetworkError_t ( * _networkCreate )( void *, void *, void ** ) = IotNetworkMbedtls_Create;

    /**
     * @brief Pointer to the metrics-wrapped network close function.
     */
    static IotNetworkError_t ( * _networkClose )( void * ) = IotNetworkMbedtls_Close;

    /**
     * @brief Pointer to the function that retrieves the server info for a connection.
     */
    static void ( * _networkServerInfo )( void *,
                                        IotMetricsTcpConnection_t * ) = IotNetworkMbedtls_GetServerInfo;

    /**
     * @brief An #IotNetworkInterface_t that wraps network abstraction functions with
     * metrics.
     */
    const IotNetworkInterface_t IotNetworkMetrics =
    {
        .create             = _metricsNetworkCreate,
        .setReceiveCallback = IotNetworkMbedtls_SetReceiveCallback,
        .send               = IotNetworkMbedtls_Send,
        .receive            = IotNetworkMbedtls_Receive,
        .close              = _metricsNetworkClose,
        .destroy            = IotNetworkMbedtls_Destroy
    };
#endif

/*-----------------------------------------------------------*/

static bool _connectionMatch( const IotLink_t * pConnectionLink,
                              void * pContext )
{
    /* Retrieve the pointer the the TCP connection record. The given link
     * pointer is never NULL. */
    IotMetricsTcpConnection_t * pTcpConnection = IotLink_Container( IotMetricsTcpConnection_t,
                                                                    pConnectionLink,
                                                                    link );

    return( pTcpConnection->pNetworkContext == pContext );
}

/*-----------------------------------------------------------*/

static IotNetworkError_t _metricsNetworkCreate( void * pConnectionInfo,
                                                void * pCredentialInfo,
                                                void ** pConnection )
{
    IotMetricsTcpConnection_t * pTcpConnection = NULL;
    IotNetworkError_t status = IOT_NETWORK_SUCCESS;

    /* Allocate memory for a new metrics connection. */
    pTcpConnection = IotNetwork_Malloc( sizeof( IotMetricsTcpConnection_t ) );

    if( pTcpConnection != NULL )
    {
        ( void ) memset( pTcpConnection, 0x00, sizeof( IotMetricsTcpConnection_t ) );

        /* Call the wrapped network create function. */
        status = _networkCreate( pConnectionInfo,
                                 pCredentialInfo,
                                 pConnection );

        /* Add the new metrics connection to the list of connections. */
        if( status == IOT_NETWORK_SUCCESS )
        {
            /* Get the connection's IPv4 address and port. */
            pTcpConnection->pNetworkContext = *pConnection;

            _networkServerInfo( pTcpConnection->pNetworkContext,
                                pTcpConnection );

            /* Add the new connection to the list of connections. */
            IotMutex_Lock( &_connectionListMutex );
            IotListDouble_InsertHead( &_connectionList, &( pTcpConnection->link ) );
            IotMutex_Unlock( &_connectionListMutex );
        }
        else
        {
            /* Free the new metrics connection on error. */
            IotNetwork_Free( pTcpConnection );
        }
    }
    else
    {
        status = IOT_NETWORK_NO_MEMORY;
    }

    return status;
}

/*-----------------------------------------------------------*/

static IotNetworkError_t _metricsNetworkClose( void * pConnection )
{
    IotLink_t * pConnectionLink = NULL;
    IotMetricsTcpConnection_t * pTcpConnection = NULL;

    /* Call the wrapped network close function. */
    IotNetworkError_t status = _networkClose( pConnection );

    /* Remove the connection from the list of active connections and free it. */
    if( status == IOT_NETWORK_SUCCESS )
    {
        IotMutex_Lock( &_connectionListMutex );
        pConnectionLink = IotListDouble_RemoveFirstMatch( &_connectionList,
                                                          NULL,
                                                          _connectionMatch,
                                                          pConnection );
        IotMutex_Unlock( &_connectionListMutex );

        if( pConnectionLink != NULL )
        {
            pTcpConnection = IotLink_Container( IotMetricsTcpConnection_t,
                                                pConnectionLink,
                                                link );

            IotNetwork_Free( pTcpConnection );
        }
    }

    return status;
}

/*-----------------------------------------------------------*/

bool IotMetrics_Init( void )
{
    IotListDouble_Create( &_connectionList );

    return IotMutex_Create( &_connectionListMutex, false );
}

/*-----------------------------------------------------------*/

void IotMetrics_Cleanup( void )
{
    IotMutex_Destroy( &_connectionListMutex );
}

/*-----------------------------------------------------------*/

void IotMetrics_GetTcpConnections( void * pContext,
                                   void ( * metricsCallback )( void *, const IotListDouble_t * ) )
{
    /* Provide the connection list. Ensure that it is not modified elsewhere by
     * locking the connection list mutex. */
    IotMutex_Lock( &_connectionListMutex );
    metricsCallback( pContext, &_connectionList );
    IotMutex_Unlock( &_connectionListMutex );
}

/*-----------------------------------------------------------*/

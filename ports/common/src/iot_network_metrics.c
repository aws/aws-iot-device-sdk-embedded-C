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
#include <stdio.h>

/* Platform threads include. */
#include "platform/iot_threads.h"

/* Metrics networking include. */
#include "iot_network_metrics.h"

/* System headers for retrieving socket info. */
#if !defined( _WIN32 ) && !defined( _WIN64 )
    #include <arpa/inet.h>
    #include <netdb.h>
    #include <sys/socket.h>
#endif

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
    #include "iot_network_openssl.h"

    /**
     * @brief Pointer to the metrics-wrapped network creation function.
     */
    static IotNetworkError_t ( * _networkCreate )( void *, void *, void ** ) = IotNetworkOpenssl_Create;

    /**
     * @brief Pointer to the metrics-wrapped network close function.
     */
    static IotNetworkError_t ( * _networkClose )( void * ) = IotNetworkOpenssl_Close;

    /**
     * @brief Pointer to the function that retrieves the socket for a connection.
     */
    static int ( * _getSocket )( void * ) = IotNetworkOpenssl_GetSocket;

    /**
     * @brief An #IotNetworkInterface_t that wraps network abstraction functions with
     * metrics.
     */
    static const IotNetworkInterface_t _networkMetrics =
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
     * @brief Pointer to the function that retrieves the socket for a connection.
     */
    static int ( * _getSocket )( void * ) = IotNetworkMbedtls_GetSocket;

    /**
     * @brief An #IotNetworkInterface_t that wraps network abstraction functions with
     * metrics.
     */
    static const IotNetworkInterface_t _networkMetrics =
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

static void _getServerInfo( int socket,
                            IotMetricsTcpConnection_t * pServerInfo )
{
    int status = 0, portLength = 0;
    struct sockaddr_storage server = { 0 };
    socklen_t length = sizeof( struct sockaddr_storage );
    const void * pServerAddress = NULL;
    char * pAddressStart = NULL;
    const char * pPortFormat = NULL;
    uint16_t remotePort = 0;
    size_t addressLength = 0;

    /* Get peer info. */
    status = getpeername( socket,
                          ( struct sockaddr * ) &server,
                          &length );

    if( status == 0 )
    {
        /* Calculate the pointer to the IP address and get the remote port based
         * on protocol version. */
        if( server.ss_family == AF_INET )
        {
            /* IPv4. */
            pServerAddress = &( ( ( struct sockaddr_in * ) &server )->sin_addr );
            remotePort = ntohs( ( ( struct sockaddr_in * ) &server )->sin_port );

            /* Print the IPv4 address at the start of the address buffer. */
            pAddressStart = pServerInfo->pRemoteAddress;
            addressLength = IOT_METRICS_IP_ADDRESS_LENGTH;
            pPortFormat = ":%hu";
        }
        else
        {
            /* IPv6. */
            pServerAddress = &( ( ( struct sockaddr_in6 * ) &server )->sin6_addr );
            remotePort = ntohs( ( ( struct sockaddr_in6 * ) &server )->sin6_port );

            /* Enclose the IPv6 address with []. */
            pServerInfo->pRemoteAddress[ 0 ] = '[';
            pAddressStart = pServerInfo->pRemoteAddress + 1;
            addressLength = IOT_METRICS_IP_ADDRESS_LENGTH - 1;
            pPortFormat = "]:%hu";
        }

        /* Convert IP address to text. */
        if( inet_ntop( server.ss_family,
                       pServerAddress,
                       pAddressStart,
                       addressLength ) != NULL )
        {
            /* Add the port to the end of the address. */
            addressLength = strlen( pServerInfo->pRemoteAddress );

            portLength = snprintf( &( pServerInfo->pRemoteAddress[ addressLength ] ),
                                   7,
                                   pPortFormat,
                                   remotePort );

            if( portLength > 0 )
            {
                pServerInfo->addressLength = addressLength + ( size_t ) portLength;

                IotLogInfo( "(Socket %d) Collecting network metrics for %s.",
                            socket,
                            pServerInfo->pRemoteAddress );
            }
            else
            {
                IotLogError( "(Socket %d) Failed to add port to IP address buffer." );
            }
        }
        else
        {
            IotLogError( "(Socket %d) Failed to convert IP address to text format.",
                         socket );
        }
    }
    else
    {
        IotLogError( "(Socket %d) Failed to query peer name.",
                     socket );
    }
}

/*-----------------------------------------------------------*/

static IotNetworkError_t _metricsNetworkCreate( void * pConnectionInfo,
                                                void * pCredentialInfo,
                                                void ** pConnection )
{
    int socket = 0;
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
            pTcpConnection->pNetworkContext = *pConnection;

            /* Get the connection's address and port. */
            socket = _getSocket( pTcpConnection->pNetworkContext );
            _getServerInfo( socket, pTcpConnection );

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

const IotNetworkInterface_t * IotNetworkMetrics_GetInterface( void )
{
    return &_networkMetrics;
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

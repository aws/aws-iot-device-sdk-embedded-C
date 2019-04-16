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

/*
 * This file servers as an example.
 * It tracks the socket metrics in network interface layer and uses openssl as underlying network.
 */

/* Linux network includes. */
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/ip.h>
#include <arpa/inet.h>

/* Network include. */
#include "platform/iot_network.h"
#include "posix/iot_network_openssl.h"

/* Metrics include. */
#include "platform/iot_metrics.h"

/* Metrics wrapper of create interface. */
static IotNetworkError_t _metricsCreate( void * pConnectionInfo,
                                         void * pCredentialInfo,
                                         void ** pConnection );

/* Metrics wrapper of close interface. */
static IotNetworkError_t _metricsClose( void * pConnection );

/* Metrics network interface which is on top of openssl network interface. */
const IotNetworkInterface_t _IotNetworkOpensslMetrics =
{
    .create             = _metricsCreate,
    .setReceiveCallback = IotNetworkOpenssl_SetReceiveCallback,
    .send               = IotNetworkOpenssl_Send,
    .receive            = IotNetworkOpenssl_Receive,
    .close              = _metricsClose,
    .destroy            = IotNetworkOpenssl_Destroy
};

/*-----------------------------------------------------------*/

static IotNetworkError_t _metricsCreate( void * pConnectionInfo,
                                         void * pCredentialInfo,
                                         void ** pConnection )
{
    /* Call the openssl create. */
    IotNetworkError_t error = IotNetworkOpenssl_Create( pConnectionInfo, pCredentialInfo, pConnection );

    /* Add socket metrics only if creation succeeded. */
    if( error == IOT_NETWORK_SUCCESS )
    {
        /* This is an hacky to to get the socket integer value. Not recommended in production code. */
        int socket = **( ( int ** ) pConnection );

        /* Assume this is Ipv4. */
        struct sockaddr_in socketAddressIpv4;
        socklen_t socklen = sizeof( struct sockaddr_in );

        IotMetricsTcpConnection_t connection;

        /* Get the ip and port from the peer socket. */
        int ret = getpeername( socket, ( struct sockaddr * ) &socketAddressIpv4, &socklen );
        ( void ) ret;

        /* Assert its succees. */
        IotMetrics_Assert( ret == 0 );

        connection.id = ( IotMetricsConnectionId_t ) socket;
        connection.remotePort = socketAddressIpv4.sin_port;
        connection.remoteIp = socketAddressIpv4.sin_addr.s_addr;

        /* Add this metircs, a established TCP connection.  */
        IotMetrics_AddTcpConnection( &connection );
    }

    return error;
}

/*-----------------------------------------------------------*/

static IotNetworkError_t _metricsClose( void * pConnection )
{
    /* This is an hacky to to get the socket integer value. Not recommended in production code. */
    int socket = *( ( int * ) pConnection );

    /* Call the openssl close. */
    IotNetworkError_t error = IotNetworkOpenssl_Close( pConnection );

    /* Remove socket metrics only if close succeeded. */
    if( error == IOT_NETWORK_SUCCESS )
    {
        /* Remove this metircs by its id.  */
        IotMetrics_RemoveTcpConnection( ( IotMetricsConnectionId_t ) socket );
    }

    return error;
}

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

/* Build using a config header, if provided. */
#ifdef IOT_CONFIG_FILE
    #include IOT_CONFIG_FILE
#endif

#include <sys/socket.h>
#include <linux/netlink.h>

/* Metrics include. */
#include "platform/iot_metrics.h"

/* Platform threads include. */
#include "platform/iot_threads.h"

bool IotMetrics_Init()
{
    return true;
}

/*-----------------------------------------------------------*/

void IotMetrics_ProcessTcpConnections( IotMetricsListCallback_t tcpConnectionsCallback )
{
    if( tcpConnectionsCallback.function != NULL )
    {
        IotListDouble_t connectionsList = IOT_LIST_DOUBLE_INITIALIZER;

        int nl_sock = 0, numbytes = 0, rtalen = 0;
        struct nlmsghdr *nlh;
        uint8_t recv_buf[1024];
        struct inet_diag_msg *diag_msg;

        //Create the monitoring socket
        if ((nl_sock = socket(AF_NETLINK, SOCK_DGRAM, NETLINK_INET_DIAG)) == -1) {
            return;
        }



        /* Execute the callback function. */
        tcpConnectionsCallback.function( tcpConnectionsCallback.param1, &connectionsList);
    }

    /* If no callback function is provided, simply return. */
}

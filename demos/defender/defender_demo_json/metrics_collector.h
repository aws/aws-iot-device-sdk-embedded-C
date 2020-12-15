/*
 * AWS IoT Device SDK for Embedded C 202012.01
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

#ifndef METRICS_COLLECTOR_H_
#define METRICS_COLLECTOR_H_

/* Standard includes. */
#include <stdint.h>

/**
 * @brief Return codes from metrics collector APIs.
 */
typedef enum
{
    MetricsCollectorSuccess = 0,
    MetricsCollectorBadParameter,
    MetricsCollectorFileOpenFailed,
    MetricsCollectorParsingFailed
} MetricsCollectorStatus_t;

/**
 * @brief Represents network stats.
 */
typedef struct NetworkStats
{
    uint32_t bytesReceived;   /**< Number of bytes received. */
    uint32_t bytesSent;       /**< Number of bytes sent. */
    uint32_t packetsReceived; /**< Number of packets (ethernet frames) received. */
    uint32_t packetsSent;     /**< Number of packets (ethernet frames) sent. */
} NetworkStats_t;

/**
 * @brief Represents a network connection.
 */
typedef struct Connection
{
    uint32_t localIp;
    uint32_t remoteIp;
    uint16_t localPort;
    uint16_t remotePort;
} Connection_t;

/**
 * @brief Get network stats.
 *
 * This function finds the network stats by reading "/proc/net/dev".
 *
 * @param[out] pOutNetworkStats The network stats.
 *
 * @return #MetricsCollectorSuccess if the network stats are successfully obtained;
 * #MetricsCollectorBadParameter if invalid parameters are passed;
 * #MetricsCollectorFileOpenFailed if the function fails to open "/proc/net/dev";
 * MetricsCollectorParsingFailed if the function fails to parses the data read
 * from "/proc/net/dev".
 */
MetricsCollectorStatus_t GetNetworkStats( NetworkStats_t * pOutNetworkStats );

/**
 * @brief Get a list of the open TCP ports.
 *
 * This function finds the open TCP ports by reading "/proc/net/tcp". It can be
 * called with @p pOutTcpPortsArray NULL to get the number of the open TCP ports.
 *
 * @param[in] pOutTcpPortsArray The array to write the open TCP ports into. This
 * can be NULL, if only the number of open ports is needed.
 * @param[in] tcpPortsArrayLength Length of the pOutTcpPortsArray, if it is not
 * NULL.
 * @param[out] pOutNumTcpOpenPorts Number of open TCP ports if @p
 * pOutTcpPortsArray NULL, else number of TCP ports written.
 *
 * @return #MetricsCollectorSuccess if open TCP ports are successfully obtained;
 * #MetricsCollectorBadParameter if invalid parameters are passed;
 * #MetricsCollectorFileOpenFailed if the function fails to open "/proc/net/tcp";
 * MetricsCollectorParsingFailed if the function fails to parses the data read
 * from "/proc/net/tcp".
 */
MetricsCollectorStatus_t GetOpenTcpPorts( uint16_t * pOutTcpPortsArray,
                                          uint32_t tcpPortsArrayLength,
                                          uint32_t * pOutNumTcpOpenPorts );

/**
 * @brief Get a list of the open UDP ports.
 *
 * This function finds the open UDP ports by reading "/proc/net/udp". It can be
 * called with pOutUdpPortsArray NULL to get the number of the open UDP ports.
 *
 * @param[in] pOutUdpPortsArray The array to write the open UDP ports into. Can
 * be NULL, if only number of open ports is needed.
 * @param[in] udpPortsArrayLength Length of the pOutUdpPortsArray, if it is not
 * NULL.
 * @param[out] pOutNumUdpOpenPorts Number of open UDP ports if @p
 * pOutUdpPortsArray NULL, else number of UDP ports written.
 *
 * @return #MetricsCollectorSuccess if open UDP ports are successfully obtained;
 * #MetricsCollectorBadParameter if invalid parameters are passed;
 * #MetricsCollectorFileOpenFailed if the function fails to open "/proc/net/udp";
 * MetricsCollectorParsingFailed if the function fails to parses the data read
 * from "/proc/net/udp".
 */
MetricsCollectorStatus_t GetOpenUdpPorts( uint16_t * pOutUdpPortsArray,
                                          uint32_t udpPortsArrayLength,
                                          uint32_t * pOutNumUdpOpenPorts );

/**
 * @brief Get a list of established connections.
 *
 * This function finds the established connections by reading "/proc/net/tcp".
 * It can be called with @p pOutConnectionsArray NULL to get the number of
 * established connections.
 *
 * @param[in] pOutConnectionsArray The array to write the established connections
 * into. This can be NULL, if only the number of established connections is
 * needed.
 * @param[in] connectionsArrayLength Length of the pOutConnectionsArray, if it
 * is not NULL.
 * @param[out] pOutNumEstablishedConnections Number of established connections if @p
 * pOutNumEstablishedConnections NULL, else number of established connections written.
 *
 * @return #MetricsCollectorSuccess if established connections are successfully obtained;
 * #MetricsCollectorBadParameter if invalid parameters are passed;
 * #MetricsCollectorFileOpenFailed if the function fails to open "/proc/net/tcp";
 * MetricsCollectorParsingFailed if the function fails to parses the data read
 * from "/proc/net/tcp".
 */
MetricsCollectorStatus_t GetEstablishedConnections( Connection_t * pOutConnectionsArray,
                                                    uint32_t connectionsArrayLength,
                                                    uint32_t * pOutNumEstablishedConnections );

#endif /* ifndef METRICS_COLLECTOR_H_ */

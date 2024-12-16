/*
 * AWS IoT Device SDK for Embedded C 202412.00
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
#include <stdlib.h>
#include <stdint.h>

/**
 * @brief Return codes from metrics collector APIs.
 */
typedef enum
{
    MetricsCollectorSuccess = 0,
    MetricsCollectorBadParameter,
    MetricsCollectorFileOpenFailed,
    MetricsCollectorParsingFailed,
    MetricsCollectorDataNotFound
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
 * @brief Represents the Cpu Usage statistics obtained from "/proc/uptime".
 * Refer to Linux manual for "/proc" filesystem for more information.
 * https://man7.org/linux/man-pages/man5/procfs.5.html
 */
typedef struct CpuUsageData
{
    uint32_t upTime;   /**< Up-time of system in seconds. */
    uint32_t idleTime; /**< Idle time of system in seconds. */
} CpuUsageStats_t;

/**
 * @brief Represents the memory data of total and available memory from "/proc/uptime".
 * Refer to Linux manual for "/proc" filesystem for more information.
 * https://man7.org/linux/man-pages/man5/procfs.5.html
 */
typedef struct MemoryStats
{
    uint32_t totalMemory;     /**< Amount of total memory in system (in kB). */
    uint32_t availableMemory; /**< Amount of available memory in system (in kB). */
} MemoryStats_t;

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

/**
 * @brief Get system uptime.
 *
 * This function finds the system uptime by reading the "/proc/uptime" file.
 *
 * @param[out] pUptime The uptime of the system.
 *
 * @return #MetricsCollectorSuccess if uptime is successfully obtained;
 * #MetricsCollectorBadParameter if invalid parameter is passed;
 * #MetricsCollectorFileOpenFailed if the function fails to open "/proc/uptime";
 * MetricsCollectorParsingFailed if the function fails to parses the data read
 * from "/proc/uptime".
 */
MetricsCollectorStatus_t GetUptime( uint64_t * pUptime );

/**
 * @brief Get system free memory.
 *
 * This function finds the free memory by reading the "/proc/meminfo" file.
 *
 * @param[out] pMemFree The free memory on the system.
 *
 * @return #MetricsCollectorSuccess if free memory is successfully obtained;
 * #MetricsCollectorBadParameter if invalid parameter is passed;
 * #MetricsCollectorFileOpenFailed if the function fails to open "/proc/meminfo";
 * MetricsCollectorParsingFailed if the function fails to parses the data read
 * from "/proc/meminfo".
 */
MetricsCollectorStatus_t GetFreeMemory( uint64_t * pMemFree );

/**
 * @brief Gets user usage for each CPU from the system.
 *
 * This function finds the usage information by reading the "/proc/stat" file.
 *
 * @param[out] pOutCpuUserUsage The memory to write the CPU usage into.
 * @param[in] cpuUserUsageLength The length of pOutCpuUserUsage.
 * @param[out] pOutNumCpuUserUsage Number of items written.
 *
 * @return #MetricsCollectorSuccess if memory data statistic is successfully calculated;
 * #MetricsCollectorBadParameter if invalid parameter is passed;
 * #MetricsCollectorFileOpenFailed if the function fails to open "/proc/stat";
 * MetricsCollectorParsingFailed if the function fails to parses the data read
 * from "/proc/stat".
 */
MetricsCollectorStatus_t GetCpuUserUsage( uint64_t * pOutCpuUserUsage,
                                          size_t cpuUserUsageLength,
                                          size_t * pOutNumCpuUserUsage );

/**
 * @brief Gets names and addresses of network interfaces from the system.
 *
 * This function finds the network interface information by reading the "/proc/net/arp" file.
 *
 * @param[out] pOutNetworkInterfaceNames The memory to write the interface names into.
 * @param[out] pOutNetworkInterfaceAddresses The memory to write the interface addresses into.
 * @param[in] bufferLength The length of pOutNetworkInterfaceNames and pOutNetworkInterfaceAddresses.
 * @param[out] pOutNumNetworkInterfaces Number of network interfaces written.
 *
 * @return #MetricsCollectorSuccess if memory data statistic is successfully calculated;
 * #MetricsCollectorBadParameter if invalid parameter is passed;
 * #MetricsCollectorFileOpenFailed if the function fails to open "/proc/net/arp";
 * MetricsCollectorParsingFailed if the function fails to parses the data read
 * from "/proc/net/arp".
 */
MetricsCollectorStatus_t GetNetworkInferfaceInfo( char ( *pOutNetworkInterfaceNames )[ 16 ],
                                                  uint32_t * pOutNetworkInterfaceAddresses,
                                                  size_t bufferLength,
                                                  size_t * pOutNumNetworkInterfaces );

#endif /* ifndef METRICS_COLLECTOR_H_ */

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

/**
 * @file metrics_collector.c
 *
 * @brief This file provides an implementation of the metrics_collector interface
 * for Linux systems.
 */

/* Standard includes. */
#include <stdio.h>
#include <ctype.h>
#include <stdlib.h>
#include <string.h>

/* POSIX includes. */
#include <arpa/inet.h>

/* Demo config. */
#include "demo_config.h"

/* Interface include. */
#include "metrics_collector.h"

/**
 * @brief The maximum length of line read from any of /proc/net/dev, /proc/net/tcp,
 * /proc/net/udp, /proc/uptime, /proc/meminfo, /proc/stat, and /proc/net/arp files.
 */
#define MAX_LINE_LENGTH                  ( 256 )

/**
 * @brief Various connection status.
 */
#define CONNECTION_STATUS_LISTEN         ( 10 )
#define CONNECTION_STATUS_ESTABLISHED    ( 1 )

/**
 * @brief Get a list of the open ports.
 *
 * This function finds the open ports by reading pProcFile. It can be called
 * with pOutPortsArray NULL to get the number of the open ports.
 *
 * @param[in] pProcFile The file to read from; either /proc/net/tcp or /proc/net/udp.
 * @param[in] pOutPortsArray The array to write the open ports into. Can be
 * NULL, if only number of open ports is needed.
 * @param[in] portsArrayLength Length of the pOutPortsArray, if it is not NULL.
 * @param[out] pOutNumOpenPorts Number of the open ports.
 *
 * @return #MetricsCollectorSuccess if open ports are successfully obtained;
 * #MetricsCollectorBadParameter if invalid parameters are passed;
 * #MetricsCollectorFileOpenFailed if the function fails to open pProcFile;
 * MetricsCollectorParsingFailed if the function fails to parses the data read
 * from pProcFile.
 */
static MetricsCollectorStatus_t getOpenPorts( const char * pProcFile,
                                              uint16_t * pOutPortsArray,
                                              uint32_t portsArrayLength,
                                              uint32_t * pOutNumOpenPorts );
/*-----------------------------------------------------------*/

static MetricsCollectorStatus_t getOpenPorts( const char * pProcFile,
                                              uint16_t * pOutPortsArray,
                                              uint32_t portsArrayLength,
                                              uint32_t * pOutNumOpenPorts )
{
    MetricsCollectorStatus_t status = MetricsCollectorSuccess;
    FILE * fileHandle = NULL;
    uint32_t lineNumber = 0;
    int32_t filledVariables;
    uint32_t connectionStatus, localPort, numOpenPorts = 0;
    char lineBuffer[ MAX_LINE_LENGTH ];

    if( ( pProcFile == NULL ) ||
        ( ( pOutPortsArray != NULL ) && ( portsArrayLength == 0 ) ) ||
        ( pOutNumOpenPorts == NULL ) )
    {
        LogError( ( "Invalid parameters. pProcFile: %p, pOutPortsArray: %p,"
                    " portsArrayLength: %u, pOutNumOpenPorts: %p.",
                    ( const void * ) pProcFile,
                    ( void * ) pOutPortsArray,
                    portsArrayLength,
                    ( void * ) pOutNumOpenPorts ) );
        status = MetricsCollectorBadParameter;
    }

    if( status == MetricsCollectorSuccess )
    {
        fileHandle = fopen( pProcFile, "r" );

        if( fileHandle == NULL )
        {
            LogError( ( "Failed to open %s.", pProcFile ) );
            status = MetricsCollectorFileOpenFailed;
        }
    }

    if( status == MetricsCollectorSuccess )
    {
        while( fgets( &( lineBuffer[ 0 ] ), MAX_LINE_LENGTH, fileHandle ) != NULL )
        {
            lineNumber++;

            LogDebug( ( "File: %s, Line: %u, Content: %s.",
                        pProcFile,
                        lineNumber,
                        &( lineBuffer[ 0 ] ) ) );

            /* Skip the first line as it is a header. */
            if( lineNumber <= 1 )
            {
                continue;
            }

            /* Parse the output. */
            filledVariables = sscanf( &( lineBuffer[ 0 ] ),
                                      "%*[^:]: %*8x:%4x %*8x:%*4x %2x",
                                      &( localPort ),
                                      &( connectionStatus ) );

            /* sscanf should fill all the 2 variables successfully. */
            if( filledVariables != 2 )
            {
                LogError( ( "Failed to parse %s.", &( lineBuffer[ 0 ] ) ) );
                status = MetricsCollectorParsingFailed;
                break;
            }

            if( connectionStatus == CONNECTION_STATUS_LISTEN )
            {
                if( pOutPortsArray != NULL )
                {
                    pOutPortsArray[ numOpenPorts ] = ( uint16_t ) localPort;
                    numOpenPorts++;

                    /* Break if the output array is full. */
                    if( portsArrayLength == numOpenPorts )
                    {
                        break;
                    }
                }
                else
                {
                    numOpenPorts++;
                }
            }
        }
    }

    if( status == MetricsCollectorSuccess )
    {
        *pOutNumOpenPorts = numOpenPorts;
    }

    if( fileHandle != NULL )
    {
        fclose( fileHandle );
    }

    return status;
}
/*-----------------------------------------------------------*/

MetricsCollectorStatus_t GetNetworkStats( NetworkStats_t * pOutNetworkStats )
{
    MetricsCollectorStatus_t status = MetricsCollectorSuccess;
    FILE * fileHandle = NULL;
    uint32_t lineNumber = 0;
    int32_t filledVariables;
    uint32_t bytesReceived, bytesSent, packetsReceived, packetsSent;
    char lineBuffer[ MAX_LINE_LENGTH ];

    if( pOutNetworkStats == NULL )
    {
        LogError( ( "Invalid parameter. pOutNetworkStats: %p.", ( void * ) pOutNetworkStats ) );
        status = MetricsCollectorBadParameter;
    }

    if( status == MetricsCollectorSuccess )
    {
        fileHandle = fopen( "/proc/net/dev", "r" );

        if( fileHandle == NULL )
        {
            LogError( ( "Failed to open /proc/net/dev." ) );
            status = MetricsCollectorFileOpenFailed;
        }
    }

    if( status == MetricsCollectorSuccess )
    {
        /* Start with everything as zero. */
        memset( pOutNetworkStats, 0, sizeof( NetworkStats_t ) );

        while( fgets( &( lineBuffer[ 0 ] ), MAX_LINE_LENGTH, fileHandle ) != NULL )
        {
            lineNumber++;

            LogDebug( ( "File: /proc/net/dev, Line: %u, Content: %s.",
                        lineNumber,
                        &( lineBuffer[ 0 ] ) ) );

            /* Skip first two lines as those are headers. */
            if( lineNumber <= 2 )
            {
                continue;
            }

            /* Parse the output. */
            filledVariables = sscanf( &( lineBuffer[ 0 ] ),
                                      "%*[^:]: %u %u %*u %*u %*u %*u %*u %*u "
                                      "%u %u %*u %*u %*u %*u %*u %*u",
                                      &( bytesReceived ),
                                      &( packetsReceived ),
                                      &( bytesSent ),
                                      &( packetsSent ) );

            /* sscanf should fill all the 4 variables successfully. */
            if( filledVariables != 4 )
            {
                LogError( ( "Failed to parse %s.", &( lineBuffer[ 0 ] ) ) );
                status = MetricsCollectorParsingFailed;
                break;
            }
            else
            {
                pOutNetworkStats->bytesReceived += bytesReceived;
                pOutNetworkStats->bytesSent += bytesSent;
                pOutNetworkStats->packetsReceived += packetsReceived;
                pOutNetworkStats->packetsSent += packetsSent;
            }
        }
    }

    if( fileHandle != NULL )
    {
        fclose( fileHandle );
    }

    return status;
}
/*-----------------------------------------------------------*/

MetricsCollectorStatus_t GetOpenTcpPorts( uint16_t * pOutTcpPortsArray,
                                          uint32_t tcpPortsArrayLength,
                                          uint32_t * pOutNumTcpOpenPorts )
{
    return getOpenPorts( "/proc/net/tcp",
                         pOutTcpPortsArray,
                         tcpPortsArrayLength,
                         pOutNumTcpOpenPorts );
}
/*-----------------------------------------------------------*/

MetricsCollectorStatus_t GetOpenUdpPorts( uint16_t * pOutUdpPortsArray,
                                          uint32_t udpPortsArrayLength,
                                          uint32_t * pOutNumUdpOpenPorts )
{
    return getOpenPorts( "/proc/net/udp",
                         pOutUdpPortsArray,
                         udpPortsArrayLength,
                         pOutNumUdpOpenPorts );
}
/*-----------------------------------------------------------*/

MetricsCollectorStatus_t GetEstablishedConnections( Connection_t * pOutConnectionsArray,
                                                    uint32_t connectionsArrayLength,
                                                    uint32_t * pOutNumEstablishedConnections )
{
    MetricsCollectorStatus_t status = MetricsCollectorSuccess;
    FILE * fileHandle = NULL;
    uint32_t lineNumber = 0, connectionStatus;
    int32_t filledVariables;
    uint32_t localIp, localPort, remoteIp, remotePort, numEstablishedConnections = 0;
    Connection_t * pEstablishedConnection;
    char lineBuffer[ MAX_LINE_LENGTH ];

    if( ( ( pOutConnectionsArray != NULL ) && ( connectionsArrayLength == 0 ) ) ||
        ( pOutNumEstablishedConnections == NULL ) )
    {
        LogError( ( "Invalid parameters. pOutConnectionsArray: %p,"
                    " connectionsArrayLength: %u, pOutNumEstablishedConnections: %p.",
                    ( void * ) pOutConnectionsArray,
                    connectionsArrayLength,
                    ( void * ) pOutNumEstablishedConnections ) );
        status = MetricsCollectorBadParameter;
    }

    if( status == MetricsCollectorSuccess )
    {
        fileHandle = fopen( "/proc/net/tcp", "r" );

        if( fileHandle == NULL )
        {
            LogError( ( "Failed to open /proc/net/tcp." ) );
            status = MetricsCollectorFileOpenFailed;
        }
    }

    if( status == MetricsCollectorSuccess )
    {
        while( fgets( &( lineBuffer[ 0 ] ), MAX_LINE_LENGTH, fileHandle ) != NULL )
        {
            lineNumber++;

            LogDebug( ( "File: /proc/net/tcp, Line: %u, Content: %s.",
                        lineNumber,
                        &( lineBuffer[ 0 ] ) ) );

            /* Skip the first line as it is a header. */
            if( lineNumber <= 1 )
            {
                continue;
            }

            /* Parse the output. */
            filledVariables = sscanf( &( lineBuffer[ 0 ] ),
                                      "%*[^:]: %8x:%4x %8x:%4x %2x",
                                      &( localIp ),
                                      &( localPort ),
                                      &( remoteIp ),
                                      &( remotePort ),
                                      &( connectionStatus ) );

            /* sscanf should fill all the 5 variables successfully. */
            if( filledVariables != 5 )
            {
                LogError( ( "Failed to parse %s.", &( lineBuffer[ 0 ] ) ) );
                status = MetricsCollectorParsingFailed;
                break;
            }

            if( connectionStatus == CONNECTION_STATUS_ESTABLISHED )
            {
                if( pOutConnectionsArray != NULL )
                {
                    /* The output array member to fill. */
                    pEstablishedConnection = &( pOutConnectionsArray[ numEstablishedConnections ] );

                    pEstablishedConnection->localIp = htonl( localIp );
                    pEstablishedConnection->remoteIp = htonl( remoteIp );
                    pEstablishedConnection->localPort = ( uint16_t ) localPort;
                    pEstablishedConnection->remotePort = ( uint16_t ) remotePort;

                    numEstablishedConnections++;

                    /* Break if the output array is full. */
                    if( connectionsArrayLength == numEstablishedConnections )
                    {
                        break;
                    }
                }
                else
                {
                    numEstablishedConnections++;
                }
            }
        }
    }

    if( status == MetricsCollectorSuccess )
    {
        *pOutNumEstablishedConnections = numEstablishedConnections;
    }

    if( fileHandle != NULL )
    {
        fclose( fileHandle );
    }

    return status;
}

/*-----------------------------------------------------------*/

MetricsCollectorStatus_t GetUptime( uint64_t * pUptime )
{
    MetricsCollectorStatus_t status = MetricsCollectorSuccess;
    FILE * fileHandle = NULL;
    int32_t filledVariables;
    char lineBuffer[ MAX_LINE_LENGTH ];

    if( pUptime == NULL )
    {
        LogError( ( "Invalid parameter; pUptime is null." ) );
        status = MetricsCollectorBadParameter;
    }

    if( status == MetricsCollectorSuccess )
    {
        fileHandle = fopen( "/proc/uptime", "r" );

        if( fileHandle == NULL )
        {
            LogError( ( "Failed to open /proc/uptime." ) );
            status = MetricsCollectorFileOpenFailed;
        }
    }

    if( status == MetricsCollectorSuccess )
    {
        if( fgets( &( lineBuffer[ 0 ] ), MAX_LINE_LENGTH, fileHandle ) != NULL )
        {
            LogDebug( ( "File: /proc/uptime, Content: %s.",
                        &( lineBuffer[ 0 ] ) ) );

            /* Parse the output. */
            filledVariables = sscanf( &( lineBuffer[ 0 ] ),
                                      "%lu",
                                      pUptime );

            /* sscanf should fill pUptime successfully. */
            if( filledVariables != 1 )
            {
                LogError( ( "Failed to parse CPU usage data. File: /proc/uptime, Data: %s.", &( lineBuffer[ 0 ] ) ) );
                status = MetricsCollectorParsingFailed;
            }
        }
    }

    if( fileHandle != NULL )
    {
        fclose( fileHandle );
    }

    return status;
}
/*-----------------------------------------------------------*/

MetricsCollectorStatus_t GetFreeMemory( uint64_t * pMemFree )
{
    MetricsCollectorStatus_t status = MetricsCollectorSuccess;
    FILE * fileHandle = NULL;
    int32_t filledVariables;
    char lineBuffer[ MAX_LINE_LENGTH ];

    if( pMemFree == NULL )
    {
        LogError( ( "Invalid parameter; pMemFree is null." ) );
        status = MetricsCollectorBadParameter;
    }

    if( status == MetricsCollectorSuccess )
    {
        fileHandle = fopen( "/proc/meminfo", "r" );

        if( fileHandle == NULL )
        {
            LogError( ( "Failed to open /proc/meminfo." ) );
            status = MetricsCollectorFileOpenFailed;
        }
    }

    if( status == MetricsCollectorSuccess )
    {
        while( fgets( &( lineBuffer[ 0 ] ), MAX_LINE_LENGTH, fileHandle ) != NULL )
        {
            /* Check if the line read is for free memory. */
            if( strncmp( lineBuffer, "MemFree:", 8 ) == 0 )
            {
                filledVariables = sscanf( lineBuffer,
                                          "%*s %lu",
                                          pMemFree );

                if( filledVariables != 1 )
                {
                    LogError( ( "Failed to parse memory data. File: /proc/memfree, Data: %s.", &( lineBuffer[ 0 ] ) ) );
                    status = MetricsCollectorParsingFailed;
                }

                break;
            }
        }
    }

    if( fileHandle != NULL )
    {
        fclose( fileHandle );
    }

    return status;
}
/*-----------------------------------------------------------*/

MetricsCollectorStatus_t GetCpuUserUsage( uint64_t * pOutCpuUserUsage,
                                          size_t cpuUserUsageLength,
                                          size_t * pOutNumCpuUserUsage )
{
    MetricsCollectorStatus_t status = MetricsCollectorSuccess;
    FILE * fileHandle = NULL;
    /* Variables for reading and processing data from "/proc/stat" file. */
    char lineBuffer[ MAX_LINE_LENGTH ];
    int32_t filledVariables = 0;

    *pOutNumCpuUserUsage = 0;

    if( pOutCpuUserUsage == NULL )
    {
        LogError( ( "Invalid parameter. pOutCpuUserUsage: %p", ( void * ) pOutCpuUserUsage ) );
        status = MetricsCollectorBadParameter;
    }

    if( status == MetricsCollectorSuccess )
    {
        fileHandle = fopen( "/proc/stat", "r" );

        if( fileHandle == NULL )
        {
            LogError( ( "Failed to open /proc/stat." ) );
            status = MetricsCollectorFileOpenFailed;
        }
    }

    if( status == MetricsCollectorSuccess )
    {
        while( ( *pOutNumCpuUserUsage < cpuUserUsageLength ) &&
               ( fgets( &( lineBuffer[ 0 ] ), MAX_LINE_LENGTH, fileHandle ) != NULL ) )
        {
            LogDebug( ( "File: /proc/stat, Content: %s.", &( lineBuffer[ 0 ] ) ) );

            /* Check if the line read is for a CPU. */
            if( strncmp( lineBuffer, "cpu", 3 ) == 0 )
            {
                filledVariables = sscanf( lineBuffer,
                                          "%*s %lu",
                                          &( pOutCpuUserUsage[ *pOutNumCpuUserUsage ] ) );

                if( filledVariables != 1 )
                {
                    LogError( ( "Failed to parse data. File: /proc/stat, Content: %s", lineBuffer ) );
                    status = MetricsCollectorParsingFailed;

                    break;
                }
                else
                {
                    *pOutNumCpuUserUsage += 1;
                }
            }
        }
    }

    if( fileHandle != NULL )
    {
        fclose( fileHandle );
    }

    return status;
}
/*-----------------------------------------------------------*/

MetricsCollectorStatus_t GetNetworkInferfaceInfo( char ( *pOutNetworkInterfaceNames )[ 16 ],
                                                  uint32_t * pOutNetworkInterfaceAddresses,
                                                  size_t bufferLength,
                                                  size_t * pOutNumNetworkInterfaces )
{
    MetricsCollectorStatus_t status = MetricsCollectorSuccess;
    FILE * fileHandle = NULL;
    /* Variables for reading and processing data from "/proc/net/arp" file. */
    char lineBuffer[ MAX_LINE_LENGTH ];
    int32_t filledVariables = 0;
    uint32_t ipPart1, ipPart2, ipPart3, ipPart4;

    *pOutNumNetworkInterfaces = 0;

    if( ( pOutNetworkInterfaceNames == NULL ) || ( pOutNetworkInterfaceAddresses == NULL ) )
    {
        LogError( ( "Invalid parameter. pOutNetworkInterfaceNames: %p, pOutNetworkInterfaceAddresses: %p",
                    ( void * ) pOutNetworkInterfaceNames,
                    ( void * ) pOutNetworkInterfaceAddresses ) );
        status = MetricsCollectorBadParameter;
    }

    if( status == MetricsCollectorSuccess )
    {
        fileHandle = fopen( "/proc/net/arp", "r" );

        if( fileHandle == NULL )
        {
            LogError( ( "Failed to open /proc/net/arp." ) );
            status = MetricsCollectorFileOpenFailed;
        }
    }

    if( status == MetricsCollectorSuccess )
    {
        /* Skip header line */
        if( fgets( &( lineBuffer[ 0 ] ), MAX_LINE_LENGTH, fileHandle ) != NULL )
        {
            while( ( *pOutNumNetworkInterfaces < bufferLength ) &&
                   ( fgets( &( lineBuffer[ 0 ] ), MAX_LINE_LENGTH, fileHandle ) != NULL ) )
            {
                LogDebug( ( "File: /proc/net/arp, Content: %s.", &( lineBuffer[ 0 ] ) ) );

                filledVariables = sscanf( lineBuffer,
                                          "%u.%u.%u.%u %*s %*s %*s %*s %15s",
                                          &ipPart1,
                                          &ipPart2,
                                          &ipPart3,
                                          &ipPart4,
                                          pOutNetworkInterfaceNames[ *pOutNumNetworkInterfaces ] );

                if( filledVariables != 5 )
                {
                    LogError( ( "Failed to parse data. File: /proc/net/arp, Content: %s", lineBuffer ) );
                    status = MetricsCollectorParsingFailed;

                    break;
                }
                else
                {
                    pOutNetworkInterfaceAddresses[ *pOutNumNetworkInterfaces ] = ( ipPart1 << 24 ) | ( ipPart2 << 16 ) | ( ipPart3 << 8 ) | ipPart4;
                    *pOutNumNetworkInterfaces += 1;
                }
            }
        }
    }

    if( fileHandle != NULL )
    {
        fclose( fileHandle );
    }

    return status;
}

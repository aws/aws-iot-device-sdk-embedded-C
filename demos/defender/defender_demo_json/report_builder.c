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

/* Standard includes. */
#include <stdio.h>
#include <string.h>
#include <assert.h>

/* Demo config. */
#include "demo_config.h"

/* Interface include. */
#include "report_builder.h"

/* Device Defender Library include. */
#include "defender.h"

/* Various JSON characters. */
#define JSON_ARRAY_OPEN_MARKER      '['
#define JSON_ARRAY_CLOSE_MARKER     ']'
#define JSON_OBJECT_OPEN_MARKER     '{'
#define JSON_OBJECT_CLOSE_MARKER    '}'
#define JSON_OBJECT_SEPARATOR       ','

/* Helper macro to check if snprintf was successful. */
#define SNPRINTF_SUCCESS( retVal, bufLen )    ( ( retVal > 0 ) && ( ( uint32_t ) retVal < bufLen ) )

/* Formats used to generate the JSON report. */
/* *INDENT-OFF* */
#define JSON_PORT_OBJECT_FORMAT          \
    "{"                                  \
    "\""DEFENDER_REPORT_PORT_KEY"\": %u" \
    "},"

#define JSON_CONNECTION_OBJECT_FORMAT                           \
    "{"                                                         \
    "\""DEFENDER_REPORT_LOCAL_PORT_KEY"\": %u,"                 \
    "\""DEFENDER_REPORT_REMOTE_ADDR_KEY"\": \"%u.%u.%u.%u:%u\"" \
    "},"

#define JSON_REPORT_FORMAT_PART1                       \
    "{"                                                \
    "\""DEFENDER_REPORT_HEADER_KEY"\": {"              \
    "\""DEFENDER_REPORT_ID_KEY"\": %u,"                \
    "\""DEFENDER_REPORT_VERSION_KEY"\": \"%u.%u\""     \
    "},"                                               \
    "\""DEFENDER_REPORT_METRICS_KEY"\": {"             \
    "\""DEFENDER_REPORT_TCP_LISTENING_PORTS_KEY"\": {" \
    "\""DEFENDER_REPORT_PORTS_KEY"\": "

#define JSON_REPORT_FORMAT_PART2                       \
    ","                                                \
    "\""DEFENDER_REPORT_TOTAL_KEY"\": %u"              \
    "},"                                               \
    "\""DEFENDER_REPORT_UDP_LISTENING_PORTS_KEY"\": {" \
    "\""DEFENDER_REPORT_PORTS_KEY"\": "

#define JSON_REPORT_FORMAT_PART3                           \
    ","                                                    \
    "\""DEFENDER_REPORT_TOTAL_KEY"\": %u"                  \
    "},"                                                   \
    "\""DEFENDER_REPORT_NETWORK_STATS_KEY"\": {"           \
    "\""DEFENDER_REPORT_BYTES_IN_KEY"\": %u,"              \
    "\""DEFENDER_REPORT_BYTES_OUT_KEY"\": %u,"             \
    "\""DEFENDER_REPORT_PKTS_IN_KEY"\": %u,"               \
    "\""DEFENDER_REPORT_PKTS_OUT_KEY"\": %u"               \
    "},"                                                   \
    "\""DEFENDER_REPORT_TCP_CONNECTIONS_KEY"\": {"         \
    "\""DEFENDER_REPORT_ESTABLISHED_CONNECTIONS_KEY"\": {" \
    "\""DEFENDER_REPORT_CONNECTIONS_KEY"\": "

#define JSON_REPORT_FORMAT_PART4                  \
    ","                                           \
    "\""DEFENDER_REPORT_TOTAL_KEY"\": %u"         \
    "}"                                           \
    "}"                                           \
    "},"                                          \
    "\""DEFENDER_REPORT_CUSTOM_METRICS_KEY"\": {" \
    "\"uptime\": [{"                              \
    "\""DEFENDER_REPORT_NUMBER_KEY"\": %lu"       \
    "}],"                                         \
    "\"free_mem\": [{"                            \
    "\""DEFENDER_REPORT_NUMBER_KEY"\": %lu"       \
    "}],"                                         \
    "\"cpu_user_usage\": [{"                      \
    "\""DEFENDER_REPORT_NUMBER_LIST_KEY"\": "

#define JSON_REPORT_FORMAT_PART5      \
    "}],"                             \
    "\"network_interface_names\": [{" \
    "\""DEFENDER_REPORT_STRING_LIST_KEY"\": "

#define JSON_REPORT_FORMAT_PART6          \
    "}],"                                 \
    "\"network_interface_addresses\": [{" \
    "\""DEFENDER_REPORT_IP_LIST_KEY"\": "

#define JSON_REPORT_FORMAT_PART7 \
    "}]"                         \
    "}"                          \
    "}"

/* *INDENT-ON* */

/*-----------------------------------------------------------*/

/**
 * @brief Write ports array to the given buffer in the format expected by the
 * AWS IoT Device Defender Service.
 *
 * This function writes an array of the following format:
 * [
 *    {
 *        "port":44207
 *    },
 *    {
 *        "port":53
 *    }
 * ]
 *
 * @param[in] pBuffer The buffer to write the ports array.
 * @param[in] bufferLength The length of the buffer.
 * @param[in] pOpenPortsArray The array containing the open ports.
 * @param[in] openPortsArrayLength Length of the pOpenPortsArray array.
 * @param[out] pOutCharsWritten Number of characters written to the buffer.
 *
 * @return #ReportBuilderSuccess if the array is successfully written;
 * #ReportBuilderBufferTooSmall if the buffer cannot hold the full array.
 */
static ReportBuilderStatus_t writePortsArray( char * pBuffer,
                                              uint32_t bufferLength,
                                              const uint16_t * pOpenPortsArray,
                                              uint32_t openPortsArrayLength,
                                              uint32_t * pOutCharsWritten );

/**
 * @brief Write established connections array to the given buffer in the format
 * expected by the AWS IoT Device Defender Service.
 *
 * This function writes array of the following format:
 * [
 *     {
 *         "local_port":44207,
 *         "remote_addr":"127.0.0.1:45148"
 *     },
 *     {
 *         "local_port":22,
 *         "remote_addr":"24.16.237.194:63552"
 *     }
 * ]
 *
 * @param[in] pBuffer The buffer to write the connections array.
 * @param[in] bufferLength The length of the buffer.
 * @param[in] pConnectionsArray The array containing the established connections.
 * @param[in] connectionsArrayLength Length of the pConnectionsArray array.
 * @param[out] pOutCharsWritten Number of characters written to the buffer.
 *
 * @return #ReportBuilderSuccess if the array is successfully written;
 * #ReportBuilderBufferTooSmall if the buffer cannot hold the full array.
 */
static ReportBuilderStatus_t writeConnectionsArray( char * pBuffer,
                                                    uint32_t bufferLength,
                                                    const Connection_t * pConnectionsArray,
                                                    uint32_t connectionsArrayLength,
                                                    uint32_t * pOutCharsWritten );

/*-----------------------------------------------------------*/

static ReportBuilderStatus_t writePortsArray( char * pBuffer,
                                              uint32_t bufferLength,
                                              const uint16_t * pOpenPortsArray,
                                              uint32_t openPortsArrayLength,
                                              uint32_t * pOutCharsWritten )
{
    char * pCurrentWritePos = pBuffer;
    uint32_t i, remainingBufferLength = bufferLength;
    int charactersWritten;
    ReportBuilderStatus_t status = ReportBuilderSuccess;

    assert( pBuffer != NULL );
    assert( bufferLength != 0 );
    assert( pOpenPortsArray != NULL );
    assert( pOutCharsWritten != NULL );

    /* Write the JSON array open marker. */
    if( remainingBufferLength > 1 )
    {
        *pCurrentWritePos = JSON_ARRAY_OPEN_MARKER;
        remainingBufferLength -= 1;
        pCurrentWritePos += 1;
    }
    else
    {
        status = ReportBuilderBufferTooSmall;
    }

    /* Write the array elements. */
    for( i = 0; ( ( i < openPortsArrayLength ) && ( status == ReportBuilderSuccess ) ); i++ )
    {
        charactersWritten = snprintf( pCurrentWritePos,
                                      remainingBufferLength,
                                      JSON_PORT_OBJECT_FORMAT,
                                      pOpenPortsArray[ i ] );

        if( !SNPRINTF_SUCCESS( charactersWritten, remainingBufferLength ) )
        {
            status = ReportBuilderBufferTooSmall;
            break;
        }
        else
        {
            remainingBufferLength -= ( uint32_t ) charactersWritten;
            pCurrentWritePos += charactersWritten;
        }
    }

    if( status == ReportBuilderSuccess )
    {
        /* Discard the last comma. */
        if( openPortsArrayLength > 0 )
        {
            pCurrentWritePos -= 1;
            remainingBufferLength += 1;
        }

        /* Write the JSON array close marker. */
        if( remainingBufferLength > 1 )
        {
            *pCurrentWritePos = JSON_ARRAY_CLOSE_MARKER;
            remainingBufferLength -= 1;
            pCurrentWritePos += 1;
        }
        else
        {
            status = ReportBuilderBufferTooSmall;
        }
    }

    if( status == ReportBuilderSuccess )
    {
        *pOutCharsWritten = bufferLength - remainingBufferLength;
    }

    return status;
}
/*-----------------------------------------------------------*/

static ReportBuilderStatus_t writeConnectionsArray( char * pBuffer,
                                                    uint32_t bufferLength,
                                                    const Connection_t * pConnectionsArray,
                                                    uint32_t connectionsArrayLength,
                                                    uint32_t * pOutCharsWritten )
{
    char * pCurrentWritePos = pBuffer;
    uint32_t i, remainingBufferLength = bufferLength;
    int charactersWritten;
    ReportBuilderStatus_t status = ReportBuilderSuccess;
    const Connection_t * pConn;

    assert( pBuffer != NULL );
    assert( bufferLength != 0 );
    assert( pConnectionsArray != NULL );
    assert( pOutCharsWritten != NULL );

    /* Write the JSON array open marker. */
    if( remainingBufferLength > 1 )
    {
        *pCurrentWritePos = JSON_ARRAY_OPEN_MARKER;
        remainingBufferLength -= 1;
        pCurrentWritePos += 1;
    }
    else
    {
        status = ReportBuilderBufferTooSmall;
    }

    /* Write the array elements. */
    for( i = 0; ( ( i < connectionsArrayLength ) && ( status == ReportBuilderSuccess ) ); i++ )
    {
        pConn = &( pConnectionsArray[ i ] );
        charactersWritten = snprintf( pCurrentWritePos,
                                      remainingBufferLength,
                                      JSON_CONNECTION_OBJECT_FORMAT,
                                      pConn->localPort,
                                      ( pConn->remoteIp >> 24 ) & 0xFF,
                                      ( pConn->remoteIp >> 16 ) & 0xFF,
                                      ( pConn->remoteIp >> 8 ) & 0xFF,
                                      ( pConn->remoteIp ) & 0xFF,
                                      pConn->remotePort );

        if( !SNPRINTF_SUCCESS( charactersWritten, remainingBufferLength ) )
        {
            status = ReportBuilderBufferTooSmall;
            break;
        }
        else
        {
            remainingBufferLength -= ( unsigned ) charactersWritten;
            pCurrentWritePos += charactersWritten;
        }
    }

    if( status == ReportBuilderSuccess )
    {
        /* Discard the last comma. */
        if( connectionsArrayLength > 0 )
        {
            pCurrentWritePos -= 1;
            remainingBufferLength += 1;
        }

        /* Write the JSON array close marker. */
        if( remainingBufferLength > 1 )
        {
            *pCurrentWritePos = JSON_ARRAY_CLOSE_MARKER;
            remainingBufferLength -= 1;
            pCurrentWritePos += 1;
        }
        else
        {
            status = ReportBuilderBufferTooSmall;
        }
    }

    if( status == ReportBuilderSuccess )
    {
        *pOutCharsWritten = bufferLength - remainingBufferLength;
    }

    return status;
}

/*-----------------------------------------------------------*/

static ReportBuilderStatus_t writeCpuUsage( char * pBuffer,
                                            uint32_t bufferLength,
                                            uint64_t * pCpuUserUsage,
                                            size_t cpuCount,
                                            uint32_t * pOutCharsWritten )
{
    char * pCurrentWritePos = pBuffer;
    uint32_t i, remainingBufferLength = bufferLength;
    int charactersWritten;
    ReportBuilderStatus_t status = ReportBuilderSuccess;

    assert( pBuffer != NULL );
    assert( bufferLength != 0 );
    assert( pCpuUserUsage != NULL );
    assert( pOutCharsWritten != NULL );

    /* Write the JSON array open marker. */
    if( remainingBufferLength > 1 )
    {
        *pCurrentWritePos = JSON_ARRAY_OPEN_MARKER;
        remainingBufferLength -= 1;
        pCurrentWritePos += 1;
    }
    else
    {
        status = ReportBuilderBufferTooSmall;
    }

    /* Write the array elements. */
    for( i = 0; ( ( i < cpuCount ) && ( status == ReportBuilderSuccess ) ); i++ )
    {
        charactersWritten = snprintf( pCurrentWritePos,
                                      remainingBufferLength,
                                      "%lu,",
                                      pCpuUserUsage[ i ] );

        if( !SNPRINTF_SUCCESS( charactersWritten, remainingBufferLength ) )
        {
            status = ReportBuilderBufferTooSmall;
            break;
        }
        else
        {
            remainingBufferLength -= ( unsigned ) charactersWritten;
            pCurrentWritePos += charactersWritten;
        }
    }

    if( status == ReportBuilderSuccess )
    {
        /* Discard the last comma. */
        if( cpuCount > 0 )
        {
            pCurrentWritePos -= 1;
            remainingBufferLength += 1;
        }

        /* Write the JSON array close marker. */
        if( remainingBufferLength > 1 )
        {
            *pCurrentWritePos = JSON_ARRAY_CLOSE_MARKER;
            remainingBufferLength -= 1;
            pCurrentWritePos += 1;
        }
        else
        {
            status = ReportBuilderBufferTooSmall;
        }
    }

    if( status == ReportBuilderSuccess )
    {
        *pOutCharsWritten = bufferLength - remainingBufferLength;
    }

    return status;
}

/*-----------------------------------------------------------*/

static ReportBuilderStatus_t writeNetworkInterfaceNames( char * pBuffer,
                                                         uint32_t bufferLength,
                                                         char ( *pNetworkInterfaceNames )[ 16 ],
                                                         size_t networkInterfaceCount,
                                                         uint32_t * pOutCharsWritten )
{
    char * pCurrentWritePos = pBuffer;
    uint32_t i, remainingBufferLength = bufferLength;
    int charactersWritten;
    ReportBuilderStatus_t status = ReportBuilderSuccess;

    assert( pBuffer != NULL );
    assert( bufferLength != 0 );
    assert( pNetworkInterfaceNames != NULL );
    assert( pOutCharsWritten != NULL );

    /* Write the JSON array open marker. */
    if( remainingBufferLength > 1 )
    {
        *pCurrentWritePos = JSON_ARRAY_OPEN_MARKER;
        remainingBufferLength -= 1;
        pCurrentWritePos += 1;
    }
    else
    {
        status = ReportBuilderBufferTooSmall;
    }

    /* Write the array elements. */
    for( i = 0; ( ( i < networkInterfaceCount ) && ( status == ReportBuilderSuccess ) ); i++ )
    {
        charactersWritten = snprintf( pCurrentWritePos,
                                      remainingBufferLength,
                                      "\"%s\",",
                                      pNetworkInterfaceNames[ i ] );

        if( !SNPRINTF_SUCCESS( charactersWritten, remainingBufferLength ) )
        {
            status = ReportBuilderBufferTooSmall;
            break;
        }
        else
        {
            remainingBufferLength -= ( unsigned ) charactersWritten;
            pCurrentWritePos += charactersWritten;
        }
    }

    if( status == ReportBuilderSuccess )
    {
        /* Discard the last comma. */
        if( networkInterfaceCount > 0 )
        {
            pCurrentWritePos -= 1;
            remainingBufferLength += 1;
        }

        /* Write the JSON array close marker. */
        if( remainingBufferLength > 1 )
        {
            *pCurrentWritePos = JSON_ARRAY_CLOSE_MARKER;
            remainingBufferLength -= 1;
            pCurrentWritePos += 1;
        }
        else
        {
            status = ReportBuilderBufferTooSmall;
        }
    }

    if( status == ReportBuilderSuccess )
    {
        *pOutCharsWritten = bufferLength - remainingBufferLength;
    }

    return status;
}

/*-----------------------------------------------------------*/

static ReportBuilderStatus_t writeNetworkInterfaceAddresses( char * pBuffer,
                                                             uint32_t bufferLength,
                                                             uint32_t * pNetworkInterfaceAddresses,
                                                             size_t networkInterfaceCount,
                                                             uint32_t * pOutCharsWritten )
{
    char * pCurrentWritePos = pBuffer;
    uint32_t i, remainingBufferLength = bufferLength;
    int charactersWritten;
    ReportBuilderStatus_t status = ReportBuilderSuccess;

    assert( pBuffer != NULL );
    assert( bufferLength != 0 );
    assert( pNetworkInterfaceAddresses != NULL );
    assert( pOutCharsWritten != NULL );

    /* Write the JSON array open marker. */
    if( remainingBufferLength > 1 )
    {
        *pCurrentWritePos = JSON_ARRAY_OPEN_MARKER;
        remainingBufferLength -= 1;
        pCurrentWritePos += 1;
    }
    else
    {
        status = ReportBuilderBufferTooSmall;
    }

    /* Write the array elements. */
    for( i = 0; ( ( i < networkInterfaceCount ) && ( status == ReportBuilderSuccess ) ); i++ )
    {
        charactersWritten = snprintf( pCurrentWritePos,
                                      remainingBufferLength,
                                      "\"%u.%u.%u.%u\",",
                                      ( pNetworkInterfaceAddresses[ i ] >> 24 ) & 0xFF,
                                      ( pNetworkInterfaceAddresses[ i ] >> 16 ) & 0xFF,
                                      ( pNetworkInterfaceAddresses[ i ] >> 8 ) & 0xFF,
                                      ( pNetworkInterfaceAddresses[ i ] ) & 0xFF );

        if( !SNPRINTF_SUCCESS( charactersWritten, remainingBufferLength ) )
        {
            status = ReportBuilderBufferTooSmall;
            break;
        }
        else
        {
            remainingBufferLength -= ( unsigned ) charactersWritten;
            pCurrentWritePos += charactersWritten;
        }
    }

    if( status == ReportBuilderSuccess )
    {
        /* Discard the last comma. */
        if( networkInterfaceCount > 0 )
        {
            pCurrentWritePos -= 1;
            remainingBufferLength += 1;
        }

        /* Write the JSON array close marker. */
        if( remainingBufferLength > 1 )
        {
            *pCurrentWritePos = JSON_ARRAY_CLOSE_MARKER;
            remainingBufferLength -= 1;
            pCurrentWritePos += 1;
        }
        else
        {
            status = ReportBuilderBufferTooSmall;
        }
    }

    if( status == ReportBuilderSuccess )
    {
        *pOutCharsWritten = bufferLength - remainingBufferLength;
    }

    return status;
}

/*-----------------------------------------------------------*/

ReportBuilderStatus_t GenerateJsonReport( char * pBuffer,
                                          uint32_t bufferLength,
                                          const ReportMetrics_t * pMetrics,
                                          uint32_t majorReportVersion,
                                          uint32_t minorReportVersion,
                                          uint32_t reportId,
                                          uint32_t * pOutReportLength )
{
    char * pCurrentWritePos = pBuffer;
    uint32_t remainingBufferLength = bufferLength, bufferWritten;
    ReportBuilderStatus_t status = ReportBuilderSuccess;
    int charactersWritten;

    if( ( pBuffer == NULL ) ||
        ( bufferLength == 0 ) ||
        ( pMetrics == NULL ) ||
        ( pOutReportLength == NULL ) )
    {
        LogError( ( "Invalid parameters. pBuffer: %p, bufferLength: %u"
                    " pMetrics: %p, pOutReportLength: %p.",
                    ( void * ) pBuffer,
                    bufferLength,
                    ( const void * ) pMetrics,
                    ( void * ) pOutReportLength ) );
        status = ReportBuilderBadParameter;
    }

    /* Write part1. */
    if( status == ReportBuilderSuccess )
    {
        charactersWritten = snprintf( pCurrentWritePos,
                                      remainingBufferLength,
                                      JSON_REPORT_FORMAT_PART1,
                                      reportId,
                                      majorReportVersion,
                                      minorReportVersion );

        if( !SNPRINTF_SUCCESS( charactersWritten, remainingBufferLength ) )
        {
            LogError( ( "Failed to write part 1." ) );
            status = ReportBuilderBufferTooSmall;
        }
        else
        {
            remainingBufferLength -= ( unsigned ) charactersWritten;
            pCurrentWritePos += charactersWritten;
        }
    }

    /* Write TCP ports array. */
    if( status == ReportBuilderSuccess )
    {
        status = writePortsArray( pCurrentWritePos,
                                  remainingBufferLength,
                                  pMetrics->pOpenTcpPortsArray,
                                  pMetrics->openTcpPortsArrayLength,
                                  &( bufferWritten ) );

        if( status == ReportBuilderSuccess )
        {
            pCurrentWritePos += bufferWritten;
            remainingBufferLength -= bufferWritten;
        }
        else
        {
            LogError( ( "Failed to write TCP ports array." ) );
        }
    }

    /* Write part2. */
    if( status == ReportBuilderSuccess )
    {
        charactersWritten = snprintf( pCurrentWritePos,
                                      remainingBufferLength,
                                      JSON_REPORT_FORMAT_PART2,
                                      pMetrics->openTcpPortsArrayLength );

        if( !SNPRINTF_SUCCESS( charactersWritten, remainingBufferLength ) )
        {
            LogError( ( "Failed to write part 2." ) );
            status = ReportBuilderBufferTooSmall;
        }
        else
        {
            remainingBufferLength -= ( unsigned ) charactersWritten;
            pCurrentWritePos += charactersWritten;
        }
    }

    /* Write UDP ports array. */
    if( status == ReportBuilderSuccess )
    {
        status = writePortsArray( pCurrentWritePos,
                                  remainingBufferLength,
                                  pMetrics->pOpenUdpPortsArray,
                                  pMetrics->openUdpPortsArrayLength,
                                  &( bufferWritten ) );

        if( status == ReportBuilderSuccess )
        {
            pCurrentWritePos += bufferWritten;
            remainingBufferLength -= bufferWritten;
        }
        else
        {
            LogError( ( "Failed to write UDP ports array." ) );
        }
    }

    /* Write part3. */
    if( status == ReportBuilderSuccess )
    {
        charactersWritten = snprintf( pCurrentWritePos,
                                      remainingBufferLength,
                                      JSON_REPORT_FORMAT_PART3,
                                      pMetrics->openUdpPortsArrayLength,
                                      pMetrics->pNetworkStats->bytesReceived,
                                      pMetrics->pNetworkStats->bytesSent,
                                      pMetrics->pNetworkStats->packetsReceived,
                                      pMetrics->pNetworkStats->packetsSent );

        if( !SNPRINTF_SUCCESS( charactersWritten, remainingBufferLength ) )
        {
            LogError( ( "Failed to write part 3." ) );
            status = ReportBuilderBufferTooSmall;
        }
        else
        {
            remainingBufferLength -= ( unsigned ) charactersWritten;
            pCurrentWritePos += charactersWritten;
        }
    }

    /* Write connections array. */
    if( status == ReportBuilderSuccess )
    {
        status = writeConnectionsArray( pCurrentWritePos,
                                        remainingBufferLength,
                                        pMetrics->pEstablishedConnectionsArray,
                                        pMetrics->establishedConnectionsArrayLength,
                                        &( bufferWritten ) );

        if( status == ReportBuilderSuccess )
        {
            pCurrentWritePos += bufferWritten;
            remainingBufferLength -= bufferWritten;
        }
        else
        {
            LogError( ( "Failed to write established connections array." ) );
        }
    }

    /* Write part4. */
    if( status == ReportBuilderSuccess )
    {
        charactersWritten = snprintf( pCurrentWritePos,
                                      remainingBufferLength,
                                      JSON_REPORT_FORMAT_PART4,
                                      pMetrics->establishedConnectionsArrayLength,
                                      pMetrics->customMetrics.uptime,
                                      pMetrics->customMetrics.memFree );

        if( !SNPRINTF_SUCCESS( charactersWritten, remainingBufferLength ) )
        {
            LogError( ( "Failed to write part 4." ) );
            status = ReportBuilderBufferTooSmall;
        }
        else
        {
            remainingBufferLength -= ( unsigned ) charactersWritten;
            pCurrentWritePos += charactersWritten;
        }
    }

    /* Write CPU usage array. */
    if( status == ReportBuilderSuccess )
    {
        status = writeCpuUsage( pCurrentWritePos,
                                remainingBufferLength,
                                pMetrics->customMetrics.pCpuUserUsage,
                                pMetrics->customMetrics.cpuCount,
                                &( bufferWritten ) );

        if( status == ReportBuilderSuccess )
        {
            pCurrentWritePos += bufferWritten;
            remainingBufferLength -= bufferWritten;
        }
        else
        {
            LogError( ( "Failed to write CPU usage array." ) );
        }
    }

    /* Write part5. */
    if( status == ReportBuilderSuccess )
    {
        charactersWritten = snprintf( pCurrentWritePos,
                                      remainingBufferLength,
                                      JSON_REPORT_FORMAT_PART5 );

        if( !SNPRINTF_SUCCESS( charactersWritten, remainingBufferLength ) )
        {
            LogError( ( "Failed to write part 5." ) );
            status = ReportBuilderBufferTooSmall;
        }
        else
        {
            remainingBufferLength -= ( unsigned ) charactersWritten;
            pCurrentWritePos += charactersWritten;
        }
    }

    /* Write network interface name array. */
    if( status == ReportBuilderSuccess )
    {
        status = writeNetworkInterfaceNames( pCurrentWritePos,
                                             remainingBufferLength,
                                             pMetrics->customMetrics.pNetworkInterfaceNames,
                                             pMetrics->customMetrics.networkInterfaceCount,
                                             &( bufferWritten ) );

        if( status == ReportBuilderSuccess )
        {
            pCurrentWritePos += bufferWritten;
            remainingBufferLength -= bufferWritten;
        }
        else
        {
            LogError( ( "Failed to write network interface name array." ) );
        }
    }

    /* Write part6. */
    if( status == ReportBuilderSuccess )
    {
        charactersWritten = snprintf( pCurrentWritePos,
                                      remainingBufferLength,
                                      JSON_REPORT_FORMAT_PART6 );

        if( !SNPRINTF_SUCCESS( charactersWritten, remainingBufferLength ) )
        {
            LogError( ( "Failed to write part 6." ) );
            status = ReportBuilderBufferTooSmall;
        }
        else
        {
            remainingBufferLength -= ( unsigned ) charactersWritten;
            pCurrentWritePos += charactersWritten;
        }
    }

    /* Write network interface address array. */
    if( status == ReportBuilderSuccess )
    {
        status = writeNetworkInterfaceAddresses( pCurrentWritePos,
                                                 remainingBufferLength,
                                                 pMetrics->customMetrics.pNetworkInterfaceAddresses,
                                                 pMetrics->customMetrics.networkInterfaceCount,
                                                 &( bufferWritten ) );

        if( status == ReportBuilderSuccess )
        {
            pCurrentWritePos += bufferWritten;
            remainingBufferLength -= bufferWritten;
        }
        else
        {
            LogError( ( "Failed to write network interface address array." ) );
        }
    }

    /* Write part7. */
    if( status == ReportBuilderSuccess )
    {
        charactersWritten = snprintf( pCurrentWritePos,
                                      remainingBufferLength,
                                      JSON_REPORT_FORMAT_PART7 );

        if( !SNPRINTF_SUCCESS( charactersWritten, remainingBufferLength ) )
        {
            LogError( ( "Failed to write part 7." ) );
            status = ReportBuilderBufferTooSmall;
        }
        else
        {
            remainingBufferLength -= ( unsigned ) charactersWritten;
            pCurrentWritePos += charactersWritten;
        }
    }

    if( status == ReportBuilderSuccess )
    {
        *pOutReportLength = bufferLength - remainingBufferLength;
    }

    return status;
}
/*-----------------------------------------------------------*/

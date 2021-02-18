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

/* Standard includes. */
#include <stdio.h>
#include <string.h>
#include <assert.h>

/* Demo config. */
#include "demo_config.h"

/* Device Defender Library include. */
#include "defender.h"

/* Interface include. */
#include "report_builder.h"

/* Various JSON characters. */
#define JSON_ARRAY_OPEN_MARKER      '['
#define JSON_ARRAY_CLOSE_MARKER     ']'
#define JSON_OBJECT_OPEN_MARKER     '{'
#define JSON_OBJECT_CLOSE_MARKER    '}'
#define JSON_OBJECT_SEPARATOR       ','

/* Helper macro to check if snprintf was successful. */
#define SNPRINTF_SUCCESS( retVal, bufLen )    ( ( retVal > 0 ) && ( ( uint32_t ) retVal < bufLen ) )


#define CUSTOM_METRIC_CPU_USAGE    "cpu_usage"

/* Formats used to generate the JSON report. */
#define JSON_PORT_OBJECT_FORMAT \
    "{"                         \
    "\"port\": %u"              \
    "},"

#define JSON_CONNECTION_OBJECT_FORMAT     \
    "{"                                   \
    "\"local_port\": %u,"                 \
    "\"remote_addr\": \"%u.%u.%u.%u:%u\"" \
    "},"

#define JSON_REPORT_FORMAT_PART1 \
    "{"                          \
    "\"header\": {"              \
    "\"report_id\": %u,"         \
    "\"version\": \"%u.%u\""     \
    "},"                         \
    "\"metrics\": {"             \
    "\"listening_tcp_ports\": {" \
    "\"ports\": "

#define JSON_REPORT_FORMAT_PART2 \
    ","                          \
    "\"total\": %u"              \
    "},"                         \
    "\"listening_udp_ports\": {" \
    "\"ports\": "

#define JSON_REPORT_FORMAT_PART3     \
    ","                              \
    "\"total\": %u"                  \
    "},"                             \
    "\"network_stats\": {"           \
    "\"bytes_in\": %u,"              \
    "\"bytes_out\": %u,"             \
    "\"packets_in\": %u,"            \
    "\"packets_out\": %u"            \
    "},"                             \
    "\"tcp_connections\": {"         \
    "\"established_connections\": {" \
    "\"connections\": "

#define JSON_REPORT_FORMAT_PART4 \
    ","                          \
    "\"total\": %u"              \
    "}"                          \
    "}"                          \
    "}"

#define JSON_REPORT_CUSTOM_METRIC_START \
    ",\"custom_metrics\":{"

#define JSON_REPORT_CUSTOM_METRIC_NUMBER_DATA_FORMAT    "%ld,"
#define JSON_REPORT_CUSTOM_METRIC_STRING_DATA_FORMAT    "%s,"
#define JSON_REPORT_CUSTOM_METRIC_IP_DATA_FORMAT        "%u.%u.%u.%u,"

#define JSON_REPORT_CUSTOM_METRIC_NUMBER_FORMAT \
    "\"%s\":["                                  \
    "{"                                         \
    "\"number\":%lld"                           \
    "}"                                         \
    "],"

#define JSON_REPORT_CUSTOM_METRIC_LIST_START \
    "\"%s\": ["                              \
    "{"                                      \
    "\"%s\": "

#define JSON_REPORT_CUSTOM_METRIC_LIST_END \
    "}"                                    \
    "],"

#define JSON_REPORT_CUSTOM_METRIC_END \
    "}"

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
 * This function write array of the following format:
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
            remainingBufferLength -= charactersWritten;
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

static ReportBuilderStatus_t writeCustomMetricListData( char * pBuffer,
                                                        uint32_t bufferLength,
                                                        CustomMetricBase_t * pCustomMetric,
                                                        uint32_t * pOutCharsWritten )
{
    char * pCurrentWritePos = pBuffer;
    uint32_t i, remainingBufferLength = bufferLength;
    int charactersWritten;
    ReportBuilderStatus_t status = ReportBuilderSuccess;
    uint32_t listLength = 0UL;

    assert( pBuffer != NULL );
    assert( pCustomMetric != NULL );
    assert( ( pCustomMetric->metricType == CustomMetricTypeNumberList ) ||
            ( pCustomMetric->metricType == CustomMetricTypeStringList ) ||
            ( pCustomMetric->metricType == CustomMetricTypeIpList ) );
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

    if( pCustomMetric->metricType == CustomMetricTypeNumberList )
    {
        listLength = ( ( CustomMetricNumberList_t * ) pCustomMetric )->numberListLength;
    }
    else if( pCustomMetric->metricType == CustomMetricTypeStringList )
    {
        listLength = ( ( CustomMetricStringList_t * ) pCustomMetric )->numOfStrings;
    }
    else
    {
        listLength = ( ( CustomMetricIpList_t * ) pCustomMetric )->numOfAddresses;
    }

    /* Write the array elements. */
    for( i = 0; ( ( i < listLength ) && ( status == ReportBuilderSuccess ) ); i++ )
    {
        if( pCustomMetric->metricType == CustomMetricTypeNumberList )
        {
            charactersWritten = snprintf( pCurrentWritePos,
                                          remainingBufferLength,
                                          JSON_REPORT_CUSTOM_METRIC_NUMBER_DATA_FORMAT,
                                          ( ( CustomMetricNumberList_t * ) pCustomMetric )->numbers[ i ] );
        }
        else if( pCustomMetric->metricType == CustomMetricTypeStringList )
        {
            charactersWritten = snprintf( pCurrentWritePos,
                                          remainingBufferLength,
                                          JSON_REPORT_CUSTOM_METRIC_STRING_DATA_FORMAT,
                                          ( ( CustomMetricStringList_t * ) pCustomMetric )->strings[ i ] );
        }
        else
        {
            uint32_t ipAddr = ( ( CustomMetricIpList_t * ) pCustomMetric )->ipAddress[ i ];
            charactersWritten = snprintf( pCurrentWritePos,
                                          remainingBufferLength,
                                          JSON_REPORT_CUSTOM_METRIC_IP_DATA_FORMAT,
                                          ( ( ipAddr >> 24 ) & 0xFF ),
                                          ( ( ipAddr >> 16 ) & 0xFF ),
                                          ( ( ipAddr >> 8 ) & 0xFF ),
                                          ( ipAddr & 0xFF ) );
        }

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
        pCurrentWritePos -= 1;
        remainingBufferLength += 1;

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
                    ( void * ) pMetrics,
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
            remainingBufferLength -= charactersWritten;
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
            remainingBufferLength -= charactersWritten;
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
            remainingBufferLength -= charactersWritten;
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
                                      pMetrics->establishedConnectionsArrayLength );

        if( !SNPRINTF_SUCCESS( charactersWritten, remainingBufferLength ) )
        {
            LogError( ( "Failed to write part 4." ) );
            status = ReportBuilderBufferTooSmall;
        }
        else
        {
            remainingBufferLength -= charactersWritten;
            pCurrentWritePos += charactersWritten;
        }
    }

    /* If provides, write custom metrics metrics. */
    if( status == ReportBuilderSuccess )
    {
        if( pMetrics->pCustomMetrics != NULL )
        {
            assert( pMetrics->numOfCustomMetrics > 0UL );

            uint32_t index = 0;

            /* Write start of custom metrics object. */
            charactersWritten = snprintf( pCurrentWritePos,
                                          remainingBufferLength,
                                          JSON_REPORT_CUSTOM_METRIC_START );

            if( !SNPRINTF_SUCCESS( charactersWritten, remainingBufferLength ) )
            {
                LogError( ( "Failed to write starting of custom metrics object." ) );
                status = ReportBuilderBufferTooSmall;
            }
            else
            {
                remainingBufferLength -= charactersWritten;
                pCurrentWritePos += charactersWritten;
            }

            for( ; index < pMetrics->numOfCustomMetrics; index++ )
            {
                /* Write start of nested JSON object for list of numbers type of custom metric. */
                charactersWritten = snprintf( pCurrentWritePos,
                                              remainingBufferLength,
                                              JSON_REPORT_CUSTOM_METRIC_LIST_START,
                                              pMetrics->pCustomMetrics[ index ]->pMetricName,
                                              DEFENDER_REPORT_NUMBER_LIST_KEY );

                if( !SNPRINTF_SUCCESS( charactersWritten, remainingBufferLength ) )
                {
                    LogError( ( "Failed to write starting of number list type of custom metric object." ) );
                    status = ReportBuilderBufferTooSmall;
                }
                else
                {
                    remainingBufferLength -= charactersWritten;
                    pCurrentWritePos += charactersWritten;
                }

                switch( pMetrics->pCustomMetrics[ index ]->metricType )
                {
                    case CustomMetricTypeNumber:
                        /* Write nested data list of numbers in the report. */
                        bufferWritten = snprintf( pCurrentWritePos,
                                                  remainingBufferLength,
                                                  "%ld",
                                                  ( ( CustomMetricNumber_t * ) pMetrics->pCustomMetrics[ index ] )->number );

                        if( !SNPRINTF_SUCCESS( charactersWritten, remainingBufferLength ) )
                        {
                            LogError( ( "Failed to write number for number type custom metric object." ) );
                            status = ReportBuilderBufferTooSmall;
                        }

                        break;

                    case CustomMetricTypeNumberList:
                    case CustomMetricTypeStringList:
                    case CustomMetricTypeIpList:

                        /* Write nested data list of numbers in the report. */
                        status = writeCustomMetricListData( pCurrentWritePos,
                                                            remainingBufferLength,
                                                            pMetrics->pCustomMetrics[ index ],
                                                            &( bufferWritten ) );

                        if( status != ReportBuilderSuccess )
                        {
                            LogError( ( "Failed to write custom metric data of list of numbers." ) );
                        }

                        break;

                    case CustomMetricTypeUknown:
                        LogError( ( "Received invalid type of custom metric object: IndexInCustomMetricsArray=%u, Type=%u",
                                    index, pMetrics->pCustomMetrics[ index ]->metricType ) );
                        break;
                }

                if( status == ReportBuilderSuccess )
                {
                    pCurrentWritePos += bufferWritten;
                    remainingBufferLength -= bufferWritten;
                }

                /* Write end of nested JSON object for list of numbers type of custom metric. */
                charactersWritten = snprintf( pCurrentWritePos,
                                              remainingBufferLength,
                                              JSON_REPORT_CUSTOM_METRIC_LIST_END );

                if( !SNPRINTF_SUCCESS( charactersWritten, remainingBufferLength ) )
                {
                    LogError( ( "Failed to write end of number list type of custom metric object." ) );
                    status = ReportBuilderBufferTooSmall;
                }
                else
                {
                    remainingBufferLength -= charactersWritten;
                    pCurrentWritePos += charactersWritten;
                }
            }

            /* Discard the last comma. */
            pCurrentWritePos -= 1;
            remainingBufferLength += 1;

            /* Write end of JSON object for custom metrics. */
            charactersWritten = snprintf( pCurrentWritePos,
                                          remainingBufferLength,
                                          JSON_REPORT_CUSTOM_METRIC_END );

            if( !SNPRINTF_SUCCESS( charactersWritten, remainingBufferLength ) )
            {
                LogError( ( "Failed to end of custom metrics object." ) );
                status = ReportBuilderBufferTooSmall;
            }
            else
            {
                remainingBufferLength -= charactersWritten;
                pCurrentWritePos += charactersWritten;
            }
        }
    }

    if( status == ReportBuilderSuccess )
    {
        /* Write closing JSON bracket. */
        if( remainingBufferLength > 0 )
        {
            *pCurrentWritePos = JSON_OBJECT_CLOSE_MARKER;
            remainingBufferLength -= charactersWritten;
            pCurrentWritePos++;
        }
        else
        {
            LogError( ( "Failed to end of JSON report with \"}\" marker." ) );
            status = ReportBuilderBufferTooSmall;
        }
    }

    if( status == ReportBuilderSuccess )
    {
        *pOutReportLength = bufferLength - remainingBufferLength;
    }

    return status;
}
/*-----------------------------------------------------------*/

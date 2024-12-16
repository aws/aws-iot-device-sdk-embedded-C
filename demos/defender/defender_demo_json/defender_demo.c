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

/*
 * Demo for showing how to use the Device Defender library's APIs. The Device
 * Defender library provides macros and helper functions for assembling MQTT
 * topics strings, and for determining whether an incoming MQTT message is
 * related to device defender. The Device Defender library does not depend on
 * any particular MQTT library, therefore the code for MQTT operations is
 * placed in another file (mqtt_operations.c). This demo uses the coreMQTT
 * library. If needed, mqtt_operations.c can be modified to replace coreMQTT
 * with another MQTT library. This demo requires using the AWS IoT broker as
 * Device Defender is an AWS service.
 *
 * This demo connects to the AWS IoT broker and subscribes to the device
 * defender topics. It then collects metrics for the open ports and sockets on
 * the device using FreeRTOS+TCP, and generates a device defender report. The
 * report is then published, and the demo waits for a response from the device
 * defender service. Upon receiving the response or timing out, the demo
 * finishes.
 */

/* Standard includes. */
#include <stdlib.h>

/* POSIX includes. */
#include <unistd.h>
#include <time.h>

/* Demo config. */
#include "demo_config.h"

/* Metrics collector. */
#include "metrics_collector.h"

/* Report builder. */
#include "report_builder.h"

/* MQTT operations. */
#include "mqtt_operations.h"

/* JSON Library. */
#include "core_json.h"

/* Device Defender Client Library. */
#include "defender.h"

/**
 * THING_NAME is required. Throw compilation error if it is not defined.
 */
#ifndef THING_NAME
    #error "Please define THING_NAME to the thing name registered with AWS IoT Core in demo_config.h."
#endif

/**
 * @brief The length of #THING_NAME.
 */
#define THING_NAME_LENGTH                           ( ( uint16_t ) ( sizeof( THING_NAME ) - 1 ) )

/**
 * @brief Number of seconds to wait for the response from AWS IoT Device
 * Defender service.
 */
#define DEFENDER_RESPONSE_WAIT_SECONDS              ( 2 )

/**
 * @brief Name of the report id field in the response from the AWS IoT Device
 * Defender service.
 */
#define DEFENDER_RESPONSE_REPORT_ID_FIELD           "reportId"

/**
 * @brief The length of #DEFENDER_RESPONSE_REPORT_ID_FIELD.
 */
#define DEFENDER_RESPONSE_REPORT_ID_FIELD_LENGTH    ( sizeof( DEFENDER_RESPONSE_REPORT_ID_FIELD ) - 1 )

/**
 * @brief The maximum number of times to run the loop in this demo.
 *
 * @note The demo loop is attempted to re-run only if it fails in an iteration.
 * Once the demo loop succeeds in an iteration, the demo exits successfully.
 */
#ifndef DEFENDER_MAX_DEMO_LOOP_COUNT
    #define DEFENDER_MAX_DEMO_LOOP_COUNT    ( 3 )
#endif

/**
 * @brief Time in seconds to wait between retries of the demo loop if
 * demo loop fails.
 */
#define DELAY_BETWEEN_DEMO_RETRY_ITERATIONS_S    ( 5 )

/**
 * @brief Status values of the device defender report.
 */
typedef enum
{
    ReportStatusNotReceived,
    ReportStatusAccepted,
    ReportStatusRejected
} ReportStatus_t;
/*-----------------------------------------------------------*/

/**
 * @brief Network Stats.
 */
static NetworkStats_t networkStats;

/**
 * @brief Open TCP ports array.
 */
static uint16_t openTcpPorts[ OPEN_TCP_PORTS_ARRAY_SIZE ];

/**
 * @brief Open UDP ports array.
 */
static uint16_t openUdpPorts[ OPEN_UDP_PORTS_ARRAY_SIZE ];

/**
 * @brief Established connections array.
 */
static Connection_t establishedConnections[ ESTABLISHED_CONNECTIONS_ARRAY_SIZE ];

/**
 * @brief CPU usage array.
 */
static uint64_t cpuUserUsage[ CPU_USER_USAGE_ARRAY_SIZE ];

/**
 * @brief Network interface names array.
 */
static char networkInterfaceNames[ NETWORK_INTERFACE_ARRAY_SIZE ][ 16 ];

/**
 * @brief Network interface addresses array.
 */
static uint32_t networkInterfaceAddresses[ NETWORK_INTERFACE_ARRAY_SIZE ];

/**
 * @brief All the metrics sent in the device defender report.
 */
static ReportMetrics_t deviceMetrics;

/**
 * @brief Report status.
 */
static ReportStatus_t reportStatus;

/**
 * @brief Buffer for generating the device defender report.
 */
static char deviceMetricsJsonReport[ DEVICE_METRICS_REPORT_BUFFER_SIZE ];

/**
 * @brief Report Id sent in the defender report.
 */
static uint32_t reportId = 0;
/*-----------------------------------------------------------*/

/**
 * @brief Callback to receive the incoming publish messages from the MQTT broker.
 *
 * @param[in] pPublishInfo Pointer to publish info of the incoming publish.
 * @param[in] packetIdentifier Packet identifier of the incoming publish.
 */
static void publishCallback( MQTTPublishInfo_t * pPublishInfo,
                             uint16_t packetIdentifier );

/**
 * @brief Collect all the metrics to be sent in the device defender report.
 *
 * @return true if all the metrics are successfully collected;
 * false otherwise.
 */
static bool collectDeviceMetrics( void );

/**
 * @brief Generate the device defender report.
 *
 * @param[out] pOutReportLength Length of the device defender report.
 *
 * @return true if the report is generated successfully;
 * false otherwise.
 */
static bool generateDeviceMetricsReport( uint32_t * pOutReportLength );

/**
 * @brief Subscribe to the device defender topics.
 *
 * @return true if the subscribe is successful;
 * false otherwise.
 */
static bool subscribeToDefenderTopics( void );

/**
 * @brief Unsubscribe from the device defender topics.
 *
 * @return true if the unsubscribe is successful;
 * false otherwise.
 */
static bool unsubscribeFromDefenderTopics( void );

/**
 * @brief Publish the generated device defender report.
 *
 * @param[in] reportLength Length of the device defender report.
 *
 * @return true if the report is published successfully;
 * false otherwise.
 */
static bool publishDeviceMetricsReport( uint32_t reportLength );

/**
 * @brief Validate the response received from the AWS IoT Device Defender Service.
 *
 * This functions checks that a valid JSON is received and the value of reportId
 * is same as was sent in the published report.
 *
 * @param[in] defenderResponse The defender response to validate.
 * @param[in] defenderResponseLength Length of the defender response.
 *
 * @return true if the response is valid;
 * false otherwise.
 */
static bool validateDefenderResponse( const char * defenderResponse,
                                      uint32_t defenderResponseLength );
/*-----------------------------------------------------------*/

static bool validateDefenderResponse( const char * defenderResponse,
                                      uint32_t defenderResponseLength )
{
    bool status = false;
    JSONStatus_t jsonResult = JSONSuccess;
    char * reportIdString;
    size_t reportIdStringLength;
    uint32_t reportIdInResponse;

    /* Is the response a valid JSON? */
    jsonResult = JSON_Validate( defenderResponse, defenderResponseLength );

    if( jsonResult != JSONSuccess )
    {
        LogError( ( "Invalid response from AWS IoT Device Defender Service: %.*s.",
                    ( int ) defenderResponseLength,
                    defenderResponse ) );
    }

    if( jsonResult == JSONSuccess )
    {
        /* Search the reportId key in the response. */
        jsonResult = JSON_Search( ( char * ) defenderResponse,
                                  defenderResponseLength,
                                  DEFENDER_RESPONSE_REPORT_ID_FIELD,
                                  DEFENDER_RESPONSE_REPORT_ID_FIELD_LENGTH,
                                  &( reportIdString ),
                                  &( reportIdStringLength ) );

        if( jsonResult != JSONSuccess )
        {
            LogError( ( "reportId key not found in the response from the"
                        "AWS IoT Device Defender Service: %.*s.",
                        ( int ) defenderResponseLength,
                        defenderResponse ) );
        }
    }

    if( jsonResult == JSONSuccess )
    {
        reportIdInResponse = ( uint32_t ) strtoul( reportIdString, NULL, 10 );

        /* Is the reportId present in the response same as was sent in the
         * published report? */
        if( reportIdInResponse == reportId )
        {
            LogInfo( ( "A valid reponse with reportId %u received from the "
                       "AWS IoT Device Defender Service.", reportId ) );
            status = true;
        }
        else
        {
            LogError( ( "Unexpected reportId found in the response from the AWS"
                        "IoT Device Defender Service. Expected: %u, Found: %u, "
                        "Complete Response: %.*s.",
                        reportIdInResponse,
                        reportId,
                        ( int ) defenderResponseLength,
                        defenderResponse ) );
        }
    }

    return status;
}
/*-----------------------------------------------------------*/

static void publishCallback( MQTTPublishInfo_t * pPublishInfo,
                             uint16_t packetIdentifier )
{
    DefenderStatus_t status;
    DefenderTopic_t api;
    bool validationResult;

    /* Silence compiler warnings about unused variables. */
    ( void ) packetIdentifier;

    status = Defender_MatchTopic( pPublishInfo->pTopicName,
                                  pPublishInfo->topicNameLength,
                                  &( api ),
                                  NULL,
                                  NULL );

    if( status == DefenderSuccess )
    {
        if( api == DefenderJsonReportAccepted )
        {
            /* Check if the response is valid and is for the report we published. */
            validationResult = validateDefenderResponse( ( const char * ) pPublishInfo->pPayload,
                                                         pPublishInfo->payloadLength );

            if( validationResult == true )
            {
                LogInfo( ( "The defender report was accepted by the service. Response: %.*s.",
                           ( int ) pPublishInfo->payloadLength,
                           ( const char * ) pPublishInfo->pPayload ) );
                reportStatus = ReportStatusAccepted;
            }
        }
        else if( api == DefenderJsonReportRejected )
        {
            /* Check if the response is valid and is for the report we published. */
            validationResult = validateDefenderResponse( ( const char * ) pPublishInfo->pPayload,
                                                         pPublishInfo->payloadLength );

            if( validationResult == true )
            {
                LogError( ( "The defender report was rejected by the service. Response: %.*s.",
                            ( int ) pPublishInfo->payloadLength,
                            ( const char * ) pPublishInfo->pPayload ) );
                reportStatus = ReportStatusRejected;
            }
        }
        else
        {
            LogError( ( "Unexpected defender API : %d.", api ) );
        }
    }
    else
    {
        LogError( ( "Unexpected publish message received. Topic: %.*s, Payload: %.*s.",
                    ( int ) pPublishInfo->topicNameLength,
                    ( const char * ) pPublishInfo->pTopicName,
                    ( int ) pPublishInfo->payloadLength,
                    ( const char * ) ( pPublishInfo->pPayload ) ) );
    }
}
/*-----------------------------------------------------------*/

static bool collectDeviceMetrics( void )
{
    bool status = false;
    MetricsCollectorStatus_t metricsCollectorStatus;
    uint32_t numOpenTcpPorts = 0, numOpenUdpPorts = 0, numEstablishedConnections = 0;
    size_t cpuCount = 0, networkInterfaceCount = 0;

    /* Collect bytes and packets sent and received. */
    metricsCollectorStatus = GetNetworkStats( &( networkStats ) );

    if( metricsCollectorStatus != MetricsCollectorSuccess )
    {
        LogError( ( "GetNetworkStats failed. Status: %d.",
                    metricsCollectorStatus ) );
    }

    /* Collect a list of open TCP ports. */
    if( metricsCollectorStatus == MetricsCollectorSuccess )
    {
        metricsCollectorStatus = GetOpenTcpPorts( &( openTcpPorts[ 0 ] ),
                                                  OPEN_TCP_PORTS_ARRAY_SIZE,
                                                  &( numOpenTcpPorts ) );

        if( metricsCollectorStatus != MetricsCollectorSuccess )
        {
            LogError( ( "GetOpenTcpPorts failed. Status: %d.",
                        metricsCollectorStatus ) );
        }
    }

    /* Collect a list of open UDP ports. */
    if( metricsCollectorStatus == MetricsCollectorSuccess )
    {
        metricsCollectorStatus = GetOpenUdpPorts( &( openUdpPorts[ 0 ] ),
                                                  OPEN_UDP_PORTS_ARRAY_SIZE,
                                                  &( numOpenUdpPorts ) );

        if( metricsCollectorStatus != MetricsCollectorSuccess )
        {
            LogError( ( "GetOpenUdpPorts failed. Status: %d.",
                        metricsCollectorStatus ) );
        }
    }

    /* Collect a list of established connections. */
    if( metricsCollectorStatus == MetricsCollectorSuccess )
    {
        metricsCollectorStatus = GetEstablishedConnections( &( establishedConnections[ 0 ] ),
                                                            ESTABLISHED_CONNECTIONS_ARRAY_SIZE,
                                                            &( numEstablishedConnections ) );

        if( metricsCollectorStatus != MetricsCollectorSuccess )
        {
            LogError( ( "GetEstablishedConnections failed. Status: %d.",
                        metricsCollectorStatus ) );
        }
    }

    /* Collect uptime from the system.
     * This is an example of a custom metric of number type. */
    if( metricsCollectorStatus == MetricsCollectorSuccess )
    {
        metricsCollectorStatus = GetUptime( &( deviceMetrics.customMetrics.uptime ) );

        if( metricsCollectorStatus != MetricsCollectorSuccess )
        {
            LogError( ( "GetUptime failed. Status: %d.",
                        metricsCollectorStatus ) );
        }
    }

    /* Collect free memory from the system.
     * This is an example of a custom metric of number type. */
    if( metricsCollectorStatus == MetricsCollectorSuccess )
    {
        metricsCollectorStatus = GetFreeMemory( &( deviceMetrics.customMetrics.memFree ) );

        if( metricsCollectorStatus != MetricsCollectorSuccess )
        {
            LogError( ( "GetFreeMemory failed. Status: %d.",
                        metricsCollectorStatus ) );
        }
    }

    /* Collect CPU usage metrics from the system.
     * This is an example of a custom metric of number-list type. */
    if( metricsCollectorStatus == MetricsCollectorSuccess )
    {
        metricsCollectorStatus = GetCpuUserUsage( &( cpuUserUsage[ 0 ] ),
                                                  CPU_USER_USAGE_ARRAY_SIZE,
                                                  &( cpuCount ) );

        if( metricsCollectorStatus != MetricsCollectorSuccess )
        {
            LogError( ( "GetCpuUserUsage failed. Status: %d.",
                        metricsCollectorStatus ) );
        }
    }

    /* Collect network interface names and addresses from the system.
     * This is an example of custom metrics of the string-list and ip-address-list types. */
    if( metricsCollectorStatus == MetricsCollectorSuccess )
    {
        metricsCollectorStatus = GetNetworkInferfaceInfo( &( networkInterfaceNames[ 0 ] ),
                                                          &( networkInterfaceAddresses[ 0 ] ),
                                                          NETWORK_INTERFACE_ARRAY_SIZE,
                                                          &( networkInterfaceCount ) );

        if( metricsCollectorStatus != MetricsCollectorSuccess )
        {
            LogError( ( "GetUptime failed. Status: %d.",
                        metricsCollectorStatus ) );
        }
    }

    /* Populate device metrics. */
    if( metricsCollectorStatus == MetricsCollectorSuccess )
    {
        status = true;
        deviceMetrics.pNetworkStats = &( networkStats );
        deviceMetrics.pOpenTcpPortsArray = &( openTcpPorts[ 0 ] );
        deviceMetrics.openTcpPortsArrayLength = numOpenTcpPorts;
        deviceMetrics.pOpenUdpPortsArray = &( openUdpPorts[ 0 ] );
        deviceMetrics.openUdpPortsArrayLength = numOpenUdpPorts;
        deviceMetrics.pEstablishedConnectionsArray = &( establishedConnections[ 0 ] );
        deviceMetrics.establishedConnectionsArrayLength = numEstablishedConnections;
        deviceMetrics.customMetrics.pCpuUserUsage = &( cpuUserUsage[ 0 ] );
        deviceMetrics.customMetrics.cpuCount = cpuCount;
        deviceMetrics.customMetrics.pNetworkInterfaceNames = &( networkInterfaceNames[ 0 ] );
        deviceMetrics.customMetrics.pNetworkInterfaceAddresses = &( networkInterfaceAddresses[ 0 ] );
        deviceMetrics.customMetrics.networkInterfaceCount = networkInterfaceCount;
    }

    return status;
}
/*-----------------------------------------------------------*/

static bool generateDeviceMetricsReport( uint32_t * pOutReportLength )
{
    bool status = false;
    ReportBuilderStatus_t reportBuilderStatus;

    /* Generate the metrics report in the format expected by the AWS IoT Device
     * Defender Service. */
    reportBuilderStatus = GenerateJsonReport( &( deviceMetricsJsonReport[ 0 ] ),
                                              DEVICE_METRICS_REPORT_BUFFER_SIZE,
                                              &( deviceMetrics ),
                                              DEVICE_METRICS_REPORT_MAJOR_VERSION,
                                              DEVICE_METRICS_REPORT_MINOR_VERSION,
                                              reportId,
                                              pOutReportLength );

    if( reportBuilderStatus != ReportBuilderSuccess )
    {
        LogError( ( "GenerateJsonReport failed. Status: %d.",
                    reportBuilderStatus ) );
    }
    else
    {
        LogDebug( ( "Generated Report: %.*s.",
                    *pOutReportLength,
                    &( deviceMetricsJsonReport[ 0 ] ) ) );
        status = true;
    }

    return status;
}
/*-----------------------------------------------------------*/

static bool subscribeToDefenderTopics( void )
{
    bool status = false;

    /* Subscribe to defender topic for responses for accepted reports. */
    status = SubscribeToTopic( DEFENDER_API_JSON_ACCEPTED( THING_NAME ),
                               DEFENDER_API_LENGTH_JSON_ACCEPTED( THING_NAME_LENGTH ) );

    if( status == false )
    {
        LogError( ( "Failed to subscribe to defender topic: %.*s.",
                    DEFENDER_API_LENGTH_JSON_ACCEPTED( THING_NAME_LENGTH ),
                    DEFENDER_API_JSON_ACCEPTED( THING_NAME ) ) );
    }

    if( status == true )
    {
        /* Subscribe to defender topic for responses for rejected reports. */
        status = SubscribeToTopic( DEFENDER_API_JSON_REJECTED( THING_NAME ),
                                   DEFENDER_API_LENGTH_JSON_REJECTED( THING_NAME_LENGTH ) );

        if( status == false )
        {
            LogError( ( "Failed to subscribe to defender topic: %.*s.",
                        DEFENDER_API_LENGTH_JSON_REJECTED( THING_NAME_LENGTH ),
                        DEFENDER_API_JSON_REJECTED( THING_NAME ) ) );
        }
    }

    return status;
}
/*-----------------------------------------------------------*/

static bool unsubscribeFromDefenderTopics( void )
{
    bool status = false;

    /* Unsubscribe from defender accepted topic. */
    status = UnsubscribeFromTopic( DEFENDER_API_JSON_ACCEPTED( THING_NAME ),
                                   DEFENDER_API_LENGTH_JSON_ACCEPTED( THING_NAME_LENGTH ) );

    if( status == true )
    {
        /* Unsubscribe from defender rejected topic. */
        status = UnsubscribeFromTopic( DEFENDER_API_JSON_REJECTED( THING_NAME ),
                                       DEFENDER_API_LENGTH_JSON_REJECTED( THING_NAME_LENGTH ) );
    }

    return status;
}
/*-----------------------------------------------------------*/

static bool publishDeviceMetricsReport( uint32_t reportLength )
{
    return PublishToTopic( DEFENDER_API_JSON_PUBLISH( THING_NAME ),
                           DEFENDER_API_LENGTH_JSON_PUBLISH( THING_NAME_LENGTH ),
                           &( deviceMetricsJsonReport[ 0 ] ),
                           reportLength );
}
/*-----------------------------------------------------------*/

/* This example uses a single application task, which shows that how to use
 * Device Defender library to generate and validate AWS IoT Device Defender
 * MQTT topics, and use the coreMQTT library to communicate with the AWS IoT
 * Device Defender service. */
int main( int argc,
          char ** argv )
{
    bool status = false;
    int exitStatus = EXIT_FAILURE;
    uint32_t reportLength = 0, i, mqttSessionEstablished = 0;
    int demoRunCount = 0;

    /* Silence compiler warnings about unused variables. */
    ( void ) argc;
    ( void ) argv;

    do
    {
        /* Start with report not received. */
        reportStatus = ReportStatusNotReceived;

        /* Set a report Id to be used.
         *
         * Reports for a Thing with a previously used report ID will be assumed to
         * be duplicates and discarded by the Device Defender service. The report
         * ID needs to be unique per report sent with a given Thing. We recommend
         * using an increasing unique id such as the current timestamp. */
        reportId = time( NULL );

        /****************************** Connect. ******************************/

        /* Attempts to connect to the AWS IoT MQTT broker over TCP. If the
         * connection fails, retries after a timeout. Timeout value will
         * exponentially increase until maximum attempts are reached. */
        LogInfo( ( "Establishing MQTT session..." ) );
        status = EstablishMqttSession( publishCallback );

        if( status != true )
        {
            LogError( ( "Failed to establish MQTT session." ) );
        }
        else
        {
            mqttSessionEstablished = 1;
        }

        /******************** Subscribe to Defender topics. *******************/

        /* Attempt to subscribe to the AWS IoT Device Defender topics.
         * Since this demo is using JSON, in subscribeToDefenderTopics() we
         * subscribe to the topics to which accepted and rejected responses are
         * received from after publishing a JSON report.
         *
         * This demo uses a constant #democonfigTHING_NAME known at compile time
         * therefore we use macros to assemble defender topic strings.
         * If the thing name is known at run time, then we could use the API
         * #Defender_GetTopic instead.
         *
         * For example, for the JSON accepted responses topic:
         *
         * #define TOPIC_BUFFER_LENGTH      ( 256U )
         *
         * // Every device should have a unique thing name registered with AWS IoT Core.
         * // This example assumes that the device has a unique serial number which is
         * // registered as the thing name with AWS IoT Core.
         * const char * pThingName = GetDeviceSerialNumber();
         * uint16_t thingNameLength = ( uint16_t ) strlen( pThingname );
         * char topicBuffer[ TOPIC_BUFFER_LENGTH ] = { 0 };
         * uint16_t topicLength = 0;
         * DefenderStatus_t status = DefenderSuccess;
         *
         * status = Defender_GetTopic( &( topicBuffer[ 0 ] ),
         *                             TOPIC_BUFFER_LENGTH,
         *                             pThingName,
         *                             thingNameLength,
         *                             DefenderJsonReportAccepted,
         *                             &( topicLength ) );
         */
        if( status == true )
        {
            LogInfo( ( "Subscribing to defender topics..." ) );
            status = subscribeToDefenderTopics();

            if( status != true )
            {
                LogError( ( "Failed to subscribe to defender topics." ) );
            }
        }

        /*********************** Collect device metrics. **********************/

        /* We then need to collect the metrics that will be sent to the AWS IoT
         * Device Defender service. This demo uses the functions declared in
         * metrics_collector.h to collect network metrics. For this demo, the
         * implementation of these functions are in metrics_collector.c and
         * collects metrics using tcp_netstat utility for FreeRTOS+TCP. */
        if( status == true )
        {
            LogInfo( ( "Collecting device metrics..." ) );
            status = collectDeviceMetrics();

            if( status != true )
            {
                LogError( ( "Failed to collect device metrics." ) );
            }
        }

        /********************** Generate defender report. *********************/

        /* The data needs to be incorporated into a JSON formatted report,
         * which follows the format expected by the Device Defender service.
         * This format is documented here:
         * https://docs.aws.amazon.com/iot/latest/developerguide/detect-device-side-metrics.html
         */
        if( status == true )
        {
            LogInfo( ( "Generating device defender report..." ) );
            status = generateDeviceMetricsReport( &( reportLength ) );

            if( status != true )
            {
                LogError( ( "Failed to generate device defender report." ) );
            }
        }

        /********************** Publish defender report. **********************/

        /* The report is then published to the Device Defender service. This report
         * is published to the MQTT topic for publishing JSON reports. As before,
         * we use the defender library macros to create the topic string, though
         * #Defender_GetTopic could be used if the Thing name is acquired at
         * run time */
        if( status == true )
        {
            LogInfo( ( "Publishing device defender report..." ) );
            status = publishDeviceMetricsReport( reportLength );

            if( status != true )
            {
                LogError( ( "Failed to publish device defender report." ) );
            }
        }

        /* Wait for the response to our report. Response will be handled by the
         * callback passed to establishMqttSession() earlier.
         * The callback will verify that the MQTT messages received are from the
         * defender service's topic. Based on whether the response comes from
         * the accepted or rejected topics, it updates reportStatus. */
        if( status == true )
        {
            for( i = 0; i < DEFENDER_RESPONSE_WAIT_SECONDS; i++ )
            {
                ( void ) ProcessLoopWithTimeout( 1000 );

                /* reportStatus is updated in the publishCallback. */
                if( reportStatus != ReportStatusNotReceived )
                {
                    break;
                }
            }
        }

        /**************************** Disconnect. *****************************/

        /* Unsubscribe and disconnect if MQTT session was established. Per the MQTT
         * protocol spec, it is okay to send UNSUBSCRIBE even if no corresponding
         * subscription exists on the broker. Therefore, it is okay to attempt
         * unsubscribe even if one more subscribe failed earlier. */
        if( reportStatus == ReportStatusNotReceived )
        {
            LogError( ( "Failed to receive response from AWS IoT Device Defender Service." ) );
            status = false;
        }

        /* Unsubscribe and disconnect if MQTT session was established. Per the MQTT
         * protocol spec, it is okay to send UNSUBSCRIBE even if no corresponding
         * subscription exists on the broker. Therefore, it is okay to attempt
         * unsubscribe even if one more subscribe failed earlier. */
        if( mqttSessionEstablished == 1 )
        {
            LogInfo( ( "Unsubscribing from defender topics..." ) );
            status = unsubscribeFromDefenderTopics();

            if( status != true )
            {
                LogError( ( "Failed to unsubscribe from defender topics." ) );
            }

            LogInfo( ( "Closing MQTT session..." ) );
            ( void ) DisconnectMqttSession();
        }

        /****************************** Finish. ******************************/

        if( ( status == true ) && ( reportStatus == ReportStatusAccepted ) )
        {
            exitStatus = EXIT_SUCCESS;
        }

        /******************* Retry in case of failure. ***********************/

        /* Increment the demo run count. */
        demoRunCount++;

        if( exitStatus == EXIT_SUCCESS )
        {
            LogInfo( ( "Demo iteration %d is successful.", demoRunCount ) );
        }
        /* Attempt to retry a failed iteration of demo for up to #DEFENDER_MAX_DEMO_LOOP_COUNT times. */
        else if( demoRunCount < DEFENDER_MAX_DEMO_LOOP_COUNT )
        {
            LogWarn( ( "Demo iteration %d failed. Retrying...", demoRunCount ) );
            sleep( DELAY_BETWEEN_DEMO_RETRY_ITERATIONS_S );
        }
        /* Failed all #DEFENDER_MAX_DEMO_LOOP_COUNT demo iterations. */
        else
        {
            LogError( ( "All %d demo iterations failed.", DEFENDER_MAX_DEMO_LOOP_COUNT ) );
            break;
        }
    } while( exitStatus != EXIT_SUCCESS );

    /* Log demo success. */
    if( exitStatus == EXIT_SUCCESS )
    {
        LogInfo( ( "Demo completed successfully." ) );
    }

    return exitStatus;
}
/*-----------------------------------------------------------*/

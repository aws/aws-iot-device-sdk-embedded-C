/*
 * AWS IoT Device SDK for Embedded C 202108.00
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
 * @file ota_demo_core_mqtt.c
 * @brief OTA update example using coreMQTT.
 */

/* Standard includes. */
#include <assert.h>
#include <stdlib.h>
#include <stdbool.h>
#include <errno.h>

/* Include Demo Config as the first non-system header. */
#include "demo_config.h"

/* OpenSSL sockets transport implementation. */
#include "openssl_posix.h"

/* Clock for timer. */
#include "clock.h"

/* pthread include. */
#include <pthread.h>
#include <semaphore.h>

/* MQTT include. */
#include "core_mqtt.h"
#include "mqtt_subscription_manager.h"

/*Include backoff algorithm header for retry logic.*/
#include "backoff_algorithm.h"

/* OTA Library include. */
#include "ota.h"
#include "ota_config.h"

/* OTA Library Interface include. */
#include "ota_os_posix.h"
#include "ota_mqtt_interface.h"
#include "ota_pal_posix.h"

/* Include firmware version struct definition. */
#include "ota_appversion32.h"

/* AWS IoT Core TLS ALPN definitions for MQTT authentication */
#include "aws_iot_alpn_defs.h"

/**
 * These configuration settings are required to run the OTA demo which uses mutual authentication.
 * Throw compilation error if the below configs are not defined.
 */
#ifndef AWS_IOT_ENDPOINT
    #error "Please define AWS IoT MQTT broker endpoint(AWS_IOT_ENDPOINT) in demo_config.h."
#endif
#ifndef ROOT_CA_CERT_PATH
    #error "Please define path to Root CA certificate of the MQTT broker(ROOT_CA_CERT_PATH) in demo_config.h."
#endif
#ifndef CLIENT_IDENTIFIER
    #error "Please define a unique client identifier, CLIENT_IDENTIFIER, in demo_config.h."
#endif
#ifndef CLIENT_CERT_PATH
    #error "Please define path to client certificate(CLIENT_CERT_PATH) in demo_config.h."
#endif
#ifndef CLIENT_PRIVATE_KEY_PATH
    #error "Please define path to client private key(CLIENT_PRIVATE_KEY_PATH) in demo_config.h."
#endif

/**
 * @brief Length of MQTT server host name.
 */
#define AWS_IOT_ENDPOINT_LENGTH             ( ( uint16_t ) ( sizeof( AWS_IOT_ENDPOINT ) - 1 ) )

/**
 * @brief Length of client identifier.
 */
#define CLIENT_IDENTIFIER_LENGTH            ( ( uint16_t ) ( sizeof( CLIENT_IDENTIFIER ) - 1 ) )

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS      ( 1000U )

/**
 * @brief Timeout for receiving CONNACK packet in milli seconds.
 */
#define CONNACK_RECV_TIMEOUT_MS             ( 2000U )

/**
 * @brief The maximum time interval in seconds which is allowed to elapse
 * between two Control Packets.
 *
 * It is the responsibility of the Client to ensure that the interval between
 * Control Packets being sent does not exceed the this Keep Alive value. In the
 * absence of sending any other Control Packets, the Client MUST send a
 * PINGREQ Packet.
 */
#define MQTT_KEEP_ALIVE_INTERVAL_SECONDS    ( 60U )

/**
 * @brief Period for waiting on ack.
 */
#define MQTT_ACK_TIMEOUT_MS                 ( 5000U )

/**
 * @brief Period for demo loop sleep in milliseconds.
 */
#define OTA_EXAMPLE_LOOP_SLEEP_PERIOD_MS    ( 5U )

/**
 * @brief Size of the network buffer to receive the MQTT message.
 *
 * The largest message size is data size from the AWS IoT streaming service,
 * otaconfigFILE_BLOCK_SIZE + extra for headers.
 */

#define OTA_NETWORK_BUFFER_SIZE                  ( otaconfigFILE_BLOCK_SIZE + 128 )

/**
 * @brief The delay used in the main OTA Demo task loop to periodically output the OTA
 * statistics like number of packets received, dropped, processed and queued per connection.
 */
#define OTA_EXAMPLE_TASK_DELAY_MS                ( 1000U )

/**
 * @brief The timeout for waiting for the agent to get suspended after closing the
 * connection.
 */
#define OTA_SUSPEND_TIMEOUT_MS                   ( 5000U )

/**
 * @brief The timeout for waiting before exiting the OTA demo.
 */
#define OTA_DEMO_EXIT_TIMEOUT_MS                 ( 3000U )

/**
 * @brief The maximum size of the file paths used in the demo.
 */
#define OTA_MAX_FILE_PATH_SIZE                   ( 260U )

/**
 * @brief The maximum size of the stream name required for downloading update file
 * from streaming service.
 */
#define OTA_MAX_STREAM_NAME_SIZE                 ( 128U )

/**
 * @brief The maximum back-off delay (in milliseconds) for retrying connection to server.
 */
#define CONNECTION_RETRY_MAX_BACKOFF_DELAY_MS    ( 5000U )

/**
 * @brief The base back-off delay (in milliseconds) to use for connection retry attempts.
 */
#define CONNECTION_RETRY_BACKOFF_BASE_MS         ( 500U )

/**
 * @brief Number of milliseconds in a second.
 */
#define NUM_MILLISECONDS_IN_SECOND               ( 1000U )

/**
 * @brief The maximum number of retries for connecting to server.
 */
#define CONNECTION_RETRY_MAX_ATTEMPTS            ( 5U )

/**
 * @brief The MQTT metrics string expected by AWS IoT.
 */
#define METRICS_STRING                           "?SDK=" OS_NAME "&Version=" OS_VERSION "&Platform=" HARDWARE_PLATFORM_NAME "&OTALib=" OTA_LIB

/**
 * @brief The length of the MQTT metrics string expected by AWS IoT.
 */
#define METRICS_STRING_LENGTH                    ( ( uint16_t ) ( sizeof( METRICS_STRING ) - 1 ) )


#ifdef CLIENT_USERNAME

/**
 * @brief Append the username with the metrics string if #CLIENT_USERNAME is defined.
 *
 * This is to support both metrics reporting and username/password based client
 * authentication by AWS IoT.
 */
    #define CLIENT_USERNAME_WITH_METRICS    CLIENT_USERNAME METRICS_STRING
#endif

/**
 * @brief The common prefix for all OTA topics.
 */
#define OTA_TOPIC_PREFIX               "$aws/things/+/"

/**
 * @brief The string used for jobs topics.
 */
#define OTA_TOPIC_JOBS                 "jobs"

/**
 * @brief The string used for streaming service topics.
 */
#define OTA_TOPIC_STREAM               "streams"

/**
 * @brief The length of the outgoing publish records array used by the coreMQTT
 * library to track QoS > 0 packet ACKS for outgoing publishes.
 */
#define OUTGOING_PUBLISH_RECORD_LEN    ( 10U )

/**
 * @brief The length of the incoming publish records array used by the coreMQTT
 * library to track QoS > 0 packet ACKS for incoming publishes.
 */
#define INCOMING_PUBLISH_RECORD_LEN    ( 10U )

/*-----------------------------------------------------------*/

/* Linkage for error reporting. */
extern int errno;

/**
 * @brief Struct for firmware version.
 */
const AppVersion32_t appFirmwareVersion =
{
    .u.x.major = APP_VERSION_MAJOR,
    .u.x.minor = APP_VERSION_MINOR,
    .u.x.build = APP_VERSION_BUILD,
};

/* Each compilation unit must define the NetworkContext struct. */
struct NetworkContext
{
    OpensslParams_t * pParams;
};

/**
 * @brief Network connection context used in this demo.
 */
static NetworkContext_t networkContext;

/**
 * @brief MQTT connection context used in this demo.
 */
static MQTTContext_t mqttContext;

/**
 * @brief Keep a flag for indicating if the MQTT connection is alive.
 */
static bool mqttSessionEstablished = false;

/**
 * @brief Structure for openssl parameters.
 */
static OpensslParams_t opensslParams;

/**
 * @brief Mutex for synchronizing coreMQTT API calls.
 */
static pthread_mutex_t mqttMutex;

/**
 * @brief Semaphore for synchronizing buffer operations.
 */
static sem_t bufferSemaphore;

/**
 * @brief Semaphore for synchronizing wait for ack.
 */
static sem_t ackSemaphore;

/**
 * @brief Enum for type of OTA job messages received.
 */
typedef enum jobMessageType
{
    jobMessageTypeNextGetAccepted = 0,
    jobMessageTypeNextNotify,
    jobMessageTypeMax
} jobMessageType_t;

/**
 * @brief The network buffer must remain valid when OTA library task is running.
 */
static uint8_t otaNetworkBuffer[ OTA_NETWORK_BUFFER_SIZE ];

/**
 * @brief Update File path buffer.
 */
uint8_t updateFilePath[ OTA_MAX_FILE_PATH_SIZE ];

/**
 * @brief Certificate File path buffer.
 */
uint8_t certFilePath[ OTA_MAX_FILE_PATH_SIZE ];

/**
 * @brief Stream name buffer.
 */
uint8_t streamName[ OTA_MAX_STREAM_NAME_SIZE ];

/**
 * @brief Decode memory.
 */
uint8_t decodeMem[ otaconfigFILE_BLOCK_SIZE ];

/**
 * @brief Bitmap memory.
 */
uint8_t bitmap[ OTA_MAX_BLOCK_BITMAP_SIZE ];

/**
 * @brief Event buffer.
 */
static OtaEventData_t eventBuffer[ otaconfigMAX_NUM_OTA_DATA_BUFFERS ];

/**
 * @brief The buffer passed to the OTA Agent from application while initializing.
 */
static OtaAppBuffer_t otaBuffer =
{
    .pUpdateFilePath    = updateFilePath,
    .updateFilePathsize = OTA_MAX_FILE_PATH_SIZE,
    .pCertFilePath      = certFilePath,
    .certFilePathSize   = OTA_MAX_FILE_PATH_SIZE,
    .pStreamName        = streamName,
    .streamNameSize     = OTA_MAX_STREAM_NAME_SIZE,
    .pDecodeMemory      = decodeMem,
    .decodeMemorySize   = otaconfigFILE_BLOCK_SIZE,
    .pFileBitmap        = bitmap,
    .fileBitmapSize     = OTA_MAX_BLOCK_BITMAP_SIZE
};

/**
 * @brief Array to track the outgoing publish records for outgoing publishes
 * with QoS > 0.
 *
 * This is passed into #MQTT_InitStatefulQoS to allow for QoS > 0.
 *
 */
static MQTTPubAckInfo_t pOutgoingPublishRecords[ OUTGOING_PUBLISH_RECORD_LEN ];

/**
 * @brief Array to track the incoming publish records for incoming publishes
 * with QoS > 0.
 *
 * This is passed into #MQTT_InitStatefulQoS to allow for QoS > 0.
 *
 */
static MQTTPubAckInfo_t pIncomingPublishRecords[ INCOMING_PUBLISH_RECORD_LEN ];

/*-----------------------------------------------------------*/

/**
 * @brief Sends an MQTT CONNECT packet over the already connected TCP socket.
 *
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] createCleanSession Creates a new MQTT session if true.
 * If false, tries to establish the existing session if there was session
 * already present in broker.
 * @param[out] pSessionPresent Session was already present in the broker or not.
 * Session present response is obtained from the CONNACK from broker.
 *
 * @return EXIT_SUCCESS if an MQTT session is established;
 * EXIT_FAILURE otherwise.
 */
static int establishMqttSession( MQTTContext_t * pMqttContext );


/**
 * @brief Publish message to a topic.
 *
 * This function publishes a message to a given topic & QoS.
 *
 * @param[in] pacTopic Mqtt topic filter.
 *
 * @param[in] topicLen Length of the topic filter.
 *
 * @param[in] pMsg Message to publish.
 *
 * @param[in] msgSize Message size.
 *
 * @param[in] qos Quality of Service
 *
 * @return OtaMqttSuccess if success , other error code on failure.
 */
static OtaMqttStatus_t mqttPublish( const char * const pacTopic,
                                    uint16_t topicLen,
                                    const char * pMsg,
                                    uint32_t msgSize,
                                    uint8_t qos );

/**
 * @brief Subscribe to the MQTT topic filter, and registers the handler for the topic filter with the subscription manager.
 *
 * This function subscribes to the Mqtt topics with the Quality of service
 * received as parameter. This function also registers a callback for the
 * topicfilter.
 *
 * @param[in] pTopicFilter Mqtt topic filter.
 *
 * @param[in] topicFilterLength Length of the topic filter.
 *
 * @param[in] qos Quality of Service
 *
 * @return OtaMqttSuccess if success , other error code on failure.
 */
static OtaMqttStatus_t mqttSubscribe( const char * pTopicFilter,
                                      uint16_t topicFilterLength,
                                      uint8_t qos );

/**
 * @brief Unsubscribe to the Mqtt topics.
 *
 * This function unsubscribes to the Mqtt topics with the Quality of service
 * received as parameter.
 *
 * @param[in] pTopicFilter Mqtt topic filter.
 *
 * @param[in] topicFilterLength Length of the topic filter.
 *
 * @param[qos] qos Quality of Service
 *
 * @return  OtaMqttSuccess if success , other error code on failure.
 */
static OtaMqttStatus_t mqttUnsubscribe( const char * pTopicFilter,
                                        uint16_t topicFilterLength,
                                        uint8_t qos );

/**
 * @brief Thread to call the OTA agent task.
 *
 * @param[in] pParam Can be used to pass down functionality to the agent task
 * @return void* returning null.
 */
static void * otaThread( void * pParam );

/**
 * @brief Start OTA demo.
 *
 * The OTA task is created with initializing the OTA agent and
 * setting the required interfaces. The demo loop then starts,
 * establishing an MQTT connection with the broker and waiting
 * for an update. After a successful update the OTA agent requests
 * a manual reset to the downloaded executable.
 *
 * @return EXIT_SUCCESS or EXIT_FAILURE.
 */
static int startOTADemo( void );

/**
 * @brief Set OTA interfaces.
 *
 * @param[in]  pOtaInterfaces pointer to OTA interface structure.
 */
static void setOtaInterfaces( OtaInterfaces_t * pOtaInterfaces );

/**
 * @brief Disconnect from the MQTT broker and close connection.
 *
 */
static void disconnect( void );

/**
 * @brief Attempt to connect to the MQTT broker.
 *
 * @return int EXIT_SUCCESS if a connection is established.
 */
static int establishConnection( void );

/**
 * @brief Initialize MQTT by setting up transport interface and network.
 *
 * @param[in] pMqttContext Structure representing MQTT connection.
 * @param[in] pNetworkContext Network context to connect on.
 * @return int EXIT_SUCCESS if MQTT component is initialized
 */
static int initializeMqtt( MQTTContext_t * pMqttContext,
                           NetworkContext_t * pNetworkContext );

/**
 * @brief Retry logic to establish a connection to the server.
 *
 * If the connection fails, keep retrying with exponentially increasing
 * timeout value, until max retries, max timeout or successful connect.
 *
 * @param[in] pNetworkContext Network context to connect on.
 * @return int EXIT_FAILURE if connection failed after retries.
 */
static int connectToServerWithBackoffRetries( NetworkContext_t * pNetworkContext );

/**
 * @brief Random number to be used as a back-off value for retrying connection.
 *
 * @return uint32_t The generated random number.
 */
static uint32_t generateRandomNumber();

/* Callbacks used to handle different events. */

/**
 * @brief The OTA agent has completed the update job or it is in
 * self test mode. If it was accepted, we want to activate the new image.
 * This typically means we should reset the device to run the new firmware.
 * If now is not a good time to reset the device, it may be activated later
 * by your user code. If the update was rejected, just return without doing
 * anything and we'll wait for another job. If it reported that we should
 * start test mode, normally we would perform some kind of system checks to
 * make sure our new firmware does the basic things we think it should do
 * but we'll just go ahead and set the image as accepted for demo purposes.
 * The accept function varies depending on your platform. Refer to the OTA
 * PAL implementation for your platform in aws_ota_pal.c to see what it
 * does for you.
 *
 * @param[in] event Event from OTA lib of type OtaJobEvent_t.
 * @return None.
 */
static void otaAppCallback( OtaJobEvent_t event,
                            void * pData );

/**
 * @brief callback to use with the MQTT context to notify incoming packet events.
 *
 * @param[in] pMqttContext MQTT context which stores the connection.
 * @param[in] pPacketInfo Parameters of the incoming packet.
 * @param[in] pDeserializedInfo Deserialized packet information to be dispatched by
 * the subscription manager to event callbacks.
 */
static void mqttEventCallback( MQTTContext_t * pMqttContext,
                               MQTTPacketInfo_t * pPacketInfo,
                               MQTTDeserializedInfo_t * pDeserializedInfo );

/**
 * @brief Callback registered with the OTA library that notifies the OTA agent
 * of an incoming PUBLISH containing a job document.
 *
 * @param[in] pContext MQTT context which stores the connection.
 * @param[in] pPublishInfo MQTT packet information which stores details of the
 * job document.
 */
static void mqttJobCallback( MQTTContext_t * pContext,
                             MQTTPublishInfo_t * pPublishInfo );

/**
 * @brief Callback that notifies the OTA library when a data block is received.
 *
 * @param[in] pContext MQTT context which stores the connection.
 * @param[in] pPublishInfo MQTT packet that stores the information of the file block.
 */
static void mqttDataCallback( MQTTContext_t * pContext,
                              MQTTPublishInfo_t * pPublishInfo );

static SubscriptionManagerCallback_t otaMessageCallback[] = { mqttJobCallback, mqttDataCallback };

/*-----------------------------------------------------------*/

void otaEventBufferFree( OtaEventData_t * const pxBuffer )
{
    if( sem_wait( &bufferSemaphore ) == 0 )
    {
        pxBuffer->bufferUsed = false;
        ( void ) sem_post( &bufferSemaphore );
    }
    else
    {
        LogError( ( "Failed to get buffer semaphore: "
                    ",errno=%s",
                    strerror( errno ) ) );
    }
}

/*-----------------------------------------------------------*/

OtaEventData_t * otaEventBufferGet( void )
{
    uint32_t ulIndex = 0;
    OtaEventData_t * pFreeBuffer = NULL;

    if( sem_wait( &bufferSemaphore ) == 0 )
    {
        for( ulIndex = 0; ulIndex < otaconfigMAX_NUM_OTA_DATA_BUFFERS; ulIndex++ )
        {
            if( eventBuffer[ ulIndex ].bufferUsed == false )
            {
                eventBuffer[ ulIndex ].bufferUsed = true;
                pFreeBuffer = &eventBuffer[ ulIndex ];
                break;
            }
        }

        ( void ) sem_post( &bufferSemaphore );
    }
    else
    {
        LogError( ( "Failed to get buffer semaphore: "
                    ",errno=%s",
                    strerror( errno ) ) );
    }

    return pFreeBuffer;
}

/*-----------------------------------------------------------*/

static void otaAppCallback( OtaJobEvent_t event,
                            void * pData )
{
    OtaErr_t err = OtaErrUninitialized;

    switch( event )
    {
        case OtaJobEventActivate:
            LogInfo( ( "Received OtaJobEventActivate callback from OTA Agent." ) );

            /* Activate the new firmware image. */
            OTA_ActivateNewImage();

            /* Shutdown OTA Agent, if it is required that the unsubscribe operations are not
             * performed while shutting down please set the second parameter to 0 instead of 1. */
            OTA_Shutdown( 0, 1 );

            /* Requires manual activation of new image.*/
            LogError( ( "New image activation failed." ) );

            break;

        case OtaJobEventFail:
            LogInfo( ( "Received OtaJobEventFail callback from OTA Agent." ) );

            /* Nothing special to do. The OTA agent handles it. */
            break;

        case OtaJobEventStartTest:

            /* This demo just accepts the image since it was a good OTA update and networking
             * and services are all working (or we would not have made it this far). If this
             * were some custom device that wants to test other things before validating new
             * image, this would be the place to kick off those tests before calling
             * OTA_SetImageState() with the final result of either accepted or rejected. */

            LogInfo( ( "Received OtaJobEventStartTest callback from OTA Agent." ) );
            err = OTA_SetImageState( OtaImageStateAccepted );

            if( err != OtaErrNone )
            {
                LogError( ( " Failed to set image state as accepted." ) );
            }

            break;

        case OtaJobEventProcessed:
            LogDebug( ( "Received OtaJobEventProcessed callback from OTA Agent." ) );

            if( pData != NULL )
            {
                otaEventBufferFree( ( OtaEventData_t * ) pData );
            }

            break;

        case OtaJobEventSelfTestFailed:
            LogDebug( ( "Received OtaJobEventSelfTestFailed callback from OTA Agent." ) );

            /* Requires manual activation of previous image as self-test for
             * new image downloaded failed.*/
            LogError( ( "Self-test failed, shutting down OTA Agent." ) );

            /* Shutdown OTA Agent, if it is required that the unsubscribe operations are not
             * performed while shutting down please set the second parameter to 0 instead of 1. */
            OTA_Shutdown( 0, 1 );

            break;

        default:
            LogDebug( ( "Received invalid callback event from OTA Agent." ) );
    }
}

jobMessageType_t getJobMessageType( const char * pTopicName,
                                    uint16_t topicNameLength )
{
    uint16_t index = 0U;
    MQTTStatus_t mqttStatus = MQTTSuccess;
    bool isMatch = false;
    jobMessageType_t jobMessageIndex = jobMessageTypeMax;

    /* For suppressing compiler-warning: unused variable. */
    ( void ) mqttStatus;

    /* Lookup table for OTA job message string. */
    static const char * const pJobTopicFilters[ jobMessageTypeMax ] =
    {
        OTA_TOPIC_PREFIX OTA_TOPIC_JOBS "/$next/get/accepted",
        OTA_TOPIC_PREFIX OTA_TOPIC_JOBS "/notify-next",
    };

    /* Match the input topic filter against the wild-card pattern of topics filters
    * relevant for the OTA Update service to determine the type of topic filter. */
    for( ; index < jobMessageTypeMax; index++ )
    {
        mqttStatus = MQTT_MatchTopic( pTopicName,
                                      topicNameLength,
                                      pJobTopicFilters[ index ],
                                      strlen( pJobTopicFilters[ index ] ),
                                      &isMatch );
        assert( mqttStatus == MQTTSuccess );

        if( isMatch )
        {
            jobMessageIndex = index;
            break;
        }
    }

    return jobMessageIndex;
}

/*-----------------------------------------------------------*/

static void mqttJobCallback( MQTTContext_t * pContext,
                             MQTTPublishInfo_t * pPublishInfo )
{
    OtaEventData_t * pData;
    OtaEventMsg_t eventMsg = { 0 };
    jobMessageType_t jobMessageType = 0;

    assert( pPublishInfo != NULL );
    assert( pContext != NULL );

    ( void ) pContext;

    jobMessageType = getJobMessageType( pPublishInfo->pTopicName, pPublishInfo->topicNameLength );

    switch( jobMessageType )
    {
        case jobMessageTypeNextGetAccepted:
        case jobMessageTypeNextNotify:

            pData = otaEventBufferGet();

            if( pData != NULL )
            {
                memcpy( pData->data, pPublishInfo->pPayload, pPublishInfo->payloadLength );
                pData->dataLength = pPublishInfo->payloadLength;
                eventMsg.eventId = OtaAgentEventReceivedJobDocument;
                eventMsg.pEventData = pData;

                /* Send job document received event. */
                OTA_SignalEvent( &eventMsg );
            }
            else
            {
                LogError( ( "No OTA data buffers available." ) );
            }

            break;

        default:
            LogInfo( ( "Received job message %s size %ld.\n\n",
                       pPublishInfo->pTopicName,
                       pPublishInfo->payloadLength ) );
    }
}

/*-----------------------------------------------------------*/

static void mqttDataCallback( MQTTContext_t * pContext,
                              MQTTPublishInfo_t * pPublishInfo )
{
    OtaEventData_t * pData;
    OtaEventMsg_t eventMsg = { 0 };

    assert( pPublishInfo != NULL );
    assert( pContext != NULL );

    ( void ) pContext;

    LogInfo( ( "Received data message callback, size %zu.\n\n", pPublishInfo->payloadLength ) );

    pData = otaEventBufferGet();

    if( pData != NULL )
    {
        memcpy( pData->data, pPublishInfo->pPayload, pPublishInfo->payloadLength );
        pData->dataLength = pPublishInfo->payloadLength;
        eventMsg.eventId = OtaAgentEventReceivedFileBlock;
        eventMsg.pEventData = pData;

        /* Send job document received event. */
        OTA_SignalEvent( &eventMsg );
    }
    else
    {
        LogError( ( "No OTA data buffers available." ) );
    }
}

/*-----------------------------------------------------------*/

static void mqttEventCallback( MQTTContext_t * pMqttContext,
                               MQTTPacketInfo_t * pPacketInfo,
                               MQTTDeserializedInfo_t * pDeserializedInfo )
{
    assert( pMqttContext != NULL );
    assert( pPacketInfo != NULL );
    assert( pDeserializedInfo != NULL );

    /* Handle incoming publish. The lower 4 bits of the publish packet
     * type is used for the dup, QoS, and retain flags. Hence masking
     * out the lower bits to check if the packet is publish. */
    if( ( pPacketInfo->type & 0xF0U ) == MQTT_PACKET_TYPE_PUBLISH )
    {
        assert( pDeserializedInfo->pPublishInfo != NULL );
        /* Handle incoming publish. */
        SubscriptionManager_DispatchHandler( pMqttContext, pDeserializedInfo->pPublishInfo );
    }
    else
    {
        /* Handle other packets. */
        switch( pPacketInfo->type )
        {
            case MQTT_PACKET_TYPE_SUBACK:
                LogInfo( ( "Received SUBACK.\n\n" ) );
                break;

            case MQTT_PACKET_TYPE_UNSUBACK:
                LogInfo( ( "Received UNSUBACK.\n\n" ) );
                break;

            case MQTT_PACKET_TYPE_PINGRESP:

                /* Nothing to be done from application as library handles
                 * PINGRESP. */
                LogWarn( ( "PINGRESP should not be handled by the application "
                           "callback when using MQTT_ProcessLoop.\n\n" ) );
                break;

            case MQTT_PACKET_TYPE_PUBACK:
                LogInfo( ( "PUBACK received for packet id %u.\n\n",
                           pDeserializedInfo->packetIdentifier ) );
                sem_post( &ackSemaphore );
                break;

            /* Any other packet type is invalid. */
            default:
                LogError( ( "Unknown packet type received:(%02x).\n\n",
                            pPacketInfo->type ) );
        }
    }
}

/*-----------------------------------------------------------*/

static uint32_t generateRandomNumber()
{
    return( rand() );
}

/*-----------------------------------------------------------*/

static int initializeMqtt( MQTTContext_t * pMqttContext,
                           NetworkContext_t * pNetworkContext )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus = MQTTBadParameter;
    MQTTFixedBuffer_t networkBuffer;
    TransportInterface_t transport;

    assert( pMqttContext != NULL );
    assert( pNetworkContext != NULL );

    /* Fill in TransportInterface send and receive function pointers.
     * For this demo, TCP sockets are used to send and receive data
     * from network.  TLS over TCP channel is used as the transport
     * layer for the MQTT connection. Network context is SSL context
     * for OpenSSL.*/
    transport.pNetworkContext = pNetworkContext;
    transport.send = Openssl_Send;
    transport.recv = Openssl_Recv;
    transport.writev = NULL;

    /* Fill the values for network buffer. */
    networkBuffer.pBuffer = otaNetworkBuffer;
    networkBuffer.size = OTA_NETWORK_BUFFER_SIZE;

    /* Initialize MQTT library. */
    mqttStatus = MQTT_Init( pMqttContext,
                            &transport,
                            Clock_GetTimeMs,
                            mqttEventCallback,
                            &networkBuffer );

    if( mqttStatus != MQTTSuccess )
    {
        returnStatus = EXIT_FAILURE;
        LogError( ( "MQTT_Init failed: Status = %s.", MQTT_Status_strerror( mqttStatus ) ) );
    }
    else
    {
        mqttStatus = MQTT_InitStatefulQoS( pMqttContext,
                                           pOutgoingPublishRecords,
                                           OUTGOING_PUBLISH_RECORD_LEN,
                                           pIncomingPublishRecords,
                                           INCOMING_PUBLISH_RECORD_LEN );

        if( mqttStatus != MQTTSuccess )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "MQTT_InitStatefulQoS failed: Status = %s.", MQTT_Status_strerror( mqttStatus ) ) );
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int connectToServerWithBackoffRetries( NetworkContext_t * pNetworkContext )
{
    int returnStatus = EXIT_SUCCESS;
    BackoffAlgorithmStatus_t backoffAlgStatus = BackoffAlgorithmSuccess;
    OpensslStatus_t opensslStatus = OPENSSL_SUCCESS;
    BackoffAlgorithmContext_t reconnectParams;
    ServerInfo_t serverInfo;
    OpensslCredentials_t opensslCredentials;
    uint16_t nextRetryBackOff;

    /* Initialize information to connect to the MQTT broker. */
    serverInfo.pHostName = AWS_IOT_ENDPOINT;
    serverInfo.hostNameLength = AWS_IOT_ENDPOINT_LENGTH;
    serverInfo.port = AWS_MQTT_PORT;

    /* Initialize credentials for establishing TLS session. */
    memset( &opensslCredentials, 0, sizeof( OpensslCredentials_t ) );
    opensslCredentials.pRootCaPath = ROOT_CA_CERT_PATH;

    /* If #CLIENT_USERNAME is defined, username/password is used for authenticating
     * the client. */
    #ifndef CLIENT_USERNAME
        opensslCredentials.pClientCertPath = CLIENT_CERT_PATH;
        opensslCredentials.pPrivateKeyPath = CLIENT_PRIVATE_KEY_PATH;
    #endif

    /* AWS IoT requires devices to send the Server Name Indication (SNI)
     * extension to the Transport Layer Security (TLS) protocol and provide
     * the complete endpoint address in the host_name field. Details about
     * SNI for AWS IoT can be found in the link below.
     * https://docs.aws.amazon.com/iot/latest/developerguide/transport-security.html */
    opensslCredentials.sniHostName = AWS_IOT_ENDPOINT;

    if( AWS_MQTT_PORT == 443 )
    {
        /* Pass the ALPN protocol name depending on the port being used.
         * Please see more details about the ALPN protocol for the AWS IoT MQTT
         * endpoint in the link below.
         * https://aws.amazon.com/blogs/iot/mqtt-with-tls-client-authentication-on-port-443-why-it-is-useful-and-how-it-works/
         *
         * For username and password based authentication in AWS IoT,
         * #AWS_IOT_PASSWORD_ALPN is used. More details can be found in the
         * link below.
         * https://docs.aws.amazon.com/iot/latest/developerguide/custom-authentication.html
         */
        #ifdef CLIENT_USERNAME
            opensslCredentials.pAlpnProtos = AWS_IOT_ALPN_MQTT_CUSTOM_AUTH_OPENSSL;
            opensslCredentials.alpnProtosLen = AWS_IOT_ALPN_MQTT_CUSTOM_AUTH_OPENSSL_LEN;
        #else
            opensslCredentials.pAlpnProtos = AWS_IOT_ALPN_MQTT_CA_AUTH_OPENSSL;
            opensslCredentials.alpnProtosLen = AWS_IOT_ALPN_MQTT_CA_AUTH_OPENSSL_LEN;
        #endif
    }

    /* Initialize reconnect attempts and interval */
    BackoffAlgorithm_InitializeParams( &reconnectParams,
                                       CONNECTION_RETRY_BACKOFF_BASE_MS,
                                       CONNECTION_RETRY_MAX_BACKOFF_DELAY_MS,
                                       CONNECTION_RETRY_MAX_ATTEMPTS );

    /* Attempt to connect to MQTT broker. If connection fails, retry after
     * a timeout. Timeout value will exponentially increase until maximum
     * attempts are reached.
     */
    do
    {
        /* Establish a TLS session with the MQTT broker. This example connects
         * to the MQTT broker as specified in AWS_IOT_ENDPOINT and AWS_MQTT_PORT
         * at the demo config header. */
        LogInfo( ( "Establishing a TLS session to %.*s:%d.",
                   AWS_IOT_ENDPOINT_LENGTH,
                   AWS_IOT_ENDPOINT,
                   AWS_MQTT_PORT ) );
        opensslStatus = Openssl_Connect( pNetworkContext,
                                         &serverInfo,
                                         &opensslCredentials,
                                         TRANSPORT_SEND_RECV_TIMEOUT_MS,
                                         TRANSPORT_SEND_RECV_TIMEOUT_MS );

        if( opensslStatus != OPENSSL_SUCCESS )
        {
            /* Generate a random number and get back-off value (in milliseconds) for the next connection retry. */
            backoffAlgStatus = BackoffAlgorithm_GetNextBackoff( &reconnectParams, generateRandomNumber(), &nextRetryBackOff );

            if( backoffAlgStatus == BackoffAlgorithmRetriesExhausted )
            {
                LogError( ( "Connection to the broker failed, all attempts exhausted." ) );
                returnStatus = EXIT_FAILURE;
            }
            else if( backoffAlgStatus == BackoffAlgorithmSuccess )
            {
                LogWarn( ( "Connection to the broker failed. Retrying connection "
                           "after %hu ms backoff.",
                           ( unsigned short ) nextRetryBackOff ) );
                Clock_SleepMs( nextRetryBackOff );
            }
        }
    } while( ( opensslStatus != OPENSSL_SUCCESS ) && ( backoffAlgStatus == BackoffAlgorithmSuccess ) );

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int establishMqttSession( MQTTContext_t * pMqttContext )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus = MQTTBadParameter;
    MQTTConnectInfo_t connectInfo = { 0 };

    bool sessionPresent = false;

    assert( pMqttContext != NULL );

    /* Establish MQTT session by sending a CONNECT packet. */

    /* If #createCleanSession is true, start with a clean session
     * i.e. direct the MQTT broker to discard any previous session data.
     * If #createCleanSession is false, directs the broker to attempt to
     * reestablish a session which was already present. */
    connectInfo.cleanSession = true;

    /* The client identifier is used to uniquely identify this MQTT client to
     * the MQTT broker. In a production device the identifier can be something
     * unique, such as a device serial number. */
    connectInfo.pClientIdentifier = CLIENT_IDENTIFIER;
    connectInfo.clientIdentifierLength = CLIENT_IDENTIFIER_LENGTH;

    /* The maximum time interval in seconds which is allowed to elapse
     * between two Control Packets.
     * It is the responsibility of the Client to ensure that the interval between
     * Control Packets being sent does not exceed the this Keep Alive value. In the
     * absence of sending any other Control Packets, the Client MUST send a
     * PINGREQ Packet. */
    connectInfo.keepAliveSeconds = MQTT_KEEP_ALIVE_INTERVAL_SECONDS;

    /* Use the username and password for authentication, if they are defined.
     * Refer to the AWS IoT documentation below for details regarding client
     * authentication with a username and password.
     * https://docs.aws.amazon.com/iot/latest/developerguide/custom-authentication.html
     * An authorizer setup needs to be done, as mentioned in the above link, to use
     * username/password based client authentication.
     *
     * The username field is populated with voluntary metrics to AWS IoT.
     * The metrics collected by AWS IoT are the operating system, the operating
     * system's version, the hardware platform, and the MQTT Client library
     * information. These metrics help AWS IoT improve security and provide
     * better technical support.
     *
     * If client authentication is based on username/password in AWS IoT,
     * the metrics string is appended to the username to support both client
     * authentication and metrics collection. */
    #ifdef CLIENT_USERNAME
        connectInfo.pUserName = CLIENT_USERNAME_WITH_METRICS;
        connectInfo.userNameLength = strlen( CLIENT_USERNAME_WITH_METRICS );
        connectInfo.pPassword = CLIENT_PASSWORD;
        connectInfo.passwordLength = strlen( CLIENT_PASSWORD );
    #else
        connectInfo.pUserName = METRICS_STRING;
        connectInfo.userNameLength = METRICS_STRING_LENGTH;
        /* Password for authentication is not used. */
        connectInfo.pPassword = NULL;
        connectInfo.passwordLength = 0U;
    #endif /* ifdef CLIENT_USERNAME */

    if( pthread_mutex_lock( &mqttMutex ) == 0 )
    {
        /* Send MQTT CONNECT packet to broker. */
        mqttStatus = MQTT_Connect( pMqttContext, &connectInfo, NULL, CONNACK_RECV_TIMEOUT_MS, &sessionPresent );

        pthread_mutex_unlock( &mqttMutex );
    }
    else
    {
        LogError( ( "Failed to acquire mutex for executing MQTT_Connect"
                    ",errno=%s",
                    strerror( errno ) ) );
    }

    if( mqttStatus != MQTTSuccess )
    {
        returnStatus = EXIT_FAILURE;
        LogError( ( "Connection with MQTT broker failed with status %s.",
                    MQTT_Status_strerror( mqttStatus ) ) );
    }
    else
    {
        LogInfo( ( "MQTT connection successfully established with broker.\n\n" ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int establishConnection( void )
{
    int returnStatus = EXIT_FAILURE;

    /* Set the pParams member of the network context with desired transport. */
    networkContext.pParams = &opensslParams;

    /* Attempt to connect to the MQTT broker. If connection fails, retry after
     * a timeout. Timeout value will be exponentially increased till the maximum
     * attempts are reached or maximum timeout value is reached. The function
     * returns EXIT_FAILURE if the TCP connection cannot be established to
     * broker after configured number of attempts. */
    returnStatus = connectToServerWithBackoffRetries( &networkContext );

    if( returnStatus != EXIT_SUCCESS )
    {
        /* Log error to indicate connection failure. */
        LogError( ( "Failed to connect to MQTT broker %.*s.",
                    AWS_IOT_ENDPOINT_LENGTH,
                    AWS_IOT_ENDPOINT ) );
    }
    else
    {
        /* Establish MQTT session on top of TCP+TLS connection. */
        LogInfo( ( "Creating an MQTT connection to %.*s.",
                   AWS_IOT_ENDPOINT_LENGTH,
                   AWS_IOT_ENDPOINT ) );

        /* Sends an MQTT Connect packet using the established TLS session,
         * then waits for connection acknowledgment (CONNACK) packet. */
        returnStatus = establishMqttSession( &mqttContext );

        if( returnStatus != EXIT_SUCCESS )
        {
            LogError( ( "Failed creating an MQTT connection to %.*s.",
                        AWS_IOT_ENDPOINT_LENGTH,
                        AWS_IOT_ENDPOINT ) );
        }
        else
        {
            LogDebug( ( "Success creating MQTT connection to %.*s.",
                        AWS_IOT_ENDPOINT_LENGTH,
                        AWS_IOT_ENDPOINT ) );

            mqttSessionEstablished = true;
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static void disconnect( void )
{
    /* Disconnect from broker. */
    LogInfo( ( "Disconnecting the MQTT connection with %s.", AWS_IOT_ENDPOINT ) );

    if( mqttSessionEstablished == true )
    {
        if( pthread_mutex_lock( &mqttMutex ) == 0 )
        {
            /* Disconnect MQTT session. */
            MQTT_Disconnect( &mqttContext );

            /* Clear the mqtt session flag. */
            mqttSessionEstablished = false;

            pthread_mutex_unlock( &mqttMutex );
        }
        else
        {
            LogError( ( "Failed to acquire mutex to execute MQTT_Disconnect"
                        ",errno=%s",
                        strerror( errno ) ) );
        }
    }
    else
    {
        LogError( ( "MQTT already disconnected." ) );
    }

    /* End TLS session, then close TCP connection. */
    ( void ) Openssl_Disconnect( &networkContext );
}

/*-----------------------------------------------------------*/

static void registerSubscriptionManagerCallback( const char * pTopicFilter,
                                                 uint16_t topicFilterLength )
{
    bool isMatch = false;
    MQTTStatus_t mqttStatus = MQTTSuccess;
    SubscriptionManagerStatus_t subscriptionStatus = SUBSCRIPTION_MANAGER_SUCCESS;

    uint16_t index = 0U;

    /* For suppressing compiler-warning: unused variable. */
    ( void ) mqttStatus;

    /* Lookup table for OTA message string. */
    static const char * const pWildCardTopicFilters[] =
    {
        OTA_TOPIC_PREFIX OTA_TOPIC_JOBS "/#",
        OTA_TOPIC_PREFIX OTA_TOPIC_STREAM "/#"
    };

    /* Match the input topic filter against the wild-card pattern of topics filters
    * relevant for the OTA Update service to determine the type of topic filter. */
    for( ; index < 2; index++ )
    {
        mqttStatus = MQTT_MatchTopic( pTopicFilter,
                                      topicFilterLength,
                                      pWildCardTopicFilters[ index ],
                                      strlen( pWildCardTopicFilters[ index ] ),
                                      &isMatch );
        assert( mqttStatus == MQTTSuccess );

        if( isMatch )
        {
            /* Register callback to subscription manager. */
            subscriptionStatus = SubscriptionManager_RegisterCallback( pWildCardTopicFilters[ index ],
                                                                       strlen( pWildCardTopicFilters[ index ] ),
                                                                       otaMessageCallback[ index ] );

            if( subscriptionStatus != SUBSCRIPTION_MANAGER_SUCCESS )
            {
                LogWarn( ( "Failed to register a callback to subscription manager with error = %d.",
                           subscriptionStatus ) );
            }

            break;
        }
    }
}

/*-----------------------------------------------------------*/

static OtaMqttStatus_t mqttSubscribe( const char * pTopicFilter,
                                      uint16_t topicFilterLength,
                                      uint8_t qos )
{
    OtaMqttStatus_t otaRet = OtaMqttSuccess;

    MQTTStatus_t mqttStatus = MQTTBadParameter;
    MQTTContext_t * pMqttContext = &mqttContext;
    MQTTSubscribeInfo_t pSubscriptionList[ 1 ];

    assert( pMqttContext != NULL );
    assert( pTopicFilter != NULL );
    assert( topicFilterLength > 0 );

    ( void ) qos;

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* Set the topic and topic length. */
    pSubscriptionList[ 0 ].pTopicFilter = pTopicFilter;
    pSubscriptionList[ 0 ].topicFilterLength = topicFilterLength;

    if( pthread_mutex_lock( &mqttMutex ) == 0 )
    {
        /* Send SUBSCRIBE packet. */
        mqttStatus = MQTT_Subscribe( pMqttContext,
                                     pSubscriptionList,
                                     sizeof( pSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                     MQTT_GetPacketId( pMqttContext ) );

        pthread_mutex_unlock( &mqttMutex );
    }
    else
    {
        LogError( ( "Failed to acquire mqtt mutex for executing MQTT_Subscribe"
                    ",errno=%s",
                    strerror( errno ) ) );
    }

    if( mqttStatus != MQTTSuccess )
    {
        LogError( ( "Failed to send SUBSCRIBE packet to broker with error = %u.",
                    mqttStatus ) );

        otaRet = OtaMqttSubscribeFailed;
    }
    else
    {
        LogInfo( ( "SUBSCRIBE topic %.*s to broker.\n\n",
                   topicFilterLength,
                   pTopicFilter ) );

        registerSubscriptionManagerCallback( pTopicFilter, topicFilterLength );
    }

    return otaRet;
}

/*-----------------------------------------------------------*/

static OtaMqttStatus_t mqttPublish( const char * const pacTopic,
                                    uint16_t topicLen,
                                    const char * pMsg,
                                    uint32_t msgSize,
                                    uint8_t qos )
{
    OtaMqttStatus_t otaRet = OtaMqttSuccess;

    MQTTStatus_t mqttStatus = MQTTBadParameter;
    MQTTPublishInfo_t publishInfo = { 0 };
    MQTTContext_t * pMqttContext = &mqttContext;
    struct timespec ts = { 0 };
    int ret;

    /* Set the required publish parameters. */
    publishInfo.pTopicName = pacTopic;
    publishInfo.topicNameLength = topicLen;
    publishInfo.qos = qos;
    publishInfo.pPayload = pMsg;
    publishInfo.payloadLength = msgSize;

    if( pthread_mutex_lock( &mqttMutex ) == 0 )
    {
        mqttStatus = MQTT_Publish( pMqttContext,
                                   &publishInfo,
                                   MQTT_GetPacketId( pMqttContext ) );

        if( mqttStatus != MQTTSuccess )
        {
            LogError( ( "Failed to send PUBLISH packet to broker with error = %u.", mqttStatus ) );

            otaRet = OtaMqttPublishFailed;
        }

        pthread_mutex_unlock( &mqttMutex );
    }
    else
    {
        LogError( ( "Failed to acquire mqtt mutex for executing MQTT_Publish"
                    ",errno=%s",
                    strerror( errno ) ) );

        otaRet = OtaMqttPublishFailed;
    }

    if( ( mqttStatus == MQTTSuccess ) && ( qos == 1 ) )
    {
        /* Calculate relative interval as current time plus number of seconds. */
        clock_gettime( CLOCK_REALTIME, &ts );
        ts.tv_sec += MQTT_ACK_TIMEOUT_MS;

        while( ( ret = sem_timedwait( &ackSemaphore, &ts ) ) == -1 && errno == EINTR )
        {
            continue;
        }

        if( ret == -1 )
        {
            LogError( ( "Failed to receive ack for publish."
                        ",errno=%s",
                        strerror( errno ) ) );

            otaRet = OtaMqttPublishFailed;
        }
    }

    return otaRet;
}

/*-----------------------------------------------------------*/

static OtaMqttStatus_t mqttUnsubscribe( const char * pTopicFilter,
                                        uint16_t topicFilterLength,
                                        uint8_t qos )
{
    OtaMqttStatus_t otaRet = OtaMqttSuccess;
    MQTTStatus_t mqttStatus = MQTTBadParameter;

    MQTTSubscribeInfo_t pSubscriptionList[ 1 ];
    MQTTContext_t * pMqttContext = &mqttContext;

    ( void ) qos;

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* Set the topic and topic length. */
    pSubscriptionList[ 0 ].pTopicFilter = pTopicFilter;
    pSubscriptionList[ 0 ].topicFilterLength = topicFilterLength;

    if( pthread_mutex_lock( &mqttMutex ) == 0 )
    {
        /* Send UNSUBSCRIBE packet. */
        mqttStatus = MQTT_Unsubscribe( pMqttContext,
                                       pSubscriptionList,
                                       sizeof( pSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                       MQTT_GetPacketId( pMqttContext ) );

        pthread_mutex_unlock( &mqttMutex );
    }
    else
    {
        LogError( ( "Failed to acquire mutex for executing MQTT_Unsubscribe"
                    ",errno=%s",
                    strerror( errno ) ) );
    }

    if( mqttStatus != MQTTSuccess )
    {
        LogError( ( "Failed to send UNSUBSCRIBE packet to broker with error = %u.",
                    mqttStatus ) );

        otaRet = OtaMqttUnsubscribeFailed;
    }
    else
    {
        LogInfo( ( "UNSUBSCRIBE topic %.*s to broker.\n\n",
                   topicFilterLength,
                   pTopicFilter ) );
    }

    return otaRet;
}

/*-----------------------------------------------------------*/

static void setOtaInterfaces( OtaInterfaces_t * pOtaInterfaces )
{
    /* Initialize OTA library OS Interface. */
    pOtaInterfaces->os.event.init = Posix_OtaInitEvent;
    pOtaInterfaces->os.event.send = Posix_OtaSendEvent;
    pOtaInterfaces->os.event.recv = Posix_OtaReceiveEvent;
    pOtaInterfaces->os.event.deinit = Posix_OtaDeinitEvent;
    pOtaInterfaces->os.timer.start = Posix_OtaStartTimer;
    pOtaInterfaces->os.timer.stop = Posix_OtaStopTimer;
    pOtaInterfaces->os.timer.delete = Posix_OtaDeleteTimer;
    pOtaInterfaces->os.mem.malloc = STDC_Malloc;
    pOtaInterfaces->os.mem.free = STDC_Free;

    /* Initialize the OTA library MQTT Interface.*/
    pOtaInterfaces->mqtt.subscribe = mqttSubscribe;
    pOtaInterfaces->mqtt.publish = mqttPublish;
    pOtaInterfaces->mqtt.unsubscribe = mqttUnsubscribe;

    /* Initialize the OTA library PAL Interface.*/
    pOtaInterfaces->pal.getPlatformImageState = otaPal_GetPlatformImageState;
    pOtaInterfaces->pal.setPlatformImageState = otaPal_SetPlatformImageState;
    pOtaInterfaces->pal.writeBlock = otaPal_WriteBlock;
    pOtaInterfaces->pal.activate = otaPal_ActivateNewImage;
    pOtaInterfaces->pal.closeFile = otaPal_CloseFile;
    pOtaInterfaces->pal.reset = otaPal_ResetDevice;
    pOtaInterfaces->pal.abort = otaPal_Abort;
    pOtaInterfaces->pal.createFile = otaPal_CreateFileForRx;
}

/*-----------------------------------------------------------*/

static void * otaThread( void * pParam )
{
    /* Calling OTA agent task. */
    OTA_EventProcessingTask( pParam );
    LogInfo( ( "OTA Agent stopped." ) );
    return NULL;
}
/*-----------------------------------------------------------*/
static int startOTADemo( void )
{
    /* Status indicating a successful demo or not. */
    int returnStatus = EXIT_SUCCESS;

    /* coreMQTT library return status. */
    MQTTStatus_t mqttStatus = MQTTBadParameter;

    /* OTA library return status. */
    OtaErr_t otaRet = OtaErrNone;

    /* OTA Agent state returned from calling OTA_GetAgentState.*/
    OtaState_t state = OtaAgentStateStopped;

    /* OTA event message used for sending event to OTA Agent.*/
    OtaEventMsg_t eventMsg = { 0 };

    /* OTA library packet statistics per job.*/
    OtaAgentStatistics_t otaStatistics = { 0 };

    /* OTA Agent thread handle.*/
    pthread_t threadHandle;

    /* Status return from call to pthread_join. */
    int returnJoin = 0;

    /* OTA interface context required for library interface functions.*/
    OtaInterfaces_t otaInterfaces;

    /* Maximum time to wait for the OTA agent to get suspended. */
    int16_t suspendTimeout;

    /* Set OTA Library interfaces.*/
    setOtaInterfaces( &otaInterfaces );

    LogInfo( ( "OTA over MQTT demo, Application version %u.%u.%u",
               appFirmwareVersion.u.x.major,
               appFirmwareVersion.u.x.minor,
               appFirmwareVersion.u.x.build ) );

    /****************************** Init OTA Library. ******************************/

    if( returnStatus == EXIT_SUCCESS )
    {
        if( ( otaRet = OTA_Init( &otaBuffer,
                                 &otaInterfaces,
                                 ( const uint8_t * ) ( CLIENT_IDENTIFIER ),
                                 otaAppCallback ) ) != OtaErrNone )
        {
            LogError( ( "Failed to initialize OTA Agent, exiting = %u.",
                        otaRet ) );

            returnStatus = EXIT_FAILURE;
        }
    }

    /****************************** Create OTA Task. ******************************/

    if( returnStatus == EXIT_SUCCESS )
    {
        if( pthread_create( &threadHandle, NULL, otaThread, NULL ) != 0 )
        {
            LogError( ( "Failed to create OTA thread: "
                        ",errno=%s",
                        strerror( errno ) ) );

            returnStatus = EXIT_FAILURE;
        }
    }

    /****************************** OTA Demo loop. ******************************/

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Wait till OTA library is stopped, output statistics for currently running
         * OTA job */
        while( ( ( state = OTA_GetState() ) != OtaAgentStateStopped ) )
        {
            if( mqttSessionEstablished != true )
            {
                /* Connect to MQTT broker and create MQTT connection. */
                if( EXIT_SUCCESS == establishConnection() )
                {
                    /* Check if OTA process was suspended and resume if required. */
                    if( state == OtaAgentStateSuspended )
                    {
                        /* Resume OTA operations. */
                        OTA_Resume();
                    }
                    else
                    {
                        /* Send start event to OTA Agent.*/
                        eventMsg.eventId = OtaAgentEventStart;
                        OTA_SignalEvent( &eventMsg );
                    }
                }
            }

            if( mqttSessionEstablished == true )
            {
                /* Acquire the mqtt mutex lock. */
                if( pthread_mutex_lock( &mqttMutex ) == 0 )
                {
                    /* Loop to receive packet from transport interface. */
                    mqttStatus = MQTT_ProcessLoop( &mqttContext );

                    pthread_mutex_unlock( &mqttMutex );
                }
                else
                {
                    LogError( ( "Failed to acquire mutex to execute process loop"
                                ",errno=%s",
                                strerror( errno ) ) );
                }

                if( ( mqttStatus == MQTTSuccess ) || ( mqttStatus == MQTTNeedMoreBytes ) )
                {
                    /* Get OTA statistics for currently executing job. */
                    OTA_GetStatistics( &otaStatistics );

                    LogInfo( ( " Received: %u   Queued: %u   Processed: %u   Dropped: %u",
                               otaStatistics.otaPacketsReceived,
                               otaStatistics.otaPacketsQueued,
                               otaStatistics.otaPacketsProcessed,
                               otaStatistics.otaPacketsDropped ) );

                    /* Delay to allow data to buffer for MQTT_ProcessLoop. */
                    Clock_SleepMs( OTA_EXAMPLE_LOOP_SLEEP_PERIOD_MS );
                }
                else
                {
                    LogError( ( "MQTT_ProcessLoop returned with status = %s.",
                                MQTT_Status_strerror( mqttStatus ) ) );

                    /* Disconnect from broker and close connection. */
                    disconnect();

                    /* Suspend OTA operations. */
                    otaRet = OTA_Suspend();

                    if( otaRet == OtaErrNone )
                    {
                        suspendTimeout = OTA_SUSPEND_TIMEOUT_MS;

                        while( ( ( state = OTA_GetState() ) != OtaAgentStateSuspended ) && ( suspendTimeout > 0 ) )
                        {
                            /* Wait for OTA Library state to suspend */
                            Clock_SleepMs( OTA_EXAMPLE_TASK_DELAY_MS );
                            suspendTimeout -= OTA_EXAMPLE_TASK_DELAY_MS;
                        }
                    }
                    else
                    {
                        LogError( ( "OTA failed to suspend. "
                                    "StatusCode=%d.", otaRet ) );
                    }
                }
            }
        }
    }

    /****************************** Wait for OTA Thread. ******************************/

    if( returnStatus == EXIT_SUCCESS )
    {
        returnJoin = pthread_join( threadHandle, NULL );

        if( returnJoin != 0 )
        {
            LogError( ( "Failed to join thread"
                        ",error code = %d",
                        returnJoin ) );

            returnStatus = EXIT_FAILURE;
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

/**
 * @brief Entry point of demo.
 *
 * This example initializes the OTA library to enable OTA updates via the
 * MQTT broker. It simply connects to the MQTT broker with the users
 * credentials and spins in an indefinite loop to allow MQTT messages to be
 * forwarded to the OTA agent for possible processing. The OTA agent does all
 * of the real work; checking to see if the message topic is one destined for
 * the OTA agent. If not, it is simply ignored.
 */
int main( int argc,
          char ** argv )
{
    ( void ) argc;
    ( void ) argv;

    /* Return error status. */
    int returnStatus = EXIT_SUCCESS;

    /* Semaphore initialization flag. */
    bool bufferSemInitialized = false;
    bool ackSemInitialized = false;
    bool mqttMutexInitialized = false;

    /* Maximum time in milliseconds to wait before exiting demo . */
    int16_t waitTimeoutMs = OTA_DEMO_EXIT_TIMEOUT_MS;

    /* Initialize semaphore for buffer operations. */
    if( sem_init( &bufferSemaphore, 0, 1 ) != 0 )
    {
        LogError( ( "Failed to initialize buffer semaphore"
                    ",errno=%s",
                    strerror( errno ) ) );

        returnStatus = EXIT_FAILURE;
    }
    else
    {
        bufferSemInitialized = true;
    }

    /* Initialize semaphore for ack. */
    if( sem_init( &ackSemaphore, 0, 0 ) != 0 )
    {
        LogError( ( "Failed to initialize ack semaphore"
                    ",errno=%s",
                    strerror( errno ) ) );

        returnStatus = EXIT_FAILURE;
    }
    else
    {
        ackSemInitialized = true;
    }

    /* Initialize mutex for coreMQTT APIs. */
    if( pthread_mutex_init( &mqttMutex, NULL ) != 0 )
    {
        LogError( ( "Failed to initialize mutex for mqtt apis"
                    ",errno=%s",
                    strerror( errno ) ) );

        returnStatus = EXIT_FAILURE;
    }
    else
    {
        mqttMutexInitialized = true;
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Initialize MQTT library. Initialization of the MQTT library needs to be
         * done only once in this demo. */
        returnStatus = initializeMqtt( &mqttContext, &networkContext );
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Start OTA demo. */
        returnStatus = startOTADemo();
    }

    /* Disconnect from broker and close connection. */
    disconnect();

    if( bufferSemInitialized == true )
    {
        /* Cleanup semaphore created for buffer operations. */
        if( sem_destroy( &bufferSemaphore ) != 0 )
        {
            LogError( ( "Failed to destroy buffer semaphore"
                        ",errno=%s",
                        strerror( errno ) ) );

            returnStatus = EXIT_FAILURE;
        }
    }

    if( ackSemInitialized == true )
    {
        /* Cleanup semaphore created for ack. */
        if( sem_destroy( &ackSemaphore ) != 0 )
        {
            LogError( ( "Failed to destroy ack semaphore"
                        ",errno=%s",
                        strerror( errno ) ) );

            returnStatus = EXIT_FAILURE;
        }
    }

    if( mqttMutexInitialized == true )
    {
        /* Cleanup mutex created for MQTT operations. */
        if( pthread_mutex_destroy( &mqttMutex ) != 0 )
        {
            LogError( ( "Failed to destroy mutex for mqtt apis"
                        ",errno=%s",
                        strerror( errno ) ) );

            returnStatus = EXIT_FAILURE;
        }
    }

    /* Wait and log message before exiting demo. */
    while( waitTimeoutMs > 0 )
    {
        Clock_SleepMs( OTA_EXAMPLE_TASK_DELAY_MS );
        waitTimeoutMs -= OTA_EXAMPLE_TASK_DELAY_MS;

        LogError( ( "Exiting demo in %d sec", waitTimeoutMs / 1000 ) );
    }

    return returnStatus;
}

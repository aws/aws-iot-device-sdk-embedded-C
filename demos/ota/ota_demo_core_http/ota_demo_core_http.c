/*
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
 * @file ota_demo_core_http.c
 * @brief A simple OTA update example.
 */

/* Standard includes. */
#include <assert.h>
#include <stdlib.h>
#include <stdbool.h>

/* Include Demo Config as the first non-system header. */
#include "demo_config.h"

/* OpenSSL sockets transport implementation. */
#include "openssl_posix.h"

/* Retry parameters. */
#include "retry_utils.h"

/* Common HTTP demo utilities. */
#include "http_demo_utils.h"

/* Clock for timer. */
#include "clock.h"

/* MQTT include. */
#include "core_mqtt.h"
#include "mqtt_subscription_manager.h"

/* OTA Library include. */
#include "ota.h"
#include "ota_config.h"
#include "ota_private.h"

/* OTA Library Interface include. */
#include "ota_os_posix.h"
#include "ota_mqtt_interface.h"
#include "ota_http_interface.h"

/* HTTP API header. */
#include "core_http_client.h"

/* Include firmware version struct definition. */
#include "ota_appversion32.h"

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
 * @brief ALPN (Application-Layer Protocol Negotiation) protocol name for AWS IoT MQTT.
 *
 * This will be used if the AWS_MQTT_PORT is configured as 443 for AWS IoT MQTT broker.
 * Please see more details about the ALPN protocol for AWS IoT MQTT endpoint
 * in the link below.
 * https://aws.amazon.com/blogs/iot/mqtt-with-tls-client-authentication-on-port-443-why-it-is-useful-and-how-it-works/
 */
#define AWS_IOT_MQTT_ALPN                   "\x0ex-amzn-mqtt-ca"

/**
 * @brief Length of ALPN protocol name.
 */
#define AWS_IOT_MQTT_ALPN_LENGTH            ( ( uint16_t ) ( sizeof( AWS_IOT_MQTT_ALPN ) - 1 ) )

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
#define TRANSPORT_SEND_RECV_TIMEOUT_MS      ( 200 )

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
 * @brief Timeout for MQTT_ProcessLoop function in milliseconds.
 */
#define MQTT_PROCESS_LOOP_TIMEOUT_MS        ( 500U )

/**
 * @brief Size of the network buffer to receive the MQTT message.
 *
 * The largest message size is data size from the AWS IoT streaming service, 2000 is reserved for
 * extra headers.
 */
#define OTA_PRESIGNED_URL_MAX_SIZE          ( 2048U )
#define OTA_MQTT_HEADER_MAX_SIZE            ( 30U )
#define NETWORK_BUFFER_SIZE                 ( OTA_PRESIGNED_URL_MAX_SIZE )

/**
 * @brief The delay used in the main OTA Demo task loop to periodically output the OTA
 * statistics like number of packets received, dropped, processed and queued per connection.
 */
#define OTA_DEMO_TASK_DELAY_SECONDS         ( 1U )

/**
 * @brief The maximum size of the file paths used in the demo.
 */
#define OTA_MAX_FILE_PATH_SIZE              ( 260 )

/**
 * @brief The maximum size of the stream name required for downloading update file
 * from streaming service.
 */
#define OTA_MAX_STREAM_NAME_SIZE            ( 128 )

/**
 * @brief The maximum size of the file bitmap where each bit represents a block
 * status.
 */
#define OTA_MAX_BLOCK_BITMAP_SIZE           ( 256 )


/**
 * @brief The MQTT metrics string expected by AWS IoT.
 */
#define METRICS_STRING           "?SDK=" OS_NAME "&Version=" OS_VERSION "&Platform=" HARDWARE_PLATFORM_NAME "&MQTTLib=" MQTT_LIB

/**
 * @brief The length of the MQTT metrics string expected by AWS IoT.
 */
#define METRICS_STRING_LENGTH    ( ( uint16_t ) ( sizeof( METRICS_STRING ) - 1 ) )

/*-----------------------------------------------------------*/

/**
 * @brief Struct for firmware version.
 */
const AppVersion32_t appFirmwareVersion =
{
    .u.x.major = APP_VERSION_MAJOR,
    .u.x.minor = APP_VERSION_MINOR,
    .u.x.build = APP_VERSION_BUILD,
};

/**
 * @brief The network buffer must remain valid when OTA library task is running.
 */
static uint8_t buffer[ OTA_NETWORK_BUFFER_SIZE ];

/**
 * @brief Keep a flag for indicating if the MQTT connection is alive.
 */
static bool mqttSessionEstablished = false;

/**
 * @brief MQTT connection context used in this demo.
 */
static MQTTContext_t mqttContext;

/**
 * @brief Network context used for HTTP connection.
 */
static NetworkContext_t networkContextHttp;

/* HTTP URL information. */
httpUrlInfo_t UrlInfo;

/**
 * @brief The host address string extracted from the pre-signed URL.
 *
 * @note S3_PRESIGNED_GET_URL_LENGTH is set as the array length here as the
 * length of the host name string cannot exceed this value.
 */
static char serverHost[ 256 ];

/* Check that size of the user buffer is defined. */
#ifndef USER_BUFFER_LENGTH
    #define USER_BUFFER_LENGTH    ( 2048 )
#endif

/**
 * @brief A buffer used in the demo for storing HTTP request headers and
 * HTTP response headers and body.
 *
 * @note This demo shows how the same buffer can be re-used for storing the HTTP
 * response after the HTTP request is sent out. However, the user can also
 * decide to use separate buffers for storing the HTTP request and response.
 */
static uint8_t userBuffer[ USER_BUFFER_LENGTH ];

/* The transport layer interface used by the HTTP Client library. */
TransportInterface_t transportInterfaceHttp;

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
uint8_t url[ OTA_PRESIGNED_URL_MAX_SIZE ];

/**
 * @brief Bitmap memory.
 */
uint8_t bitmap[ OTA_MAX_BLOCK_BITMAP_SIZE ];

/**
 * @brief Event buffer.
 */
static OtaEventData_t eventBuffer;

/**
 * @brief The buffer passed to the OTA Agent from application while initializing.
 */
static OtaAppBuffer_t otaBuffer =
{
    .pUpdateFilePath    = updateFilePath,
    .updateFilePathsize = OTA_MAX_FILE_PATH_SIZE,
    .pCertFilePath      = certFilePath,
    .certFilePathSize   = OTA_MAX_FILE_PATH_SIZE,
    .url                = url,
    .urlSize            = OTA_PRESIGNED_URL_MAX_SIZE,
    .pFileBitmap        = bitmap,
    .fileBitmapSize     = OTA_MAX_BLOCK_BITMAP_SIZE
};


/*-----------------------------------------------------------*/

/**
 * @brief The application callback function for getting the incoming publish
 * and incoming acks reported from MQTT library.
 *
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] pPacketInfo Packet Info pointer for the incoming packet.
 * @param[in] pDeserializedInfo Deserialized information from the incoming packet.
 */
static void eventCallback( MQTTContext_t * pMqttContext,
                           MQTTPacketInfo_t * pPacketInfo,
                           MQTTDeserializedInfo_t * pDeserializedInfo );

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
static int establishMqttSession( MQTTContext_t * pMqttContext,
                                 bool createCleanSession,
                                 bool * pSessionPresent );

/*
 * Publish a message to the specified client/topic at the given QOS.
 */
static OtaErr_t mqttPublish( const char * const pacTopic,
                             uint16_t topicLen,
                             const char * pMsg,
                             uint32_t msgSize,
                             uint8_t qos );

/*
 * Subscribe to the topics.
 */
static OtaErr_t mqttSubscribe( const char * pTopicFilter,
                               uint16_t topicFilterLength,
                               uint8_t qos,
                               void * pCallback );

/*
 * Unsubscribe from the topics.
 */
static OtaErr_t mqttUnsubscribe( const char * pTopicFilter,
                                 uint16_t topicFilterLength,
                                 uint8_t qos );

/*-----------------------------------------------------------*/

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
 * @param[in] event Specify if this demo is running with the AWS IoT
 * MQTT server. Set this to `false` if using another MQTT server.
 * @return None.
 */
static void otaAppCallback( OtaJobEvent_t event )
{
    OtaErr_t err = OTA_ERR_UNINITIALIZED;

    /* OTA job is completed. so delete the MQTT and network connection. */
    if( event == OtaJobEventActivate )
    {
        LogInfo( ( "Received OtaJobEventActivate callback from OTA Agent." ) );

        /* OTA job is completed. so delete the network connection. */
        MQTT_Disconnect( &mqttContext );

        /* Activate the new firmware image. */
        OTA_ActivateNewImage();

        /* We should never get here as new image activation must reset the device.*/
        LogError( ( "New image activation failed." ) );

        for( ; ; )
        {
        }
    }
    else if( event == OtaJobEventFail )
    {
        LogInfo( ( "Received OtaJobEventFail callback from OTA Agent." ) );

        /* Nothing special to do. The OTA agent handles it. */
    }
    else if( event == OtaJobEventStartTest )
    {
        /* This demo just accepts the image since it was a good OTA update and networking
         * and services are all working (or we wouldn't have made it this far). If this
         * were some custom device that wants to test other things before calling it OK,
         * this would be the place to kick off those tests before calling OTA_SetImageState()
         * with the final result of either accepted or rejected. */

        LogInfo( ( "Received OtaJobEventStartTest callback from OTA Agent." ) );
        err = OTA_SetImageState( OtaImageStateAccepted );

        if( err != OTA_ERR_NONE )
        {
            LogError( ( " Error! Failed to set image state as accepted." ) );
        }
    }
}

/*-----------------------------------------------------------*/

static void mqttJobCallback( MQTTContext_t * pContext,
                             MQTTPublishInfo_t * pPublishInfo )
{
    assert( pPublishInfo != NULL );
    assert( pContext != NULL );

    OtaEventData_t * pData;
    OtaEventMsg_t eventMsg = { 0 };

    LogInfo( ( "Received job message callback, size %d.\n\n", pPublishInfo->payloadLength ) );

    pData = &eventBuffer;

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
        LogError( ( "Error: No OTA data buffers available.\r\n" ) );
    }
}

/*-----------------------------------------------------------*/

static void mqttDataCallback( MQTTContext_t * pContext,
                              MQTTPublishInfo_t * pPublishInfo )
{
    assert( pPublishInfo != NULL );
    assert( pContext != NULL );

    OtaEventData_t * pData;
    OtaEventMsg_t eventMsg = { 0 };

    LogInfo( ( "Received data message callback, size %d.\n\n", pPublishInfo->payloadLength ) );

    pData = &eventBuffer;

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
        LogError( ( "Error: No OTA data buffers available.\r\n" ) );
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
    /* assert( pDeserializedInfo->packetIdentifier != MQTT_PACKET_ID_INVALID ); */

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
                /* TODO, handle suback for OTA. */
                break;

            case MQTT_PACKET_TYPE_UNSUBACK:
                LogInfo( ( "Received UNSUBACK.\n\n" ) );
                /* TODO, handle ubsuback for OTA. */
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
                break;

            /* Any other packet type is invalid. */
            default:
                LogError( ( "Unknown packet type received:(%02x).\n\n",
                            pPacketInfo->type ) );
        }
    }
}

/*-----------------------------------------------------------*/

static int connectToServerWithBackoffRetries( NetworkContext_t * pNetworkContext )
{
    int returnStatus = EXIT_SUCCESS;
    RetryUtilsStatus_t retryUtilsStatus = RetryUtilsSuccess;
    OpensslStatus_t opensslStatus = OPENSSL_SUCCESS;
    RetryUtilsParams_t reconnectParams;
    ServerInfo_t serverInfo;
    OpensslCredentials_t opensslCredentials;

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
         * https://docs.aws.amazon.com/iot/latest/developerguide/enhanced-custom-auth-using.html
         */
        #ifdef CLIENT_USERNAME
            opensslCredentials.pAlpnProtos = AWS_IOT_PASSWORD_ALPN;
            opensslCredentials.alpnProtosLen = AWS_IOT_PASSWORD_ALPN_LENGTH;
        #else
            opensslCredentials.pAlpnProtos = AWS_IOT_MQTT_ALPN;
            opensslCredentials.alpnProtosLen = AWS_IOT_MQTT_ALPN_LENGTH;
        #endif
    }

    /* Initialize reconnect attempts and interval */
    RetryUtils_ParamsReset( &reconnectParams );

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
            LogWarn( ( "Connection to the broker failed. Retrying connection with backoff and jitter." ) );
            retryUtilsStatus = RetryUtils_BackoffAndSleep( &reconnectParams );
        }

        if( retryUtilsStatus == RetryUtilsRetriesExhausted )
        {
            LogError( ( "Connection to the broker failed, all attempts exhausted." ) );
            returnStatus = EXIT_FAILURE;
        }
    } while( ( opensslStatus != OPENSSL_SUCCESS ) && ( retryUtilsStatus == RetryUtilsSuccess ) );

    return returnStatus;
}

/*-----------------------------------------------------------*/

static OtaErr_t mqttSubscribe( const char * pTopicFilter,
                               uint16_t topicFilterLength,
                               uint8_t qos,
                               void * pCallback )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;

    MQTTSubscribeInfo_t pSubscriptionList[ 1 ];

    assert( pTopicFilter != NULL );
    assert( topicFilterLength > 0 );

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* This example subscribes to only one topic and uses QOS1. */
    pSubscriptionList[ 0 ].qos = qos;
    pSubscriptionList[ 0 ].pTopicFilter = pTopicFilter;
    pSubscriptionList[ 0 ].topicFilterLength = topicFilterLength;

    /* Send SUBSCRIBE packet. */
    mqttStatus = MQTT_Subscribe( &mqttContext,
                                 pSubscriptionList,
                                 sizeof( pSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                 MQTT_GetPacketId( &mqttContext ) );

    if( mqttStatus != MQTTSuccess )
    {
        LogError( ( "Failed to send SUBSCRIBE packet to broker with error = %u.",
                    mqttStatus ) );
        returnStatus = EXIT_FAILURE;
    }
    else
    {
        LogInfo( ( "SUBSCRIBE topic %.*s to broker.\n\n",
                   topicFilterLength,
                   pTopicFilter ) );

        /* Process incoming packet from the broker. Acknowledgment for subscription
         * ( SUBACK ) will be received here. However after sending the subscribe, the
         * client may receive a publish before it receives a subscribe ack. Since this
         * demo is subscribing to the topic to which no one is publishing, probability
         * of receiving publish message before subscribe ack is zero; but application
         * must be ready to receive any packet. This demo uses MQTT_ProcessLoop to
         * receive packet from network. */
        mqttStatus = MQTT_ProcessLoop( &mqttContext, 1000 );

        if( mqttStatus != MQTTSuccess )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "MQTT_ProcessLoop returned with status = %u.",
                        mqttStatus ) );
        }
    }

    /* Register callback to suncription manager. */
    SubscriptionManager_RegisterCallback( pTopicFilter, topicFilterLength, pCallback );

    return returnStatus;
}

/*
 * Publish a message to the specified client/topic at the given QOS.
 */
static OtaErr_t mqttPublish( const char * const pacTopic,
                             uint16_t topicLen,
                             const char * pMsg,
                             uint32_t msgSize,
                             uint8_t qos )
{
    OtaErr_t otaErrRet = OTA_ERR_UNINITIALIZED;

    MQTTStatus_t mqttStatus = MQTTBadParameter;
    MQTTPublishInfo_t publishInfo;
    MQTTContext_t * pMqttContext = &mqttContext;

    publishInfo.pTopicName = pacTopic;
    publishInfo.topicNameLength = topicLen;
    publishInfo.qos = qos;
    publishInfo.pPayload = pMsg;
    publishInfo.payloadLength = msgSize;

    mqttStatus = MQTT_Publish( pMqttContext,
                               &publishInfo,
                               MQTT_GetPacketId( pMqttContext ) );

    if( mqttStatus == MQTTSuccess )
    {
        /* Wait for the publish to complete. */
        mqttStatus = MQTT_ProcessLoop( pMqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );

        if( mqttStatus != MQTTSuccess )
        {
            LogError( ( " Publish ack wait failed with error = %u.", mqttStatus ) );

            otaErrRet = OTA_ERR_PUBLISH_FAILED;
        }
        else
        {
            LogInfo( ( " Publish success.\n\r" ) );

            otaErrRet = OTA_ERR_NONE;
        }
    }
    else
    {
        LogError( ( "Failed to send PUBLISH packet to broker with error = %u.", mqttStatus ) );

        otaErrRet = OTA_ERR_PUBLISH_FAILED;
    }

    return otaErrRet;
}

static OtaErr_t mqttUnsubscribe( const char * pTopicFilter,
                                 uint16_t topicFilterLength,
                                 uint8_t qos )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;

    MQTTSubscribeInfo_t pSubscriptionList[ 1 ];

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* This example subscribes to and unsubscribes from only one topic
     * and uses QOS1. */
    pSubscriptionList[ 0 ].qos = qos;
    pSubscriptionList[ 0 ].pTopicFilter = pTopicFilter;
    pSubscriptionList[ 0 ].topicFilterLength = topicFilterLength;

    /* Send UNSUBSCRIBE packet. */
    mqttStatus = MQTT_Unsubscribe( &mqttContext,
                                   pSubscriptionList,
                                   sizeof( pSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                   MQTT_GetPacketId( &mqttContext ) );

    if( mqttStatus != MQTTSuccess )
    {
        LogError( ( "Failed to send UNSUBSCRIBE packet to broker with error = %s.",
                    MQTT_Status_strerror( mqttStatus ) ) );
        returnStatus = EXIT_FAILURE;
    }
    else
    {
        /* Process Incoming UNSUBACK packet from the broker. */
        mqttStatus = MQTT_ProcessLoop( &mqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );

        if( mqttStatus != MQTTSuccess )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "MQTT_ProcessLoop returned with status = %s.",
                        MQTT_Status_strerror( mqttStatus ) ) );
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int establishMqttSession( MQTTContext_t * pMqttContext,
                                 bool createCleanSession,
                                 bool * pSessionPresent )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    MQTTConnectInfo_t connectInfo = { 0 };

    assert( pMqttContext != NULL );
    assert( pSessionPresent != NULL );

    /* Establish MQTT session by sending a CONNECT packet. */

    /* If #createCleanSession is true, start with a clean session
     * i.e. direct the MQTT broker to discard any previous session data.
     * If #createCleanSession is false, directs the broker to attempt to
     * reestablish a session which was already present. */
    connectInfo.cleanSession = createCleanSession;

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
     * https://docs.aws.amazon.com/iot/latest/developerguide/enhanced-custom-authentication.html
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

    /* Send MQTT CONNECT packet to broker. */
    mqttStatus = MQTT_Connect( pMqttContext, &connectInfo, NULL, CONNACK_RECV_TIMEOUT_MS, pSessionPresent );

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

static int initializeMqtt( MQTTContext_t * pMqttContext,
                           NetworkContext_t * pNetworkContext )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    MQTTFixedBuffer_t networkBuffer;
    TransportInterface_t transport;

    assert( pMqttContext != NULL );
    assert( pNetworkContext != NULL );

    /* Fill in TransportInterface send and receive function pointers.
     * For this demo, TCP sockets are used to send and receive data
     * from network. Network context is SSL context for OpenSSL.*/
    transport.pNetworkContext = pNetworkContext;
    transport.send = Openssl_Send;
    transport.recv = Openssl_Recv;

    /* Fill the values for network buffer. */
    networkBuffer.pBuffer = buffer;
    networkBuffer.size = NETWORK_BUFFER_SIZE;

    /* Initialize MQTT library. */
    mqttStatus = MQTT_Init( pMqttContext,
                            &transport,
                            Clock_GetTimeMs,
                            mqttEventCallback,
                            &networkBuffer );

    if( mqttStatus != MQTTSuccess )
    {
        returnStatus = EXIT_FAILURE;
        LogError( ( "MQTT init failed: Status = %s.", MQTT_Status_strerror( mqttStatus ) ) );
    }

    return returnStatus;
}

static int32_t connectToServer( NetworkContext_t * pNetworkContext,
                                char * pUrl )
{
    int32_t returnStatus = EXIT_FAILURE;
    HTTPStatus_t httpStatus = HTTPSuccess;

    /* The location of the host address within the pre-signed URL. */
    const char * pAddress = NULL;

    /* Status returned by OpenSSL transport implementation. */
    OpensslStatus_t opensslStatus;
    /* Credentials to establish the TLS connection. */
    OpensslCredentials_t opensslCredentials;
    /* Information about the server to send the HTTP requests. */
    ServerInfo_t serverInfo;

    /* Initialize TLS credentials. */
    ( void ) memset( &opensslCredentials, 0, sizeof( opensslCredentials ) );
    opensslCredentials.pRootCaPath = ROOT_CA_CERT_PATH_HTTP;

    /* Retrieve the address location and length from S3_PRESIGNED_GET_URL. */
    getUrlAddress( pUrl,
                   strlen( pUrl ),
                   &UrlInfo.pAddress,
                   &UrlInfo.addressLength );

    if( 1 /* returnStatus == EXIT_SUCCESS */ )
    {
        /* serverHost should consist only of the host address located in
         * S3_PRESIGNED_GET_URL. */
        memcpy( serverHost, UrlInfo.pAddress, UrlInfo.addressLength );
        serverHost[ UrlInfo.addressLength ] = '\0';

        /* Initialize server information. */
        serverInfo.pHostName = serverHost;
        serverInfo.hostNameLength = UrlInfo.addressLength;
        serverInfo.port = AWS_HTTPS_PORT;

        /* Establish a TLS session with the HTTP server. This example connects
         * to the HTTP server as specified in SERVER_HOST and HTTPS_PORT in
         * demo_config.h. */
        LogInfo( ( "Establishing a TLS session with %s:%d.",
                   serverHost,
                   AWS_HTTPS_PORT ) );

        opensslStatus = Openssl_Connect( pNetworkContext,
                                         &serverInfo,
                                         &opensslCredentials,
                                         TRANSPORT_SEND_RECV_TIMEOUT_MS,
                                         TRANSPORT_SEND_RECV_TIMEOUT_MS );

        returnStatus = ( opensslStatus == OPENSSL_SUCCESS ) ? EXIT_SUCCESS : EXIT_FAILURE;
    }

    return returnStatus;
}

static OtaErr_t httpInit( const char * pUrl )
{
    /* OTA lib return error code. */
    OtaErr_t ret = OTA_ERR_UNINITIALIZED;

    /* Return value from libs. */
    int32_t returnStatus = EXIT_SUCCESS;

    /* Establish HTTPs connection */
    LogInfo( ( "Performing TLS handshake on top of the TCP connection." ) );

    /* Attempt to connect to the HTTPs server. If connection fails, retry after
     * a timeout. Timeout value will be exponentially increased till the maximum
     * attempts are reached or maximum timeout value is reached. The function
     * returns EXIT_FAILURE if the TCP connection cannot be established to
     * broker after configured number of attempts. */
    returnStatus = connectToServer( &networkContextHttp, pUrl );

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Define the transport interface. */
        ( void ) memset( &transportInterfaceHttp, 0, sizeof( transportInterfaceHttp ) );
        transportInterfaceHttp.recv = Openssl_Recv;
        transportInterfaceHttp.send = Openssl_Send;
        transportInterfaceHttp.pNetworkContext = &networkContextHttp;

        getUrlPath( pUrl, strlen( pUrl ), &UrlInfo.pPath,
                    &UrlInfo.pathLength );

        ret = OTA_ERR_NONE;
    }
    else
    {
        /* Log an error to indicate connection failure after all
         * reconnect attempts are over. */
        LogError( ( "Failed to connect to HTTP server %s.",
                    serverHost ) );

        ret = OTA_ERR_HTTP_INIT_FAILED;
    }

    return ret;
}

static OtaErr_t httpRequest( uint32_t rangeStart,
                             uint32_t rangeEnd )
{
    /* Return value of this method. */
    int32_t returnStatus = EXIT_SUCCESS;

    /* OTA lib return error code. */
    OtaErr_t ret = OTA_ERR_UNINITIALIZED;

    static uint8_t url[ 34 ];

    OtaEventData_t * pData;
    OtaEventMsg_t eventMsg = { 0 };

    /* Configurations of the initial request headers that are passed to
     * #HTTPClient_InitializeRequestHeaders. */
    HTTPRequestInfo_t requestInfo;
    /* Represents a response returned from an HTTP server. */
    HTTPResponse_t response;
    /* Represents header data that will be sent in an HTTP request. */
    HTTPRequestHeaders_t requestHeaders;

    /* Return value of all methods from the HTTP Client library API. */
    HTTPStatus_t httpStatus = HTTPSuccess;

    /* Initialize all HTTP Client library API structs to 0. */
    ( void ) memset( &requestInfo, 0, sizeof( requestInfo ) );
    ( void ) memset( &response, 0, sizeof( response ) );
    ( void ) memset( &requestHeaders, 0, sizeof( requestHeaders ) );

    /* Initialize the request object. */
    requestInfo.pHost = serverHost;
    requestInfo.hostLen = UrlInfo.addressLength;
    requestInfo.pMethod = HTTP_METHOD_GET;
    requestInfo.methodLen = sizeof( HTTP_METHOD_GET ) - 1;
    requestInfo.pPath = UrlInfo.pPath;
    requestInfo.pathLen = UrlInfo.pathLength;



    /* Set "Connection" HTTP header to "keep-alive" so that multiple requests
     * can be sent over the same established TCP connection. */
    requestInfo.reqFlags = HTTP_REQUEST_KEEP_ALIVE_FLAG;

    /* Set the buffer used for storing request headers. */
    requestHeaders.pBuffer = userBuffer;
    requestHeaders.bufferLen = USER_BUFFER_LENGTH;

    httpStatus = HTTPClient_InitializeRequestHeaders( &requestHeaders,
                                                      &requestInfo );

    HTTPClient_AddRangeHeader( &requestHeaders, rangeStart, rangeEnd );

    if( httpStatus == HTTPSuccess )
    {
        /* Initialize the response object. The same buffer used for storing
         * request headers is reused here. */
        response.pBuffer = userBuffer;
        response.bufferLen = USER_BUFFER_LENGTH;

        /* Send the request and receive the response. */
        httpStatus = HTTPClient_Send( &transportInterfaceHttp,
                                      &requestHeaders,
                                      NULL,
                                      0,
                                      &response,
                                      0 );
    }
    else
    {
        LogError( ( "Failed to initialize HTTP request headers: Error=%s.",
                    HTTPClient_strerror( httpStatus ) ) );
    }

    if( httpStatus != HTTPSuccess )
    {
        returnStatus = EXIT_FAILURE;

        ret = OTA_ERR_HTTP_REQUEST_FAILED;
    }
    else
    {
        pData = otaEventBufferGet();

        /* Get the data from response buffer. */
        memcpy( pData->data, response.pBody, response.bodyLen );
        pData->dataLength = response.bodyLen;

        /* Send job document received event. */
        eventMsg.eventId = OtaAgentEventReceivedFileBlock;
        eventMsg.pEventData = pData;
        OTA_SignalEvent( &eventMsg );

        ret = OTA_ERR_NONE;
    }

    return returnStatus;
}

static OtaErr_t httpDeinit( void )
{
    int32_t returnStatus = EXIT_SUCCESS;

    OtaErr_t ret = OTA_ERR_UNINITIALIZED;

    /* Disconnect.*/
    returnStatus = Openssl_Disconnect( &networkContextHttp );

    if( returnStatus == OPENSSL_SUCCESS )
    {
        ret = OTA_ERR_NONE;
    }
    else
    {
        ret = OTA_ERR_HTTP_REQUEST_FAILED;
    }

    return ret;
}

static void setOtaInterface( OtaInterfaces_t * pOtaInterfaces )
{
    /* Initialize OTA library OS Interface. */
    pOtaInterfaces->os.event.init = Posix_OtaInitEvent;
    pOtaInterfaces->os.event.send = Posix_OtaSendEvent;
    pOtaInterfaces->os.event.recv = Posix_OtaReceiveEvent;
    pOtaInterfaces->os.event.deinit = Posix_OtaDeinitEvent;

    /* Intialize the OTA library MQTT Interface.*/
    pOtaInterfaces->mqtt.subscribe = mqttSubscribe;
    pOtaInterfaces->mqtt.publish = mqttPublish;
    pOtaInterfaces->mqtt.unsubscribe = mqttUnsubscribe;
    pOtaInterfaces->mqtt.jobCallback = mqttJobCallback;
    pOtaInterfaces->mqtt.dataCallback = mqttDataCallback;

    /* Intialize the OTA library HTTP Interface.*/
    pOtaInterfaces->http.init = httpInit;
    pOtaInterfaces->http.request = httpRequest;
    pOtaInterfaces->http.deinit = httpDeinit;

    /* Intialize the OTA library PAL Interface.*/
    pOtaInterfaces->pal.getPlatformImageState = prvPAL_GetPlatformImageState;
    pOtaInterfaces->pal.setPlatformImageState = prvPAL_SetPlatformImageState;
    pOtaInterfaces->pal.writeBlock = prvPAL_WriteBlock;
    pOtaInterfaces->pal.activateNewImage = prvPAL_ActivateNewImage;
    pOtaInterfaces->pal.closeFile = prvPAL_CloseFile;
    pOtaInterfaces->pal.resetDevice = prvPAL_ResetDevice;
    pOtaInterfaces->pal.abortUpdate = prvPAL_Abort;
}

/*-----------------------------------------------------------*/

void startOTADemo( MQTTContext_t * pMqttContext )
{
    /* Status indicating a successful demo or not. */
    int32_t returnStatus = EXIT_SUCCESS;

    /* coreMQTT library return status. */
    MQTTStatus_t mqttStatus = MQTTSuccess;

    /* OTA Agent state returned from calling OTA_GetAgentState.*/
    OtaState_t state = OtaAgentStateStopped; /*ToDo OtaState_t add agent? */

    /* OTA Aevent message used for sending event to OTA Agent.*/
    OtaEventMsg_t eventMsg = { 0 };

    /* OTA Agent thread handle.*/
    pthread_t threadHandle;

    /* OTA interface context required for library interface functions.*/
    OtaInterfaces_t otaInterfaces;

    /* Set OTA Library interfaces.*/
    setOtaInterface( &otaInterfaces );

    /* Initialize the OTA Agent , if it is resuming the OTA statistics will be cleared for new
     * connection.*/
    OTA_AgentInit( &otaBuffer,
                   &otaInterfaces,
                   ( const uint8_t * ) ( CLIENT_IDENTIFIER ),
                   otaAppCallback );

    sleep( OTA_DEMO_TASK_DELAY_SECONDS );

    /* Create the OTA Agent thread with default attributes.*/
    pthread_create( &threadHandle, NULL, otaAgentTask, NULL );

    /* Send start event to OTA Agent.*/
    eventMsg.eventId = OtaAgentEventStart;
    OTA_SignalEvent( &eventMsg );

    /* Wait forever for OTA traffic but allow other tasks to run and output statistics only once
     * per second. */
    while( ( ( state = OTA_GetAgentState() ) != OtaAgentStateStopped ) )
    {
        sleep( OTA_DEMO_TASK_DELAY_SECONDS );

        LogInfo( ( " Received: %u   Queued: %u   Processed: %u   Dropped: %u",
                   OTA_GetPacketsReceived(),
                   OTA_GetPacketsQueued(),
                   OTA_GetPacketsProcessed(),
                   OTA_GetPacketsDropped() ) );

        if( state == OtaAgentStateWaitingForJob )
        {
            mqttStatus = MQTT_ProcessLoop( pMqttContext, 1000 );

            if( mqttStatus != MQTTSuccess )
            {
                LogError( ( "MQTT_ProcessLoop returned with status = %u.",
                            mqttStatus ) );
            }
        }
        else
        {
            sleep( OTA_DEMO_TASK_DELAY_SECONDS );
        }
    }
}

/*-----------------------------------------------------------*/

/**
 * @brief Entry point of demo.
 *
 * The example shown below uses OTA Library APIs to receive and update the
 * firmare Over-the-Air.
 *
 * The example uses MQTT connection for communicting with AWS IoT OTA service
 * using QoS 1. The update file is downloaded over HTTP using the S3 pre-signed
 * url received over the MQTT connection.
 *
 * ToDo : Improve this comment and code.
 */
int main( int argc,
          char ** argv )
{
    ( void ) argc;
    ( void ) argv;

    /* Return error status. */
    int32_t returnStatus = EXIT_SUCCESS;

    /* Network context required for network interface functions.*/
    NetworkContext_t networkContext = { 0 };

    /* Flag to indicate that an MQTT client session is saved.*/
    bool clientSessionPresent = false;

    LogInfo( ( "OTA over HTTP demo, Application version %u.%u.%u",
               appFirmwareVersion.u.x.major,
               appFirmwareVersion.u.x.minor,
               appFirmwareVersion.u.x.build ) );

    /* Initialize MQTT library. Initialization of the MQTT library needs to be
     * done only once in this demo. */
    returnStatus = initializeMqtt( &mqttContext, &networkContext );

    if( returnStatus == EXIT_SUCCESS )
    {
        for( ; ; )
        {
            /* Attempt to connect to the MQTT broker. If connection fails, retry after
             * a timeout. Timeout value will be exponentially increased till the maximum
             * attempts are reached or maximum timeout value is reached. The function
             * returns EXIT_FAILURE if the TCP connection cannot be established to
             * broker after configured number of attempts. */
            returnStatus = connectToServerWithBackoffRetries( &networkContext );

            if( returnStatus == EXIT_FAILURE )
            {
                /* Log error to indicate connection failure after all
                 * reconnect attempts are over. */
                LogError( ( "Failed to connect to MQTT broker %.*s.",
                            AWS_IOT_ENDPOINT_LENGTH,
                            AWS_IOT_ENDPOINT ) );
            }
            else
            {
                /* Sends an MQTT Connect packet to establish a clean connection over the
                 * established TLS session, then waits for connection acknowledgment
                 * (CONNACK) packet. */
                if( EXIT_SUCCESS == establishMqttSession( &mqttContext,
                                                          true, /* clean session */
                                                          &clientSessionPresent ) )
                {
                    mqttSessionEstablished = true;
                }
            }

            if( mqttSessionEstablished )
            {
                /* If TLS session is established, start the OTA agent. */
                startOTADemo( &mqttContext );
            }
        }
    }

    return returnStatus;
}

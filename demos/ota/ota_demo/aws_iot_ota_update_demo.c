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
 * @file aws_iot_ota_update_demo.c
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

/* Clock for timer. */
#include "clock.h"

/* MQTT include. */
#include "core_mqtt.h"
#include "mqtt_subscription_manager.h"

/* OTA Library include. */
#include "aws_iot_ota_agent.h"
#include "aws_ota_agent_config.h"
#include "aws_iot_ota_agent_private.h"

/* OTA Library Interface include. */
#include "ota_os_posix.h"
#include "ota_mqtt_interface.h"

/* Include firmware version struct definition. */
#include "iot_appversion32.h"

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
#define OTA_PRESIGNED_URL_MAX_SIZE   ( 1500U )
#define OTA_MQTT_HEADER_MAX_SIZE     ( 30U )
#define NETWORK_BUFFER_SIZE          ( ( 1U << otaconfigLOG2_FILE_BLOCK_SIZE ) + \
                                       OTA_PRESIGNED_URL_MAX_SIZE + \
                                       OTA_MQTT_HEADER_MAX_SIZE )

/**
 * @brief The delay used in the main OTA Demo task loop to periodically output the OTA
 * statistics like number of packets received, dropped, processed and queued per connection.
 */
#define OTA_DEMO_TASK_DELAY_SECONDS         ( 1U )

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
static uint8_t buffer[ NETWORK_BUFFER_SIZE ];

/**
 * @brief Keep a flag for indicating if the MQTT connection is alive.
 */
static bool mqttSessionEstablished = false;

/**
 * @brief MQTT connection context used in this demo.
 */
static MQTTContext_t globalMqttContext;

/*-----------------------------------------------------------*/

/*
 * Publish a message to the specified client/topic at the given QOS.
 */
 static OtaErr_t publish( const char * const pacTopic,
                          uint16_t topicLen,
                          const char * pMsg,
                          uint32_t msgSize,
                          uint8_t qos );


static OtaErr_t subscribe( const char * pTopicFilter,
                           uint16_t topicFilterLength,
                           uint8_t qos,
                           void * pCallback );

static OtaErr_t unsubscribe( const char * pTopicFilter,
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
static void App_OTACompleteCallback( OtaJobEvent_t event )
{
    OtaErr_t err = OTA_ERR_UNINITIALIZED;

    /* OTA job is completed. so delete the MQTT and network connection. */
    if( event == OtaJobEventActivate )
    {
        LogInfo( ( "Received OtaJobEventActivate callback from OTA Agent." ) );

        /* OTA job is completed. so delete the network connection. */
        MQTT_Disconnect( &globalMqttContext );

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

static void jobCallback( MQTTContext_t * pContext, MQTTPublishInfo_t * pPublishInfo )
{
    assert( pPublishInfo != NULL );
    assert( pContext != NULL );

    OtaEventData_t * pData;
    OtaEventMsg_t eventMsg = { 0 };

    LogInfo( ( "Received job message callback, size %d.\n\n", pPublishInfo->payloadLength ) );

    pData = otaEventBufferGet();


        if( pData != NULL )
        {
            memcpy( pData->data, pPublishInfo->pPayload, pPublishInfo->payloadLength );
            pData->dataLength = pPublishInfo->payloadLength ;
            eventMsg.eventId = OtaAgentEventReceivedJobDocument;
            eventMsg.pEventData = pData;

            /* Send job document received event. */
            OTA_SignalEvent( &eventMsg );
        }
        else
        {
            OTA_LOG_L1( "Error: No OTA data buffers available.\r\n" );
        }

}

/*-----------------------------------------------------------*/

static void dataCallback( MQTTContext_t * pContext, MQTTPublishInfo_t * pPublishInfo )
{
    assert( pPublishInfo != NULL );
    assert( pContext != NULL );

    OtaEventData_t * pData;
    OtaEventMsg_t eventMsg = { 0 };

    LogInfo( ( "Received data message callback, size %d.\n\n", pPublishInfo->payloadLength ) );

    pData = otaEventBufferGet();

        if( pData != NULL )
        {
            memcpy( pData->data, pPublishInfo->pPayload, pPublishInfo->payloadLength );
            pData->dataLength = pPublishInfo->payloadLength ;
            eventMsg.eventId = OtaAgentEventReceivedFileBlock;
            eventMsg.pEventData = pData;

            /* Send job document received event. */
            OTA_SignalEvent( &eventMsg );
        }
        else
        {
            OTA_LOG_L1( "Error: No OTA data buffers available.\r\n" );
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
   // assert( pDeserializedInfo->packetIdentifier != MQTT_PACKET_ID_INVALID );

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
                // TODO, handle suback for OTA.
                break;

            case MQTT_PACKET_TYPE_UNSUBACK:
                LogInfo( ( "Received UNSUBACK.\n\n" ) );
                // TODO, handle ubsuback for OTA.
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

static int establishMqttSession( MQTTContext_t * pMqttContext,
                                 NetworkContext_t * pNetworkContext,
                                 bool createCleanSession,
                                 bool * pSessionPresent )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    MQTTConnectInfo_t connectInfo;
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
        LogError( ( "MQTT init failed with status %s.", MQTT_Status_strerror( mqttStatus ) ) );
    }
    else
    {
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

        /* Username and password for authentication. Not used in this demo. */
        connectInfo.pUserName = NULL;
        connectInfo.userNameLength = 0U;
        connectInfo.pPassword = NULL;
        connectInfo.passwordLength = 0U;

        /* Send MQTT CONNECT packet to broker. */
        mqttStatus = MQTT_Connect( pMqttContext, &connectInfo, NULL, CONNACK_RECV_TIMEOUT_MS, pSessionPresent );

        if( mqttStatus != MQTTSuccess )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "Connection with MQTT broker failed with status %u.", mqttStatus ) );
        }
        else
        {
            LogInfo( ( "MQTT connection successfully established with broker.\n\n" ) );
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static OtaErr_t subscribe( const char * pTopicFilter,
                           uint16_t topicFilterLength,
                           uint8_t qos,
                           void * pCallback )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    MQTTContext_t * pMqttContext = &globalMqttContext;
    MQTTSubscribeInfo_t pSubscriptionList[ 1 ];

    assert( pMqttContext != NULL );
    assert( pTopicFilter != NULL );
    assert( topicFilterLength > 0 );

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* This example subscribes to only one topic and uses QOS1. */
    pSubscriptionList[ 0 ].qos = qos;
    pSubscriptionList[ 0 ].pTopicFilter = pTopicFilter;
    pSubscriptionList[ 0 ].topicFilterLength = topicFilterLength;

    /* Send SUBSCRIBE packet. */
    mqttStatus = MQTT_Subscribe( pMqttContext,
                                 pSubscriptionList,
                                 sizeof( pSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                 MQTT_GetPacketId( pMqttContext ) );

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
                   pTopicFilter) );

        /* Process incoming packet from the broker. Acknowledgment for subscription
         * ( SUBACK ) will be received here. However after sending the subscribe, the
         * client may receive a publish before it receives a subscribe ack. Since this
         * demo is subscribing to the topic to which no one is publishing, probability
         * of receiving publish message before subscribe ack is zero; but application
         * must be ready to receive any packet. This demo uses MQTT_ProcessLoop to
         * receive packet from network. */
        mqttStatus = MQTT_ProcessLoop( pMqttContext, 1000 );

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
 static OtaErr_t publish( const char * const pacTopic,
                          uint16_t topicLen,
                          const char * pMsg,
                          uint32_t msgSize,
                          uint8_t qos )
{
    OtaErr_t otaErrRet = OTA_ERR_UNINITIALIZED;

    MQTTStatus_t mqttStatus = MQTTBadParameter;
    MQTTPublishInfo_t publishInfo;
    MQTTContext_t * pMqttContext = &globalMqttContext;

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

static OtaErr_t unsubscribe( const char * pTopicFilter,
                             uint16_t topicFilterLength,
                             uint8_t qos )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;

    MQTTSubscribeInfo_t pSubscriptionList[ 1 ];
    MQTTContext_t * pMqttContext = &globalMqttContext;

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* This example subscribes to and unsubscribes from only one topic
     * and uses QOS1. */
    pSubscriptionList[ 0 ].qos = qos;
    pSubscriptionList[ 0 ].pTopicFilter = pTopicFilter;
    pSubscriptionList[ 0 ].topicFilterLength = topicFilterLength;

    /* Send UNSUBSCRIBE packet. */
    mqttStatus = MQTT_Unsubscribe( pMqttContext,
                                   pSubscriptionList,
                                   sizeof( pSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                    MQTT_GetPacketId( pMqttContext ) );

    if( mqttStatus != MQTTSuccess )
    {
        LogError( ( "Failed to send UNSUBSCRIBE packet to broker with error = %s.",
                    MQTT_Status_strerror( mqttStatus ) ) );
        returnStatus = EXIT_FAILURE;
    }
    else
    {
        /* Process Incoming UNSUBACK packet from the broker. */
        mqttStatus = MQTT_ProcessLoop( pMqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );

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

void startOTADemo( MQTTContext_t * pMqttContext )
{
    int ret = 0;
    MQTTStatus_t mqttStatus;
    OtaEventMsg_t eventMsg = { 0 };

    /* MQTT susbsrciption manager parameters.*/
    SubscriptionManagerStatus_t mqttManagerStatus = 0u;
    MQTTSubscribeInfo_t subscriptionInfo;
    uint16_t topicLen = 0;
    size_t subscriptionCount = 1;

    /* OTA Agent state.*/
    OtaState_t state = OtaAgentStateStopped;

    /* OTA Agent thread handle. */
    pthread_t threadHandle;

    /* Initialize OTA library OS Interface. */
	static OtaOSInterface_t otaOSInterface;
    otaOSInterface.event.init = ota_InitEvent;
	otaOSInterface.event.send = ota_SendEvent;
	otaOSInterface.event.recv = ota_ReceiveEvent;
	otaOSInterface.event.deinit = ota_DeinitEvent;

    /* Intialize the OTA library MQTT Interface.*/
    static OtaMqttInterface_t otaMqttInterface;
    otaMqttInterface.subscribe = subscribe;
    otaMqttInterface.publish = publish;
    otaMqttInterface.unsubscribe = unsubscribe;
    otaMqttInterface.jobCallback = jobCallback;
    otaMqttInterface.dataCallback= dataCallback;

    /* Initialize the OTA Agent , if it is resuming the OTA statistics will be cleared for new
     * connection.*/
    OTA_AgentInit( ( void * ) ( pMqttContext ),
                    &otaOSInterface,
                    &otaMqttInterface,
                    ( const uint8_t * ) ( CLIENT_IDENTIFIER ),
                    App_OTACompleteCallback,
                    ( uint32_t ) ~0 );

    sleep( OTA_DEMO_TASK_DELAY_SECONDS );

    /* Create the OTA Agent thread with default attributes.*/
	pthread_create( &threadHandle, NULL, otaAgentTask, NULL );

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
                   
       if(state == OtaAgentStateWaitingForJob )
       {
            mqttStatus = MQTT_ProcessLoop( pMqttContext, 1000 );

            if( mqttStatus != MQTTSuccess )
            {
                LogError( ( "MQTT_ProcessLoop returned with status = %u.",
                        mqttStatus ) );
            }
       }
     
    }

}

/*-----------------------------------------------------------*/

/**
 * @brief Entry point of demo.
 *
 * This example initializes the OTA agent to enable OTA updates via the
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

    int returnStatus = EXIT_SUCCESS;
    NetworkContext_t networkContext;
    bool mqttSessionPresent = false;

    LogInfo( ( "OTA over MQTT demo version %u.%u.%u",
               appFirmwareVersion.u.x.major,
               appFirmwareVersion.u.x.minor,
               appFirmwareVersion.u.x.build ) );

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
            if( EXIT_SUCCESS == establishMqttSession( &globalMqttContext,
                                                      &networkContext,
                                                      true, /* clean session */
                                                      &mqttSessionPresent ) )
            {
                mqttSessionEstablished = true;
            }

        }

        if( mqttSessionEstablished )
        {
            /* If TLS session is established, start the OTA agent. */
            startOTADemo( &globalMqttContext );
        }
    }

    return returnStatus;
}

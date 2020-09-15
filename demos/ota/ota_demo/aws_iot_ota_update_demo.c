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

/* Include Demo Config as the first non-system header. */
#include "demo_config.h"

/* OpenSSL sockets transport implementation. */
#include "openssl_posix.h"

/* Reconnect parameters. */
#include "transport_reconnect.h"

/* Clock for timer. */
#include "clock.h"

/* MQTT include. */
#include "mqtt.h"
#include "mqtt_subscription_manager.h"

/* OTA include. */
#include "aws_iot_ota_agent.h"
#include "aws_ota_agent_config.h"
#include "aws_iot_ota_agent_internal.h"

/* Include firmware version struct definition. */
#include "aws_application_version.h"

/* OTA Library Interface includes. */
#include "ota_os_posix.h"
#include "ota_os_interface.h"

/* Evaluates to the length of a constant string defined like 'static const char str[]= "xyz"; */
#define CONST_STRLEN( s )    ( ( ( uint32_t ) sizeof( s ) ) - 1UL )

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

static MQTTContext_t MqttContext;
/**
 * These configuration settings are required to run the mutual auth demo.
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
 * @brief Size of the network buffer to receive the MQTT message.
 *
 * The largest message size is data size from the AWS IoT streaming service, 2000 is reserved for
 * extra headers.
 */
#define NETWORK_BUFFER_SIZE    ( ( 1U << otaconfigLOG2_FILE_BLOCK_SIZE ) + 2000 )

/**
 * @brief The delay used in the main OTA Demo task loop to periodically output the OTA
 * statistics like number of packets received, dropped, processed and queued per connection.
 */
#define OTA_DEMO_TASK_DELAY_SECONDS         ( 1U )

/*-----------------------------------------------------------*/

/**
 * @brief Handle of the MQTT connection used in this demo.
 */
static MQTTContext_t * pMqttContext = NULL;

/**
 * @brief Buffer to receive the MQTT message.
 */
static uint8_t buffer[ NETWORK_BUFFER_SIZE ];

/**
 * @brief Keep a flag for indicating if the MQTT connection is alive.
 */
static bool mqttSessionEstablished = false;

int32_t SubscribeToTopic( const char * pTopicFilter,
                          uint16_t topicFilterLength,
                            MQTTQoS_t eQOS );

static const char pcOTA_JobsGetNext_TopicTemplate[] = "$aws/things/%s/jobs/$next/get";

static MQTTStatus_t prvPublishMessage( 
                                         const char * const pacTopic,
                                         uint16_t usTopicLen,
                                         const char * pcMsg,
                                         uint32_t ulMsgSize,
                                         MQTTQoS_t eQOS );

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

static void otaMessageCallback( MQTTContext_t * pContext, MQTTPublishInfo_t * pPublishInfo )
{
   // static char buff[1024];
    assert( pPublishInfo != NULL );
    assert( pContext != NULL );

    OTA_EventData_t * pxData;
    OTA_EventMsg_t xEventMsg = { 0 };

    /* Suppress unused parameter warning when asserts are disabled in build. */
    ( void ) pContext;


    // TODO, notify OTA agent about the incoming message.

    LogInfo( ( "Received ota message callback.\n\n" ) );

    pxData = prvOTAEventBufferGet();


        if( pxData != NULL )
        {
            memcpy( pxData->ucData, pPublishInfo->pPayload, pPublishInfo->payloadLength );
            pxData->ulDataLength = pPublishInfo->payloadLength ;
            xEventMsg.xEventId = eOTA_AgentEvent_ReceivedJobDocument;
            xEventMsg.pxEventData = pxData;

            /* Send job document received event. */
            OTA_SignalEvent( &xEventMsg );
        }
        else
        {
            OTA_LOG_L1( "Error: No OTA data buffers available.\r\n", OTA_DATA_BLOCK_SIZE );
        }

}

static void otaDataCallback( MQTTContext_t * pContext, MQTTPublishInfo_t * pPublishInfo )
{
      // static char buff[1024];
    assert( pPublishInfo != NULL );
    assert( pContext != NULL );

    OTA_EventData_t * pxData;
    OTA_EventMsg_t xEventMsg = { 0 };

    /* Suppress unused parameter warning when asserts are disabled in build. */
    ( void ) pContext;

   // memcpy( buff, pPublishInfo->pPayload, pPublishInfo->payloadLength );

    // TODO, notify OTA agent about the incoming message.

    LogInfo( ( "Received ota message callback.\n\n" ) );

    pxData = prvOTAEventBufferGet();


        if( pxData != NULL )
        {
            memcpy( pxData->ucData, pPublishInfo->pPayload, pPublishInfo->payloadLength );
            pxData->ulDataLength = pPublishInfo->payloadLength ;
            xEventMsg.xEventId = eOTA_AgentEvent_ReceivedFileBlock;
            xEventMsg.pxEventData = pxData;

            /* Send job document received event. */
            OTA_SignalEvent( &xEventMsg );
        }
        else
        {
            OTA_LOG_L1( "Error: No OTA data buffers available.\r\n", OTA_DATA_BLOCK_SIZE );
        }
}

static int connectToServerWithBackoffRetries( NetworkContext_t * pNetworkContext )
{
    int returnStatus = EXIT_SUCCESS;
    bool retriesArePending = true;
    OpensslStatus_t opensslStatus = OPENSSL_SUCCESS;
    TransportReconnectParams_t reconnectParams;
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
    Transport_ReconnectParamsReset( &reconnectParams );

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
            retriesArePending = Transport_ReconnectBackoffAndSleep( &reconnectParams );
        }

        if( retriesArePending == false )
        {
            LogError( ( "Connection to the broker failed, all attempts exhausted." ) );
            returnStatus = EXIT_FAILURE;
        }
    } while( ( opensslStatus != OPENSSL_SUCCESS ) && ( retriesArePending == true ) );

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
 * @param[in] eEvent Specify if this demo is running with the AWS IoT
 * MQTT server. Set this to `false` if using another MQTT server.
 * @return None.
 */
static void App_OTACompleteCallback( OTA_JobEvent_t eEvent )
{
    OTA_Err_t xErr = kOTA_Err_Uninitialized;

    /* OTA job is completed. so delete the MQTT and network connection. */
    if( eEvent == eOTA_JobEvent_Activate )
    {
        LogInfo( ( "Received eOTA_JobEvent_Activate callback from OTA Agent." ) );

        /* OTA job is completed. so delete the network connection. */
        if( pMqttContext != NULL )
        {
            MQTT_Disconnect( pMqttContext );
        }

        /* Activate the new firmware image. */
        OTA_ActivateNewImage();

        /* We should never get here as new image activation must reset the device.*/
        LogError( ( "New image activation failed." ) );

        for( ; ; )
        {
        }
    }
    else if( eEvent == eOTA_JobEvent_Fail )
    {
        LogInfo( ( "Received eOTA_JobEvent_Fail callback from OTA Agent." ) );

        /* Nothing special to do. The OTA agent handles it. */
    }
    else if( eEvent == eOTA_JobEvent_StartTest )
    {
        /* This demo just accepts the image since it was a good OTA update and networking
         * and services are all working (or we wouldn't have made it this far). If this
         * were some custom device that wants to test other things before calling it OK,
         * this would be the place to kick off those tests before calling OTA_SetImageState()
         * with the final result of either accepted or rejected. */

        LogInfo( ( "Received eOTA_JobEvent_StartTest callback from OTA Agent." ) );
        xErr = OTA_SetImageState( eOTA_ImageState_Accepted );

        if( xErr != kOTA_Err_None )
        {
            LogError( ( " Error! Failed to set image state as accepted." ) );
        }
    }
}
static void  prvRequestJob( );
/*-----------------------------------------------------------*/

void startOTAUpdateDemo( MQTTContext_t * pMqttContext )
{
    OTA_State_t eState;
    MQTTStatus_t mqttStatus = MQTTBadParameter;
    SubscriptionManagerStatus_t mqttManagerStatus = 0u;
    uint32_t mqttProcessTimeMs = 0U;
    const char * pTopicFilter = "ota";


     uint16_t usTopicLen = 0;
     static char pcJobTopic[ 256 ];
     static char pcJobTopic2[ 256 ];
     static const char pcOTA_JobsGetNextAccepted_TopicTemplate[] = "$aws/things/%s/jobs/$next/get/accepted";
     static const char pcOTA_JobsNotifyNext_TopicTemplate[] = "$aws/things/%s/jobs/notify-next";
     MQTTSubscribeInfo_t subscriptionInfo;
    size_t subscriptionCount = 1;

    /* OTA OS context. */
	OtaEventContext_t EventCtx ;

	/* Initialize OTA OS interface. */
	OtaOsInterface_t OtaOSInterface;

    OtaOSInterface.event.init = ota_InitEvent;
	OtaOSInterface.event.send = ota_SendEvent;
	OtaOSInterface.event.recv = ota_ReceiveEvent;
	OtaOSInterface.event.deinit = ota_DeinitEvent;
	OtaOSInterface.event.pEventCtx = &EventCtx;

    //subscribe to the OTA topics
    /* Build the first topic. */
    usTopicLen = ( uint16_t ) snprintf( pcJobTopic,
                                        sizeof( pcJobTopic ),
                                        pcOTA_JobsGetNextAccepted_TopicTemplate,
                                        ( const uint8_t * ) CLIENT_IDENTIFIER );

    
    SubscribeToTopic(pcJobTopic, usTopicLen,MQTTQoS1 );
    
    SubscriptionManager_RegisterCallback( pcJobTopic,
                                          usTopicLen,
                                          otaMessageCallback );

    
    
    usTopicLen = ( uint16_t ) snprintf( pcJobTopic2,
                                        sizeof( pcJobTopic2 ),
                                        pcOTA_JobsNotifyNext_TopicTemplate,
                                        ( const uint8_t * ) ( CLIENT_IDENTIFIER ) );

    SubscribeToTopic(pcJobTopic2, usTopicLen,  MQTTQoS1);

  SubscriptionManager_RegisterCallback( pcJobTopic2,
                                        usTopicLen,
                                        otaMessageCallback );

    


    /* Initialize the OTA Agent , if it is resuming the OTA statistics will be cleared for new
     * connection.*/
    OTA_AgentInit( ( void * ) ( pMqttContext ),
                    &OtaOSInterface,
                   ( const uint8_t * ) ( CLIENT_IDENTIFIER ),
                   App_OTACompleteCallback,
                   ( uint32_t ) ~0 );

       sleep( 2);         

      prvRequestJob ();

    /* Wait forever for OTA traffic but allow other tasks to run and output statistics only once
     * per second. */
    while( ( ( eState = OTA_GetAgentState() ) != eOTA_AgentState_Stopped ) )
    {

        LogInfo( ( " Received: %u   Queued: %u   Processed: %u   Dropped: %u",
                   //OTA_GetAgentState(),
                   OTA_GetPacketsReceived(),
                   OTA_GetPacketsQueued(),
                   OTA_GetPacketsProcessed(),
                   OTA_GetPacketsDropped() ) );

        sleep( OTA_DEMO_TASK_DELAY_SECONDS );
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
    int returnStatus = EXIT_SUCCESS;
    NetworkContext_t networkContext;
    
    bool mqttSessionPresent = false;

    ( void ) argc;
    ( void ) argv;

    LogInfo( ( "OTA demo version %u.%u.%u",
               xAppFirmwareVersion.u.x.ucMajor,
               xAppFirmwareVersion.u.x.ucMinor,
               xAppFirmwareVersion.u.x.usBuild ) );

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
            if( EXIT_SUCCESS == establishMqttSession( &MqttContext,
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
            startOTAUpdateDemo( &MqttContext );
        }
    }

    return returnStatus;
}


int32_t SubscribeToTopic( const char * pTopicFilter,
                          uint16_t topicFilterLength,
                           MQTTQoS_t eQOS )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    MQTTContext_t * pMqttContext = &MqttContext;
    MQTTSubscribeInfo_t pSubscriptionList[ 1 ];



    assert( pMqttContext != NULL );
    assert( pTopicFilter != NULL );
    assert( topicFilterLength > 0 );

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* This example subscribes to only one topic and uses QOS1. */
    pSubscriptionList[ 0 ].qos = eQOS;
    pSubscriptionList[ 0 ].pTopicFilter = pTopicFilter;
    pSubscriptionList[ 0 ].topicFilterLength = topicFilterLength;

    /* Generate packet identifier for the SUBSCRIBE packet. */
   // globalSubscribePacketIdentifier = MQTT_GetPacketId( pMqttContext );

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

                  // sleep (3 );

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

    return returnStatus;
}

static void  prvRequestJob( )
{
    static char pcJobTopic[ 256 ];
    static uint32_t ulReqCounter = 0;
    MQTTStatus_t eResult;
    uint32_t ulMsgLen;
    uint16_t usTopicLen;
    OTA_Err_t xError = kOTA_Err_PublishFailed;
    static const char pcOTA_GetNextJob_MsgTemplate[] = "{\"clientToken\":\"%u:%s\"}";

    /* The following buffer is big enough to hold a dynamically constructed $next/get job message.
     * It contains a client token that is used to track how many requests have been made. */
    char pcMsg[ CONST_STRLEN( pcOTA_GetNextJob_MsgTemplate ) + 10U  + otaconfigMAX_THINGNAME_LEN ];

    /* Subscribe to the OTA job notification topic. */

    /*lint -e586 Intentionally using snprintf. */
    ulMsgLen = ( uint32_t ) snprintf( pcMsg,
                                      sizeof( pcMsg ),
                                      pcOTA_GetNextJob_MsgTemplate,
                                      ulReqCounter,
                                      ( const uint8_t * ) ( CLIENT_IDENTIFIER ));

    ulReqCounter++;
    usTopicLen = ( uint16_t ) snprintf( pcJobTopic,
                                        sizeof( pcJobTopic ),
                                        pcOTA_JobsGetNext_TopicTemplate,
                                        ( const uint8_t * ) ( CLIENT_IDENTIFIER ) );

                                        

   SubscriptionManager_RegisterCallback( pcJobTopic,
                                         usTopicLen,
                                         otaMessageCallback );

    if( ( usTopicLen > 0U ) && ( usTopicLen < sizeof( pcJobTopic ) ) )
    {
        prvPublishMessage( pcJobTopic, usTopicLen, pcMsg, ulMsgLen, MQTTQoS1 );

    }

    return kOTA_Err_None;
}

static const char pcOTA_StreamData_TopicTemplate[] = "$aws/things/%s/streams/%s/data/cbor";
static const char pcOTA_GetStream_TopicTemplate[] = "$aws/things/%s/streams/%s/get/cbor";

OTA_Err_t prvInitFileTransfer_Mqtt( OTA_AgentContext_t * pxAgentCtx )
{
    const OTA_FileContext_t * pFileContext = &( pxAgentCtx->pxOTA_Files[ pxAgentCtx->ulFileIndex ] );
    static char pcOTA_RxStreamTopic[ 256 ];
    uint16_t usTopicLen = 0;

    usTopicLen = ( uint16_t ) snprintf( pcOTA_RxStreamTopic,
                                        sizeof( pcOTA_RxStreamTopic ),
                                        pcOTA_StreamData_TopicTemplate,
                                        ( const uint8_t * ) ( CLIENT_IDENTIFIER ) ,
                                        ( const char * ) pFileContext->pucStreamName );


    SubscribeToTopic( pcOTA_RxStreamTopic,usTopicLen , MQTTQoS0);

        SubscriptionManager_RegisterCallback( pcOTA_RxStreamTopic,
                                          usTopicLen,
                                          otaDataCallback );

                                          return 0;

   return 0;
}

#define OTA_CLIENT_TOKEN               "rdy"   

OTA_Err_t prvRequestFileBlock_Mqtt( OTA_AgentContext_t * pxAgentCtx )
{
    DEFINE_OTA_METHOD_NAME( "prvRequestFileBlock_Mqtt" );

    size_t xMsgSizeFromStream;
    uint32_t ulNumBlocks, ulBitmapLen;
    uint32_t ulMsgSizeToPublish = 0;
    uint32_t ulTopicLen = 0;
    MQTTStatus_t mqttStatus = MQTTBadParameter;
    OTA_Err_t xErr = kOTA_Err_Uninitialized;
    char pcMsg[ OTA_REQUEST_MSG_MAX_SIZE ];
    char pcTopicBuffer[ 256 ];

    /*
     * Get the current file context.
     */
    OTA_FileContext_t * C = &( pxAgentCtx->pxOTA_Files[ pxAgentCtx->ulFileIndex ] );

    /* Reset number of blocks requested. */
    pxAgentCtx->ulNumOfBlocksToReceive = otaconfigMAX_NUM_BLOCKS_REQUEST;

    if( C != NULL )
    {
        ulNumBlocks = ( C->ulFileSize + ( OTA_FILE_BLOCK_SIZE - 1U ) ) >> otaconfigLOG2_FILE_BLOCK_SIZE;
        ulBitmapLen = ( ulNumBlocks + ( BITS_PER_BYTE - 1U ) ) >> LOG2_BITS_PER_BYTE;

        if( OTA_CBOR_Encode_GetStreamRequestMessage(
                ( uint8_t * ) pcMsg,
                sizeof( pcMsg ),
                &xMsgSizeFromStream,
                OTA_CLIENT_TOKEN,
                ( int32_t ) C->ulServerFileID,
                ( int32_t ) ( OTA_FILE_BLOCK_SIZE & 0x7fffffffUL ), /* Mask to keep lint happy. It's still a constant. */
                0,
                C->pucRxBlockBitmap,
                ulBitmapLen,
                otaconfigMAX_NUM_BLOCKS_REQUEST ) )
        {
            xErr = kOTA_Err_None;
        }
        else
        {
            OTA_LOG_L1( "[%s] CBOR encode failed.\r\n", OTA_METHOD_NAME );
            xErr = kOTA_Err_FailedToEncodeCBOR;
        }
    }

    if( xErr == kOTA_Err_None )
    {
        ulMsgSizeToPublish = ( uint32_t ) xMsgSizeFromStream;

        /* Try to build the dynamic data REQUEST topic to publish to. */
        ulTopicLen = ( uint32_t ) snprintf( pcTopicBuffer, /*lint -e586 Intentionally using snprintf. */
                                            sizeof( pcTopicBuffer ),
                                            pcOTA_GetStream_TopicTemplate,
                                            pxAgentCtx->pcThingName,
                                            ( const char * ) C->pucStreamName );

        if( ( ulTopicLen > 0U ) && ( ulTopicLen < sizeof( pcTopicBuffer ) ) )
        {
            xErr = kOTA_Err_None;
        }
        else
        {
            /* 0 should never happen since we supply the format strings. It must be overflow. */
            OTA_LOG_L1( "[%s] Failed to build stream topic!\r\n", OTA_METHOD_NAME );
            xErr = kOTA_Err_TopicTooLarge;
        }
    }

       /* Publish the mesage. */
       prvPublishMessage( pcTopicBuffer, ulTopicLen, pcMsg, ulMsgSizeToPublish, MQTTQoS0 );


    return xErr;
}

/*
 * Publish a message to the specified client/topic at the given QOS.
 */
static MQTTStatus_t prvPublishMessage( const char * const pacTopic,
                                       uint16_t usTopicLen,
                                       const char * pcMsg,
                                       uint32_t ulMsgSize,
                                       MQTTQoS_t eQOS )
{
    MQTTStatus_t mqttStatus = MQTTBadParameter;
    MQTTPublishInfo_t publishInfo;
    MQTTContext_t * pMqttContext = &MqttContext;

    publishInfo.pTopicName = pacTopic;
    publishInfo.topicNameLength = usTopicLen;
    publishInfo.qos = eQOS;
    publishInfo.pPayload = pcMsg;
    publishInfo.payloadLength = ulMsgSize;

    mqttStatus = MQTT_Publish( pMqttContext,
                               &publishInfo,
                               MQTT_GetPacketId( pMqttContext ) );

    if( mqttStatus == MQTTSuccess )
    {
        /* Wait for the publish to complete. */
        mqttStatus = MQTT_ProcessLoop( pMqttContext, 1000 );

        if( mqttStatus != MQTTSuccess )
        {
            OTA_LOG_L1( " Publish ack wait failed.\n\r" );
        }
    }
    else
    {
        OTA_LOG_L1( "[%s] Failed to send PUBLISH packet to broker with error = %u.", mqttStatus );
    }

    return mqttStatus;
}


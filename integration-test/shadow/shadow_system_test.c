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
 * @file shadow_system_test.c
 * @brief Integration tests for the SHADOW library via MQTT Library
 * when communicating with AWS IoT from a POSIX platform.
 */

#include <string.h>
#include <stdbool.h>
#include <assert.h>

/* Include config file before other non-system includes. */
#include "test_config.h"

#include "unity.h"

/* SHADOW API header. */
#include "shadow.h"

/* Include paths for public enums, structures, and macros. */
#include "core_mqtt.h"

/* Include OpenSSL implementation of transport interface. */
#include "openssl_posix.h"

/* Include clock for timer. */
#include "clock.h"

/**
 * These configuration settings are required to run the shadow library integration test.
 * Throw compilation error if the below configs are not defined.
 */
#ifndef AWS_IOT_ENDPOINT
    #error "AWS_IOT_ENDPOINT should be defined for the Shadow integration tests."
#endif

#ifndef ROOT_CA_CERT_PATH
    #error "ROOT_CA_CERT_PATH should be defined for the Shadow integration tests."
#endif

#ifndef CLIENT_CERT_PATH
    #error "CLIENT_CERT_PATH should be defined for the Shadow integration tests."
#endif

#ifndef CLIENT_PRIVATE_KEY_PATH
    #error "CLIENT_PRIVATE_KEY_PATH should be defined for the Shadow integration tests."
#endif

#ifndef CLIENT_IDENTIFIER
    #error "CLIENT_IDENTIFIER should be defined for the Shadow integration tests."
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
 * @brief Size of the network buffer for MQTT packets.
 */
#define NETWORK_BUFFER_SIZE                 ( 1024U )

/**
 * @brief Client identifier for MQTT session in the tests.
 */
#define TEST_CLIENT_IDENTIFIER              "SHADOW-SYSTEM-Test"

/**
 * @brief Length of the client identifier.
 */
#define TEST_CLIENT_IDENTIFIER_LENGTH       ( sizeof( TEST_CLIENT_IDENTIFIER ) - 1u )

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS      ( 2000U )

/**
 * @brief Timeout for receiving CONNACK packet in milli seconds.
 */
#define CONNACK_RECV_TIMEOUT_MS             ( 1000U )

/**
 * @brief Time interval in seconds at which an MQTT PINGREQ need to be sent to
 * broker.
 */
#define MQTT_KEEP_ALIVE_INTERVAL_SECONDS    ( 5U )

/**
 * @brief Timeout for MQTT_ProcessLoop() function in milliseconds.
 * The timeout value is appropriately chosen for receiving an incoming
 * PUBLISH message and ack responses for QoS 1 and QoS 2 communications
 * with the broker.
 */
#define MQTT_PROCESS_LOOP_TIMEOUT_MS        ( 1000U )

/**
 * @brief The exampled predefine thing name.
 *
 * This is the example predefine thing name and could be compiled in ROM code.
 */
#define THING_NAME                          "testShadowSystem"

/**
 * @brief The size of #THING_NAME.
 */
#define THING_NAME_LENGTH                   ( ( uint16_t ) ( sizeof( THING_NAME ) - 1 ) )

/**
 * @brief The Shadow document used for update topic desired tests.
 */
#define TEST_SHADOW_DESIRED                 "{\"state\": {\"desired\": {\"key\": true}}, \"clientToken\":\"shadowSystemTest\"}"

/**
 * @brief The length of #TEST_SHADOW_DESIRED.
 */
#define TEST_SHADOW_DESIRED_LENGTH          ( sizeof( TEST_SHADOW_DESIRED ) - 1 )

/**
 * @brief The length of the outgoing publish records array used by the coreMQTT
 * library to track QoS > 0 packet ACKS for outgoing publishes.
 */
#define OUTGOING_PUBLISH_RECORD_LEN         ( 10U )

/**
 * @brief The length of the incoming publish records array used by the coreMQTT
 * library to track QoS > 0 packet ACKS for incoming publishes.
 */
#define INCOMING_PUBLISH_RECORD_LEN         ( 10U )

/*-----------------------------------------------------------*/

/**
 * @brief Packet Identifier generated when Subscribe request was sent to the broker;
 * it is used to match received Subscribe ACK to the transmitted subscribe.
 */
static uint16_t globalSubscribePacketIdentifier = 0U;

/**
 * @brief Packet Identifier generated when Unsubscribe request was sent to the broker;
 * it is used to match received Unsubscribe ACK to the transmitted unsubscribe
 * request.
 */
static uint16_t globalUnsubscribePacketIdentifier = 0U;

/**
 * @brief Packet Identifier generated when Publish request was sent to the broker;
 * it is used to match acknowledgement responses to the transmitted publish
 * request.
 */
static uint16_t globalPublishPacketIdentifier = 0U;

/**
 * @brief Represents the OpenSSL context used for TLS session with the broker
 * for tests.
 */
static NetworkContext_t networkContext;

/**
 * @brief Parameters for the Openssl Context.
 */
static OpensslParams_t opensslParams;

/**
 * @brief Represents the hostname and port of the broker.
 */
static ServerInfo_t serverInfo;

/**
 * @brief TLS credentials needed to connect to the broker.
 */
static OpensslCredentials_t opensslCredentials;

/**
 * @brief The context representing the MQTT connection with the broker for
 * the test case.
 */
static MQTTContext_t context;

/**
 * @brief Flag that represents whether a persistent session was resumed
 * with the broker for the test.
 */
static bool persistentSession = false;

/**
 * @brief Flag to represent whether a SUBACK is received from the broker.
 */
static bool receivedSubAck = false;

/**
 * @brief Flag to represent whether an UNSUBACK is received from the broker.
 */
static bool receivedUnsubAck = false;

/**
 * @brief Flag to represent whether a PUBACK is received from the broker.
 */
static bool receivedPubAck = false;

/**
 * @brief Flag to represent whether a PUBREC is received from the broker.
 */
static bool receivedPubRec = false;

/**
 * @brief Flag to represent whether a PUBREL is received from the broker.
 */
static bool receivedPubRel = false;

/**
 * @brief Flag to represent whether a PUBCOMP is received from the broker.
 */
static bool receivedPubComp = false;

/**
 * @brief Represents incoming PUBLISH information.
 */
static MQTTPublishInfo_t incomingInfo;

/**
 * @brief Flag to represent result from a /update/accepted received from the broker.
 */
static bool receivedUpdateAcceptedResult = false;

/**
 * @brief Flag to represent result from a /update/rejected received from the broker.
 */
static bool receivedUpdateRejectedResult = false;

/**
 * @brief Flag to represent result from a /update/delta sending from the broker.
 */
static bool receivedUpdateDeltaResult = false;

/**
 * @brief Flag to represent result from a /update/documents sending from the broker.
 */
static bool receivedUpdateDocumentsResult = false;

/**
 * @brief Flag to represent result from a /delete/accepted sending from the broker.
 */
static bool receivedDeleteAcceptedResult = false;

/**
 * @brief Flag to represent result from a /delete/rejected sending from the broker.
 */
static bool receivedDeleteRejectedResult = false;

/**
 * @brief Flag to represent result from a /get/accepted is received from the broker.
 */
static bool receivedGetAcceptedResult = false;

/**
 * @brief Flag to represent result from a /get/rejected  is received from the broker.
 */
static bool receivedGetRejectedResult = false;

/**
 * @brief Buffer to hold constructed topic strings
 */
static char topicString[ SHADOW_TOPIC_LEN_MAX( SHADOW_THINGNAME_LENGTH_MAX, SHADOW_NAME_LENGTH_MAX ) ];

/**
 * @brief Buffer to hold the expected shadow name used to filter incoming messages from the broker
 */
static char expectedShadowNameString[ SHADOW_NAME_LENGTH_MAX ];

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

/* Each compilation unit must define the NetworkContext struct. */
struct NetworkContext
{
    OpensslParams_t * pParams;
};

/**
 * @brief Sends an MQTT CONNECT packet over the already connected TCP socket.
 *
 * @param[in] pContext MQTT context pointer.
 * @param[in] pNetworkContext Network context for OpenSSL transport implementation.
 * @param[in] createCleanSession Creates a new MQTT session if true.
 * If false, tries to establish the existing session if there was session
 * already present in broker.
 * @param[out] pSessionPresent Session was already present in the broker or not.
 * Session present response is obtained from the CONNACK from broker.
 */
static void establishMqttSession( MQTTContext_t * pContext,
                                  NetworkContext_t * pNetworkContext,
                                  bool createCleanSession,
                                  bool * pSessionPresent );

/**
 * @brief The application callback function that is expected to be invoked by the
 * MQTT library for incoming publish and incoming acks received over the network.
 *
 * @param[in] pContext MQTT context pointer.
 * @param[in] pPacketInfo Packet Info pointer for the incoming packet.
 * @param[in] pDeserializedInfo Deserialized information from the incoming packet.
 */
static void eventCallback( MQTTContext_t * pContext,
                           MQTTPacketInfo_t * pPacketInfo,
                           MQTTDeserializedInfo_t * pDeserializedInfo );

/**
 * @brief Call #MQTT_ProcessLoop in a loop for the duration of a timeout or
 * #MQTT_ProcessLoop returns a failure.
 *
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] ulTimeoutMs Duration to call #MQTT_ProcessLoop for.
 *
 * @return Returns the return value of the last call to #MQTT_ProcessLoop unless
 * the last call returned MQTTNeedMoreBytes -in that case it returns MQTTSuccess.
 */
static MQTTStatus_t processLoopWithTimeout( MQTTContext_t * pMqttContext,
                                            uint32_t ulTimeoutMs );

/*-----------------------------------------------------------*/

static void establishMqttSession( MQTTContext_t * pContext,
                                  NetworkContext_t * pNetworkContext,
                                  bool createCleanSession,
                                  bool * pSessionPresent )
{
    MQTTConnectInfo_t connectInfo;
    TransportInterface_t transport = { NULL };
    MQTTFixedBuffer_t networkBuffer;

    assert( pContext != NULL );
    assert( pNetworkContext != NULL );

    /* The network buffer must remain valid for the lifetime of the MQTT context. */
    static uint8_t buffer[ NETWORK_BUFFER_SIZE ];

    /* Setup the transport interface object for the library. */
    transport.pNetworkContext = pNetworkContext;
    transport.send = Openssl_Send;
    transport.recv = Openssl_Recv;
    transport.writev = NULL;

    /* Fill the values for network buffer. */
    networkBuffer.pBuffer = buffer;
    networkBuffer.size = NETWORK_BUFFER_SIZE;

    /* Initialize MQTT library. */
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_Init( pContext,
                                               &transport,
                                               Clock_GetTimeMs,
                                               eventCallback,
                                               &networkBuffer ) );

    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_InitStatefulQoS( pContext,
                                                          pOutgoingPublishRecords,
                                                          OUTGOING_PUBLISH_RECORD_LEN,
                                                          pIncomingPublishRecords,
                                                          INCOMING_PUBLISH_RECORD_LEN ) );

    /* Establish MQTT session with a CONNECT packet. */

    connectInfo.cleanSession = createCleanSession;
    connectInfo.pClientIdentifier = TEST_CLIENT_IDENTIFIER;
    connectInfo.clientIdentifierLength = TEST_CLIENT_IDENTIFIER_LENGTH;

    /* The interval at which an MQTT PINGREQ needs to be sent out to broker. */
    connectInfo.keepAliveSeconds = MQTT_KEEP_ALIVE_INTERVAL_SECONDS;

    /* Username and password for authentication. Not used in this test. */
    connectInfo.pUserName = NULL;
    connectInfo.userNameLength = 0U;
    connectInfo.pPassword = NULL;
    connectInfo.passwordLength = 0U;

    /* Send MQTT CONNECT packet to broker. */
    TEST_ASSERT_EQUAL( MQTTSuccess, MQTT_Connect( pContext,
                                                  &connectInfo,
                                                  NULL,
                                                  CONNACK_RECV_TIMEOUT_MS,
                                                  pSessionPresent ) );
}

static void eventCallback( MQTTContext_t * pContext,
                           MQTTPacketInfo_t * pPacketInfo,
                           MQTTDeserializedInfo_t * pDeserializedInfo )
{
    ShadowMessageType_t messageType = ShadowMessageTypeMaxNum;
    const char * pThingName = NULL;
    uint8_t thingNameLength = 0U;
    const char * pShadowName = NULL;
    uint8_t shadowNameLength = 0U;
    uint16_t packetIdentifier;

    ( void ) pContext;

    assert( pDeserializedInfo != NULL );
    assert( pContext != NULL );
    assert( pPacketInfo != NULL );

    packetIdentifier = pDeserializedInfo->packetIdentifier;

    /* Handle incoming publish. The lower 4 bits of the publish packet
     * type is used for the dup, QoS, and retain flags. Hence masking
     * out the lower bits to check if the packet is publish. */
    if( ( pPacketInfo->type & 0xF0U ) == MQTT_PACKET_TYPE_PUBLISH )
    {
        assert( pDeserializedInfo->pPublishInfo != NULL );

        /* Let the Device Shadow library tell us whether this is a device shadow message. */
        if( SHADOW_SUCCESS == Shadow_MatchTopicString( pDeserializedInfo->pPublishInfo->pTopicName,
                                                       pDeserializedInfo->pPublishInfo->topicNameLength,
                                                       &messageType,
                                                       &pThingName,
                                                       &thingNameLength,
                                                       &pShadowName,
                                                       &shadowNameLength ) )
        {
            /* Only accept the message if it has the expected Thing and Shadow names */
            if( ( strncmp( pThingName, THING_NAME, THING_NAME_LENGTH ) == 0 ) &&
                ( thingNameLength == THING_NAME_LENGTH ) &&
                ( strncmp( pShadowName, expectedShadowNameString, strlen( expectedShadowNameString ) ) == 0 ) &&
                ( shadowNameLength == strlen( expectedShadowNameString ) ) )
            {
                const char * pPayload = ( const char * ) pDeserializedInfo->pPublishInfo->pPayload;
                uint16_t payloadLength = strlen( pPayload );

                /* Upon successful return, the messageType has been filled in. */
                if( messageType == ShadowMessageTypeUpdateDelta )
                {
                    receivedUpdateDeltaResult = true;
                    LogInfo( ( "/update/delta payload:%.*s.\n\n", payloadLength, pPayload ) );
                    /* validate the each field in json payload if meet our expectation. */
                }
                else if( ( messageType == ShadowMessageTypeUpdateDocuments ) )
                {
                    receivedUpdateDocumentsResult = true;
                    LogInfo( ( "/update/documents json payload:%.*s.\n\n", payloadLength, pPayload ) );
                }
                else if( ( messageType == ShadowMessageTypeUpdateAccepted ) )
                {
                    receivedUpdateAcceptedResult = true;
                    LogInfo( ( "/update/accepted json payload:%.*s.\n\n", payloadLength, pPayload ) );
                }
                else if( ( messageType == ShadowMessageTypeUpdateRejected ) )
                {
                    receivedUpdateRejectedResult = true;
                    LogInfo( ( "/update/rejected json payload:%.*s.\n\n", payloadLength, pPayload ) );
                }
                else if( ( messageType == ShadowMessageTypeGetAccepted ) )
                {
                    receivedGetAcceptedResult = true;
                    LogInfo( ( "/get/accepted json payload:%.*s.\n\n", payloadLength, pPayload ) );
                }
                else if( ( messageType == ShadowMessageTypeGetRejected ) )
                {
                    receivedGetRejectedResult = true;
                    LogInfo( ( "/get/rejected json payload:%.*s.\n\n", payloadLength, pPayload ) );
                }
                else if( ( messageType == ShadowMessageTypeDeleteAccepted ) )
                {
                    receivedDeleteAcceptedResult = true;
                    LogInfo( ( "/delete/accepted json payload:%.*s.\n\n", payloadLength, pPayload ) );
                }
                else if( ( messageType == ShadowMessageTypeDeleteRejected ) )
                {
                    receivedDeleteRejectedResult = true;
                    LogInfo( ( "/delete/rejected json payload:%.*s.\n\n", payloadLength, pPayload ) );
                }
                else
                {
                    LogInfo( ( "other message type:%d !!\n\n", messageType ) );
                }
            }
            else
            {
                LogError( ( "Received unexpected Thing (%.*s) or Shadow (%.*s) name\n\n",
                            thingNameLength, pThingName, shadowNameLength, pShadowName ) );
            }
        }
        else
        {
            LogError( ( "Shadow_MatchTopicString parse failed:%.*s !!\n\n",
                        ( int ) strlen( ( const char * ) pDeserializedInfo->pPublishInfo->pTopicName ),
                        ( const char * ) pDeserializedInfo->pPublishInfo->pTopicName ) );
        }
    }
    else
    {
        /* Handle other packets. */
        switch( pPacketInfo->type )
        {
            case MQTT_PACKET_TYPE_SUBACK:
                /* Set the flag to represent reception of SUBACK. */
                receivedSubAck = true;

                LogDebug( ( "Received SUBACK: PacketID=%u",
                            packetIdentifier ) );
                /* Make sure ACK packet identifier matches with Request packet identifier. */
                TEST_ASSERT_EQUAL( globalSubscribePacketIdentifier, packetIdentifier );
                break;

            case MQTT_PACKET_TYPE_PINGRESP:

                /* Nothing to be done from application as library handles
                 * PINGRESP. */
                LogDebug( ( "Received PINGRESP" ) );
                break;

            case MQTT_PACKET_TYPE_UNSUBACK:
                /* Set the flag to represent reception of UNSUBACK. */
                receivedUnsubAck = true;

                LogDebug( ( "Received UNSUBACK: PacketID=%u",
                            packetIdentifier ) );
                /* Make sure ACK packet identifier matches with Request packet identifier. */
                TEST_ASSERT_EQUAL( globalUnsubscribePacketIdentifier, packetIdentifier );
                break;

            case MQTT_PACKET_TYPE_PUBACK:
                /* Set the flag to represent reception of PUBACK. */
                receivedPubAck = true;

                /* Make sure ACK packet identifier matches with Request packet identifier. */
                TEST_ASSERT_EQUAL( globalPublishPacketIdentifier, packetIdentifier );

                LogDebug( ( "Received PUBACK: PacketID=%u",
                            packetIdentifier ) );
                break;

            case MQTT_PACKET_TYPE_PUBREC:
                /* Set the flag to represent reception of PUBREC. */
                receivedPubRec = true;

                /* Make sure ACK packet identifier matches with Request packet identifier. */
                TEST_ASSERT_EQUAL( globalPublishPacketIdentifier, packetIdentifier );

                LogDebug( ( "Received PUBREC: PacketID=%u",
                            packetIdentifier ) );
                break;

            case MQTT_PACKET_TYPE_PUBREL:
                /* Set the flag to represent reception of PUBREL. */
                receivedPubRel = true;

                /* Nothing to be done from application as library handles
                 * PUBREL. */
                LogDebug( ( "Received PUBREL: PacketID=%u",
                            packetIdentifier ) );
                break;

            case MQTT_PACKET_TYPE_PUBCOMP:
                /* Set the flag to represent reception of PUBACK. */
                receivedPubComp = true;

                /* Make sure ACK packet identifier matches with Request packet identifier. */
                TEST_ASSERT_EQUAL( globalPublishPacketIdentifier, packetIdentifier );

                /* Nothing to be done from application as library handles
                 * PUBCOMP. */
                LogDebug( ( "Received PUBCOMP: PacketID=%u",
                            packetIdentifier ) );
                break;

            /* Any other packet type is invalid. */
            default:
                LogError( ( "Unknown packet type received:(%02x).",
                            pPacketInfo->type ) );
        }
    }
}

static MQTTStatus_t subscribeToTopic( MQTTContext_t * pContext,
                                      const char * pTopic,
                                      uint16_t topicLength,
                                      MQTTQoS_t qos )
{
    MQTTStatus_t mqttStatus = MQTTSuccess;
    MQTTSubscribeInfo_t pSubscriptionList[ 1 ];

    assert( pContext != NULL );
    assert( pTopic != NULL );
    assert( topicLength != 0 );

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* topic /update/accepted and uses qos. */
    pSubscriptionList[ 0 ].qos = qos;
    pSubscriptionList[ 0 ].pTopicFilter = pTopic;
    pSubscriptionList[ 0 ].topicFilterLength = topicLength;

    /* Generate packet identifier for the SUBSCRIBE packet. */
    globalSubscribePacketIdentifier = MQTT_GetPacketId( pContext );

    /* Send SUBSCRIBE packet. */
    mqttStatus = MQTT_Subscribe( pContext,
                                 pSubscriptionList,
                                 sizeof( pSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                 globalSubscribePacketIdentifier );

    if( mqttStatus == MQTTSuccess )
    {
        mqttStatus = processLoopWithTimeout( pContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );
    }

    if( mqttStatus == MQTTSuccess )
    {
        TEST_ASSERT_TRUE( receivedSubAck );
        receivedSubAck = false;
    }

    return mqttStatus;
}

static MQTTStatus_t unsubscribeFromTopic( MQTTContext_t * pContext,
                                          const char * pTopic,
                                          uint16_t topicLength,
                                          MQTTQoS_t qos )
{
    MQTTStatus_t mqttStatus = MQTTSuccess;
    MQTTSubscribeInfo_t pSubscriptionList[ 1 ];

    assert( pContext != NULL );
    assert( pTopic != NULL );
    assert( topicLength != 0 );

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* topic /update/accepted and uses qos. */
    pSubscriptionList[ 0 ].qos = qos;
    pSubscriptionList[ 0 ].pTopicFilter = pTopic;
    pSubscriptionList[ 0 ].topicFilterLength = topicLength;

    /* Generate packet identifier for the SUBSCRIBE packet. */
    globalUnsubscribePacketIdentifier = MQTT_GetPacketId( pContext );

    /* Send UNSUBSCRIBE packet. */
    mqttStatus = MQTT_Unsubscribe( pContext,
                                   pSubscriptionList,
                                   sizeof( pSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                   globalUnsubscribePacketIdentifier );

    if( mqttStatus == MQTTSuccess )
    {
        mqttStatus = processLoopWithTimeout( pContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );
    }

    if( mqttStatus == MQTTSuccess )
    {
        TEST_ASSERT_TRUE( receivedUnsubAck );
    }

    return mqttStatus;
}

static MQTTStatus_t publishToTopic( MQTTContext_t * pContext,
                                    const char * pTopic,
                                    const char * pPayload,
                                    MQTTQoS_t qos )
{
    MQTTStatus_t mqttStatus = MQTTSuccess;
    MQTTPublishInfo_t publishInfo;

    assert( pContext != NULL );

    /* Set the retain flag to false to avoid side-effects across test runs. */
    publishInfo.retain = false;

    publishInfo.qos = qos;
    publishInfo.dup = false;
    publishInfo.pTopicName = pTopic;
    publishInfo.topicNameLength = strlen( pTopic );
    publishInfo.pPayload = pPayload;
    publishInfo.payloadLength = strlen( pPayload );

    /* Get a new packet id. */
    globalPublishPacketIdentifier = MQTT_GetPacketId( pContext );

    /* Send PUBLISH packet. */
    mqttStatus = MQTT_Publish( pContext,
                               &publishInfo,
                               globalPublishPacketIdentifier );

    if( mqttStatus == MQTTSuccess )
    {
        mqttStatus = processLoopWithTimeout( pContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );
    }

    if( mqttStatus == MQTTSuccess )
    {
        /* We do not expect a PUBACK from the broker for the QoS 0 PUBLISH. */
        TEST_ASSERT_FALSE( receivedPubAck );
    }

    return mqttStatus;
}

static uint16_t createTopicString( ShadowTopicStringType_t topicType,
                                   const char * pShadowName,
                                   uint16_t shadowNameLength )
{
    assert( pShadowName != NULL );

    uint16_t topicLength = 0;

    TEST_ASSERT_EQUAL( SHADOW_SUCCESS, Shadow_AssembleTopicString( topicType,
                                                                   THING_NAME,
                                                                   THING_NAME_LENGTH,
                                                                   pShadowName,
                                                                   shadowNameLength,
                                                                   topicString,
                                                                   sizeof( topicString ),
                                                                   &topicLength ) );

    /* Other functions expect the topic string to be null terminated */
    topicString[ topicLength ] = '\0';

    return topicLength;
}

static void testSequence( const char * pShadowName,
                          uint16_t shadowNameLength )
{
    assert( pShadowName != NULL );
    assert( shadowNameLength < sizeof( expectedShadowNameString ) );

    /* Setup the expected shadow name used to filter incoming messages for only the correct shadow */
    strncpy( expectedShadowNameString, pShadowName, shadowNameLength );

    /* A buffer containing the update document. It has static duration to prevent
     * it from being placed on the call stack. */
    static char updateDocument[ 1 ] = { 0 };

    uint16_t topicLength;

    /* Subscribe to shadow topic /delete/accepted with Qos 0. */
    topicLength = createTopicString( ShadowTopicStringTypeDeleteAccepted, pShadowName, shadowNameLength );
    TEST_ASSERT_EQUAL( MQTTSuccess, subscribeToTopic( &context,
                                                      topicString,
                                                      topicLength,
                                                      MQTTQoS0 ) );

    /* Subscribe to shadow topic /delete/rejected with Qos 0. */
    topicLength = createTopicString( ShadowTopicStringTypeDeleteRejected, pShadowName, shadowNameLength );
    TEST_ASSERT_EQUAL( MQTTSuccess, subscribeToTopic( &context,
                                                      topicString,
                                                      topicLength,
                                                      MQTTQoS0 ) );

    /* Subscribe to shadow topic /get/accepted with Qos 0. */
    topicLength = createTopicString( ShadowTopicStringTypeGetAccepted, pShadowName, shadowNameLength );
    TEST_ASSERT_EQUAL( MQTTSuccess, subscribeToTopic( &context,
                                                      topicString,
                                                      topicLength,
                                                      MQTTQoS0 ) );

    /* Subscribe to shadow topic /get/rejected with Qos 0. */
    topicLength = createTopicString( ShadowTopicStringTypeGetRejected, pShadowName, shadowNameLength );
    TEST_ASSERT_EQUAL( MQTTSuccess, subscribeToTopic( &context,
                                                      topicString,
                                                      topicLength,
                                                      MQTTQoS0 ) );

    /* Subscribe to shadow topic /update/accepted with Qos 0. */
    topicLength = createTopicString( ShadowTopicStringTypeUpdateAccepted, pShadowName, shadowNameLength );
    TEST_ASSERT_EQUAL( MQTTSuccess, subscribeToTopic( &context,
                                                      topicString,
                                                      topicLength,
                                                      MQTTQoS0 ) );

    /* Subscribe to shadow topic /update/rejected with Qos 0. */
    topicLength = createTopicString( ShadowTopicStringTypeUpdateRejected, pShadowName, shadowNameLength );
    TEST_ASSERT_EQUAL( MQTTSuccess, subscribeToTopic( &context,
                                                      topicString,
                                                      topicLength,
                                                      MQTTQoS0 ) );

    /* Subscribe to shadow topic /update/delta with Qos 0. */
    topicLength = createTopicString( ShadowTopicStringTypeUpdateDelta, pShadowName, shadowNameLength );
    TEST_ASSERT_EQUAL( MQTTSuccess, subscribeToTopic( &context,
                                                      topicString,
                                                      topicLength,
                                                      MQTTQoS0 ) );

    /* Subscribe to shadow topic /update/documents with Qos 0. */
    topicLength = createTopicString( ShadowTopicStringTypeUpdateDocuments, pShadowName, shadowNameLength );
    TEST_ASSERT_EQUAL( MQTTSuccess, subscribeToTopic( &context,
                                                      topicString,
                                                      topicLength,
                                                      MQTTQoS0 ) );

    /* First of all, try to delete any Shadow document in the cloud.
     * This could trigger the /delete/accepted or /delete/rejected
     * based on the thing status on the cloud.
     */
    ( void ) createTopicString( ShadowTopicStringTypeDelete, pShadowName, shadowNameLength );
    TEST_ASSERT_EQUAL( MQTTSuccess, publishToTopic( &context,
                                                    topicString,
                                                    updateDocument,
                                                    MQTTQoS0 ) );

    /* Check the flag for /delete/accepted or /delete/rejected (if the shadow does not already exist). */
    TEST_ASSERT_TRUE( ( receivedDeleteAcceptedResult || receivedDeleteRejectedResult ) );

    /* Publish to the shadow topic /update with reported payload,
     *  that we subscribed to, with Qos 0. */
    ( void ) createTopicString( ShadowTopicStringTypeUpdate, pShadowName, shadowNameLength );
    TEST_ASSERT_EQUAL( MQTTSuccess, publishToTopic( &context,
                                                    topicString,
                                                    TEST_SHADOW_DESIRED,
                                                    MQTTQoS0 ) );

    /* Check the flag for /update/documents*/
    TEST_ASSERT_TRUE( receivedUpdateDocumentsResult );

    /* Check the flag for /update/delta. */
    TEST_ASSERT_TRUE( receivedUpdateDeltaResult );

    /* Check the flag for /update/accepted. */
    TEST_ASSERT_TRUE( receivedUpdateAcceptedResult );

    /* Finally, sending null payload on topic /get to trigger /get/accepted. */
    ( void ) createTopicString( ShadowTopicStringTypeGet, pShadowName, shadowNameLength );
    TEST_ASSERT_EQUAL( MQTTSuccess, publishToTopic( &context,
                                                    topicString,
                                                    updateDocument,
                                                    MQTTQoS0 ) );

    /* Check the flag for /get/accepted */
    TEST_ASSERT_TRUE( receivedGetAcceptedResult );

    /* Un-subscribe from a topic with Qos 0. */
    topicLength = createTopicString( ShadowTopicStringTypeUpdateDelta, pShadowName, shadowNameLength );
    TEST_ASSERT_EQUAL( MQTTSuccess, unsubscribeFromTopic( &context,
                                                          topicString,
                                                          topicLength,
                                                          MQTTQoS0 ) );
}

static MQTTStatus_t processLoopWithTimeout( MQTTContext_t * pMqttContext,
                                            uint32_t ulTimeoutMs )
{
    uint32_t ulMqttProcessLoopTimeoutTime;
    uint32_t ulCurrentTime;

    MQTTStatus_t eMqttStatus = MQTTSuccess;

    ulCurrentTime = pMqttContext->getTime();
    ulMqttProcessLoopTimeoutTime = ulCurrentTime + ulTimeoutMs;

    /* Call MQTT_ProcessLoop multiple times a timeout happens, or
     * MQTT_ProcessLoop fails. */
    while( ( ulCurrentTime < ulMqttProcessLoopTimeoutTime ) &&
           ( eMqttStatus == MQTTSuccess || eMqttStatus == MQTTNeedMoreBytes ) )
    {
        eMqttStatus = MQTT_ProcessLoop( pMqttContext );
        ulCurrentTime = pMqttContext->getTime();
    }

    if( eMqttStatus == MQTTNeedMoreBytes )
    {
        eMqttStatus = MQTTSuccess;
    }

    return eMqttStatus;
}

/* ============================   UNITY FIXTURES ============================ */

/* Called before each test method. */
void setUp( void )
{
    /* Reset file-scoped global variables. */
    receivedSubAck = false;
    receivedUnsubAck = false;
    receivedPubAck = false;
    receivedPubRec = false;
    receivedPubRel = false;
    receivedPubComp = false;
    persistentSession = false;
    receivedUpdateDeltaResult = false;
    receivedUpdateDocumentsResult = false;
    receivedUpdateAcceptedResult = false;
    receivedUpdateRejectedResult = false;
    receivedDeleteAcceptedResult = false;
    receivedDeleteRejectedResult = false;
    receivedGetAcceptedResult = false;
    receivedGetRejectedResult = false;

    memset( &incomingInfo, 0u, sizeof( MQTTPublishInfo_t ) );
    memset( &opensslCredentials, 0u, sizeof( OpensslCredentials_t ) );
    memset( &opensslParams, 0u, sizeof( OpensslParams_t ) );
    opensslCredentials.pRootCaPath = ROOT_CA_CERT_PATH;
    opensslCredentials.pClientCertPath = CLIENT_CERT_PATH;
    opensslCredentials.pPrivateKeyPath = CLIENT_PRIVATE_KEY_PATH;
    opensslCredentials.sniHostName = AWS_IOT_ENDPOINT;
    serverInfo.pHostName = AWS_IOT_ENDPOINT;
    serverInfo.hostNameLength = AWS_IOT_ENDPOINT_LENGTH;
    serverInfo.port = AWS_MQTT_PORT;

    networkContext.pParams = &opensslParams;

    /* Establish a TCP connection with the server endpoint, then
     * establish TLS session on top of TCP connection. */
    TEST_ASSERT_EQUAL( OPENSSL_SUCCESS, Openssl_Connect( &networkContext,
                                                         &serverInfo,
                                                         &opensslCredentials,
                                                         TRANSPORT_SEND_RECV_TIMEOUT_MS,
                                                         TRANSPORT_SEND_RECV_TIMEOUT_MS ) );
    TEST_ASSERT_NOT_EQUAL( -1, opensslParams.socketDescriptor );
    TEST_ASSERT_NOT_NULL( opensslParams.pSsl );

    /* Establish MQTT session on top of the TCP+TLS connection. */
    establishMqttSession( &context, &networkContext, true, &persistentSession );
}

/* Called after each test method. */
void tearDown( void )
{
    MQTTStatus_t mqttStatus;
    OpensslStatus_t opensslStatus;

    /* Free memory, if allocated during test case execution. */
    if( incomingInfo.pTopicName != NULL )
    {
        free( ( void * ) incomingInfo.pTopicName );
    }

    if( incomingInfo.pPayload != NULL )
    {
        free( ( void * ) incomingInfo.pPayload );
    }

    /* Terminate MQTT connection. */
    mqttStatus = MQTT_Disconnect( &context );

    /* Terminate TLS session and TCP connection. */
    opensslStatus = Openssl_Disconnect( &networkContext );

    /* Make any assertions at the end so that all memory is deallocated before
     * the end of this function. */
    TEST_ASSERT_EQUAL( MQTTSuccess, mqttStatus );
    TEST_ASSERT_EQUAL( OPENSSL_SUCCESS, opensslStatus );
}

/* ========================== Test Cases ============================ */

/**
 * @brief Subscribes the classic shadow topics: /update/delta, /update/documents,
 * /update/accepted, /delete/accepted, /get/accepted, then publish the
 * regarding payloads to verify if receiving the notification from the
 * subscribed topics, and then finally unsubscribes from update/delta.
 */
void test_Shadow_System_Classic( void )
{
    testSequence( SHADOW_NAME_CLASSIC, ( ( uint16_t ) ( sizeof( SHADOW_NAME_CLASSIC ) - 1 ) ) );
}

/**
 * @brief Subscribes the named shadow topics: /update/delta, /update/documents,
 * /update/accepted, /delete/accepted, /get/accepted, then publish the
 * regarding payloads to verify if receiving the notification from the
 * subscribed topics, and then finally unsubscribes from update/delta.
 */
void test_Shadow_System_Named( void )
{
    const char shadowName[] = { "testShadowName" };

    testSequence( shadowName, ( ( uint16_t ) ( sizeof( shadowName ) - 1 ) ) );
}

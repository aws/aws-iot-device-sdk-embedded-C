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

/*
 * Demo for showing the use of MQTT APIs to establish an MQTT session,
 * subscribe to a topic, publish to a topic, receive incoming publishes,
 * unsubscribe from a topic and disconnect the MQTT session.
 *
 * The example is single threaded and uses statically allocated memory;
 * it uses QOS2 and therefore implements a retransmission mechanism
 * for Publish messages. Retransmission of publish messages are attempted
 * when a MQTT connection is established with a session that was already
 * present. All the outgoing publish messages waiting to receive PUBREC
 * are resend in this demo. In order to support retransmission all the outgoing
 * publishes are stored until a PUBREC is received.
 */

/**
 * @file mqtt_demo_connection_sharing.c
 * @brief MQTT Demo application that showcases multiplexing of the same MQTT connection
 * across multiple topic subscriptions using a subscription manager.
 */

/* Standard includes. */
#include <assert.h>
#include <stdlib.h>
#include <string.h>

/* POSIX includes. */
#include <unistd.h>

/* Include Demo Config as the first non-system header. */
#include "demo_config.h"

/* MQTT API header. */
#include "mqtt.h"

/* OpenSSL sockets transport implementation. */
#include "openssl_posix.h"

/* Reconnect parameters. */
#include "transport_reconnect.h"

/* Clock for timer. */
#include "clock.h"

/* Include subscription manager. */
#include "mqtt_subscription_manager.h"

/**
 * These configuration settings are required to run the basic TLS demo.
 * Throw compilation error if the below configs are not defined.
 */
#ifndef ROOT_CA_CERT_PATH
    #error "Please define path to Root CA certificate of the MQTT broker(ROOT_CA_CERT_PATH) in demo_config.h."
#endif
#ifndef CLIENT_IDENTIFIER
    #error "Please define a unique CLIENT_IDENTIFIER."
#endif

/**
 * Provide default values for undefined configuration settings.
 */
#ifndef BROKER_PORT
    #define BROKER_PORT    ( 8883 )
#endif

#ifndef NETWORK_BUFFER_SIZE
    #define NETWORK_BUFFER_SIZE    ( 1024U )
#endif

/**
 * @brief Length of client identifier.
 */
#define CLIENT_IDENTIFIER_LENGTH                ( ( uint16_t ) ( sizeof( CLIENT_IDENTIFIER ) - 1 ) )

/**
 * @brief Timeout for receiving CONNACK packet in milli seconds.
 */
#define CONNACK_RECV_TIMEOUT_MS                 ( 1000U )

/**
 * @brief The MQTT topic filter to subscribe to for temperature data in the demo.
 *
 * The topic name starts with the client identifier to ensure that each demo
 * interacts with a unique topic name.
 */
#define DEMO_TEMPERATURE_TOPIC_FILTER           CLIENT_IDENTIFIER "/demo/temperature/+"

/**
 * @brief The length of the temperature topic filter.
 */
#define DEMO_TEMPERATURE_TOPIC_FILTER_LENGTH    ( ( uint16_t ) ( sizeof( DEMO_TEMPERATURE_TOPIC_FILTER ) - 1U ) )

/**
 * @brief The MQTT topic for the high temperature data value that the demo will
 * publish to.
 *
 * The topic name starts with the client identifier to ensure that each demo
 * interacts with a unique topic name.
 */
#define DEMO_TEMPERATURE_HIGH_TOPIC             CLIENT_IDENTIFIER "/demo/temperature/high"

/**
 * @brief The length of the high temperature topic name.
 */
#define DEMO_TEMPERATURE_HIGH_TOPIC_LENGTH      ( ( uint16_t ) ( sizeof( DEMO_TEMPERATURE_HIGH_TOPIC ) - 1U ) )

/**
 * @brief The MQTT topic for the high temperature data value that the demo will
 * publish to.
 *
 * The topic name starts with the client identifier to ensure that each demo
 * interacts with a unique topic name.
 */
#define DEMO_TEMPERATURE_LOW_TOPIC              CLIENT_IDENTIFIER "/demo/temperature/low"

/**
 * @brief The length of the high temperature topic name.
 */
#define DEMO_TEMPERATURE_LOW_TOPIC_LENGTH       ( ( uint16_t ) ( sizeof( DEMO_TEMPERATURE_LOW_TOPIC ) - 1U ) )

/**
 * @brief The MQTT topic filter to subscribe and publish to for humidity data in the demo.
 *
 * The topic name starts with the client identifier to ensure that each demo
 * interacts with a unique topic name.
 */
#define DEMO_HUMIDITY_TOPIC                     CLIENT_IDENTIFIER "/demo/humidity"

/**
 * @brief The length of the humidity topic.
 */
#define DEMO_HUMIDITY_TOPIC_LENGTH              ( ( uint16_t ) ( sizeof( DEMO_HUMIDITY_TOPIC ) - 1U ) )

/**
 * @brief The MQTT topic filter to subscribe and publish to for precipitation data in the demo.
 *
 * The topic name starts with the client identifier to ensure that each demo
 * interacts with a unique topic name.
 */
#define DEMO_PRECIPITATION_TOPIC                CLIENT_IDENTIFIER "/demo/precipitation"

/**
 * @brief The length of the precipitation topic.
 */
#define DEMO_PRECIPITATION_TOPIC_LENGTH         ( ( uint16_t ) ( sizeof( DEMO_PRECIPITATION_TOPIC ) - 1U ) )

/**
 * @brief The MQTT message for the #DEMO_TEMPERATURE_HIGH_TOPIC topic published
 * in this example.
 */
#define DEMO_TEMPERATURE_HIGH_MESSAGE           "Today's High is 80 degree F"

/**
 * @brief The MQTT message for the #DEMO_TEMPERATURE_LOW_TOPIC topic published
 * in this example.
 */
#define DEMO_TEMPERATURE_LOW_MESSAGE            "Today's Low 52 degree F"

/**
 * @brief The MQTT message for the #DEMO_HUMIDITY_TOPIC topic published in this example.
 */
#define DEMO_HUMIDITY_MESSAGE                   "Today's humidity at 58%"

/**
 * @brief The MQTT message for the #DEMO_PRECIPITATION_TOPIC_LENGTH topic published in this example.
 */
#define DEMO_PRECIPITATION_MESSAGE              "Today's precipitation at 9%"

/**
 * @brief Maximum number of outgoing publishes maintained in the application
 * until an ack is received from the broker.
 */
#define MAX_OUTGOING_PUBLISHES                  ( 5U )

/**
 * @brief Invalid packet identifier for the MQTT packets. Zero is always an
 * invalid packet identifier as per MQTT 3.1.1 spec.
 */
#define MQTT_PACKET_ID_INVALID                  ( ( uint16_t ) 0U )

/**
 * @brief Timeout for MQTT_ProcessLoop function in milliseconds.
 */
#define MQTT_PROCESS_LOOP_TIMEOUT_MS            ( 500U )

/**
 * @brief The maximum time interval in seconds which is allowed to elapse
 *  between two Control Packets.
 *
 *  It is the responsibility of the Client to ensure that the interval between
 *  Control Packets being sent does not exceed the this Keep Alive value. In the
 *  absence of sending any other Control Packets, the Client MUST send a
 *  PINGREQ Packet.
 */
#define MQTT_KEEP_ALIVE_INTERVAL_SECONDS        ( 60U )

/**
 * @brief Delay in seconds between two iterations of subscribePublishLoop().
 */
#define MQTT_SUBPUB_LOOP_DELAY_SECONDS          ( 5U )

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS          ( 200 )

/*-----------------------------------------------------------*/

/**
 * @brief Structure to keep the MQTT publish packets until an ack is received
 * for QoS2 publishes.
 */
typedef struct PublishPackets
{
    /**
     * @brief Packet identifier of the publish packet.
     */
    uint16_t packetId;

    /**
     * @brief Publish info of the publish packet.
     */
    MQTTPublishInfo_t pubInfo;
} PublishPackets_t;

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
 * @brief Array to keep the outgoing publish messages.
 * These stored outgoing publish messages are kept until a successful ack
 * is received.
 */
static PublishPackets_t outgoingPublishPackets[ MAX_OUTGOING_PUBLISHES ] = { 0 };

/**
 * @brief The network buffer must remain valid for the lifetime of the MQTT context.
 */
static uint8_t buffer[ NETWORK_BUFFER_SIZE ];

/**
 * @brief Flag to represent whether that the temperature callback has been invoked with
 * incoming PUBLISH message for high temperature data.
 */
static bool globalReceivedHighTemperatureData = false;

/**
 * @brief Flag to represent whether that the temperature callback has been invoked with
 * incoming PUBLISH message for low temperature data.
 */
static bool globalReceivedLowTemperatureData = false;

/**
 * @brief Flag to represent whether that the humidity topic callback has been invoked.
 */
static bool globalReceivedHumidityData = false;

/**
 * @brief Flag to represent whether that the precipitation topic callback has been invoked.
 */
static bool globalReceivedPrecipitationData = false;

/*-----------------------------------------------------------*/

/**
 * @brief Connect to MQTT broker with reconnection retries.
 *
 * If connection fails, retry is attempted after a timeout.
 * Timeout value will exponentially increased till maximum
 * timeout value is reached or the number of attempts are exhausted.
 *
 * @param[out] pNetworkContext The output parameter to return the created network context.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on successful connection.
 */
static int connectToServerWithBackoffRetries( NetworkContext_t * pNetworkContext );

/**
 * @brief A function that connects to MQTT broker,
 * subscribes to a topic, publishes to the same topic
 * MQTT_PUBLISH_COUNT_PER_LOOP number of times, and verifies if it
 * receives the Publish message back.
 *
 * @param[in] pNetworkContext Pointer to the network context created using Openssl_Connect.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on success.
 */
static int subscribePublishLoop( NetworkContext_t * pNetworkContext );

/**
 * @brief The function to handle the incoming publishes.
 *
 * @param[in] pPublishInfo Pointer to publish info of the incoming publish.
 * @param[in] packetIdentifier Packet identifier of the incoming publish.
 */
static void handleIncomingPublish( MQTTPublishInfo_t * pPublishInfo );

/**
 * @brief Callback that is registered for the temperature data topic filter,
 * #DEMO_TEMPERATURE_TOPIC_FILTER, with the subscription manager.
 *
 * The callback determines the type of temperature data ("high" or "low") received
 * on the incoming PUBLISH topic, prints the data, and sets the associated
 * global flag for the temperature data type to reception of data.
 *
 * @param[in] pContext The MQTT context associated with the incoming PUBLISH.
 * @param[in] pPublishInfo Deserialized publish info pointer for the incoming
 * packet.
 */
static void temperatureDataCallback( MQTTContext_t * pContext,
                                     MQTTPublishInfo_t * pPublishInfo );

/**
 * @brief Callback that is registered for the humidity data topic filter,
 * #DEMO_HUMIDITY_TOPIC, with the subscription manager.
 *
 * The callback prints the received humidity data, and sets a global
 * flag to indicate invocation of the callback.
 *
 * @param[in] pContext The MQTT context associated with the incoming PUBLISH.
 * @param[in] pPublishInfo Deserialized publish info pointer for the incoming
 * packet.
 */
static void humidityDataCallback( MQTTContext_t * pContext,
                                  MQTTPublishInfo_t * pPublishInfo );

/**
 * @brief Callback that is registered for the precipitation data topic filter,
 * #DEMO_PRECIPITATION_TOPIC, with the subscription manager.
 *
 * The callback prints the received precipitation data, and sets a global
 * flag to indicate invocation of the callback.
 *
 * @param[in] pContext The MQTT context associated with the incoming PUBLISH.
 * @param[in] pPublishInfo Deserialized publish info pointer for the incoming
 * packet.
 */
static void precipitationDataCallback( MQTTContext_t * pContext,
                                       MQTTPublishInfo_t * pPublishInfo );

/**
 * @brief The callback function that is registered with the MQTT connection
 * for dispatching incoming publish messages to their registered callbacks,
 * and handling incoming acks reported from the MQTT library.
 *
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] pPacketInfo Packet Info pointer for the incoming packet.
 * @param[in] packetIdentifier Packet identifier of the incoming packet.
 * @param[in] pDeserializedInfo Deserialized information from the incoming packet.
 * packet.
 */
static void commonEventHandler( MQTTContext_t * pMqttContext,
                                MQTTPacketInfo_t * pPacketInfo,
                                MQTTDeserializedInfo_t * pDeserializedInfo );

/**
 * @brief Sends an MQTT CONNECT packet over the already connected TCP socket.
 *
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] pNetworkContext Pointer to the network context created using Openssl_Connect.
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
                                 NetworkContext_t * pNetworkContext,
                                 bool createCleanSession,
                                 bool * pSessionPresent );

/**
 * @brief Close an MQTT session by sending MQTT DISCONNECT.
 *
 * @param[in] pMqttContext MQTT context pointer.
 *
 * @return EXIT_SUCCESS if DISCONNECT was successfully sent;
 * EXIT_FAILURE otherwise.
 */
static int disconnectMqttSession( MQTTContext_t * pMqttContext );

/**
 * @brief Sends an MQTT SUBSCRIBE to subscribe to the passed
 * topic filter.
 *
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] pTopicFilter The topic filter to subscribe to.
 * @param[in] topicFilterLength The length of the topic filter.
 *
 * @return EXIT_SUCCESS if SUBSCRIBE was successfully sent;
 * EXIT_FAILURE otherwise.
 */
static int subscribeToTopic( MQTTContext_t * pMqttContext,
                             const char * pTopicFilter,
                             uint16_t topicFilterLength );

/**
 * @brief Sends an MQTT UNSUBSCRIBE to unsubscribe from
 * #MQTT_EXAMPLE_TOPIC defined at the top of the file.
 *
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] pTopicFilter The topic filter to subscribe to.
 * @param[in] topicFilterLength The length of the topic filter.
 *
 * @return EXIT_SUCCESS if UNSUBSCRIBE was successfully sent;
 * EXIT_FAILURE otherwise.
 */
static int unsubscribeFromTopic( MQTTContext_t * pMqttContext,
                                 const char * pTopicFilter,
                                 uint16_t topicFilterLength );

/**
 * @brief Sends an MQTT PUBLISH to the passed topic
 * with the passed message.
 *
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] pTopic The topic on which to send a PUBLISH message.
 * @param[in] topicLength The length of the topic.
 * @param[in] pMessage The message payload to PUBLISH.
 * @return EXIT_SUCCESS if PUBLISH was successfully sent;
 * EXIT_FAILURE otherwise.
 */
static int publishToTopic( MQTTContext_t * pMqttContext,
                           const char * pTopic,
                           uint16_t topicLength,
                           const char * pMessage );

/**
 * @brief Function to get the free index at which an outgoing publish
 * can be stored.
 *
 * @param[out] pIndex The output parameter to return the index at which an
 * outgoing publish message can be stored.
 *
 * @return EXIT_FAILURE if no more publishes can be stored;
 * EXIT_SUCCESS if an index to store the next outgoing publish is obtained.
 */
static int getNextFreeIndexForOutgoingPublishes( uint8_t * pIndex );

/**
 * @brief Function to clean up an outgoing publish at given index from the
 * #outgoingPublishPackets array.
 *
 * @param[in] index The index at which a publish message has to be cleaned up.
 */
static void cleanupOutgoingPublishAt( uint8_t index );

/**
 * @brief Function to clean up all the outgoing publishes maintained in the
 * array.
 */
static void cleanupOutgoingPublishes( void );

/**
 * @brief Function to clean up the publish packet with the given packet id.
 *
 * @param[in] packetId Packet identifier of the packet to be cleaned up from
 * the array.
 */
static void cleanupOutgoingPublishWithPacketID( uint16_t packetId );

/**
 * @brief Function to resend the publishes if a session is re-established with
 * the broker. This function handles the resending of the QoS2 publish packets,
 * which are maintained locally.
 *
 * @param[in] pMqttContext MQTT context pointer.
 */
static int handlePublishResend( MQTTContext_t * pMqttContext );

/*-----------------------------------------------------------*/

static int connectToServerWithBackoffRetries( NetworkContext_t * pNetworkContext )
{
    int returnStatus = EXIT_SUCCESS;
    bool retriesArePending = true;
    OpensslStatus_t opensslStatus = OPENSSL_SUCCESS;
    TransportReconnectParams_t reconnectParams;
    ServerInfo_t serverInfo;
    OpensslCredentials_t opensslCredentials;

    /* Initialize information to connect to the MQTT broker. */
    serverInfo.pHostName = BROKER_ENDPOINT;
    serverInfo.hostNameLength = BROKER_ENDPOINT_LENGTH;
    serverInfo.port = BROKER_PORT;

    /* Initialize credentials for establishing TLS session. */
    memset( &opensslCredentials, 0, sizeof( OpensslCredentials_t ) );
    opensslCredentials.pRootCaPath = ROOT_CA_CERT_PATH;

    /* Initialize reconnect attempts and interval */
    Transport_ReconnectParamsReset( &reconnectParams );

    /* Attempt to connect to MQTT broker. If connection fails, retry after
     * a timeout. Timeout value will exponentially increase till maximum
     * attempts are reached.
     */
    do
    {
        /* Establish a TLS session with the MQTT broker. This example connects
         * to the MQTT broker as specified in AWS_IOT_ENDPOINT and AWS_MQTT_PORT at
         * the top of this file. */
        LogInfo( ( "Establishing a TLS session to %.*s:%d.",
                   BROKER_ENDPOINT_LENGTH,
                   BROKER_ENDPOINT,
                   BROKER_PORT ) );
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

static int getNextFreeIndexForOutgoingPublishes( uint8_t * pIndex )
{
    int returnStatus = EXIT_FAILURE;
    uint8_t index = 0;

    assert( outgoingPublishPackets != NULL );
    assert( pIndex != NULL );

    for( index = 0; index < MAX_OUTGOING_PUBLISHES; index++ )
    {
        /* A free index is marked by invalid packet id.
         * Check if the the index has a free slot. */
        if( outgoingPublishPackets[ index ].packetId == MQTT_PACKET_ID_INVALID )
        {
            returnStatus = EXIT_SUCCESS;
            break;
        }
    }

    /* Copy the available index into the output param. */
    *pIndex = index;

    return returnStatus;
}
/*-----------------------------------------------------------*/

static void cleanupOutgoingPublishAt( uint8_t index )
{
    assert( outgoingPublishPackets != NULL );
    assert( index < MAX_OUTGOING_PUBLISHES );

    /* Clear the outgoing publish packet. */
    ( void ) memset( &( outgoingPublishPackets[ index ] ),
                     0x00,
                     sizeof( outgoingPublishPackets[ index ] ) );
}

/*-----------------------------------------------------------*/

static void cleanupOutgoingPublishes( void )
{
    assert( outgoingPublishPackets != NULL );

    /* Clean up all the outgoing publish packets. */
    ( void ) memset( outgoingPublishPackets, 0x00, sizeof( outgoingPublishPackets ) );
}

/*-----------------------------------------------------------*/

static void cleanupOutgoingPublishWithPacketID( uint16_t packetId )
{
    uint8_t index = 0;

    assert( outgoingPublishPackets != NULL );
    assert( packetId != MQTT_PACKET_ID_INVALID );

    /* Clean up all the saved outgoing publishes. */
    for( ; index < MAX_OUTGOING_PUBLISHES; index++ )
    {
        if( outgoingPublishPackets[ index ].packetId == packetId )
        {
            cleanupOutgoingPublishAt( index );
            LogInfo( ( "Cleaned up outgoing publish packet with packet id %u.\n\n",
                       packetId ) );
            break;
        }
    }
}

/*-----------------------------------------------------------*/

static int handlePublishResend( MQTTContext_t * pMqttContext )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus = MQTTSuccess;
    uint8_t index = 0U;

    assert( outgoingPublishPackets != NULL );

    /* Resend all the QoS1 publishes still in the array. These are the
     * publishes that hasn't received a PUBREC. When a PUBREC is
     * received, the publish is removed from the array. */
    for( index = 0U; index < MAX_OUTGOING_PUBLISHES; index++ )
    {
        if( outgoingPublishPackets[ index ].packetId != MQTT_PACKET_ID_INVALID )
        {
            outgoingPublishPackets[ index ].pubInfo.dup = true;

            LogInfo( ( "Sending duplicate PUBLISH with packet id %u.",
                       outgoingPublishPackets[ index ].packetId ) );
            mqttStatus = MQTT_Publish( pMqttContext,
                                       &outgoingPublishPackets[ index ].pubInfo,
                                       outgoingPublishPackets[ index ].packetId );

            if( mqttStatus != MQTTSuccess )
            {
                LogError( ( "Sending duplicate PUBLISH for packet id %u "
                            " failed with status %u.",
                            outgoingPublishPackets[ index ].packetId,
                            mqttStatus ) );
                returnStatus = EXIT_FAILURE;
                break;
            }
            else
            {
                LogInfo( ( "Sent duplicate PUBLISH successfully for packet id %u.\n\n",
                           outgoingPublishPackets[ index ].packetId ) );
            }
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static void handleIncomingPublish( MQTTPublishInfo_t * pPublishInfo )
{
    assert( pPublishInfo != NULL );

    /* Process incoming Publish. */
    LogInfo( ( "Incoming QOS : %d.", pPublishInfo->qos ) );


    LogInfo( ( "Incoming Publish Topic Name: %.*s matches subscribed topic.\n"
               "Incoming Publish Message : %.*s.\n\n",
               pPublishInfo->topicNameLength,
               pPublishInfo->pTopicName,
               ( int ) pPublishInfo->payloadLength,
               ( const char * ) pPublishInfo->pPayload ) );
}

/*-----------------------------------------------------------*/

static void temperatureDataCallback( MQTTContext_t * pContext,
                                     MQTTPublishInfo_t * pPublishInfo )
{
    assert( pPublishInfo != NULL );
    assert( pContext != NULL );

    LogInfo( ( "Invoked temperature callback." ) );

    /* Determine whether the incoming PUBLISH message is for "high"
     * or "low" temperature data. */
    if( ( pPublishInfo->topicNameLength == DEMO_TEMPERATURE_HIGH_TOPIC_LENGTH ) &&
        ( strncmp( pPublishInfo->pTopicName, DEMO_TEMPERATURE_HIGH_TOPIC,
                   DEMO_TEMPERATURE_HIGH_TOPIC_LENGTH ) == 0 ) )
    {
        /* Incoming PUBLISH message has been received on the High Temperature topic.
         * Set the flag to indicate that the high temperature data has been received. */
        globalReceivedHighTemperatureData = true;
    }
    else if( ( pPublishInfo->topicNameLength == DEMO_TEMPERATURE_LOW_TOPIC_LENGTH ) &&
             ( strncmp( pPublishInfo->pTopicName, DEMO_TEMPERATURE_LOW_TOPIC,
                        DEMO_TEMPERATURE_LOW_TOPIC_LENGTH ) == 0 ) )
    {
        /* Incoming PUBLISH message has been received on the Low Temperature topic.
         * Set the flag to indicate that the low temperature data has been received. */
        globalReceivedLowTemperatureData = true;
    }
    else
    {
        LogError( ( "Callback failed to identify the temperature data type received." ) );
    }

    handleIncomingPublish( pPublishInfo );
}

static void humidityDataCallback( MQTTContext_t * pContext,
                                  MQTTPublishInfo_t * pPublishInfo )
{
    assert( pPublishInfo != NULL );
    assert( pContext != NULL );

    LogInfo( ( "Invoked humidity callback." ) );

    /* Set the global flag to indicate that the humidity data has been received. */
    globalReceivedHumidityData = true;

    handleIncomingPublish( pPublishInfo );
}

static void precipitationDataCallback( MQTTContext_t * pContext,
                                       MQTTPublishInfo_t * pPublishInfo )
{
    assert( pPublishInfo != NULL );
    assert( pContext != NULL );

    LogInfo( ( "Invoked precipitation callback." ) );

    /* Set the global flag to indicate that the humidity data has been received. */
    globalReceivedPrecipitationData = true;

    handleIncomingPublish( pPublishInfo );
}

static void commonEventHandler( MQTTContext_t * pMqttContext,
                                MQTTPacketInfo_t * pPacketInfo,
                                MQTTDeserializedInfo_t * pDeserializedInfo )
{
    assert( pMqttContext != NULL );
    assert( pPacketInfo != NULL );
    assert( pDeserializedInfo != NULL );
    assert( pDeserializedInfo->packetIdentifier != MQTT_PACKET_ID_INVALID );

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
                /* Make sure ACK packet identifier matches with Request packet identifier. */
                assert( globalSubscribePacketIdentifier == pDeserializedInfo->packetIdentifier );
                break;

            case MQTT_PACKET_TYPE_UNSUBACK:
                LogInfo( ( "Received UNSUBACK.\n\n" ) );
                /* Make sure ACK packet identifier matches with Request packet identifier. */
                assert( globalUnsubscribePacketIdentifier == pDeserializedInfo->packetIdentifier );
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
                /* Cleanup publish packet when a PUBREC is received. */
                cleanupOutgoingPublishWithPacketID( pDeserializedInfo->packetIdentifier );
                break;

            /* Any other packet type is invalid. */
            default:
                LogError( ( "Unknown packet type received:(%02x).\n\n",
                            pPacketInfo->type ) );
        }
    }
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
                            commonEventHandler,
                            &networkBuffer );

    if( mqttStatus != MQTTSuccess )
    {
        returnStatus = EXIT_FAILURE;
        LogError( ( "MQTT init failed with status %u.", mqttStatus ) );
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

static int disconnectMqttSession( MQTTContext_t * pMqttContext )
{
    MQTTStatus_t mqttStatus = MQTTSuccess;
    int returnStatus = EXIT_SUCCESS;

    assert( pMqttContext != NULL );

    /* Send DISCONNECT. */
    mqttStatus = MQTT_Disconnect( pMqttContext );

    if( mqttStatus != MQTTSuccess )
    {
        LogError( ( "Sending MQTT DISCONNECT failed with status = %u.",
                    mqttStatus ) );
        returnStatus = EXIT_FAILURE;
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int subscribeToTopic( MQTTContext_t * pMqttContext,
                             const char * pTopicFilter,
                             uint16_t topicFilterLength )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    MQTTSubscribeInfo_t pSubscriptionList[ 1 ];

    assert( pMqttContext != NULL );

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* This example subscribes to only one topic and uses QOS1. */
    pSubscriptionList[ 0 ].qos = MQTTQoS1;
    pSubscriptionList[ 0 ].pTopicFilter = pTopicFilter;
    pSubscriptionList[ 0 ].topicFilterLength = topicFilterLength;

    /* Generate packet identifier for the SUBSCRIBE packet. */
    globalSubscribePacketIdentifier = MQTT_GetPacketId( pMqttContext );

    /* Send SUBSCRIBE packet. */
    mqttStatus = MQTT_Subscribe( pMqttContext,
                                 pSubscriptionList,
                                 sizeof( pSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                 globalSubscribePacketIdentifier );

    if( mqttStatus != MQTTSuccess )
    {
        LogError( ( "Failed to send SUBSCRIBE packet to broker with error = %u.",
                    mqttStatus ) );
        returnStatus = EXIT_FAILURE;
    }
    else
    {
        LogInfo( ( "SUBSCRIBE sent for topic %.*s to broker.\n\n",
                   topicFilterLength,
                   pTopicFilter ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int unsubscribeFromTopic( MQTTContext_t * pMqttContext,
                                 const char * pTopicFilter,
                                 uint16_t topicFilterLength )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    MQTTSubscribeInfo_t pSubscriptionList[ 1 ];

    assert( pMqttContext != NULL );

    /* Start with everything at 0. */
    ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

    /* This example subscribes to and unsubscribes from only one topic
     * and uses QOS2. */
    pSubscriptionList[ 0 ].qos = MQTTQoS2;
    pSubscriptionList[ 0 ].pTopicFilter = pTopicFilter;
    pSubscriptionList[ 0 ].topicFilterLength = topicFilterLength;

    /* Generate packet identifier for the UNSUBSCRIBE packet. */
    globalUnsubscribePacketIdentifier = MQTT_GetPacketId( pMqttContext );

    /* Send UNSUBSCRIBE packet. */
    mqttStatus = MQTT_Unsubscribe( pMqttContext,
                                   pSubscriptionList,
                                   sizeof( pSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                   globalUnsubscribePacketIdentifier );

    if( mqttStatus != MQTTSuccess )
    {
        LogError( ( "Failed to send UNSUBSCRIBE packet to broker with error = %u.",
                    mqttStatus ) );
        returnStatus = EXIT_FAILURE;
    }
    else
    {
        LogInfo( ( "UNSUBSCRIBE sent for topic %.*s to broker.\n\n",
                   topicFilterLength,
                   pTopicFilter ) );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int publishToTopic( MQTTContext_t * pMqttContext,
                           const char * pTopic,
                           uint16_t topicLength,
                           const char * pMessage )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus = MQTTSuccess;
    uint8_t publishIndex = MAX_OUTGOING_PUBLISHES;

    assert( pMqttContext != NULL );

    /* Get the next free index for the outgoing publish. All QoS2 outgoing
     * publishes are stored until a PUBREC is received. These messages are
     * stored for supporting a resend if a network connection is broken before
     * receiving a PUBREC. */
    returnStatus = getNextFreeIndexForOutgoingPublishes( &publishIndex );

    if( returnStatus == EXIT_FAILURE )
    {
        LogError( ( "Unable to find a free spot for outgoing PUBLISH message.\n\n" ) );
    }
    else
    {
        /* This example publishes with QOS1. */
        outgoingPublishPackets[ publishIndex ].pubInfo.qos = MQTTQoS1;
        outgoingPublishPackets[ publishIndex ].pubInfo.pTopicName = pTopic;
        outgoingPublishPackets[ publishIndex ].pubInfo.topicNameLength = topicLength;
        outgoingPublishPackets[ publishIndex ].pubInfo.pPayload = pMessage;
        outgoingPublishPackets[ publishIndex ].pubInfo.payloadLength = strlen( pMessage );

        /* Get a new packet id. */
        outgoingPublishPackets[ publishIndex ].packetId = MQTT_GetPacketId( pMqttContext );

        /* Send PUBLISH packet. */
        mqttStatus = MQTT_Publish( pMqttContext,
                                   &outgoingPublishPackets[ publishIndex ].pubInfo,
                                   outgoingPublishPackets[ publishIndex ].packetId );

        if( mqttStatus != MQTTSuccess )
        {
            LogError( ( "Failed to send PUBLISH packet to broker with error = %u.",
                        mqttStatus ) );
            cleanupOutgoingPublishAt( publishIndex );
            returnStatus = EXIT_FAILURE;
        }
        else
        {
            LogInfo( ( "PUBLISH sent for topic %.*s to broker with packet ID %u.\n\n",
                       topicLength,
                       pTopic,
                       outgoingPublishPackets[ publishIndex ].packetId ) );
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int subscribePublishLoop( NetworkContext_t * pNetworkContext )
{
    int returnStatus = EXIT_SUCCESS;
    bool mqttSessionEstablished = false, sessionPresent;
    MQTTContext_t mqttContext;
    MQTTStatus_t mqttStatus = MQTTSuccess;

    /* Establish MQTT session on top of TCP+TLS connection. */
    LogInfo( ( "Creating an MQTT connection to %.*s.",
               BROKER_ENDPOINT_LENGTH,
               BROKER_ENDPOINT ) );

    /* Sends an MQTT Connect packet using the established TLS session,
     * then waits for connection acknowledgment (CONNACK) packet. */
    returnStatus = establishMqttSession( &mqttContext, pNetworkContext, false, &sessionPresent );

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Keep a flag for indicating if MQTT session is established. This
         * flag will mark that an MQTT DISCONNECT has to be sent at the end
         * of the demo even if there are intermediate failures. */
        mqttSessionEstablished = true;
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Check if session is present and if there are any outgoing publishes
         * that need to resend. This is only valid if the broker is
         * re-establishing a session which was already present. */
        if( sessionPresent == true )
        {
            LogInfo( ( "An MQTT session with broker is re-established."
                       "Resending unacked publishes." ) );

            /* Handle all the resend of publish messages. */
            returnStatus = handlePublishResend( &mqttContext );
        }
        else
        {
            LogInfo( ( "A clean MQTT connection is established."
                       " Cleaning up all the stored outgoing publishes.\n\n" ) );

            /* Clean up the outgoing publishes waiting for ack as this new
             * connection doesn't re-establish an existing session. */
            cleanupOutgoingPublishes();
        }
    }

    /* Subscribe to a wildcard temperature topic filter so that we can receive incoming PUBLISH
     * messages from multiple topics from the broker. */
    if( returnStatus == EXIT_SUCCESS )
    {
        /* Register the subscription callback for the temperature topic filter, containing the
         * '+' wildcard character, so that the incoming PUBLISH messages from the broker for
         * both temperature topic types (for "high" and "low" topics) can be handled by the
         * callback. */
        ( void ) SubscriptionManager_RegisterCallback( DEMO_TEMPERATURE_TOPIC_FILTER,
                                                       DEMO_TEMPERATURE_TOPIC_FILTER_LENGTH,
                                                       temperatureDataCallback );

        /* The client is now connected to the broker. Subscribe to the topic
         * as specified in DEMO_TEMPERATURE_TOPIC_FILTER at the top of this file by sending a
         * subscribe packet. This client will then publish to the two temperature topics
         * specified at the top of the file, so it will expect all the messages it sends to
         * the broker to be sent back to it from the broker. The subscription manager would
         * then dispatch all messages from the temperature topics to the above registered
         * callback. This demo uses QOS1 in Subscribe, therefore, the Publish messages received
         * from the broker will have QOS1. */
        LogInfo( ( "Subscribing to the MQTT topic %.*s.",
                   DEMO_TEMPERATURE_TOPIC_FILTER_LENGTH,
                   DEMO_TEMPERATURE_TOPIC_FILTER ) );
        returnStatus = subscribeToTopic( &mqttContext,
                                         DEMO_TEMPERATURE_TOPIC_FILTER,
                                         DEMO_TEMPERATURE_TOPIC_FILTER_LENGTH );
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Process incoming packet from the broker. Acknowledgment for subscription
         * ( SUBACK ) will be received here. However after sending the subscribe, the
         * client may receive a publish before it receives a subscribe ack. Since this
         * demo is subscribing to the topic to which no one is publishing, probability
         * of receiving publish message before subscribe ack is zero; but application
         * must be ready to receive any packet. This demo uses MQTT_ProcessLoop to
         * receive packet from network. */
        mqttStatus = MQTT_ProcessLoop( &mqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );

        if( mqttStatus != MQTTSuccess )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "MQTT_ProcessLoop returned with status = %u.",
                        mqttStatus ) );

            /* Remove the registered callback for the temperature topic filter as
            * the subscription operation for the topic filter did not succeed. */
            ( void ) SubscriptionManager_RemoveCallback( DEMO_TEMPERATURE_TOPIC_FILTER,
                                                         DEMO_TEMPERATURE_TOPIC_FILTER_LENGTH );
        }
    }

    /* PUBLISH to the "high" temperature topic, so that the broker can send the PUBLISH message
     * back to us. The temperature callback should be invoked on receiving the message back
     * from the broker, as we have registered the callback on a wildcard topic filter for
     * temperature topics. */
    if( returnStatus == EXIT_SUCCESS )
    {
        /* Publish messages to all service topics so that broker will forward it back to us,
         * and cause registered callbacks to be invoked. */
        LogInfo( ( "Publishing to topic %s.",
                   DEMO_TEMPERATURE_HIGH_TOPIC ) );

        returnStatus = publishToTopic( &mqttContext,
                                       DEMO_TEMPERATURE_HIGH_TOPIC,
                                       DEMO_TEMPERATURE_HIGH_TOPIC_LENGTH,
                                       DEMO_TEMPERATURE_HIGH_MESSAGE );

        /* Calling MQTT_ProcessLoop to process incoming publish echo, since
         * application subscribed to the same topic the broker will send
         * publish message back to the application. This function also
         * sends ping request to broker if MQTT_KEEP_ALIVE_INTERVAL_SECONDS
         * has expired since the last MQTT packet sent and receive
         * ping responses. */
        mqttStatus = MQTT_ProcessLoop( &mqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );

        if( mqttStatus != MQTTSuccess )
        {
            LogWarn( ( "MQTT_ProcessLoop failed: Error = %s.",
                       MQTT_Status_strerror( mqttStatus ) ) );
        }

        /* The temperature callback should have been invoked for handling the incoming
         * PUBLISH message on the "high" temperature topic. */
        else if( globalReceivedHighTemperatureData != true )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "Registered callback was not invoked on sending a PUBLISH to "
                        "the high temperature topic: Topic=%s", DEMO_TEMPERATURE_HIGH_TOPIC ) );
        }
    }

    /* PUBLISH to the "low" temperature topic, so that the broker can send the PUBLISH message
     * back to us. The temperature callback should be invoked on receiving the message back
     * from the broker, as we have registered the callback on a wildcard topic filter for
     * temperature topics. */
    if( returnStatus == EXIT_SUCCESS )
    {
        /* Publish messages to all service topics so that broker will forward it back to us,
         * and cause registered callbacks to be invoked. */
        LogInfo( ( "Publishing to topic %s.",
                   DEMO_TEMPERATURE_LOW_TOPIC ) );

        returnStatus = publishToTopic( &mqttContext,
                                       DEMO_TEMPERATURE_LOW_TOPIC,
                                       DEMO_TEMPERATURE_LOW_TOPIC_LENGTH,
                                       DEMO_TEMPERATURE_LOW_MESSAGE );

        /* Calling MQTT_ProcessLoop to process incoming publish echo, since
         * application subscribed to the same topic the broker will send
         * publish message back to the application. This function also
         * sends ping request to broker if MQTT_KEEP_ALIVE_INTERVAL_SECONDS
         * has expired since the last MQTT packet sent and receive
         * ping responses. */
        mqttStatus = MQTT_ProcessLoop( &mqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );

        if( mqttStatus != MQTTSuccess )
        {
            LogWarn( ( "MQTT_ProcessLoop failed: Error = %s.",
                       MQTT_Status_strerror( mqttStatus ) ) );
        }

        /* The temperature callback should have been invoked for handling the incoming
         * PUBLISH message on the "low" temperature topic. */
        else if( globalReceivedLowTemperatureData != true )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "Registered callback was not invoked on sending a PUBLISH to "
                        "the low temperature topic: Topic=%s", DEMO_TEMPERATURE_LOW_TOPIC ) );
        }
    }

    /* Subscribe to a humidity topic filter, this time without any wildcard characters, so that we can
     * receive incoming PUBLISH message only on the same topic from the broker. */
    if( returnStatus == EXIT_SUCCESS )
    {
        /* Register subscription callback for the wildcard notification topic filter. */
        ( void ) SubscriptionManager_RegisterCallback( DEMO_HUMIDITY_TOPIC,
                                                       DEMO_HUMIDITY_TOPIC_LENGTH,
                                                       humidityDataCallback );

        /* The client is now connected to the broker. Subscribe to the humidity topic
        * by sending a subscribe packet. This client will then publish to the same topic it
        * subscribed to, so it will expect all the messages it sends to the broker
        * to be sent back to it from the broker. This demo uses QOS2 in Subscribe,
        * therefore, the Publish messages received from the broker will have QOS2. */
        LogInfo( ( "Subscribing to the MQTT topic %s.",
                   DEMO_HUMIDITY_TOPIC ) );
        returnStatus = subscribeToTopic( &mqttContext,
                                         DEMO_HUMIDITY_TOPIC,
                                         DEMO_HUMIDITY_TOPIC_LENGTH );
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Process incoming packet from the broker. Acknowledgment for subscription
         * ( SUBACK ) will be received here. However after sending the subscribe, the
         * client may receive a publish before it receives a subscribe ack. Since this
         * demo is subscribing to the topic to which no one is publishing, probability
         * of receiving publish message before subscribe ack is zero; but application
         * must be ready to receive any packet. This demo uses MQTT_ProcessLoop to
         * receive packet from network. */
        mqttStatus = MQTT_ProcessLoop( &mqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );

        if( mqttStatus != MQTTSuccess )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "MQTT_ProcessLoop returned with status = %u.",
                        mqttStatus ) );

            /* Remove registered callback for the notify wildcard topic filter. */
            ( void ) SubscriptionManager_RemoveCallback( DEMO_HUMIDITY_TOPIC,
                                                         strlen( DEMO_HUMIDITY_TOPIC ) );
        }
    }

    /* PUBLISH to the humidity topic, so that the broker can send the PUBLISH message
     * back to us. The humidity callback should be invoked on receiving the message back
     * from the broker, as we have registered the callback for the humidity topic filter. */
    if( returnStatus == EXIT_SUCCESS )
    {
        /* Publish messages to all service topics so that broker will forward it back to us,
         * and cause registered callbacks to be invoked.  */
        LogInfo( ( "Publish to topic %s.",
                   DEMO_HUMIDITY_TOPIC ) );

        returnStatus = publishToTopic( &mqttContext,
                                       DEMO_HUMIDITY_TOPIC,
                                       DEMO_HUMIDITY_TOPIC_LENGTH,
                                       DEMO_HUMIDITY_MESSAGE );

        /* Calling MQTT_ProcessLoop to process incoming publish echo, since
         * application subscribed to the same topic the broker will send
         * publish message back to the application. This function also
         * sends ping request to broker if MQTT_KEEP_ALIVE_INTERVAL_SECONDS
         * has expired since the last MQTT packet sent and receive
         * ping responses. */
        mqttStatus = MQTT_ProcessLoop( &mqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );

        if( mqttStatus != MQTTSuccess )
        {
            LogWarn( ( "MQTT_ProcessLoop failed: Error = %s.",
                       MQTT_Status_strerror( mqttStatus ) ) );
        }

        /* The humidity callback should have been invoked for handling the incoming
         * PUBLISH message on the humidity topic. */
        else if( globalReceivedHumidityData != true )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "Registered callback was not invoked on sending a PUBLISH to "
                        "the humidity topic: Topic=%s", DEMO_HUMIDITY_TOPIC ) );
        }
    }

    /* Subscribe to the precipitation topic filter, this time also without any wildcard characters,
     * so that we can receive incoming PUBLISH message only on the same topic from the broker. */
    if( returnStatus == EXIT_SUCCESS )
    {
        /* Register subscription callback for the wildcard notification topic filter. */
        ( void ) SubscriptionManager_RegisterCallback( DEMO_PRECIPITATION_TOPIC,
                                                       DEMO_PRECIPITATION_TOPIC_LENGTH,
                                                       precipitationDataCallback );

        /* The client is now connected to the broker. Subscribe to the precipitation topic
         * by sending a subscribe packet. This client will then publish to the same topic it
         * subscribed to, so it will expect all the messages it sends to the broker
         * to be sent back to it from the broker. This demo uses QOS2 in Subscribe,
         * therefore, the Publish messages received from the broker will have QOS2. */
        LogInfo( ( "Subscribing to the MQTT topic %s.",
                   DEMO_PRECIPITATION_TOPIC ) );
        returnStatus = subscribeToTopic( &mqttContext,
                                         DEMO_PRECIPITATION_TOPIC,
                                         DEMO_PRECIPITATION_TOPIC_LENGTH );
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Process incoming packet from the broker. Acknowledgment for subscription
         * ( SUBACK ) will be received here. However after sending the subscribe, the
         * client may receive a publish before it receives a subscribe ack. Since this
         * demo is subscribing to the topic to which no one is publishing, probability
         * of receiving publish message before subscribe ack is zero; but application
         * must be ready to receive any packet. This demo uses MQTT_ProcessLoop to
         * receive packet from network. */
        mqttStatus = MQTT_ProcessLoop( &mqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );

        if( mqttStatus != MQTTSuccess )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "MQTT_ProcessLoop returned with status = %u.",
                        mqttStatus ) );

            /* Remove registered callback for the notify wildcard topic filter. */
            ( void ) SubscriptionManager_RemoveCallback( DEMO_PRECIPITATION_TOPIC,
                                                         strlen( DEMO_PRECIPITATION_TOPIC ) );
        }
    }

    /* PUBLISH to the precipitation topic, so that the broker can send the PUBLISH message
     * back to us. The precipitation callback should be invoked on receiving the message back
     * from the broker, as we have registered the callback for the precipitation topic filter. */
    if( returnStatus == EXIT_SUCCESS )
    {
        /* Publish messages to all service topics so that broker will forward it back to us,
         * and cause registered callbacks to be invoked.  */
        LogInfo( ( "Publish to topic %s.",
                   DEMO_PRECIPITATION_TOPIC ) );

        returnStatus = publishToTopic( &mqttContext,
                                       DEMO_PRECIPITATION_TOPIC,
                                       DEMO_PRECIPITATION_TOPIC_LENGTH,
                                       DEMO_PRECIPITATION_MESSAGE );

        /* Calling MQTT_ProcessLoop to process incoming publish echo, since
         * application subscribed to the same topic the broker will send
         * publish message back to the application. This function also
         * sends ping request to broker if MQTT_KEEP_ALIVE_INTERVAL_SECONDS
         * has expired since the last MQTT packet sent and receive
         * ping responses. */
        mqttStatus = MQTT_ProcessLoop( &mqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );

        if( mqttStatus != MQTTSuccess )
        {
            LogWarn( ( "MQTT_ProcessLoop failed: Error = %s.",
                       MQTT_Status_strerror( mqttStatus ) ) );
        }

        /* The precipitation callback should have been invoked for handling the incoming
         * PUBLISH message on the precipitation topic. */
        else if( globalReceivedPrecipitationData != true )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "Registered callback was not invoked on sending a PUBLISH to "
                        "the precipitation topic: Topic=%s", DEMO_PRECIPITATION_TOPIC ) );
        }
    }

    /* As we don't have any further PUBLISH/SUBSCRIBE operations in the loop iteration further
     * we will perform clean-up operations of removing the subscription callbacks registrations,
     * and unsubscribing from the temperature and humidity topic filters.*/

    /* Remove all callbacks from the subscription manager. */
    if( returnStatus == EXIT_SUCCESS )
    {
        /* Remove the callback for temperature topics. */
        SubscriptionManager_RemoveCallback( DEMO_TEMPERATURE_TOPIC_FILTER,
                                            DEMO_TEMPERATURE_TOPIC_FILTER_LENGTH );

        /* Remove the callback for the humidity topic filter. */
        SubscriptionManager_RemoveCallback( DEMO_HUMIDITY_TOPIC,
                                            DEMO_HUMIDITY_TOPIC_LENGTH );

        /* Remove the callback for the precipitation topic filter. */
        SubscriptionManager_RemoveCallback( DEMO_PRECIPITATION_TOPIC,
                                            DEMO_PRECIPITATION_TOPIC_LENGTH );

        /* Unsubscribe from the temperature topic filter. */
        LogInfo( ( "Unsubscribing from the MQTT temperature topic filter: %.*s.",
                   DEMO_TEMPERATURE_TOPIC_FILTER_LENGTH,
                   DEMO_TEMPERATURE_TOPIC_FILTER ) );
        returnStatus = unsubscribeFromTopic( &mqttContext,
                                             DEMO_TEMPERATURE_TOPIC_FILTER,
                                             DEMO_TEMPERATURE_TOPIC_FILTER_LENGTH );
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Process Incoming UNSUBACK packet from the broker. */
        mqttStatus = MQTT_ProcessLoop( &mqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );

        if( mqttStatus != MQTTSuccess )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "MQTT_ProcessLoop returned with status = %u.",
                        mqttStatus ) );
        }
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Unsubscribe from the humidity topic. */
        LogInfo( ( "Unsubscribing from the MQTT humidity topic filter %s.",
                   DEMO_HUMIDITY_TOPIC ) );
        returnStatus = unsubscribeFromTopic( &mqttContext,
                                             DEMO_HUMIDITY_TOPIC,
                                             DEMO_HUMIDITY_TOPIC_LENGTH );
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Process Incoming UNSUBACK packet from the broker. */
        mqttStatus = MQTT_ProcessLoop( &mqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );

        if( mqttStatus != MQTTSuccess )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "MQTT_ProcessLoop returned with status = %u.",
                        mqttStatus ) );
        }
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Unsubscribe from the precipitation topic filter. */
        LogInfo( ( "Unsubscribing from the MQTT precipitation topic filter %s.",
                   DEMO_PRECIPITATION_TOPIC ) );
        returnStatus = unsubscribeFromTopic( &mqttContext,
                                             DEMO_PRECIPITATION_TOPIC,
                                             DEMO_PRECIPITATION_TOPIC_LENGTH );
    }

    if( returnStatus == EXIT_SUCCESS )
    {
        /* Process Incoming UNSUBACK packet from the broker. */
        mqttStatus = MQTT_ProcessLoop( &mqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );

        if( mqttStatus != MQTTSuccess )
        {
            returnStatus = EXIT_FAILURE;
            LogError( ( "MQTT_ProcessLoop returned with status = %u.",
                        mqttStatus ) );
        }
    }

    /* Send an MQTT Disconnect packet over the already connected TCP socket.
     * There is no corresponding response for the disconnect packet. After sending
     * disconnect, client must close the network connection. */
    if( mqttSessionEstablished == true )
    {
        LogInfo( ( "Disconnecting the MQTT connection with %.*s.",
                   BROKER_ENDPOINT_LENGTH,
                   BROKER_ENDPOINT ) );

        if( returnStatus == EXIT_FAILURE )
        {
            /* Returned status is not used to update the local status as there
             * were failures in demo execution. */
            ( void ) disconnectMqttSession( &mqttContext );
        }
        else
        {
            returnStatus = disconnectMqttSession( &mqttContext );
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

/**
 * @brief Entry point of demo.
 *
 * The example shown below uses MQTT APIs to send and receive MQTT packets
 * over the TLS connection established using OpenSSL.
 *
 * The example is single threaded and uses statically allocated memory;
 * it uses QOS2 and therefore implements a retransmission mechanism
 * for Publish messages. Retransmission of publish messages are attempted
 * when a MQTT connection is established with a session that was already
 * present. All the outgoing publish messages waiting to receive PUBREC
 * are resent in this demo. In order to support retransmission all the outgoing
 * publishes are stored until a PUBREC is received.
 */
int main( int argc,
          char ** argv )
{
    int returnStatus = EXIT_SUCCESS;
    NetworkContext_t networkContext;

    ( void ) argc;
    ( void ) argv;

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
                        BROKER_ENDPOINT_LENGTH,
                        BROKER_ENDPOINT ) );
        }
        else
        {
            /* If TLS session is established, execute Subscribe/Publish loop. */
            returnStatus = subscribePublishLoop( &networkContext );
        }

        if( returnStatus == EXIT_SUCCESS )
        {
            /* Log message indicating an iteration completed successfully. */
            LogInfo( ( "Demo completed successfully." ) );
        }

        /* End TLS session, then close TCP connection. */
        ( void ) Openssl_Disconnect( &networkContext );

        LogInfo( ( "Short delay before starting the next iteration ....\n " ) );
        sleep( MQTT_SUBPUB_LOOP_DELAY_SECONDS );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

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
 * Demo for showing the use of MQTT APIs to establish an MQTT session,
 * subscribe to a topic, publish to a topic, receive incoming publishes,
 * unsubscribe from a topic and disconnect the MQTT session.
 *
 * The example is single threaded and uses statically allocated memory;
 * it uses QOS1 and therefore implements a retransmission mechanism
 * for Publish messages. Retransmission of publish messages are attempted
 * when a MQTT connection is established with a session that was already
 * present. All the outgoing publish messages waiting to receive PUBACK
 * are resend in this demo. In order to support retransmission all the outgoing
 * publishes are stored until a PUBACK is received.
 */

/**
 * @file mqtt_demo_subscription_manager.c
 * @brief MQTT Demo application that showcases multiplexing of the same MQTT connection
 * across multiple topic subscriptions using a subscription manager.
 */

/* Standard includes. */
#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* POSIX includes. */
#include <unistd.h>

/* Include Demo Config as the first non-system header. */
#include "demo_config.h"

/* MQTT API headers. */
#include "core_mqtt.h"
#include "core_mqtt_state.h"

/* OpenSSL sockets transport implementation. */
#include "openssl_posix.h"

/*Include backoff algorithm header for retry logic.*/
#include "backoff_algorithm.h"

/* Clock for timer. */
#include "clock.h"

/* Include subscription manager. */
#include "mqtt_subscription_manager.h"

/**
 * These configuration settings are required to run the basic TLS demo.
 * Throw compilation error if the below configs are not defined.
 */
#ifndef BROKER_ENDPOINT
    #error "Please define an MQTT broker endpoint, BROKER_ENDPOINT, in demo_config.h."
#endif
#ifndef ROOT_CA_CERT_PATH
    #error "Please define path to Root CA certificate of the MQTT broker, ROOT_CA_CERT_PATH, in demo_config.h."
#endif
#ifndef CLIENT_IDENTIFIER
    #error "Please define a unique CLIENT_IDENTIFIER."
#endif

/**
 * @brief Length of MQTT server host name.
 */
#define BROKER_ENDPOINT_LENGTH      ( ( uint16_t ) ( sizeof( BROKER_ENDPOINT ) - 1 ) )

/**
 * @brief Length of path to server certificate.
 */
#define ROOT_CA_CERT_PATH_LENGTH    ( ( uint16_t ) ( sizeof( ROOT_CA_CERT_PATH ) - 1 ) )

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
#define CLIENT_IDENTIFIER_LENGTH                 ( ( uint16_t ) ( sizeof( CLIENT_IDENTIFIER ) - 1 ) )

/**
 * @brief The maximum number of retries for connecting to server.
 */
#define CONNECTION_RETRY_MAX_ATTEMPTS            ( 5U )

/**
 * @brief The maximum back-off delay (in milliseconds) for retrying connection to server.
 */
#define CONNECTION_RETRY_MAX_BACKOFF_DELAY_MS    ( 5000U )

/**
 * @brief The base back-off delay (in milliseconds) to use for connection retry attempts.
 */
#define CONNECTION_RETRY_BACKOFF_BASE_MS         ( 500U )


/**
 * @brief Timeout for receiving CONNACK packet in milli seconds.
 */
#define CONNACK_RECV_TIMEOUT_MS                 ( 1000U )

/**
 * @brief The MQTT topic filter to subscribe to for temperature data in the demo.
 */
#define DEMO_TEMPERATURE_TOPIC_FILTER           CLIENT_IDENTIFIER "/demo/temperature/+"

/**
 * @brief The length of the temperature topic filter.
 */
#define DEMO_TEMPERATURE_TOPIC_FILTER_LENGTH    ( ( uint16_t ) ( sizeof( DEMO_TEMPERATURE_TOPIC_FILTER ) - 1U ) )

/**
 * @brief The MQTT topic for the high temperature data value that the demo will
 * publish to.
 */
#define DEMO_TEMPERATURE_HIGH_TOPIC             CLIENT_IDENTIFIER "/demo/temperature/high"

/**
 * @brief The length of the high temperature topic name.
 */
#define DEMO_TEMPERATURE_HIGH_TOPIC_LENGTH      ( ( uint16_t ) ( sizeof( DEMO_TEMPERATURE_HIGH_TOPIC ) - 1U ) )

/**
 * @brief The MQTT topic for the high temperature data value that the demo will
 * publish to.
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
 * @brief Timeout for MQTT_ProcessLoop function in milliseconds.
 */
#define MQTT_PROCESS_LOOP_TIMEOUT_MS            ( 500U )

/**
 * @brief The maximum time interval in seconds which is allowed to elapse
 * between two Control Packets.
 *
 * It is the responsibility of the Client to ensure that the interval between
 * Control Packets being sent does not exceed the this Keep Alive value. In the
 * absence of sending any other Control Packets, the Client MUST send a
 * PINGREQ Packet.
 */
#define MQTT_KEEP_ALIVE_INTERVAL_SECONDS        ( 60U )

/**
 * @brief Delay in seconds between two iterations of subscribePublishLoop().
 */
#define MQTT_SUBPUB_LOOP_DELAY_SECONDS          ( 5U )

/**
 * @brief Transport timeout in milliseconds for transport send and receive.
 */
#define TRANSPORT_SEND_RECV_TIMEOUT_MS          ( 1000 )

/**
 * @brief The length of the outgoing publish records array used by the coreMQTT
 * library to track QoS > 0 packet ACKS for outgoing publishes.
 */
#define OUTGOING_PUBLISH_RECORD_LEN             ( 10U )

/**
 * @brief The length of the incoming publish records array used by the coreMQTT
 * library to track QoS > 0 packet ACKS for incoming publishes.
 */
#define INCOMING_PUBLISH_RECORD_LEN             ( 10U )

/*-----------------------------------------------------------*/

/**
 * @brief Structure to keep the MQTT publish packets until an ack is received
 * for QoS1 publishes.
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
 * @brief Packet Identifier updated when an ACK packet is received.
 *
 * It is used to match an expected ACK for a transmitted packet.
 */
static uint16_t globalAckPacketIdentifier = 0U;

/**
 * @brief Packet Identifier generated when Subscribe request was sent to the broker;
 * it is used to match received Subscribe ACK to the transmitted subscribe.
 */
static uint16_t lastSubscribePacketIdentifier = 0U;

/**
 * @brief Packet Identifier generated when Unsubscribe request was sent to the broker;
 * it is used to match received Unsubscribe ACK to the transmitted unsubscribe
 * request.
 */
static uint16_t lastUnsubscribePacketIdentifier = 0U;

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

/* Each compilation unit must define the NetworkContext struct. */
struct NetworkContext
{
    OpensslParams_t * pParams;
};

/*-----------------------------------------------------------*/

/**
 * @brief The random number generator to use for exponential backoff with
 * jitter retry logic.
 *
 * @return The generated random number.
 */
static uint32_t generateRandomNumber();

/**
 * @brief Connect to MQTT broker with reconnection retries.
 *
 * If connection fails, retry is attempted after a back-off period.
 * The back-off period will exponentially increase until either the maximum
 * back-off period is reached or the number of attempts are exhausted.
 *
 * @param[out] pNetworkContext The output parameter to return the created network context.
 * @param[out] pMqttContext The output to return the created MQTT context.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on successful connection.
 */
static int connectToServerWithBackoffRetries( NetworkContext_t * pNetworkContext,
                                              MQTTContext_t * pMqttContext );

/**
 * @brief A function that uses the passed MQTT connection to
 * subscribe to a topic, publish to the same topic
 * MQTT_PUBLISH_COUNT_PER_LOOP number of times, and verify if it
 * receives the Publish message back.
 *
 * @param[in] pMqttContext MQTT context pointer.
 *
 * @return EXIT_FAILURE on failure; EXIT_SUCCESS on success.
 */
static int subscribePublishLoop( MQTTContext_t * pMqttContext );

/**
 * @brief The function to handle the incoming publishes.
 *
 * @param[in] pPublishInfo Pointer to publish info of the incoming publish.
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
 * @brief Subscribes to the passed topic filter by sending an MQTT SUBSCRIBE
 * packet and waiting for a SUBACK acknowledgement response from the broker.
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
 * @brief Utility to subscribe to the passed topic filter and register
 * a callback for it in the subscription manager.
 *
 * The registered callback will be invoked by the subscription manager
 * when PUBLISH messages on topic(s) that match the registered topic filter
 * are received from the broker.
 *
 * @param[in] pContext The MQTT context representing the MQTT connection.
 * @param[in] pTopicFilter The topic filter to subscribe to and register a
 * callback for in the subscription manager.
 * @param[in] topicFilterLength The length of the topic filter, @p pTopicFilter.
 * @param[in] callback The callback to register for the topic filter with the
 * subscription manager.
 *
 * @return EXIT_SUCCESS if subscription and callback registration operations
 * for the topic filter were successfully; EXIT_FAILURE otherwise.
 */
static int subscribeToAndRegisterTopicFilter( MQTTContext_t * pContext,
                                              const char * pTopicFilter,
                                              uint16_t topicFilterLength,
                                              SubscriptionManagerCallback_t callback );

/**
 * @brief Unsubscribe from the passed topic filters by sending
 * a single MQTT UNSUBSCRIBE packet to the broker and waiting for
 * an acknowledgement response with UNSUBACK packet.
 *
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] pTopicFilters The list of topic filter to unsubscribe from.
 * @param[in] numOfTopicFilters The number of topic filters in the list.
 *
 * @return EXIT_SUCCESS if UNSUBSCRIBE was successfully sent;
 * EXIT_FAILURE otherwise.
 */
static int unsubscribeFromTopicFilters( MQTTContext_t * pMqttContext,
                                        const MQTTSubscribeInfo_t * pTopicFilters,
                                        size_t numOfTopicFilters );

/**
 * @brief Sends an MQTT PUBLISH to the passed topic
 * with the passed message and waits for acknowledgement response
 * from the broker. Also, this function processes an incoming PUBLISH
 * packet of the same message that the broker should send back to us.
 *
 * As this demo subscribes to topic filters that match the topics
 * that it publishes to, the broker should send back to us the same
 * message that we publish to it.
 *
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] pTopic The topic on which to send a PUBLISH message.
 * @param[in] topicLength The length of the topic.
 * @param[in] pMessage The message payload to PUBLISH.
 *
 * @return EXIT_SUCCESS if PUBLISH was successfully sent and processing
 * of incoming PUBLISH was successful; EXIT_FAILURE otherwise.
 */
static int publishToTopicAndProcessIncomingMessage( MQTTContext_t * pMqttContext,
                                                    const char * pTopic,
                                                    uint16_t topicLength,
                                                    const char * pMessage );

/**
 * @brief Wait for an expected ACK packet to be received.
 *
 * This function handles waiting for an expected ACK packet by calling
 * #MQTT_ProcessLoop and waiting for #mqttCallback to set the global ACK
 * packet identifier to the expected ACK packet identifier.
 *
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] usPacketIdentifier Packet identifier for expected ACK packet.
 * @param[in] ulTimeout Maximum duration to wait for expected ACK packet.
 *
 * @return true if the expected ACK packet was received, false otherwise.
 */
static int waitForPacketAck( MQTTContext_t * pMqttContext,
                             uint16_t usPacketIdentifier,
                             uint32_t ulTimeout );

/**
 * @brief Call #MQTT_ProcessLoop in a loop for the duration of a timeout or
 * #MQTT_ProcessLoop returns a failure.
 *
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] ulTimeoutMs Duration to call #MQTT_ProcessLoop for.
 *
 * @return Returns the return value of the last call to #MQTT_ProcessLoop.
 */
static MQTTStatus_t processLoopWithTimeout( MQTTContext_t * pMqttContext,
                                            uint32_t ulTimeoutMs );

/*-----------------------------------------------------------*/

static uint32_t generateRandomNumber()
{
    return( rand() );
}

/*-----------------------------------------------------------*/
static int connectToServerWithBackoffRetries( NetworkContext_t * pNetworkContext,
                                              MQTTContext_t * pMqttContext )
{
    int returnStatus = EXIT_FAILURE;
    BackoffAlgorithmStatus_t backoffAlgStatus = BackoffAlgorithmSuccess;
    OpensslStatus_t opensslStatus = OPENSSL_SUCCESS;
    BackoffAlgorithmContext_t reconnectParams;
    ServerInfo_t serverInfo;
    OpensslCredentials_t opensslCredentials;
    uint16_t nextRetryBackOff;
    struct timespec tp;
    bool sessionPresent = false;

    /* Initialize information to connect to the MQTT broker. */
    serverInfo.pHostName = BROKER_ENDPOINT;
    serverInfo.hostNameLength = BROKER_ENDPOINT_LENGTH;
    serverInfo.port = BROKER_PORT;

    /* Initialize credentials for establishing TLS session. */
    memset( &opensslCredentials, 0, sizeof( OpensslCredentials_t ) );
    opensslCredentials.pRootCaPath = ROOT_CA_CERT_PATH;
    opensslCredentials.sniHostName = BROKER_ENDPOINT;

    /* Seed pseudo random number generator used in the demo for
     * backoff period calculation when retrying failed network operations
     * with broker. */

    /* Get current time to seed pseudo random number generator. */
    ( void ) clock_gettime( CLOCK_REALTIME, &tp );
    /* Seed pseudo random number generator with nanoseconds. */
    srand( tp.tv_nsec );


    /* Initialize reconnect attempts and interval. */
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
         * to the MQTT broker as specified in BROKER_ENDPOINT and AWS_MQTT_PORT at
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

        if( opensslStatus == OPENSSL_SUCCESS )
        {
            /* Establish MQTT session on top of TCP+TLS connection. */
            LogInfo( ( "Creating an MQTT connection to %.*s.",
                       BROKER_ENDPOINT_LENGTH,
                       BROKER_ENDPOINT ) );

            /* Sends an MQTT Connect packet to establish a clean connection over the
             * established TLS session, then waits for connection acknowledgment
             * (CONNACK) packet. */
            returnStatus = establishMqttSession( pMqttContext,
                                                 pNetworkContext,
                                                 true, /* clean session */
                                                 &sessionPresent );

            if( returnStatus == EXIT_FAILURE )
            {
                /* End TLS session, then close TCP connection. */
                ( void ) Openssl_Disconnect( pNetworkContext );
            }
            else
            {
                /* As we requested a clean session with the MQTT broker, the broker
                 * should have sent the acknowledgement packet (CONNACK) with the
                 * session present bit set to 0. */
                assert( sessionPresent == false );
            }
        }

        if( returnStatus == EXIT_FAILURE )
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
    } while( ( returnStatus == EXIT_FAILURE ) && ( backoffAlgStatus == BackoffAlgorithmSuccess ) );

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

    /* Suppress unused parameter warning when asserts are disabled in build. */
    ( void ) pContext;

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

    /* Suppress unused parameter warning when asserts are disabled in build. */
    ( void ) pContext;

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

    /* Suppress unused parameter warning when asserts are disabled in build. */
    ( void ) pContext;

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
                assert( lastSubscribePacketIdentifier == pDeserializedInfo->packetIdentifier );

                /* Update the global ACK packet identifier. */
                globalAckPacketIdentifier = pDeserializedInfo->packetIdentifier;
                break;

            case MQTT_PACKET_TYPE_UNSUBACK:
                LogInfo( ( "Received UNSUBACK.\n\n" ) );
                /* Make sure ACK packet identifier matches with Request packet identifier. */
                assert( lastUnsubscribePacketIdentifier == pDeserializedInfo->packetIdentifier );

                /* Update the global ACK packet identifier. */
                globalAckPacketIdentifier = pDeserializedInfo->packetIdentifier;
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

                /* Update the global ACK packet identifier. */
                globalAckPacketIdentifier = pDeserializedInfo->packetIdentifier;
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
    transport.writev = NULL;

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
        LogError( ( "MQTT disconnect failed: Error=%s",
                    MQTT_Status_strerror( mqttStatus ) ) );
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

    /* This demo subscribes and publishes to topics at Qos1, so the publish
     * messages received from the broker should have QoS1 as well. */
    pSubscriptionList[ 0 ].qos = MQTTQoS1;
    pSubscriptionList[ 0 ].pTopicFilter = pTopicFilter;
    pSubscriptionList[ 0 ].topicFilterLength = topicFilterLength;

    /* Generate packet identifier for the SUBSCRIBE packet. */
    lastSubscribePacketIdentifier = MQTT_GetPacketId( pMqttContext );

    /* Send SUBSCRIBE packet. */
    mqttStatus = MQTT_Subscribe( pMqttContext,
                                 pSubscriptionList,
                                 sizeof( pSubscriptionList ) / sizeof( MQTTSubscribeInfo_t ),
                                 lastSubscribePacketIdentifier );

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

        /* Wait for acknowledgement packet (SUBACK) from the broker in response to the
         * subscribe request. */
        returnStatus = waitForPacketAck( pMqttContext,
                                         lastSubscribePacketIdentifier,
                                         MQTT_PROCESS_LOOP_TIMEOUT_MS );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int subscribeToAndRegisterTopicFilter( MQTTContext_t * pContext,
                                              const char * pTopicFilter,
                                              uint16_t topicFilterLength,
                                              SubscriptionManagerCallback_t callback )
{
    int returnStatus = EXIT_SUCCESS;
    SubscriptionManagerStatus_t managerStatus = ( SubscriptionManagerStatus_t ) 0u;

    /* Register the topic filter and its callback with subscription manager.
     * On an incoming PUBLISH message whose topic name that matches the topic filter
     * being registered, its callback will be invoked. */
    managerStatus = SubscriptionManager_RegisterCallback( pTopicFilter,
                                                          topicFilterLength,
                                                          callback );

    if( managerStatus != SUBSCRIPTION_MANAGER_SUCCESS )
    {
        returnStatus = EXIT_FAILURE;
    }
    else
    {
        LogInfo( ( "Subscribing to the MQTT topic %.*s.",
                   topicFilterLength,
                   pTopicFilter ) );

        returnStatus = subscribeToTopic( pContext,
                                         pTopicFilter,
                                         topicFilterLength );
    }

    if( returnStatus != EXIT_SUCCESS )
    {
        /* Remove the registered callback for the temperature topic filter as
        * the subscription operation for the topic filter did not succeed. */
        ( void ) SubscriptionManager_RemoveCallback( pTopicFilter,
                                                     topicFilterLength );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int unsubscribeFromTopicFilters( MQTTContext_t * pMqttContext,
                                        const MQTTSubscribeInfo_t * pTopicFilters,
                                        size_t numOfTopicFilters )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTStatus_t mqttStatus;
    size_t index = 0U;

    /* Generate packet identifier for the UNSUBSCRIBE packet. */
    lastUnsubscribePacketIdentifier = MQTT_GetPacketId( pMqttContext );

    /* Send UNSUBSCRIBE packet. */
    mqttStatus = MQTT_Unsubscribe( pMqttContext,
                                   pTopicFilters,
                                   numOfTopicFilters,
                                   lastUnsubscribePacketIdentifier );

    if( mqttStatus != MQTTSuccess )
    {
        LogError( ( "Failed to send UNSUBSCRIBE packet to broker. Error=%s.",
                    MQTT_Status_strerror( mqttStatus ) ) );
        returnStatus = EXIT_FAILURE;
    }
    else
    {
        LogInfo( ( "UNSUBSCRIBE sent for the following topic filter(s)" ) );

        for( index = 0U; index < numOfTopicFilters; index++ )
        {
            LogInfo( ( "%.*s",
                       pTopicFilters[ index ].topicFilterLength,
                       pTopicFilters[ index ].pTopicFilter ) );
        }

        /* Process Incoming UNSUBACK packet from the broker. */
        returnStatus = waitForPacketAck( pMqttContext,
                                         lastUnsubscribePacketIdentifier,
                                         MQTT_PROCESS_LOOP_TIMEOUT_MS );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int publishToTopicAndProcessIncomingMessage( MQTTContext_t * pMqttContext,
                                                    const char * pTopic,
                                                    uint16_t topicLength,
                                                    const char * pMessage )
{
    int returnStatus = EXIT_SUCCESS;

    MQTTStatus_t mqttStatus = MQTTSuccess;
    MQTTPublishInfo_t publishInfo;
    uint16_t pubPacketId = MQTT_PACKET_ID_INVALID;

    assert( pMqttContext != NULL );

    ( void ) memset( &publishInfo, 0x00, sizeof( MQTTPublishInfo_t ) );

    if( returnStatus == EXIT_FAILURE )
    {
        LogError( ( "Unable to find a free spot for outgoing PUBLISH message.\n\n" ) );
    }
    else
    {
        /* This example publishes with QOS1. */
        publishInfo.qos = MQTTQoS1;
        publishInfo.pTopicName = pTopic;
        publishInfo.topicNameLength = topicLength;
        publishInfo.pPayload = pMessage;
        publishInfo.payloadLength = strlen( pMessage );

        /* Get a new packet ID for the publish. */
        pubPacketId = MQTT_GetPacketId( pMqttContext );

        /* Send PUBLISH packet. */
        mqttStatus = MQTT_Publish( pMqttContext,
                                   &publishInfo,
                                   pubPacketId );

        if( mqttStatus != MQTTSuccess )
        {
            LogError( ( "Failed to send PUBLISH packet to broker with error = %u.",
                        mqttStatus ) );
            returnStatus = EXIT_FAILURE;
        }
        else
        {
            LogInfo( ( "PUBLISH sent for topic %.*s to broker with packet ID %u.\n\n",
                       topicLength,
                       pTopic,
                       pubPacketId ) );

            /* Calling MQTT_ProcessLoop to process incoming publish echo, since
             * application subscribed to the same topic the broker will send
             * publish message back to the application. This function also
             * sends ping request to broker if MQTT_KEEP_ALIVE_INTERVAL_SECONDS
             * has expired since the last MQTT packet sent and receive
             * ping responses. */
            mqttStatus = processLoopWithTimeout( pMqttContext, MQTT_PROCESS_LOOP_TIMEOUT_MS );

            if( ( mqttStatus != MQTTSuccess ) && ( mqttStatus != MQTTNeedMoreBytes ) )
            {
                LogWarn( ( "MQTT_ProcessLoop failed: Error = %s.",
                           MQTT_Status_strerror( mqttStatus ) ) );
            }
        }
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int subscribePublishLoop( MQTTContext_t * pMqttContext )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTSubscribeInfo_t pSubscriptionList[ 3 ];

    /* Subscribe to a wildcard temperature topic filter so that we can receive incoming PUBLISH
     * messages from multiple topics from the broker. */
    if( returnStatus == EXIT_SUCCESS )
    {
        /* Register the subscription callback for the temperature topic filter, containing the
         * '+' wildcard character, so that the incoming PUBLISH messages from the broker for
         * both temperature topic types (for "high" and "low" topics) can be handled by the
         * callback. */
        returnStatus = subscribeToAndRegisterTopicFilter( pMqttContext,
                                                          DEMO_TEMPERATURE_TOPIC_FILTER,
                                                          DEMO_TEMPERATURE_TOPIC_FILTER_LENGTH,
                                                          temperatureDataCallback );
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

        returnStatus = publishToTopicAndProcessIncomingMessage( pMqttContext,
                                                                DEMO_TEMPERATURE_HIGH_TOPIC,
                                                                DEMO_TEMPERATURE_HIGH_TOPIC_LENGTH,
                                                                DEMO_TEMPERATURE_HIGH_MESSAGE );
    }

    /* The temperature callback should have been invoked for handling the incoming
     * PUBLISH message on the "high" temperature topic. */
    if( returnStatus == EXIT_SUCCESS )
    {
        if( globalReceivedHighTemperatureData != true )
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

        returnStatus = publishToTopicAndProcessIncomingMessage( pMqttContext,
                                                                DEMO_TEMPERATURE_LOW_TOPIC,
                                                                DEMO_TEMPERATURE_LOW_TOPIC_LENGTH,
                                                                DEMO_TEMPERATURE_LOW_MESSAGE );
    }

    /* The temperature callback should have been invoked for handling the incoming
     * PUBLISH message on the "low" temperature topic. */
    if( returnStatus == EXIT_SUCCESS )
    {
        if( globalReceivedLowTemperatureData != true )
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
        returnStatus = subscribeToAndRegisterTopicFilter( pMqttContext,
                                                          DEMO_HUMIDITY_TOPIC,
                                                          DEMO_HUMIDITY_TOPIC_LENGTH,
                                                          humidityDataCallback );
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

        returnStatus = publishToTopicAndProcessIncomingMessage( pMqttContext,
                                                                DEMO_HUMIDITY_TOPIC,
                                                                DEMO_HUMIDITY_TOPIC_LENGTH,
                                                                DEMO_HUMIDITY_MESSAGE );
    }

    /* The humidity callback should have been invoked for handling the incoming
     * PUBLISH message on the humidity topic. */
    if( returnStatus == EXIT_SUCCESS )
    {
        if( globalReceivedHumidityData != true )
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
        returnStatus = subscribeToAndRegisterTopicFilter( pMqttContext,
                                                          DEMO_PRECIPITATION_TOPIC,
                                                          DEMO_PRECIPITATION_TOPIC_LENGTH,
                                                          precipitationDataCallback );
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

        returnStatus = publishToTopicAndProcessIncomingMessage( pMqttContext,
                                                                DEMO_PRECIPITATION_TOPIC,
                                                                DEMO_PRECIPITATION_TOPIC_LENGTH,
                                                                DEMO_PRECIPITATION_MESSAGE );
    }

    /* The precipitation callback should have been invoked for handling the incoming
     * PUBLISH message on the precipitation topic. */
    if( returnStatus == EXIT_SUCCESS )
    {
        if( globalReceivedPrecipitationData != true )
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

        /* Set the subscription list memory to zero . */
        ( void ) memset( ( void * ) pSubscriptionList, 0x00, sizeof( pSubscriptionList ) );

        /* Populate the array with topic filters to unsubscribe from.
         * We will use a single UNSUBSCRIBE packet to unsubscribe from all
         * topic filters. */
        pSubscriptionList[ 0 ].pTopicFilter = DEMO_TEMPERATURE_TOPIC_FILTER;
        pSubscriptionList[ 0 ].topicFilterLength = DEMO_TEMPERATURE_TOPIC_FILTER_LENGTH;
        pSubscriptionList[ 1 ].pTopicFilter = DEMO_HUMIDITY_TOPIC;
        pSubscriptionList[ 1 ].topicFilterLength = DEMO_HUMIDITY_TOPIC_LENGTH;
        pSubscriptionList[ 2 ].pTopicFilter = DEMO_PRECIPITATION_TOPIC;
        pSubscriptionList[ 2 ].topicFilterLength = DEMO_PRECIPITATION_TOPIC_LENGTH;

        /* Unsubscribe from all topic filters of temperature, humidity and
         * precipitation data. */
        returnStatus = unsubscribeFromTopicFilters( pMqttContext,
                                                    pSubscriptionList,
                                                    sizeof( pSubscriptionList )
                                                    / sizeof( MQTTSubscribeInfo_t ) );
    }

    /* Send an MQTT Disconnect packet over the already connected TCP socket.
     * There is no corresponding response for the disconnect packet. After sending
     * disconnect, client must close the network connection. */
    LogInfo( ( "Disconnecting the MQTT connection with %.*s.",
               BROKER_ENDPOINT_LENGTH,
               BROKER_ENDPOINT ) );

    if( returnStatus == EXIT_FAILURE )
    {
        /* Returned status is not used to update the local status as there
         * were failures in demo execution. */
        ( void ) disconnectMqttSession( pMqttContext );
    }
    else
    {
        returnStatus = disconnectMqttSession( pMqttContext );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

static int waitForPacketAck( MQTTContext_t * pMqttContext,
                             uint16_t usPacketIdentifier,
                             uint32_t ulTimeout )
{
    uint32_t ulMqttProcessLoopEntryTime;
    uint32_t ulMqttProcessLoopTimeoutTime;
    uint32_t ulCurrentTime;

    MQTTStatus_t eMqttStatus = MQTTSuccess;
    int returnStatus = EXIT_FAILURE;

    /* Reset the ACK packet identifier being received. */
    globalAckPacketIdentifier = 0U;

    ulCurrentTime = pMqttContext->getTime();
    ulMqttProcessLoopEntryTime = ulCurrentTime;
    ulMqttProcessLoopTimeoutTime = ulCurrentTime + ulTimeout;

    /* Call MQTT_ProcessLoop multiple times until the expected packet ACK
     * is received, a timeout happens, or MQTT_ProcessLoop fails. */
    while( ( globalAckPacketIdentifier != usPacketIdentifier ) &&
           ( ulCurrentTime < ulMqttProcessLoopTimeoutTime ) &&
           ( eMqttStatus == MQTTSuccess || eMqttStatus == MQTTNeedMoreBytes ) )
    {
        /* Event callback will set #globalAckPacketIdentifier when receiving
         * appropriate packet. */
        eMqttStatus = MQTT_ProcessLoop( pMqttContext );
        ulCurrentTime = pMqttContext->getTime();
    }

    if( ( ( eMqttStatus != MQTTSuccess ) && ( eMqttStatus != MQTTNeedMoreBytes ) ) ||
        ( globalAckPacketIdentifier != usPacketIdentifier ) )
    {
        LogError( ( "MQTT_ProcessLoop failed to receive ACK packet: Expected ACK Packet ID=%02X, LoopDuration=%u, Status=%s",
                    usPacketIdentifier,
                    ( ulCurrentTime - ulMqttProcessLoopEntryTime ),
                    MQTT_Status_strerror( eMqttStatus ) ) );
    }
    else
    {
        returnStatus = EXIT_SUCCESS;
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

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

    return eMqttStatus;
}

/*-----------------------------------------------------------*/

/**
 * @brief Entry point of demo.
 *
 * The example shown below uses MQTT APIs to send and receive MQTT packets
 * over the TLS connection established using OpenSSL.
 *
 * The example is single threaded, uses statically allocated memory, and
 * uses QOS1 for publishing messages to the broker.
 */
int main( int argc,
          char ** argv )
{
    int returnStatus = EXIT_SUCCESS;
    MQTTContext_t mqttContext = { 0 };
    NetworkContext_t networkContext;
    OpensslParams_t opensslParams;

    ( void ) argc;
    ( void ) argv;

    /* Set the pParams member of the network context with desired transport. */
    networkContext.pParams = &opensslParams;

    for( ; ; )
    {
        /* Attempt to connect to the MQTT broker. If connection fails, retry after
         * a timeout. Timeout value will be exponentially increased till the maximum
         * attempts are reached or maximum timeout value is reached. The function
         * returns EXIT_FAILURE if the TCP connection cannot be established to
         * broker after configured number of attempts. */
        returnStatus = connectToServerWithBackoffRetries( &networkContext, &mqttContext );

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
            returnStatus = subscribePublishLoop( &mqttContext );

            /* End TLS session, then close TCP connection. */
            ( void ) Openssl_Disconnect( &networkContext );
        }

        if( returnStatus == EXIT_SUCCESS )
        {
            /* Log message indicating an iteration completed successfully. */
            LogInfo( ( "Demo completed successfully." ) );
        }

        LogInfo( ( "Short delay (of %u seconds) before starting the next iteration ....\n",
                   MQTT_SUBPUB_LOOP_DELAY_SECONDS ) );
        sleep( MQTT_SUBPUB_LOOP_DELAY_SECONDS );
    }

    return returnStatus;
}

/*-----------------------------------------------------------*/

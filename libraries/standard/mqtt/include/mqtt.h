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

#ifndef MQTT_H
#define MQTT_H

/* Include config file before other headers. */
#include "mqtt_config.h"
#include "mqtt_lightweight.h"

#include "transport_interface.h"

/**
 * @brief Invalid packet identifier.
 *
 * Zero is an invalid packet identifier as per MQTT v3.1.1 spec.
 */
#define MQTT_PACKET_ID_INVALID    ( ( uint16_t ) 0U )

struct MQTTPubAckInfo;
typedef struct MQTTPubAckInfo         MQTTPubAckInfo_t;

struct MQTTContext;
typedef struct MQTTContext            MQTTContext_t;

struct MQTTDeserializedInfo;
typedef struct MQTTDeserializedInfo   MQTTDeserializedInfo_t;

/**
 * @brief Application provided callback to retrieve the current time in
 * milliseconds.
 *
 * @return The current time in milliseconds.
 */
typedef uint32_t (* MQTTGetCurrentTimeFunc_t )( void );

/**
 * @brief Application callback for receiving incoming publishes and incoming
 * acks.
 *
 * @note This callback will be called only if packets are deserialized with a
 * result of #MQTTSuccess or #MQTTServerRefused. The latter can be obtained
 * when deserializing a SUBACK, indicating a broker's rejection of a subscribe.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pPacketInfo Information on the type of incoming MQTT packet.
 * @param[in] pDeserializedInfo Deserialized information from incoming packet.
 */
typedef void (* MQTTEventCallback_t )( MQTTContext_t * pContext,
                                       MQTTPacketInfo_t * pPacketInfo,
                                       MQTTDeserializedInfo_t * pDeserializedInfo );

/**
 * @brief Values indicating if an MQTT connection exists.
 */
typedef enum MQTTConnectionStatus
{
    MQTTNotConnected, /**< @brief MQTT Connection is inactive. */
    MQTTConnected     /**< @brief MQTT Connection is active. */
} MQTTConnectionStatus_t;

/**
 * @brief The state of QoS 1 or QoS 2 MQTT publishes, used in the state engine.
 */
typedef enum MQTTPublishState
{
    MQTTStateNull = 0,  /**< @brief An empty state with no corresponding PUBLISH. */
    MQTTPublishSend,    /**< @brief The library will send an outgoing PUBLISH packet. */
    MQTTPubAckSend,     /**< @brief The library will send a PUBACK for a received PUBLISH. */
    MQTTPubRecSend,     /**< @brief The library will send a PUBREC for a received PUBLISH. */
    MQTTPubRelSend,     /**< @brief The library will send a PUBREL for a received PUBREC. */
    MQTTPubCompSend,    /**< @brief The library will send a PUBCOMP for a received PUBREL. */
    MQTTPubAckPending,  /**< @brief The library is awaiting a PUBACK for an outgoing PUBLISH. */
    MQTTPubRecPending,  /**< @brief The library is awaiting a PUBREC for an outgoing PUBLISH. */
    MQTTPubRelPending,  /**< @brief The library is awaiting a PUBREL for an incoming PUBLISH. */
    MQTTPubCompPending, /**< @brief The library is awaiting a PUBCOMP for an outgoing PUBLISH. */
    MQTTPublishDone     /**< @brief The PUBLISH has been completed. */
} MQTTPublishState_t;

/**
 * @brief Packet types used in acknowledging QoS 1 or QoS 2 publishes.
 */
typedef enum MQTTPubAckType
{
    MQTTPuback, /**< @brief PUBACKs are sent in response to a QoS 1 PUBLISH. */
    MQTTPubrec, /**< @brief PUBRECs are sent in response to a QoS 2 PUBLISH. */
    MQTTPubrel, /**< @brief PUBRELs are sent in response to a PUBREC. */
    MQTTPubcomp /**< @brief PUBCOMPs are sent in response to a PUBREL. */
} MQTTPubAckType_t;

/**
 * @brief An element of the state engine records for QoS 1/2 publishes.
 */
struct MQTTPubAckInfo
{
    uint16_t packetId;               /**< @brief The packet ID of the original PUBLISH. */
    MQTTQoS_t qos;                   /**< @brief The QoS of the original PUBLISH. */
    MQTTPublishState_t publishState; /**< @brief The current state of the publish process. */
};

/**
 * @brief A struct representing an MQTT connection.
 */
struct MQTTContext
{
    /**
     * @brief State engine records for outgoing publishes.
     */
    MQTTPubAckInfo_t outgoingPublishRecords[ MQTT_STATE_ARRAY_MAX_COUNT ];

    /**
     * @brief State engine records for incoming publishes.
     */
    MQTTPubAckInfo_t incomingPublishRecords[ MQTT_STATE_ARRAY_MAX_COUNT ];

    /**
     * @brief The transport interface used by the MQTT connection.
     */
    TransportInterface_t transportInterface;

    /**
     * @brief The buffer used in sending and receiving packets from the network.
     */
    MQTTFixedBuffer_t networkBuffer;

    /**
     * @brief The next available ID for outgoing MQTT packets.
     */
    uint16_t nextPacketId;

    /**
     * @brief Whether the context currently has a connection to the broker.
     */
    MQTTConnectionStatus_t connectStatus;

    /**
     * @brief Function used to get millisecond timestamps.
     */
    MQTTGetCurrentTimeFunc_t getTime;

    /**
     * @brief Callback function used to give deserialized MQTT packets to the application.
     */
    MQTTEventCallback_t appCallback;

    /**
     * @brief Timestamp of the last packet sent by the library.
     */
    uint32_t lastPacketTime;

    /**
     * @brief Whether the library sent a packet during a call of #MQTT_ProcessLoop or
     * #MQTT_ReceiveLoop.
     */
    bool controlPacketSent;

    /* Keep alive members. */
    uint16_t keepAliveIntervalSec; /**< @brief Keep Alive interval. */
    uint32_t pingReqSendTimeMs;    /**< @brief Timestamp of the last sent PINGREQ. */
    uint32_t pingRespTimeoutMs;    /**< @brief Timeout for waiting for a PINGRESP. */
    bool waitingForPingResp;       /**< @brief If the library is currently awaiting a PINGRESP. */
};

/**
 * @brief Struct to hold deserialized packet information for an #MQTTEventCallback_t
 * callback.
 */
struct MQTTDeserializedInfo
{
    uint16_t packetIdentifier;          /**< @brief Packet ID of deserialized packet. */
    MQTTPublishInfo_t * pPublishInfo;   /**< @brief Pointer to deserialized publish info. */
    MQTTStatus_t deserializationResult; /**< @brief Return code of deserialization. */
};

/**
 * @brief Initialize an MQTT context.
 *
 * This function must be called on an MQTT context before any other function.
 *
 * @note The getTime callback function must be defined. If there is no time
 * implementation, it is the responsibility of the application to provide a
 * dummy function to always return 0, and provide 0 timeouts for functions. This
 * will ensure all time based functions will run for a single iteration.
 *
 * @brief param[in] pContext The context to initialize.
 * @brief param[in] pTransportInterface The transport interface to use with the context.
 * @brief param[in] getTimeFunction The time utility function to use with the context.
 * @brief param[in] userCallback The user callback to use with the context to notify about
 * incoming packet events.
 * @brief param[in] pNetworkBuffer Network buffer provided for the context.
 *
 * @return #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSuccess otherwise.
 */
MQTTStatus_t MQTT_Init( MQTTContext_t * pContext,
                        const TransportInterface_t * pTransportInterface,
                        MQTTGetCurrentTimeFunc_t getTimeFunction,
                        MQTTEventCallback_t userCallback,
                        const MQTTFixedBuffer_t * pNetworkBuffer );

/**
 * @brief Establish an MQTT session.
 *
 * This function will send MQTT CONNECT packet and receive a CONNACK packet. The
 * send and receive from the network is done through the transport interface.
 *
 * The maximum time this function waits for a CONNACK is decided in one of the
 * following ways:
 * 1. If #timeoutMs is greater than 0:
 *    #getTime is used to ensure that the function does not wait more than #timeoutMs
 *    for CONNACK.
 * 2. If #timeoutMs is 0:
 *    The network receive for CONNACK is retried up to the number of times configured
 *    by #MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pConnectInfo MQTT CONNECT packet information.
 * @param[in] pWillInfo Last Will and Testament. Pass NULL if Last Will and
 * Testament is not used.
 * @param[in] timeoutMs Maximum time in milliseconds to wait for a CONNACK packet.
 * A zero timeout makes use of the retries for receiving CONNACK as configured with
 * #MQTT_MAX_CONNACK_RECEIVE_RETRY_COUNT.
 * @param[out] pSessionPresent Whether a previous session was present.
 * Only relevant if not establishing a clean session.
 *
 * @return #MQTTNoMemory if the #MQTTContext_t.networkBuffer is too small to
 * hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSendFailed if transport send failed;
 * #MQTTRecvFailed if transport receive failed for CONNACK;
 * #MQTTNoDataAvailable if no data available to receive in transport until
 * the #timeoutMs for CONNACK;
 * #MQTTSuccess otherwise.
 *
 * @note This API may spend more time than provided in the timeoutMS parameters in
 * certain conditions as listed below:
 *
 * 1. Timeouts are incorrectly configured - If the timeoutMS is less than the
 *    transport receive timeout and if a CONNACK packet is not received within
 *    the transport receive timeout, the API will spend the transport receive
 *    timeout (which is more time than the timeoutMs). It is the case of incorrect
 *    timeout configuration as the timeoutMs parameter passed to this API must be
 *    greater than the transport receive timeout. Please refer to the transport
 *    interface documentation for more details about timeout configurations.
 *
 * 2. Partial CONNACK packet is received right before the expiry of the timeout - It
 *    is possible that first two bytes of CONNACK packet (packet type and remaining
 *    length) are received right before the expiry of the timeoutMS. In that case,
 *    the API makes one more network receive call in an attempt to receive the remaining
 *    2 bytes. In the worst case, it can happen that the remaining 2 bytes are never
 *    received and this API will end up spending timeoutMs + transport receive timeout.
 */
MQTTStatus_t MQTT_Connect( MQTTContext_t * pContext,
                           const MQTTConnectInfo_t * pConnectInfo,
                           const MQTTPublishInfo_t * pWillInfo,
                           uint32_t timeoutMs,
                           bool * pSessionPresent );

/**
 * @brief Sends MQTT SUBSCRIBE for the given list of topic filters to
 * the broker.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[in] packetId packet ID generated by #MQTT_GetPacketId.
 *
 * @return #MQTTNoMemory if the #MQTTContext_t.networkBuffer is too small to
 * hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSendFailed if transport write failed;
 * #MQTTSuccess otherwise.
 */
MQTTStatus_t MQTT_Subscribe( MQTTContext_t * pContext,
                             const MQTTSubscribeInfo_t * pSubscriptionList,
                             size_t subscriptionCount,
                             uint16_t packetId );

/**
 * @brief Publishes a message to the given topic name.
 *
 * @brief param[in] pContext Initialized MQTT context.
 * @brief param[in] pPublishInfo MQTT PUBLISH packet parameters.
 * @brief param[in] packetId packet ID generated by #MQTT_GetPacketId.
 *
 * @return #MQTTNoMemory if pBuffer is too small to hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSendFailed if transport write failed;
 * #MQTTSuccess otherwise.
 */
MQTTStatus_t MQTT_Publish( MQTTContext_t * pContext,
                           const MQTTPublishInfo_t * pPublishInfo,
                           uint16_t packetId );

/**
 * @brief Sends an MQTT PINGREQ to broker.
 *
 * @param[in] pContext Initialized and connected MQTT context.
 *
 * @return #MQTTNoMemory if pBuffer is too small to hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSendFailed if transport write failed;
 * #MQTTSuccess otherwise.
 */
MQTTStatus_t MQTT_Ping( MQTTContext_t * pContext );

/**
 * @brief Sends MQTT UNSUBSCRIBE for the given list of topic filters to
 * the broker.
 *
 * @param[in] pContext Initialized MQTT context.
 * @param[in] pSubscriptionList List of MQTT subscription info.
 * @param[in] subscriptionCount The number of elements in pSubscriptionList.
 * @param[in] packetId packet ID generated by #MQTT_GetPacketId.
 *
 * @return #MQTTNoMemory if the #MQTTContext_t.networkBuffer is too small to
 * hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSendFailed if transport write failed;
 * #MQTTSuccess otherwise.
 */
MQTTStatus_t MQTT_Unsubscribe( MQTTContext_t * pContext,
                               const MQTTSubscribeInfo_t * pSubscriptionList,
                               size_t subscriptionCount,
                               uint16_t packetId );

/**
 * @brief Disconnect an MQTT session.
 *
 * @param[in] pContext Initialized and connected MQTT context.
 *
 * @return #MQTTNoMemory if the #MQTTContext_t.networkBuffer is too small to
 * hold the MQTT packet;
 * #MQTTBadParameter if invalid parameters are passed;
 * #MQTTSendFailed if transport send failed;
 * #MQTTSuccess otherwise.
 */
MQTTStatus_t MQTT_Disconnect( MQTTContext_t * pContext );

/**
 * @brief Loop to receive packets from the transport interface. Handles keep
 * alive.
 *
 * @param[in] pContext Initialized and connected MQTT context.
 * @param[in] timeoutMs Minimum time in milliseconds that the receive loop will
 * run, unless an error occurs.
 *
 * @return #MQTTBadParameter if context is NULL;
 * #MQTTRecvFailed if a network error occurs during reception;
 * #MQTTSendFailed if a network error occurs while sending an ACK or PINGREQ;
 * #MQTTBadResponse if an invalid packet is received;
 * #MQTTKeepAliveTimeout if the server has not sent a PINGRESP before
 * pContext->pingRespTimeoutMs milliseconds;
 * #MQTTIllegalState if an incoming QoS 1/2 publish or ack causes an
 * invalid transition for the internal state machine;
 * #MQTTSuccess on success.
 */
MQTTStatus_t MQTT_ProcessLoop( MQTTContext_t * pContext,
                               uint32_t timeoutMs );

/**
 * @brief Loop to receive packets from the transport interface. Does not handle
 * keep alive.
 *
 * @note Passing a timeout value of 0 will run the loop for a single iteration.
 *
 * @param[in] pContext Initialized and connected MQTT context.
 * @param[in] timeoutMs Minimum time in milliseconds that the receive loop will
 * run, unless an error occurs.
 *
 * @return #MQTTBadParameter if context is NULL;
 * #MQTTRecvFailed if a network error occurs during reception;
 * #MQTTSendFailed if a network error occurs while sending an ACK or PINGREQ;
 * #MQTTBadResponse if an invalid packet is received;
 * #MQTTIllegalState if an incoming QoS 1/2 publish or ack causes an
 * invalid transition for the internal state machine;
 * #MQTTSuccess on success.
 */
MQTTStatus_t MQTT_ReceiveLoop( MQTTContext_t * pContext,
                               uint32_t timeoutMs );

/**
 * @brief Get a packet ID that is valid according to the MQTT 3.1.1 spec.
 *
 * @param[in] pContext Initialized MQTT context.
 *
 * @return A non-zero number.
 */
uint16_t MQTT_GetPacketId( MQTTContext_t * pContext );

/**
 * @brief Error code to string conversion for MQTT statuses.
 *
 * @param[in] status The status to convert to a string.
 *
 * @return The string representation of the status.
 */
const char * MQTT_Status_strerror( MQTTStatus_t status );

#endif /* ifndef MQTT_H */

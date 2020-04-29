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

#ifndef MQTT_LIGHTWEIGHT_H
#define MQTT_LIGHTWEIGHT_H

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "config.h"

/* MQTT packet types. */
#define MQTT_PACKET_TYPE_CONNECT         ( ( uint8_t ) 0x10U ) /**< @brief CONNECT (client-to-server). */
#define MQTT_PACKET_TYPE_CONNACK         ( ( uint8_t ) 0x20U ) /**< @brief CONNACK (server-to-client). */
#define MQTT_PACKET_TYPE_DISCONNECT      ( ( uint8_t ) 0xE0U ) /**< @brief DISCONNECT (client-to-server). */

struct MQTTFixedBuffer;
typedef struct MQTTFixedBuffer MQTTFixedBuffer_t;

struct MQTTConnectInfo;
typedef struct MQTTConnectInfo MQTTConnectInfo_t;

struct MQTTSubscribeInfo;
typedef struct MQTTSubscribeInfo MQTTSubscribeInfo_t;

struct MqttPublishInfo;
typedef struct MqttPublishInfo MQTTPublishInfo_t;

struct MQTTPacketInfo;
typedef struct MQTTPacketInfo MQTTPacketInfo_t;

/**
 * @brief Signature of the transport interface receive function.
 *
 * A function with this signature must be provided to the MQTT library to read
 * data off the network.
 *
 * @param[in] context The context provided with this function.
 * @param[out] pBuffer Buffer to receive network data.
 * @param[in] bytesToRecv Bytes to receive from the network. pBuffer must be at
 * least this size.
 *
 * @return The number of bytes received; negative value on failure.
 */
typedef int32_t (* MQTTTransportRecvFunc_t )( MQTTNetworkContext_t context,
                                              void * pBuffer,
                                              size_t bytesToRecv );

/**
 * @brief Return codes from MQTT functions.
 */
typedef enum MQTTStatus
{
    MQTTSuccess = 0,    /**< Function completed successfully. */
    MQTTBadParameter,   /**< At least one parameter was invalid. */
    MQTTNoMemory,       /**< A provided buffer was too small. */
    MQTTSendFailed,     /**< The transport send function failed. */
    MQTTRecvFailed,     /**< The transport receive function failed. */
    MQTTBadResponse,    /**< An invalid packet was received from the server. */
    MQTTServerRefused   /**< The server refused a CONNECT or SUBSCRIBE. */
} MQTTStatus_t;

/**
 * @brief MQTT Quality of Service values.
 */
typedef enum MQTTQoS
{
    MQTTQoS0 = 0,    /**< Delivery at most once. */
    MQTTQoS1 = 1,    /**< Delivery at least once. */
    MQTTQoS2 = 2     /**< Delivery exactly once. */
} MQTTQoS_t;

/**
 * @brief Buffer passed to MQTT library.
 *
 * These buffers are not copied and must remain in scope for the duration of the
 * MQTT operation.
 */
struct MQTTFixedBuffer
{
    uint8_t * pBuffer;    /**< @brief Pointer to buffer. */
    size_t size;          /**< @brief Size of buffer. */
};

/**
 * @brief MQTT CONNECT packet parameters.
 */
struct MQTTConnectInfo
{
    /**
     * @brief Whether to establish a new, clean session or resume a previous session.
     */
    bool cleanSession;

    /**
     * @brief MQTT keep alive period.
     */
    uint16_t keepAliveSeconds;

    /**
     * @brief MQTT client identifier. Must be unique per client.
     */
    const char * pClientIdentifier;

    /**
     * @brief Length of the client identifier.
     */
    uint16_t clientIdentifierLength;

    /**
     * @brief MQTT user name. Set to NULL if not used.
     */
    const char * pUserName;

    /**
     * @brief Length of MQTT user name. Set to 0 if not used.
     */
    uint16_t userNameLength;

    /**
     * @brief MQTT password. Set to NULL if not used.
     */
    const char * pPassword;

    /**
     * @brief Length of MQTT password. Set to 0 if not used.
     */
    uint16_t passwordLength;
};

/**
 * @brief MQTT SUBSCRIBE packet parameters.
 */
struct MQTTSubscribeInfo
{
    /**
     * @brief Quality of Service for subscription.
     */
    MQTTQoS_t qos;

    /**
     * @brief Topic filter for subscription.
     */
    const char * pTopicFilter;

    /**
     * @brief Length of subscription topic filter.
     */
    uint16_t topicFilterLength;
};

/**
 * @brief MQTT PUBLISH packet parameters.
 */
struct MqttPublishInfo
{
    /**
     * @brief Quality of Service for message.
     */
    MQTTQoS_t qos;

    /**
     * @brief Whether this is a retained message.
     */
    bool retain;

    /**
     * @brief Topic name for message.
     */
    const char * pTopicName;

    /**
     * @brief Length of topic name.
     */
    uint16_t topicNameLength;

    /**
     * @brief Message payload.
     */
    const void * pPayload;

    /**
     * @brief Message payload length.
     */
    size_t payloadLength;
};

/**
 * @brief MQTT incoming packet parameters.
 */
struct MQTTPacketInfo
{
    /**
     * @brief Type of incoming MQTT packet.
     */
    uint8_t type;

    /**
     * @brief Packet identifier of incoming MQTT packet.
     */
    uint16_t packetIdentifier;

    /**
     * @brief Remaining serialized data in the MQTT packet.
     */
    uint8_t * pRemainingData;

    /**
     * @brief Length of remaining serialized data.
     */
    size_t remainingLength;
};

/**
 * @brief Get the size and Remaining Length of an MQTT CONNECT packet.
 *
 * @param[in] pConnectInfo MQTT CONNECT packet parameters.
 * @param[in] pWillInfo Last Will and Testament. Pass NULL if not used.
 * @param[out] pRemainingLength The Remaining Length of the MQTT CONNECT packet.
 * @param[out] pPacketSize The total size of the MQTT CONNECT packet.
 *
 * @return #MQTTBadParameter if the packet would exceed the size allowed by the
 * MQTT spec; #MQTTSuccess otherwise.
 */
MQTTStatus_t MQTT_GetConnectPacketSize( const MQTTConnectInfo_t * const pConnectInfo,
                                        const MQTTPublishInfo_t * const pWillInfo,
                                        size_t * const pRemainingLength,
                                        size_t * const pPacketSize );

/**
 * @brief Serialize an MQTT CONNECT packet in the given buffer.
 *
 * @param[in] pConnectInfo MQTT CONNECT packet parameters.
 * @param[in] pWillInfo Last Will and Testament. Pass NULL if not used.
 * @param[in] remainingLength Remaining Length provided by #MQTT_GetConnectPacketSize.
 * @param[out] pBuffer Buffer for packet serialization.
 *
 * @return #MQTTNoMemory if pBuffer is too small to hold the MQTT packet;
 * #MQTTSuccess otherwise.
 */
MQTTStatus_t MQTT_SerializeConnect( const MQTTConnectInfo_t * const pConnectInfo,
                                    const MQTTPublishInfo_t * const pWillInfo,
                                    size_t remainingLength,
                                    const MQTTFixedBuffer_t * const pBuffer );

MQTTStatus_t MQTT_SubscriptionPacketSize( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                          size_t subscriptionCount,
                                          size_t * pRemainingLength,
                                          size_t * pPacketSize );

MQTTStatus_t MQTT_SerializeSubscribe( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                      size_t subscriptionCount,
                                      uint16_t packetId,
                                      size_t remainingLength,
                                      const MQTTFixedBuffer_t * const pBuffer );

MQTTStatus_t MQTT_SerializeUnsubscribe( const MQTTSubscribeInfo_t * const pSubscriptionList,
                                        size_t subscriptionCount,
                                        uint16_t packetId,
                                        size_t remainingLength,
                                        const MQTTFixedBuffer_t * const pBuffer );

MQTTStatus_t MQTT_GetPublishPacketSize( const MQTTPublishInfo_t * const pPublishInfo,
                                        size_t * const pRemainingLength,
                                        size_t * const pPacketSize );

MQTTStatus_t MQTT_SerializePublish( const MQTTPublishInfo_t * const pPublishInfo,
                                    uint16_t packetId,
                                    size_t remainingLength,
                                    const MQTTFixedBuffer_t * const pBuffer );

MQTTStatus_t MQTT_SerializePublishHeader( const MQTTPublishInfo_t * const pPublishInfo,
                                          uint16_t packetId,
                                          size_t remainingLength,
                                          const MQTTFixedBuffer_t * const pBuffer,
                                          size_t * const pHeaderSize );

/**
 * @brief Get the size of an MQTT DISCONNECT packet.
 *
 * @param[out] pPacketSize The size of the MQTT DISCONNECT packet.
 *
 * @return Always returns #MQTTSuccess.
 */
MQTTStatus_t MQTT_GetDisconnectPacketSize( size_t * pPacketSize );

/**
 * @brief Serialize an MQTT DISCONNECT packet into the given buffer.
 *
 * @param[out] pBuffer Buffer for packet serialization.
 *
 * @return #MQTTNoMemory if pBuffer is too small to hold the MQTT packet;
 * #MQTTSuccess otherwise.
 */
MQTTStatus_t MQTT_SerializeDisconnect( const MQTTFixedBuffer_t * const pBuffer );

MQTTStatus_t MQTT_SerializePingreq( const MQTTFixedBuffer_t * const pBuffer );

MQTTStatus_t MQTT_GetIncomingPacket( MQTTTransportRecvFunc_t recvFunc,
                                     MQTTNetworkContext_t networkContext,
                                     MQTTPacketInfo_t * const pIncomingPacket );

MQTTStatus_t MQTT_DeserializePublish( const MQTTPacketInfo_t * const pIncomingPacket,
                                      uint16_t * const pPacketId,
                                      MQTTPublishInfo_t * const pPublishInfo );

MQTTStatus_t MQTT_DeserializeAck( const MQTTPacketInfo_t * const pIncomingPacket,
                                  uint16_t * const pPacketId,
                                  bool * const pSessionPresent );

#endif

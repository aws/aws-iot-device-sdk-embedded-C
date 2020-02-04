/*
 * IoT MQTT V2.1.0
 * Copyright (C) 2019 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file iot_mqtt_common_types.h
 * @brief MQTT library common types for lightweigh and managed API.
 */

#ifndef IOT_MQTT_COMMON_TYPES_H_
#define IOT_MQTT_COMMON_TYPES_H_

/* Standard includes. */
#include <stdbool.h>
#include <stdint.h>
#include <stddef.h>

/*-------------------------- MQTT enumerated types --------------------------*/

/**
 * @enums{mqtt,MQTT library}
 */

/**
 * @ingroup mqtt_datatypes_enums
 * @brief Return codes of [MQTT functions](@ref mqtt_functions).
 *
 * The function @ref mqtt_function_strerror can be used to get a return code's
 * description.
 */
typedef enum IotMqttError
{
    /**
     * @brief MQTT operation completed successfully.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_connect
     * - @ref mqtt_function_publishasync with QoS 0 parameter
     * - @ref mqtt_function_wait
     * - @ref mqtt_function_subscribesync
     * - @ref mqtt_function_unsubscribesync
     * - @ref mqtt_function_publishsync
     *
     * Will also be the value of an operation completion callback's
     * #IotMqttCallbackParam_t.result when successful.
     */
    IOT_MQTT_SUCCESS = 0,

    /**
     * @brief MQTT operation queued, awaiting result.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_subscribeasync
     * - @ref mqtt_function_unsubscribeasync
     * - @ref mqtt_function_publishasync with QoS 1 parameter
     */
    IOT_MQTT_STATUS_PENDING = 1,

    /**
     * @brief Initialization failed.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_init
     */
    IOT_MQTT_INIT_FAILED = 2,

    /**
     * @brief At least one parameter is invalid.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_connect
     * - @ref mqtt_function_subscribeasync and @ref mqtt_function_subscribesync
     * - @ref mqtt_function_unsubscribeasync and @ref mqtt_function_unsubscribesync
     * - @ref mqtt_function_publishasync and @ref mqtt_function_publishsync
     * - @ref mqtt_function_wait
     */
    IOT_MQTT_BAD_PARAMETER = 3,

    /**
     * @brief MQTT operation failed because of memory allocation failure.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_connect
     * - @ref mqtt_function_subscribeasync and @ref mqtt_function_subscribesync
     * - @ref mqtt_function_unsubscribeasync and @ref mqtt_function_unsubscribesync
     * - @ref mqtt_function_publishasync and @ref mqtt_function_publishsync
     */
    IOT_MQTT_NO_MEMORY = 4,

    /**
     * @brief MQTT operation failed because the network was unusable.
     *
     * This return value may indicate that the network is disconnected.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_connect
     * - @ref mqtt_function_wait
     * - @ref mqtt_function_subscribesync
     * - @ref mqtt_function_unsubscribesync
     * - @ref mqtt_function_publishsync
     *
     * May also be the value of an operation completion callback's
     * #IotMqttCallbackParam_t.result.
     */
    IOT_MQTT_NETWORK_ERROR = 5,

    /**
     * @brief MQTT operation could not be scheduled, i.e. enqueued for sending.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_connect
     * - @ref mqtt_function_subscribeasync and @ref mqtt_function_subscribesync
     * - @ref mqtt_function_unsubscribeasync and @ref mqtt_function_unsubscribesync
     * - @ref mqtt_function_publishasync and @ref mqtt_function_publishsync
     */
    IOT_MQTT_SCHEDULING_ERROR = 6,

    /**
     * @brief MQTT response packet received from the network is malformed.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_connect
     * - @ref mqtt_function_wait
     * - @ref mqtt_function_subscribesync
     * - @ref mqtt_function_unsubscribesync
     * - @ref mqtt_function_publishsync
     *
     * May also be the value of an operation completion callback's
     * #IotMqttCallbackParam_t.result.
     *
     * @note If this value is received, the network connection has been closed.
     */
    IOT_MQTT_BAD_RESPONSE = 7,

    /**
     * @brief A blocking MQTT operation timed out.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_connect
     * - @ref mqtt_function_wait
     * - @ref mqtt_function_subscribesync
     * - @ref mqtt_function_unsubscribesync
     * - @ref mqtt_function_publishsync
     */
    IOT_MQTT_TIMEOUT = 8,

    /**
     * @brief A CONNECT or at least one subscription was refused by the server.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_connect
     * - @ref mqtt_function_wait, but only when its #IotMqttOperation_t parameter
     * is associated with a SUBSCRIBE operation.
     * - @ref mqtt_function_subscribesync
     *
     * May also be the value of an operation completion callback's
     * #IotMqttCallbackParam_t.result for a SUBSCRIBE.
     *
     * @note If this value is returned and multiple subscriptions were passed to
     * @ref mqtt_function_subscribeasync (or @ref mqtt_function_subscribesync), it's
     * still possible that some of the subscriptions succeeded. This value only
     * signifies that AT LEAST ONE subscription was rejected. The function @ref
     * mqtt_function_issubscribed can be used to determine which subscriptions
     * were accepted or rejected.
     */
    IOT_MQTT_SERVER_REFUSED = 9,

    /**
     * @brief A QoS 1 PUBLISH received no response and [the retry limit]
     * (#IotMqttPublishInfo_t.retryLimit) was reached.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_wait, but only when its #IotMqttOperation_t parameter
     * is associated with a QoS 1 PUBLISH operation
     * - @ref mqtt_function_publishsync
     *
     * May also be the value of an operation completion callback's
     * #IotMqttCallbackParam_t.result for a QoS 1 PUBLISH.
     */
    IOT_MQTT_RETRY_NO_RESPONSE = 10,

    /**
     * @brief An API function was called before @ref mqtt_function_init.
     *
     * Functions that may return this value:
     * - @ref mqtt_function_connect
     * - @ref mqtt_function_subscribeasync
     * - @ref mqtt_function_subscribesync
     * - @ref mqtt_function_unsubscribeasync
     * - @ref mqtt_function_unsubscribesync
     * - @ref mqtt_function_publishasync
     * - @ref mqtt_function_publishsync
     * - @ref mqtt_function_wait
     */
    IOT_MQTT_NOT_INITIALIZED = 11
} IotMqttError_t;

/**
 * @ingroup mqtt_datatypes_enums
 * @brief Types of MQTT operations.
 *
 * The function @ref mqtt_function_operationtype can be used to get an operation
 * type's description.
 */
typedef enum IotMqttOperationType
{
    IOT_MQTT_CONNECT,           /**< Client-to-server CONNECT. */
    IOT_MQTT_PUBLISH_TO_SERVER, /**< Client-to-server PUBLISH. */
    IOT_MQTT_PUBACK,            /**< Client-to-server PUBACK. */
    IOT_MQTT_SUBSCRIBE,         /**< Client-to-server SUBSCRIBE. */
    IOT_MQTT_UNSUBSCRIBE,       /**< Client-to-server UNSUBSCRIBE. */
    IOT_MQTT_PINGREQ,           /**< Client-to-server PINGREQ. */
    IOT_MQTT_DISCONNECT         /**< Client-to-server DISCONNECT. */
} IotMqttOperationType_t;

/**
 * @ingroup mqtt_datatypes_enums
 * @brief Quality of service levels for MQTT PUBLISH messages.
 *
 * All MQTT PUBLISH messages, including Last Will and Testament and messages
 * received on subscription filters, have an associated <i>Quality of Service</i>,
 * which defines any delivery guarantees for that message.
 * - QoS 0 messages will be delivered at most once. This is a "best effort"
 * transmission with no retransmissions.
 * - QoS 1 messages will be delivered at least once. See #IotMqttPublishInfo_t
 * for the retransmission strategy this library uses to redeliver messages
 * assumed to be lost.
 *
 * @attention QoS 2 is not supported by this library and should not be used.
 */
typedef enum IotMqttQos
{
    IOT_MQTT_QOS_0 = 0, /**< Delivery at most once. */
    IOT_MQTT_QOS_1 = 1, /**< Delivery at least once. See #IotMqttPublishInfo_t for client-side retry strategy. */
    IOT_MQTT_QOS_2 = 2  /**< Delivery exactly once. Unsupported, but enumerated for completeness. */
} IotMqttQos_t;

/**
 * @ingroup mqtt_datatypes_enums
 * @brief The reason that an MQTT connection (and its associated network connection)
 * was disconnected.
 *
 * When an MQTT connection is closed, its associated [disconnect callback]
 * (@ref IotMqttNetworkInfo_t::disconnectCallback) will be invoked. This type
 * is passed inside of an #IotMqttCallbackParam_t to provide a reason for the
 * disconnect.
 */
typedef enum IotMqttDisconnectReason
{
    IOT_MQTT_DISCONNECT_CALLED,   /**< @ref mqtt_function_disconnect was invoked. */
    IOT_MQTT_BAD_PACKET_RECEIVED, /**< An invalid packet was received from the network. */
    IOT_MQTT_KEEP_ALIVE_TIMEOUT   /**< Keep-alive response was not received within @ref IOT_MQTT_RESPONSE_WAIT_MS. */
} IotMqttDisconnectReason_t;

/*------------------------- MQTT parameter structs --------------------------*/

#ifndef IOT_MQTT_MANAGED_API

/**
 * @brief The type used to represent network connections.
 *
 * For the light weight MQTT API, it is application's responsibility to define and 
 * interpret IotNetworkConnection_t, therefore it is defined as void * here.
 */
    typedef void * IotNetworkConnection_t;
#endif

/**
 * @paramstructs{mqtt,MQTT}
 */

/**
 * @ingroup mqtt_datatypes_paramstructs
 * @brief Information on a PUBLISH message.
 *
 * @paramfor @ref mqtt_function_connect, @ref mqtt_function_publishasync
 *
 * Passed to @ref mqtt_function_publishasync as the message to publish and @ref
 * mqtt_function_connect as the Last Will and Testament (LWT) message.
 *
 * @initializer{IotMqttPublishInfo_t,IOT_MQTT_PUBLISH_INFO_INITIALIZER}
 *
 * #IotMqttPublishInfo_t.retryMs and #IotMqttPublishInfo_t.retryLimit are only
 * relevant to QoS 1 PUBLISH messages. They are ignored for QoS 0 PUBLISH
 * messages and LWT messages. These members control retransmissions of QoS 1
 * messages under the following rules:
 * - Retransmission is disabled when #IotMqttPublishInfo_t.retryLimit is 0.
 * After sending the PUBLISH, the library will wait indefinitely for a PUBACK.
 * - If #IotMqttPublishInfo_t.retryLimit is greater than 0, then QoS 1 publishes
 * that do not receive a PUBACK within #IotMqttPublishInfo_t.retryMs will be
 * retransmitted, up to #IotMqttPublishInfo_t.retryLimit times.
 *
 * Retransmission follows a truncated exponential backoff strategy. The constant
 * @ref IOT_MQTT_RETRY_MS_CEILING controls the maximum time between retransmissions.
 *
 * After #IotMqttPublishInfo_t.retryLimit retransmissions are sent, the MQTT
 * library will wait @ref IOT_MQTT_RESPONSE_WAIT_MS before a final check
 * for a PUBACK. If no PUBACK was received within this time, the QoS 1 PUBLISH
 * fails with the code #IOT_MQTT_RETRY_NO_RESPONSE.
 *
 * @note The lengths of the strings in this struct should not include the NULL
 * terminator. Strings in this struct do not need to be NULL-terminated.
 *
 * @note The AWS IoT MQTT broker does not support the DUP bit.  More
 * information about connecting to AWS IoT via MQTT is available
 * [here](https://docs.aws.amazon.com/iot/latest/developerguide/mqtt.html).
 *
 * <b>Example</b>
 *
 * Consider a situation where
 * - @ref IOT_MQTT_RETRY_MS_CEILING is 60000
 * - #IotMqttPublishInfo_t.retryMs is 2000
 * - #IotMqttPublishInfo_t.retryLimit is 20
 *
 * A PUBLISH message will be retransmitted at the following times after the initial
 * transmission if no PUBACK is received:
 * - 2000 ms (2000 ms after previous transmission)
 * - 6000 ms (4000 ms after previous transmission)
 * - 14000 ms (8000 ms after previous transmission)
 * - 30000 ms (16000 ms after previous transmission)
 * - 62000 ms (32000 ms after previous transmission)
 * - 122000 ms, 182000 ms, 242000 ms... (every 60000 ms until 20 transmissions have been sent)
 *
 * After the 20th retransmission, the MQTT library will wait
 * @ref IOT_MQTT_RESPONSE_WAIT_MS before checking a final time for a PUBACK.
 */
typedef struct IotMqttPublishInfo
{
    IotMqttQos_t qos;         /**< @brief QoS of message. Must be 0 or 1. */
    bool retain;              /**< @brief MQTT message retain flag. */

    const char * pTopicName;  /**< @brief Topic name of PUBLISH. */
    uint16_t topicNameLength; /**< @brief Length of #IotMqttPublishInfo_t.pTopicName. */

    const void * pPayload;    /**< @brief Payload of PUBLISH. */
    size_t payloadLength;     /**< @brief Length of #IotMqttPublishInfo_t.pPayload. For LWT messages, this is limited to 65535. */

    uint32_t retryMs;         /**< @brief If no response is received within this time, the message is retransmitted. */
    uint32_t retryLimit;      /**< @brief How many times to attempt retransmission. */
} IotMqttPublishInfo_t;

/**
 * @ingroup mqtt_datatypes_paramstructs
 * @brief MQTT subscription.
 *
 * @paramfor @ref mqtt_function_subscribeasync, @ref mqtt_function_unsubscribeasync,
 * @ref mqtt_function_subscribesync, @ref mqtt_function_unsubscribesync
 *
 * An array of these is passed to @ref mqtt_function_subscribeasync and @ref
 * mqtt_function_unsubscribeasync. However, #IotMqttSubscription_t.callback and
 * and #IotMqttSubscription_t.qos are ignored by @ref mqtt_function_unsubscribeasync.
 *
 * @initializer{IotMqttSubscription_t,IOT_MQTT_SUBSCRIPTION_INITIALIZER}
 *
 * @note The lengths of the strings in this struct should not include the NULL
 * terminator. Strings in this struct do not need to be NULL-terminated.
 * @see #IotMqttCallbackInfo_t for details on setting a callback function.
 */
typedef struct IotMqttSubscription
{
    /**
     * @brief QoS of messages delivered on subscription.
     *
     * Must be `0` or `1`. Ignored by @ref mqtt_function_unsubscribeasync.
     */
    IotMqttQos_t qos;

    const char * pTopicFilter;  /**< @brief Topic filter of subscription. */
    uint16_t topicFilterLength; /**< @brief Length of #IotMqttSubscription_t.pTopicFilter. */
    #ifdef IOT_MQTT_MANAGED_API

        /**
         * @brief Callback to invoke when a message is received.
         *
         * See #IotMqttCallbackInfo_t. Ignored by @ref mqtt_function_unsubscribeasync.
         *
         * @note This parameter is used by managed MQTT API, Lightweight MQTT API does
         * not use this parameter.
         */
        IotMqttCallbackInfo_t callback;
    #endif
} IotMqttSubscription_t;

/**
 * @ingroup mqtt_datatypes_paramstructs
 * @brief MQTT connection details.
 *
 * @paramfor @ref mqtt_function_connect
 *
 * Passed as an argument to @ref mqtt_function_connect. Most members of this struct
 * correspond to the content of an [MQTT CONNECT packet.]
 * (http://docs.oasis-open.org/mqtt/mqtt/v3.1.1/csprd02/mqtt-v3.1.1-csprd02.html#_Toc385349764)
 *
 * @initializer{IotMqttConnectInfo_t,IOT_MQTT_CONNECT_INFO_INITIALIZER}
 *
 * @note The lengths of the strings in this struct should not include the NULL
 * terminator. Strings in this struct do not need to be NULL-terminated.
 */
typedef struct IotMqttConnectInfo
{
    /**
     * @brief Specifies if this MQTT connection is to an AWS IoT MQTT server.
     *
     * Set this member to `true` when connecting to the AWS IoT MQTT broker or
     * `false` otherwise.  Additional details about connecting to AWS IoT
     * via MQTT are available [here]
     * (https://docs.aws.amazon.com/iot/latest/developerguide/mqtt.html)
     *
     * @attention This setting <b>MUST</b> be `true` when using the AWS IoT MQTT
     * server; it <b>MUST</b> be `false` otherwise.
     * @note Currently, @ref IOT_MQTT_CONNECT_INFO_INITIALIZER sets this
     * this member to `true`.
     */
    bool awsIotMqttMode;

    /**
     * @brief Whether this connection is a clean session.
     *
     * MQTT servers can maintain and topic filter subscriptions and unacknowledged
     * PUBLISH messages. These form part of an <i>MQTT session</i>, which is identified by
     * the [client identifier](@ref IotMqttConnectInfo_t.pClientIdentifier).
     *
     * Setting this value to `true` establishes a <i>clean session</i>, which causes
     * the MQTT server to discard any previous session data for a client identifier.
     * When the client disconnects, the server discards all session data. If this
     * value is `true`, #IotMqttConnectInfo_t.pPreviousSubscriptions and
     * #IotMqttConnectInfo_t.previousSubscriptionCount are ignored.
     *
     * Setting this value to `false` does one of the following:
     * - If no previous session exists, the MQTT server will create a new
     * <i>persistent session</i>. The server may maintain subscriptions and
     * unacknowledged PUBLISH messages after a client disconnects, to be restored
     * once the same client identifier reconnects.
     * - If a previous session exists, the MQTT server restores all of the session's
     * subscriptions for the client identifier and may immediately transmit any
     * unacknowledged PUBLISH packets to the client.
     *
     * When a client with a persistent session disconnects, the MQTT server
     * continues to maintain all subscriptions and unacknowledged PUBLISH messages.
     * The client must also remember the session subscriptions to restore them
     * upon reconnecting. #IotMqttConnectInfo_t.pPreviousSubscriptions and
     * #IotMqttConnectInfo_t.previousSubscriptionCount are used to restore a
     * previous session's subscriptions client-side.
     */
    bool cleanSession;

    /**
     * @brief An array of MQTT subscriptions present in a previous session, if any.
     *
     * Pointer to the start of an array of subscriptions present a previous session,
     * if any. These subscriptions will be immediately restored upon reconnecting.
     *
     * [Optional] The field can also be used to pass a list of subscriptions to be
     * stored locally without a SUBSCRIBE packet being sent to the broker. These subscriptions
     * are useful to invoke application level callbacks for messages received on unsolicited
     * topics from the broker.
     *
     * This member is ignored if it is `NULL`. If this member is not `NULL`,
     * #IotMqttConnectInfo_t.previousSubscriptionCount must be nonzero.
     */
    const IotMqttSubscription_t * pPreviousSubscriptions;

    /**
     * @brief The number of MQTT subscriptions present in a previous session, if any.
     *
     * Number of subscriptions contained in the array
     * #IotMqttConnectInfo_t.pPreviousSubscriptions.
     *
     * This value is ignored if #IotMqttConnectInfo_t.pPreviousSubscriptions
     * is `NULL`. If #IotMqttConnectInfo_t.pPreviousSubscriptions is not `NULL`,
     * this value must be nonzero.
     */
    size_t previousSubscriptionCount;

    /**
     * @brief A message to publish if the new MQTT connection is unexpectedly closed.
     *
     * A Last Will and Testament (LWT) message may be published if this connection is
     * closed without sending an MQTT DISCONNECT packet. This pointer should be set to
     * an #IotMqttPublishInfo_t representing any LWT message to publish. If an LWT
     * is not needed, this member must be set to `NULL`.
     *
     * Unlike other PUBLISH messages, an LWT message is limited to 65535 bytes in
     * length. Additionally, [pWillInfo->retryMs](@ref IotMqttPublishInfo_t.retryMs)
     * and [pWillInfo->retryLimit](@ref IotMqttPublishInfo_t.retryLimit) will
     * be ignored.
     */
    const IotMqttPublishInfo_t * pWillInfo;

    uint16_t keepAliveSeconds;       /**< @brief Period of keep-alive messages. Set to 0 to disable keep-alive. */

    const char * pClientIdentifier;  /**< @brief MQTT client identifier. */
    uint16_t clientIdentifierLength; /**< @brief Length of #IotMqttConnectInfo_t.pClientIdentifier. */

    /**
     * @brief Username for MQTT connection.
     *
     * The MQTT username and password can be used for AWS IoT Enhanced Custom
     * Authentication as described [here]
     * (https://docs.aws.amazon.com/iot/latest/developerguide/enhanced-custom-authentication.html).
     */
    const char * pUserName;
    uint16_t userNameLength; /**< @brief Length of #IotMqttConnectInfo_t.pUserName. */
    const char * pPassword;  /**< @brief Password for MQTT connection. */
    uint16_t passwordLength; /**< @brief Length of #IotMqttConnectInfo_t.pPassword. */
} IotMqttConnectInfo_t;

/**
 * @ingroup mqtt_datatypes_paramstructs
 * @brief MQTT packet details.
 *
 * @paramfor @ref mqtt_function_deserializeresponse @ref mqtt_function_deserializepublish
 *
 * Passed as an argument to public low level mqtt deserialize functions.
 *
 * @initializer{IotMqttPacketInfo_t,IOT_MQTT_PACKET_INFO_INITIALIZER}
 *
 * @note This structure should be only used while accessing low level MQTT deserialization API.
 * The low level serialization/ deserialization API should be only used for implementing
 * light weight single threaded mqtt client.
 */
typedef struct IotMqttPacketInfo
{
    uint8_t * pRemainingData;     /**< @brief (Input) The remaining data in MQTT packet. */
    size_t remainingLength;       /**< @brief (Input) Length of the remaining data in the MQTT packet. */
    uint16_t packetIdentifier;    /**< @brief (Output) MQTT packet identifier. */
    uint8_t type;                 /**< @brief (Input) A value identifying the packet type. */
    IotMqttPublishInfo_t pubInfo; /**< @brief (Output) Publish info in case of deserializing PUBLISH. */
} IotMqttPacketInfo_t;

/**
 * @brief Function pointer to read the next available byte on a network connection.
 * @param[in] pNetworkContext reference to network connection like socket.
 * @param[out] pNextByte Pointer to the byte read from the network.
 */
typedef IotMqttError_t (* IotMqttGetNextByte_t)( IotNetworkConnection_t pNetworkContext,
                                                 uint8_t * pNextByte );

#endif /* ifndef IOT_MQTT_COMMON_TYPES_H_ */

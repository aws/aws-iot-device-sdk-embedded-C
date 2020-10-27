/*
 * AWS IoT Device SDK for Embedded C V202009.00
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

#ifndef MQTT_OPERATIONS_H_
#define MQTT_OPERATIONS_H_

/* MQTT API header. */
#include "core_mqtt.h"

/**
 * @brief Application callback type to handle the incoming publishes.
 *
 * @param[in] pPublishInfo Pointer to publish info of the incoming publish.
 * @param[in] packetIdentifier Packet identifier of the incoming publish.
 */
typedef void (* MQTTPublishCallback_t )( MQTTPublishInfo_t * pPublishInfo,
                                         uint16_t packetIdentifier );

/**
 * @brief Establish a MQTT connection.
 *
 * @param[in] publishCallback The callback function to receive incoming
 * publishes from the MQTT broker.
 *
 * @return EXIT_SUCCESS if an MQTT session is established;
 * EXIT_FAILURE otherwise.
 */
int EstablishMqttSession( MQTTPublishCallback_t publishCallback );

/**
 * @brief Disconnect the MQTT connection.
 *
 * @return EXIT_SUCCESS if the MQTT session was successfully disconnected;
 * EXIT_FAILURE otherwise.
 */
int DisconnectMqttSession( void );

/**
 * @brief Subscribe to a MQTT topic filter.
 *
 * @param[in] pTopicFilter The topic filter to subscribe to.
 * @param[in] topicFilterLength Length of the topic buffer.
 *
 * @return EXIT_SUCCESS if subscribe operation was successful;
 * EXIT_FAILURE otherwise.
 */
int SubscribeToTopic( const char * pTopicFilter,
                      uint16_t topicFilterLength );

/**
 * @brief Unsubscribe from a MQTT topic filter.
 *
 * @param[in] pTopicFilter The topic filter to unsubscribe from.
 * @param[in] topicFilterLength Length of the topic buffer.
 *
 * @return EXIT_SUCCESS if unsubscribe operation was successful;
 * EXIT_FAILURE otherwise.
 */
int UnsubscribeFromTopic( const char * pTopicFilter,
                          uint16_t topicFilterLength );

/**
 * @brief Publish a message to a MQTT topic.
 *
 * @param[in] pTopic The topic to publish the message on.
 * @param[in] topicLength Length of the topic.
 * @param[in] pMessage The message to publish.
 * @param[in] messageLength Length of the message.
 *
 * @return EXIT_SUCCESS if PUBLISH was successfully sent;
 * EXIT_FAILURE otherwise.
 */
int PublishToTopic( const char * pTopic,
                    uint16_t topicLength,
                    const char * pMessage,
                    size_t messageLength );

/**
 * @brief Invoke the core MQTT library's process loop function.
 *
 * @return EXIT_SUCCESS if process loop was successful;
 * EXIT_FAILURE otherwise.
 */
int ProcessLoop( void );

#endif /* ifndef MQTT_OPERATIONS_H_ */

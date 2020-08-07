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

#ifndef SHADOW_DEMO_HELPERS_H_
#define SHADOW_DEMO_HELPERS_H_

/* MQTT API header. */
#include "mqtt.h"

/**
 * @brief Establish a MQTT connection.
 *
 * @param[in] appCallback The callback function used to receive incoming
 * publishes and incoming acks from MQTT library.
 *
 * @return EXIT_SUCCESS if an MQTT session is established;
 * EXIT_FAILURE otherwise.
 */
int32_t establishMqttSession( MQTTEventCallback_t eventCallback );

/**
 * @brief Handle the incoming packet if it's not related to the device shadow.
 *
 * @param[in] pPacketInfo Packet Info pointer for the incoming packet.
 * @param[in] packetIdentifier Packet identifier of the incoming packet.
 */
void handleOtherIncomingPacket( MQTTPacketInfo_t * pPacketInfo,
                                uint16_t packetIdentifier );

/**
 * @brief Close the MQTT connection.
 *
 * @return EXIT_SUCCESS if DISCONNECT was successfully sent;
 * EXIT_FAILURE otherwise.
 */
int32_t disconnectMqttSession( void );

/**
 * @brief Subscribe to a MQTT topic.
 *
 * @param[in] pTopicBuffer Pointer to the shadow topic buffer.
 * @param[in] topicLength Indicates the length of the shadow
 * topic buffer.
 *
 * @return EXIT_SUCCESS if SUBSCRIBE was successfully sent;
 * EXIT_FAILURE otherwise.
 */
int32_t subscribeToTopic( const char * pTopicBuffer,
                          uint16_t topicLength );

/**
 * @brief Sends an MQTT UNSUBSCRIBE to unsubscribe from the shadow
 * topic.
 *
 * @param[in] pTopicBuffer Pointer to the shadow topic buffer.
 * @param[in] topicLength Indicates the length of the shadow
 * topic buffer.
 *
 * @return EXIT_SUCCESS if UNSUBSCRIBE was successfully sent;
 * EXIT_FAILURE otherwise.
 */
int32_t unsubscribeFromTopic( const char * pTopicBuffer,
                              uint16_t topicLength );

/**
 * @brief Publish a message to a MQTT topic.
 *
 * @param[in] pTopic Points to the topic .
 * @param[in] topicLength The length of the topic.
 * @param[in] pPayload Points to the payload .
 * @param[in] payloadLength The length of the payload.
 *
 * @return EXIT_SUCCESS if PUBLISH was successfully sent;
 * EXIT_FAILURE otherwise.
 */
int32_t publishToTopic( const char * pTopicBuffer,
                        int32_t topicLength,
                        const char * pPayload,
                        size_t payloadLength );

#endif /* ifndef SHADOW_DEMO_HELPERS_H_ */

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
 * @file mqtt_subscription_manager.h
 * @brief The API of a subscription manager for handling subscription callbacks
 * to topic filters in MQTT operations.
 */

#ifndef SUBSCRIPTION_MANAGER_H_
#define SUBSCRIPTION_MANAGER_H_

/* Include MQTT library. */
#include "mqtt.h"

/**
 * @brief Callback type to be registered for a topic filter with the subscription manager.
 * For incoming PUBLISH messages received on topics that match the registered topic filter
 * with the callback, the callback would be invoked by the subscription manager.
 *
 * @param[in] pContext The context associated with the MQTT connection.
 * @param[in] pPublishInfo The incoming PUBLISH message information.
 */
typedef void (* SubscriptionManager_Callback_t )( MQTTContext_t * pContext,
                                                  MQTTPublishInfo_t * pPublishInfo );

/**
 * @brief Dispatches the incoming PUBLISH message to the callbacks that have their
 * registered topic filters matching the incoming PUBLISH topic name. The dispatch
 * handler will invoke all these callbacks with matching topic filters.
 *
 * @param[in] pContext The context associated with the MQTT connection.
 * @param[in] pPublishInfo The incoming PUBLISH message information.
 */
void SubscriptionManager_DispatchHandler( MQTTContext_t * pContext,
                                          MQTTPublishInfo_t * pPublishInfo );

/**
 * @brief Utility to register a callback for a topic filter in the subscription manager.
 * The callback will be invoked when an incoming PUBLISH message on a topic that matches
 * the topic filter, @a pTopicFilter, is dispatched by the subscription manager.
 * The subscription manager accepts wildcard topics.
 *
 * @param[in] pTopicFilter The topic filter to register the callback for.
 * @param[in] topicFilterLength The length of the topic filter string.
 * @param[in] callback The callback to be registered for the topic filter.
 *
 * @return true if registration of the callback is successful; otherwise, false
 * if the either the registry is full OR a registered callback already exists for
 * the topic filter in the subscription manager.
 */
bool SubscriptionManager_RegisterCallback( const char * pTopicFilter,
                                           uint16_t topicFileterLength,
                                           SubscriptionManager_Callback_t pCallback );

/**
 * @brief Utility to remove the callback registered for a topic filter from the
 * subscription manager.
 *
 * @param[in] pTopicFilter The topic filter to remove from the subscription manager.
 * @param[in] topicFilterLength The length of the topic filter string.
 */
void SubscriptionManager_RemoveCallback( const char * pTopicFilter,
                                         uint16_t topicFileterLength );


#endif /* ifndef SUBSCRIPTION_MANAGER_H_ */

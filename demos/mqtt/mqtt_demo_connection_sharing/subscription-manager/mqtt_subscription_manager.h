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

#ifndef SUBSCRIPTION_MANAGER_H_
#define SUBSCRIPTION_MANAGER_H_

#include "mqtt.h"

/* Callback type that would be invoked for the incoming PUBLISH message on the topic(s)
 * that it is registered with the subscription manager. */
typedef void (* SubscriptionManager_Callback_t )( uint16_t packetIdentifier,
                                                  MQTTPublishInfo_t * pPublishInfo );

/* Dispatch Handler that dispatches incoming PUBLISH message on the topic that has
 * matching topic filters registered in the subscription manager.
 *
 * Design Points -
 *   * The application will use a common event callback/handler for processing acks
 *      and handling retries of PUBLISHes and Subscription requests.
 *   * Only PUBLISH messages will be forwarded to this message dispatcher/handler as
 *     individual callbacks only want to process incoming PUBLISH message.
 */
void SubscriptionManager_DispatchHandler( uint16_t packetIdentifier,
                                          MQTTPublishInfo_t * pPublishInfo );

/* Utility to register a callback for incoming PUBLISH topic(s). */
bool SubscriptionManager_RegisterCallback( const char * pTopicFilter,
                                           size_t topicFileterLength,
                                           SubscriptionManager_Callback_t callback );

/* Utility to remove the callback registered for invocation on incoming PUBLISH messages
 * on the passed topic filter . */
void SubscriptionManager_RemoveCallback( const char * pTopicFilter,
                                         size_t topicFileterLength );


#endif /* ifndef SUBSCRIPTION_MANAGER_H_ */

/*
 * IoT MQTT V2.1.0
 * Copyright (C) 2018 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file iot_mqtt_validate.c
 * @brief Implements functions that validate the structs of the MQTT library.
 */

/* The config header is always included first. */
#include "iot_config.h"

/* MQTT internal include. */
#include "private/iot_mqtt_internal.h"

/**
 * @brief Check that an #IotMqttPublishInfo_t is valid.
 *
 * @param[in] awsIotMqttMode Specifies if this PUBLISH packet is being sent to
 * an AWS IoT MQTT server.
 * @param[in] maximumPayloadLength Maximum payload length.
 * @param[in] pPublishTypeDescription String describing the publish type.
 * @param[in] pPublishInfo The #IotMqttPublishInfo_t to validate.
 *
 * @return `true` if `pPublishInfo` is valid; `false` otherwise.
 */
static bool _validatePublish( bool awsIotMqttMode,
                              size_t maximumPayloadLength,
                              const char * pPublishTypeDescription,
                              const IotMqttPublishInfo_t * pPublishInfo );

/*-----------------------------------------------------------*/

bool _IotMqtt_ValidateConnect( const IotMqttConnectInfo_t * pConnectInfo )
{
    bool status = true;
    uint16_t maxClientIdLength = MQTT_SERVER_MAX_CLIENTID_LENGTH;
    bool enforceMaxClientIdLength = false;

    /* Check for NULL. */
    if( pConnectInfo == NULL )
    {
        IotLogError( "MQTT connection information cannot be NULL." );

        status = false;
        goto cleanup;
    }

    /* Check that a client identifier was set. */
    if( pConnectInfo->pClientIdentifier == NULL )
    {
        IotLogError( "Client identifier must be set." );

        status = false;
        goto cleanup;
    }

    /* Check for a zero-length client identifier. Zero-length client identifiers
     * are not allowed with clean sessions. */
    if( pConnectInfo->clientIdentifierLength == 0 )
    {
        IotLogWarn( "A zero-length client identifier was provided." );

        if( pConnectInfo->cleanSession == true )
        {
            IotLogError( "A zero-length client identifier cannot be used with a clean session." );

            status = false;
            goto cleanup;
        }
    }

    /* Check that the number of persistent session subscriptions is valid. */
    if( pConnectInfo->pPreviousSubscriptions != NULL )
    {
        if( _IotMqtt_ValidateSubscriptionList( IOT_MQTT_SUBSCRIBE,
                                               pConnectInfo->awsIotMqttMode,
                                               pConnectInfo->pPreviousSubscriptions,
                                               pConnectInfo->previousSubscriptionCount ) == false )
        {
            status = false;
            goto cleanup;
        }
    }

    /* If will info is provided, check that it is valid. */
    if( pConnectInfo->pWillInfo != NULL )
    {
        if( _IotMqtt_ValidateLwtPublish( pConnectInfo->awsIotMqttMode,
                                         pConnectInfo->pWillInfo ) == false )
        {
            status = false;
            goto cleanup;
        }
    }

    /* The AWS IoT MQTT service enforces a client ID length limit. */
    if( pConnectInfo->awsIotMqttMode == true )
    {
        maxClientIdLength = AWS_IOT_MQTT_SERVER_MAX_CLIENTID_LENGTH;
        enforceMaxClientIdLength = true;
    }

    if( pConnectInfo->clientIdentifierLength > maxClientIdLength )
    {
        if( enforceMaxClientIdLength == false )
        {
            IotLogWarn( "A client identifier length of %hu is longer than %hu, "
                        "which is "
                        "the longest client identifier a server must accept.",
                        pConnectInfo->clientIdentifierLength,
                        maxClientIdLength );
        }
        else
        {
            IotLogError( "A client identifier length of %hu exceeds the "
                         "maximum supported length of %hu.",
                         pConnectInfo->clientIdentifierLength,
                         maxClientIdLength );

            status = false;
            goto cleanup;
        }
    }

cleanup:
    return status;
}

/*-----------------------------------------------------------*/

static bool _validatePublish( bool awsIotMqttMode,
                              size_t maximumPayloadLength,
                              const char * pPublishTypeDescription,
                              const IotMqttPublishInfo_t * pPublishInfo )
{
    bool status = true;

    /* This parameter is not used when logging is disabled. */
    ( void ) pPublishTypeDescription;

    /* Check for NULL. */
    if( pPublishInfo == NULL )
    {
        IotLogError( "Publish information cannot be NULL." );

        status = false;
        goto cleanup;
    }

    /* Check topic name for NULL or zero-length. */
    if( pPublishInfo->pTopicName == NULL )
    {
        IotLogError( "Publish topic name must be set." );
    }

    if( pPublishInfo->topicNameLength == 0 )
    {
        IotLogError( "Publish topic name length cannot be 0." );

        status = false;
        goto cleanup;
    }

    if( pPublishInfo->payloadLength != 0 )
    {
        if( pPublishInfo->payloadLength > maximumPayloadLength )
        {
            IotLogError( "%s payload size of %zu exceeds maximum length of %zu.",
                         pPublishTypeDescription,
                         pPublishInfo->payloadLength,
                         maximumPayloadLength );

            status = false;
            goto cleanup;
        }
        else
        {
            if( pPublishInfo->pPayload == NULL )
            {
                IotLogError( "Nonzero payload length cannot have a NULL payload." );

                status = false;
                goto cleanup;
            }
        }
    }

    /* Check for a valid QoS. */
    if( pPublishInfo->qos != IOT_MQTT_QOS_0 )
    {
        if( pPublishInfo->qos != IOT_MQTT_QOS_1 )
        {
            IotLogError( "Publish QoS must be either 0 or 1." );

            status = false;
            goto cleanup;
        }
    }

    /* Check the retry parameters. */
    if( pPublishInfo->retryLimit > 0 )
    {
        if( pPublishInfo->retryMs == 0 )
        {
            IotLogError( "Publish retry time must be positive." );

            status = false;
            goto cleanup;
        }
    }

    /* Check for compatibility with AWS IoT MQTT server. */
    if( awsIotMqttMode == true )
    {
        /* Check for retained message. */
        if( pPublishInfo->retain == true )
        {
            IotLogError( "AWS IoT does not support retained publish messages." );

            status = false;
            goto cleanup;
        }

        /* Check topic name length. */
        if( pPublishInfo->topicNameLength > AWS_IOT_MQTT_SERVER_MAX_TOPIC_LENGTH )
        {
            IotLogError( "AWS IoT does not support topic names longer than %d bytes.",
                         AWS_IOT_MQTT_SERVER_MAX_TOPIC_LENGTH );

            status = false;
            goto cleanup;
        }
    }

cleanup:
    return status;
}

/*-----------------------------------------------------------*/

bool _IotMqtt_ValidatePublish( bool awsIotMqttMode,
                               const IotMqttPublishInfo_t * pPublishInfo )
{
    size_t maximumPayloadLength = MQTT_SERVER_MAX_PUBLISH_PAYLOAD_LENGTH;

    if( awsIotMqttMode == true )
    {
        maximumPayloadLength = AWS_IOT_MQTT_SERVER_MAX_PUBLISH_PAYLOAD_LENGTH;
    }

    return _validatePublish( awsIotMqttMode,
                             maximumPayloadLength,
                             "Publish",
                             pPublishInfo );
}

/*-----------------------------------------------------------*/

bool _IotMqtt_ValidateLwtPublish( bool awsIotMqttMode,
                                  const IotMqttPublishInfo_t * pLwtPublishInfo )
{
    return _validatePublish( awsIotMqttMode,
                             MQTT_SERVER_MAX_LWT_PAYLOAD_LENGTH,
                             "LWT",
                             pLwtPublishInfo );
}

/*-----------------------------------------------------------*/

bool _IotMqtt_ValidateOperation( IotMqttOperation_t operation )
{
    bool status = true;

    /* Check for NULL. */
    if( operation == NULL )
    {
        IotLogError( "Operation reference cannot be NULL." );

        status = false;
        goto cleanup;
    }

    /* Check that reference is waitable. */
    if( ( operation->u.operation.flags & IOT_MQTT_FLAG_WAITABLE ) != IOT_MQTT_FLAG_WAITABLE )
    {
        IotLogError( "Operation is not waitable." );

        status = false;
        goto cleanup;
    }

cleanup:
    return status;
}

/*-----------------------------------------------------------*/

bool _IotMqtt_ValidateSubscriptionList( IotMqttOperationType_t operation,
                                        bool awsIotMqttMode,
                                        const IotMqttSubscription_t * pListStart,
                                        size_t listSize )
{
    bool status = true;
    size_t i = 0;
    uint16_t j = 0;
    const IotMqttSubscription_t * pListElement = NULL;

    /* Operation must be either subscribe or unsubscribe. */
    IotMqtt_Assert( ( operation == IOT_MQTT_SUBSCRIBE ) ||
                    ( operation == IOT_MQTT_UNSUBSCRIBE ) );

    /* Check for empty list. */
    if( pListStart == NULL )
    {
        IotLogError( "Subscription list pointer cannot be NULL." );

        status = false;
        goto cleanup;
    }

    if( listSize == 0 )
    {
        IotLogError( "Empty subscription list." );

        status = false;
        goto cleanup;
    }

    /* AWS IoT supports at most 8 topic filters in a single SUBSCRIBE packet. */
    if( awsIotMqttMode == true )
    {
        if( listSize > AWS_IOT_MQTT_SERVER_MAX_TOPIC_FILTERS_PER_SUBSCRIBE )
        {
            IotLogError( "AWS IoT does not support more than %d topic filters per "
                         "subscription request.",
                         AWS_IOT_MQTT_SERVER_MAX_TOPIC_FILTERS_PER_SUBSCRIBE );

            status = false;
            goto cleanup;
        }
    }

    for( i = 0; i < listSize; i++ )
    {
        pListElement = &( pListStart[ i ] );

        /* Check for a valid QoS and callback function when subscribing. */
        if( operation == IOT_MQTT_SUBSCRIBE )
        {
            if( pListElement->qos != IOT_MQTT_QOS_0 )
            {
                if( pListElement->qos != IOT_MQTT_QOS_1 )
                {
                    IotLogError( "Subscription QoS must be either 0 or 1." );

                    status = false;
                    goto cleanup;
                }
            }

            if( pListElement->callback.function == NULL )
            {
                IotLogError( "Callback function must be set." );

                status = false;
                goto cleanup;
            }
        }

        /* Check subscription topic filter. */
        if( pListElement->pTopicFilter == NULL )
        {
            IotLogError( "Subscription topic filter cannot be NULL." );

            status = false;
            goto cleanup;
        }

        if( pListElement->topicFilterLength == 0 )
        {
            IotLogError( "Subscription topic filter length cannot be 0." );

            status = false;
            goto cleanup;
        }

        /* Check for compatibility with AWS IoT MQTT server. */
        if( awsIotMqttMode == true )
        {
            /* Check topic filter length. */
            if( pListElement->topicFilterLength > AWS_IOT_MQTT_SERVER_MAX_TOPIC_LENGTH )
            {
                IotLogError( "AWS IoT does not support topic filters longer than %d bytes.",
                             AWS_IOT_MQTT_SERVER_MAX_TOPIC_LENGTH );

                status = false;
                goto cleanup;
            }
        }

        /* Check that the wildcards '+' and '#' are being used correctly. */
        for( j = 0; j < pListElement->topicFilterLength; j++ )
        {
            switch( pListElement->pTopicFilter[ j ] )
            {
                /* Check that the single level wildcard '+' is used correctly. */
                case '+':

                    /* Unless '+' is the first character in the filter, it must be preceded by '/'. */
                    if( j > 0 )
                    {
                        if( pListElement->pTopicFilter[ j - 1 ] != '/' )
                        {
                            IotLogError( "Invalid topic filter %.*s -- '+' must be preceded by '/'.",
                                         pListElement->topicFilterLength,
                                         pListElement->pTopicFilter );

                            status = false;
                            goto cleanup;
                        }
                    }

                    /* Unless '+' is the last character in the filter, it must be succeeded by '/'. */
                    if( j < pListElement->topicFilterLength - 1 )
                    {
                        if( pListElement->pTopicFilter[ j + 1 ] != '/' )
                        {
                            IotLogError( "Invalid topic filter %.*s -- '+' must be succeeded by '/'.",
                                         pListElement->topicFilterLength,
                                         pListElement->pTopicFilter );

                            status = false;
                            goto cleanup;
                        }
                    }

                    break;

                /* Check that the multi-level wildcard '#' is used correctly. */
                case '#':

                    /* '#' must be the last character in the filter. */
                    if( j != pListElement->topicFilterLength - 1 )
                    {
                        IotLogError( "Invalid topic filter %.*s -- '#' must be the last character.",
                                     pListElement->topicFilterLength,
                                     pListElement->pTopicFilter );

                        status = false;
                        goto cleanup;
                    }

                    /* Unless '#' is standalone, it must be preceded by '/'. */
                    if( pListElement->topicFilterLength > 1 )
                    {
                        if( pListElement->pTopicFilter[ j - 1 ] != '/' )
                        {
                            IotLogError( "Invalid topic filter %.*s -- '#' must be preceded by '/'.",
                                         pListElement->topicFilterLength,
                                         pListElement->pTopicFilter );

                            status = false;
                            goto cleanup;
                        }
                    }

                    break;

                default:
                    break;
            }
        }
    }

cleanup:
    return status;
}

/*-----------------------------------------------------------*/

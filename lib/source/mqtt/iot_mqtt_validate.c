/*
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

/* Build using a config header, if provided. */
#ifdef IOT_CONFIG_FILE
    #include IOT_CONFIG_FILE
#endif

/* MQTT internal include. */
#include "private/iot_mqtt_internal.h"

/*-----------------------------------------------------------*/

bool _IotMqtt_ValidateNetIf( const IotMqttNetIf_t * const pNetworkInterface )
{
    /* Check for NULL. */
    if( pNetworkInterface == NULL )
    {
        IotLogError( "Network interface cannot be NULL." );

        return false;
    }

    /* Check for a non-NULL send function. */
    if( pNetworkInterface->send == NULL )
    {
        IotLogError( "Network interface send function must be set." );

        return false;
    }

    /* The MQTT 3.1.1 spec suggests disconnecting the client on errors. Check
     * that a function has been provided to do this. */
    if( pNetworkInterface->disconnect == NULL )
    {
        IotLogWarn( "No disconnect function was provided. The MQTT connection will not be "
                    "closed on errors, which is against MQTT 3.1.1 specification." );
    }

    /* Check that the freePacket function pointer is set if any other serializer
     * override is set. */
    #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
        if( pNetworkInterface->freePacket == NULL )
        {
            /* Check serializer overrides. */
            if( ( pNetworkInterface->serialize.connect != NULL ) ||
                ( pNetworkInterface->serialize.publish != NULL ) ||
                ( pNetworkInterface->serialize.publishSetDup != NULL ) ||
                ( pNetworkInterface->serialize.puback != NULL ) ||
                ( pNetworkInterface->serialize.subscribe != NULL ) ||
                ( pNetworkInterface->serialize.unsubscribe != NULL ) ||
                ( pNetworkInterface->serialize.pingreq != NULL ) ||
                ( pNetworkInterface->serialize.disconnect != NULL ) )
            {
                IotLogError( "Network interface must have a freePacket function "
                             "if a serializer override isn't NULL." );

                return false;
            }

            /* Check deserializer overrides. */
            if( ( pNetworkInterface->deserialize.connack != NULL ) ||
                ( pNetworkInterface->deserialize.puback != NULL ) ||
                ( pNetworkInterface->deserialize.publish != NULL ) ||
                ( pNetworkInterface->deserialize.suback != NULL ) ||
                ( pNetworkInterface->deserialize.unsuback != NULL ) ||
                ( pNetworkInterface->deserialize.pingresp != NULL ) )
            {
                IotLogError( "Network interface must have a freePacket function "
                             "if a deserializer override isn't NULL." );

                return false;
            }
        }
    #endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */

    return true;
}

/*-----------------------------------------------------------*/

bool _IotMqtt_ValidateConnect( const IotMqttConnectInfo_t * const pConnectInfo )
{
    /* Check for NULL. */
    if( pConnectInfo == NULL )
    {
        IotLogError( "MQTT connection information cannot be NULL." );

        return false;
    }

    /* Check that a client identifier was set. */
    if( pConnectInfo->pClientIdentifier == NULL )
    {
        IotLogError( "Client identifier must be set." );

        return false;
    }

    /* Check for a zero-length client identifier. Zero-length client identifiers
     * are not allowed with clean sessions. */
    if( pConnectInfo->clientIdentifierLength == 0 )
    {
        IotLogWarn( "A zero-length client identifier was provided." );

        if( pConnectInfo->cleanSession == true )
        {
            IotLogError( "A zero-length client identifier cannot be used with a clean session." );

            return false;
        }
    }

    /* Check that the number of persistent session subscriptions is valid. */
    if( pConnectInfo->cleanSession == false )
    {
        if( ( pConnectInfo->pPreviousSubscriptions != NULL ) &&
            ( pConnectInfo->previousSubscriptionCount == 0 ) )
        {
            IotLogError( "Previous subscription count cannot be 0." );

            return false;
        }
    }

    /* In MQTT 3.1.1, servers are not obligated to accept client identifiers longer
     * than 23 characters. */
    if( pConnectInfo->clientIdentifierLength > 23 )
    {
        IotLogWarn( "A client identifier length of %hu is longer than 23, which is "
                    "the longest client identifier a server must accept.",
                    pConnectInfo->clientIdentifierLength );
    }

    /* Check for compatibility with the AWS IoT MQTT service limits. */
    if( pConnectInfo->awsIotMqttMode == true )
    {
        /* Check that client identifier is within the service limit. */
        if( pConnectInfo->clientIdentifierLength > _AWS_IOT_MQTT_SERVER_MAX_CLIENTID )
        {
            IotLogError( "AWS IoT does not support client identifiers longer than %d bytes.",
                         _AWS_IOT_MQTT_SERVER_MAX_CLIENTID );

            return false;
        }

        /* Check for compliance with AWS IoT keep-alive limits. */
        if( pConnectInfo->keepAliveSeconds == 0 )
        {
            IotLogWarn( "AWS IoT does not support disabling keep-alive. Default keep-alive "
                        "of %d seconds will be used.",
                        _AWS_IOT_MQTT_SERVER_MAX_KEEPALIVE );
        }
        else if( pConnectInfo->keepAliveSeconds < _AWS_IOT_MQTT_SERVER_MIN_KEEPALIVE )
        {
            IotLogWarn( "AWS IoT does not support keep-alive intervals less than %d seconds. "
                        "An interval of %d seconds will be used.",
                        _AWS_IOT_MQTT_SERVER_MIN_KEEPALIVE,
                        _AWS_IOT_MQTT_SERVER_MIN_KEEPALIVE );
        }
        else if( pConnectInfo->keepAliveSeconds > _AWS_IOT_MQTT_SERVER_MAX_KEEPALIVE )
        {
            IotLogWarn( "AWS IoT does not support keep-alive intervals greater than %d seconds. "
                        "An interval of %d seconds will be used.",
                        _AWS_IOT_MQTT_SERVER_MAX_KEEPALIVE,
                        _AWS_IOT_MQTT_SERVER_MAX_KEEPALIVE );
        }
    }

    return true;
}

/*-----------------------------------------------------------*/

bool _IotMqtt_ValidatePublish( bool awsIotMqttMode,
                               const IotMqttPublishInfo_t * const pPublishInfo )
{
    /* Check for NULL. */
    if( pPublishInfo == NULL )
    {
        IotLogError( "Publish information cannot be NULL." );

        return false;
    }

    /* Check topic name for NULL or zero-length. */
    if( ( pPublishInfo->pTopicName == NULL ) || ( pPublishInfo->topicNameLength == 0 ) )
    {
        IotLogError( "Publish topic name must be set." );

        return false;
    }

    /* Only allow NULL payloads with zero-length. */
    if( ( pPublishInfo->pPayload == NULL ) && ( pPublishInfo->payloadLength != 0 ) )
    {
        IotLogError( "Nonzero payload length cannot have a NULL payload." );

        return false;
    }

    /* Check for a valid QoS. */
    if( pPublishInfo->qos != IOT_MQTT_QOS_0 )
    {
        if( pPublishInfo->qos != IOT_MQTT_QOS_1 )
        {
            IotLogError( "Publish QoS must be either 0 or 1." );

            return false;
        }
    }

    /* Check the retry parameters. */
    if( pPublishInfo->retryLimit > 0 )
    {
        if( pPublishInfo->retryMs == 0 )
        {
            IotLogError( "Publish retry time must be positive." );

            return false;
        }
    }

    /* Check for compatibility with AWS IoT MQTT server. */
    if( awsIotMqttMode == true )
    {
        /* Check for retained message. */
        if( pPublishInfo->retain == true )
        {
            IotLogError( "AWS IoT does not support retained publish messages." );

            return false;
        }

        /* Check topic name length. */
        if( pPublishInfo->topicNameLength > _AWS_IOT_MQTT_SERVER_MAX_TOPIC_LENGTH )
        {
            IotLogError( "AWS IoT does not support topic names longer than %d bytes.",
                         _AWS_IOT_MQTT_SERVER_MAX_TOPIC_LENGTH );

            return false;
        }
    }

    return true;
}

/*-----------------------------------------------------------*/

bool _IotMqtt_ValidateReference( IotMqttReference_t reference )
{
    _mqttOperation_t * pOperation = ( _mqttOperation_t * ) reference;

    /* Check for NULL. */
    if( pOperation == NULL )
    {
        IotLogError( "Reference cannot be NULL." );

        return false;
    }

    /* Check that reference is waitable. */
    if( ( pOperation->flags & IOT_MQTT_FLAG_WAITABLE ) != IOT_MQTT_FLAG_WAITABLE )
    {
        IotLogError( "Reference is not a waitable MQTT operation." );

        return false;
    }

    return true;
}

/*-----------------------------------------------------------*/

bool _IotMqtt_ValidateSubscriptionList( IotMqttOperationType_t operation,
                                        bool awsIotMqttMode,
                                        const IotMqttSubscription_t * const pListStart,
                                        size_t listSize )
{
    size_t i = 0;
    uint16_t j = 0;
    const IotMqttSubscription_t * pListElement = NULL;

    /* Operation must be either subscribe or unsubscribe. */
    IotMqtt_Assert( ( operation == IOT_MQTT_SUBSCRIBE ) ||
                    ( operation == IOT_MQTT_UNSUBSCRIBE ) );

    /* Check for empty list. */
    if( ( listSize == 0 ) || ( pListStart == NULL ) )
    {
        IotLogError( "Empty subscription list." );

        return false;
    }

    /* AWS IoT supports at most 8 topic filters in a single SUBSCRIBE packet. */
    if( awsIotMqttMode == true )
    {
        if( listSize > _AWS_IOT_MQTT_SERVER_MAX_TOPIC_FILTERS_PER_SUBSCRIBE )
        {
            IotLogError( "AWS IoT does not support more than %d topic filters per "
                         "subscription request.",
                         _AWS_IOT_MQTT_SERVER_MAX_TOPIC_FILTERS_PER_SUBSCRIBE );

            return false;
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

                    return false;
                }
            }

            if( pListElement->callback.function == NULL )
            {
                IotLogError( "Callback function must be set." );

                return false;
            }
        }

        /* Check subscription topic filter. */
        if( ( pListElement->pTopicFilter == NULL ) || ( pListElement->topicFilterLength == 0 ) )
        {
            IotLogError( "Subscription topic filter must be set." );

            return false;
        }

        /* Check for compatibility with AWS IoT MQTT server. */
        if( awsIotMqttMode == true )
        {
            /* Check topic filter length. */
            if( pListElement->topicFilterLength > _AWS_IOT_MQTT_SERVER_MAX_TOPIC_LENGTH )
            {
                IotLogError( "AWS IoT does not support topic filters longer than %d bytes.",
                             _AWS_IOT_MQTT_SERVER_MAX_TOPIC_LENGTH );

                return false;
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
                    if( ( j > 0 ) && ( pListElement->pTopicFilter[ j - 1 ] != '/' ) )
                    {
                        IotLogError( "Invalid topic filter %.*s -- '+' must be preceded by '/'.",
                                     pListElement->topicFilterLength,
                                     pListElement->pTopicFilter );

                        return false;
                    }

                    /* Unless '+' is the last character in the filter, it must be succeeded by '/'. */
                    if( ( j < pListElement->topicFilterLength - 1 ) &&
                        ( pListElement->pTopicFilter[ j + 1 ] != '/' ) )
                    {
                        IotLogError( "Invalid topic filter %.*s -- '+' must be succeeded by '/'.",
                                     pListElement->topicFilterLength,
                                     pListElement->pTopicFilter );

                        return false;
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

                        return false;
                    }

                    /* Unless '#' is standalone, it must be preceded by '/'. */
                    if( ( pListElement->topicFilterLength > 1 ) &&
                        ( pListElement->pTopicFilter[ j - 1 ] != '/' ) )
                    {
                        IotLogError( "Invalid topic filter %.*s -- '#' must be preceded by '/'.",
                                     pListElement->topicFilterLength,
                                     pListElement->pTopicFilter );

                        return false;
                    }

                    break;

                default:
                    break;
            }
        }
    }

    return true;
}

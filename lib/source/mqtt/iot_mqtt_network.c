/*
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
 * @file iot_mqtt_network.c
 * @brief Implements functions involving transport layer connections.
 */

/* Build using a config header, if provided. */
#ifdef IOT_CONFIG_FILE
    #include IOT_CONFIG_FILE
#endif

/* Standard includes. */
#include <string.h>

/* MQTT internal include. */
#include "private/iot_mqtt_internal.h"

/* Platform layer includes. */
#include "platform/iot_threads.h"

/*-----------------------------------------------------------*/

/**
 * @brief Send a PUBACK for a received QoS 1 PUBLISH packet.
 *
 * @param[in] pMqttConnection Which connection the PUBACK should be sent over.
 * @param[in] packetIdentifier Which packet identifier to include in PUBACK.
 */
static void _sendPuback( _mqttConnection_t * const pMqttConnection,
                         uint16_t packetIdentifier );

/*-----------------------------------------------------------*/

static void _sendPuback( _mqttConnection_t * const pMqttConnection,
                         uint16_t packetIdentifier )
{
    _mqttOperation_t * pPubackOperation = NULL;

    /* Choose a PUBACK serializer function. */
    IotMqttError_t ( * serializePuback )( uint16_t,
                                          uint8_t ** const,
                                          size_t * const ) = _IotMqtt_SerializePuback;

    #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
        if( pMqttConnection->network.serialize.puback != NULL )
        {
            serializePuback = pMqttConnection->network.serialize.puback;
        }
    #endif

    IotLogDebug( "Sending PUBACK for received PUBLISH %hu.", packetIdentifier );

    /* Create a PUBACK operation. */
    if( _IotMqtt_CreateOperation( &pPubackOperation,
                                  0,
                                  NULL ) != IOT_MQTT_SUCCESS )
    {
        IotLogWarn( "Failed to create PUBACK operation." );

        return;
    }

    /* Generate a PUBACK packet from the packet identifier. */
    if( serializePuback( packetIdentifier,
                         &( pPubackOperation->pMqttPacket ),
                         &( pPubackOperation->packetSize ) ) != IOT_MQTT_SUCCESS )
    {
        IotLogWarn( "Failed to generate PUBACK packet." );
        _IotMqtt_DestroyOperation( pPubackOperation );

        return;
    }

    /* Set the remaining members of the PUBACK operation and push it to the
     * send queue for network transmission. */
    pPubackOperation->operation = IOT_MQTT_PUBACK;
    pPubackOperation->pMqttConnection = pMqttConnection;

    if( _IotMqtt_EnqueueOperation( pPubackOperation,
                                   &( _IotMqttSend ) ) != IOT_MQTT_SUCCESS )
    {
        IotLogWarn( "Failed to enqueue PUBACK for sending." );
        _IotMqtt_DestroyOperation( pPubackOperation );
    }
}

/*-----------------------------------------------------------*/

int32_t IotMqtt_ReceiveCallback( void * pMqttConnection,
                                 void * pConnection,
                                 const uint8_t * pReceivedData,
                                 size_t dataLength,
                                 size_t offset,
                                 void ( *freeReceivedData )( void * ) )
{
    size_t bytesProcessed = 0, totalBytesProcessed = 0, remainingDataLength = 0;
    _mqttConnection_t * pConnectionInfo = *( ( _mqttConnection_t ** ) ( pMqttConnection ) );
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    uint16_t packetIdentifier = 0;
    const uint8_t * pNextPacket = pReceivedData;
    _mqttOperation_t * pOperation = NULL, * pFirstPublish = NULL, * pLastPublish = NULL;

    /* Network connection parameter is ignored. */
    ( void ) pConnection;

    /* Choose a packet type decoder function. */
    uint8_t ( * getPacketType )( const uint8_t * const,
                                 size_t ) = _IotMqtt_GetPacketType;

    #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
        if( pConnectionInfo->network.getPacketType != NULL )
        {
            getPacketType = pConnectionInfo->network.getPacketType;
        }
    #endif

    /* Ensure that offset is smaller than dataLength. */
    if( offset >= dataLength )
    {
        return 0;
    }

    /* Adjust the packet pointer based on the offset. */
    pNextPacket += offset;
    remainingDataLength = dataLength - offset;

    /* Process the stream of data until the entire stream is proccessed or an
     * incomplete packet is found. */
    while( ( totalBytesProcessed < remainingDataLength ) && ( status != IOT_MQTT_BAD_RESPONSE ) )
    {
        switch( getPacketType( pNextPacket, remainingDataLength - totalBytesProcessed ) )
        {
            case _MQTT_PACKET_TYPE_CONNACK:
                IotLog_PrintBuffer( "CONNACK in data stream:", pNextPacket, remainingDataLength - totalBytesProcessed );

                /* Deserialize the CONNACK. */
                IotMqttError_t ( * deserializeConnack )( const uint8_t * const,
                                                         size_t,
                                                         size_t * const ) = _IotMqtt_DeserializeConnack;

                #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
                    if( pConnectionInfo->network.deserialize.connack != NULL )
                    {
                        deserializeConnack = pConnectionInfo->network.deserialize.connack;
                    }
                #endif

                status = deserializeConnack( pNextPacket,
                                             remainingDataLength - totalBytesProcessed,
                                             &bytesProcessed );

                /* If a complete CONNACK was deserialized, check if there's an
                 * in-progress CONNECT operation. */
                if( bytesProcessed > 0 )
                {
                    pOperation = _IotMqtt_FindOperation( IOT_MQTT_CONNECT, NULL );

                    if( pOperation != NULL )
                    {
                        pOperation->status = status;
                        _IotMqtt_Notify( pOperation );
                    }
                }

                break;

            case _MQTT_PACKET_TYPE_PUBLISH:
                IotLog_PrintBuffer( "PUBLISH in data stream:", pNextPacket, remainingDataLength - totalBytesProcessed );

                /* Allocate memory to handle the incoming PUBLISH. */
                pOperation = IotMqtt_MallocOperation( sizeof( _mqttOperation_t ) );

                if( pOperation == NULL )
                {
                    IotLogWarn( "Failed to allocate memory for incoming PUBLISH." );
                    bytesProcessed = 0;

                    break;
                }

                /* Set the members of the incoming PUBLISH operation. */
                ( void ) memset( pOperation, 0x00, sizeof( _mqttOperation_t ) );
                pOperation->incomingPublish = true;
                pOperation->pMqttConnection = pConnectionInfo;

                /* Deserialize the PUBLISH into an IotMqttPublishInfo_t. */
                IotMqttError_t ( * deserializePublish )( const uint8_t * const,
                                                         size_t,
                                                         IotMqttPublishInfo_t * const,
                                                         uint16_t * const,
                                                         size_t * const ) = _IotMqtt_DeserializePublish;

                #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
                    if( pConnectionInfo->network.deserialize.publish != NULL )
                    {
                        deserializePublish = pConnectionInfo->network.deserialize.publish;
                    }
                #endif

                status = deserializePublish( pNextPacket,
                                             remainingDataLength - totalBytesProcessed,
                                             &( pOperation->publishInfo ),
                                             &packetIdentifier,
                                             &bytesProcessed );

                /* If a complete PUBLISH was deserialized, process it. */
                if( ( bytesProcessed > 0 ) && ( status == IOT_MQTT_SUCCESS ) )
                {
                    /* If a QoS 1 PUBLISH was received, send a PUBACK. */
                    if( pOperation->publishInfo.QoS == 1 )
                    {
                        _sendPuback( pConnectionInfo, packetIdentifier );
                    }

                    /* Change the first and last PUBLISH pointers. */
                    if( pFirstPublish == NULL )
                    {
                        pFirstPublish = pOperation;
                        pLastPublish = pOperation;
                    }
                    else
                    {
                        pLastPublish->pNextPublish = pOperation;
                        pLastPublish = pOperation;
                    }
                }
                else
                {
                    /* Free the PUBLISH operation here if the PUBLISH packet isn't
                     * valid. */
                    IotMqtt_FreeOperation( pOperation );
                }

                break;

            case _MQTT_PACKET_TYPE_PUBACK:
                IotLog_PrintBuffer( "PUBACK in data stream:", pNextPacket, remainingDataLength - totalBytesProcessed );

                /* Deserialize the PUBACK to get the packet identifier. */
                IotMqttError_t ( * deserializePuback )( const uint8_t * const,
                                                        size_t,
                                                        uint16_t * const,
                                                        size_t * const ) = _IotMqtt_DeserializePuback;

                #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
                    if( pConnectionInfo->network.deserialize.puback != NULL )
                    {
                        deserializePuback = pConnectionInfo->network.deserialize.puback;
                    }
                #endif

                status = deserializePuback( pNextPacket,
                                            remainingDataLength - totalBytesProcessed,
                                            &packetIdentifier,
                                            &bytesProcessed );

                /* If a complete PUBACK packet was deserialized, find an in-progress
                 * PUBLISH with a matching client identifier. */
                if( bytesProcessed > 0 )
                {
                    pOperation = _IotMqtt_FindOperation( IOT_MQTT_PUBLISH_TO_SERVER, &packetIdentifier );

                    if( pOperation != NULL )
                    {
                        pOperation->status = status;
                        _IotMqtt_Notify( pOperation );
                    }
                }

                break;

            case _MQTT_PACKET_TYPE_SUBACK:
                IotLog_PrintBuffer( "SUBACK in data stream:", pNextPacket, remainingDataLength - totalBytesProcessed );

                /* Deserialize the SUBACK to get the packet identifier. */
                IotMqttError_t ( * deserializeSuback )( IotMqttConnection_t,
                                                        const uint8_t * const,
                                                        size_t,
                                                        uint16_t * const,
                                                        size_t * const ) = _IotMqtt_DeserializeSuback;

                #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
                    if( pConnectionInfo->network.deserialize.suback != NULL )
                    {
                        deserializeSuback = pConnectionInfo->network.deserialize.suback;
                    }
                #endif

                status = deserializeSuback( pConnectionInfo,
                                            pNextPacket,
                                            remainingDataLength - totalBytesProcessed,
                                            &packetIdentifier,
                                            &bytesProcessed );

                /* If a complete SUBACK was deserialized, find an in-progress
                 * SUBACK with a matching client identifier. */
                if( bytesProcessed > 0 )
                {
                    pOperation = _IotMqtt_FindOperation( IOT_MQTT_SUBSCRIBE, &packetIdentifier );

                    if( pOperation != NULL )
                    {
                        pOperation->status = status;
                        _IotMqtt_Notify( pOperation );
                    }
                }

                break;

            case _MQTT_PACKET_TYPE_UNSUBACK:
                IotLog_PrintBuffer( "UNSUBACK in data stream:", pNextPacket, remainingDataLength - totalBytesProcessed );

                /* Deserialize the UNSUBACK to get the packet identifier. */
                IotMqttError_t ( * deserializeUnsuback )( const uint8_t * const,
                                                          size_t,
                                                          uint16_t * const,
                                                          size_t * const ) = _IotMqtt_DeserializeUnsuback;

                #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
                    if( pConnectionInfo->network.deserialize.unsuback != NULL )
                    {
                        deserializeUnsuback = pConnectionInfo->network.deserialize.unsuback;
                    }
                #endif

                status = deserializeUnsuback( pNextPacket,
                                              remainingDataLength - totalBytesProcessed,
                                              &packetIdentifier,
                                              &bytesProcessed );

                /* If a complete UNSUBACK was deserialized, find an in-progress
                 * UNSUBACK with a matching client identifier. */
                if( bytesProcessed > 0 )
                {
                    pOperation = _IotMqtt_FindOperation( IOT_MQTT_UNSUBSCRIBE, &packetIdentifier );

                    if( pOperation != NULL )
                    {
                        pOperation->status = status;
                        _IotMqtt_Notify( pOperation );
                    }
                }

                break;

            case _MQTT_PACKET_TYPE_PINGRESP:
                IotLog_PrintBuffer( "PINGRESP in data stream:", pNextPacket, remainingDataLength - totalBytesProcessed );

                /* Deserialize the PINGRESP. */
                IotMqttError_t ( * deserializePingresp )( const uint8_t * const,
                                                          size_t,
                                                          size_t * const ) = _IotMqtt_DeserializePingresp;

                #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
                    if( pConnectionInfo->network.deserialize.pingresp != NULL )
                    {
                        deserializePingresp = pConnectionInfo->network.deserialize.pingresp;
                    }
                #endif

                status = deserializePingresp( pNextPacket,
                                              remainingDataLength - totalBytesProcessed,
                                              &bytesProcessed );

                /* If a complete PINGRESP was deserialized, check if there's an
                 * in-progress PINGREQ operation. */
                if( bytesProcessed > 0 )
                {
                    pOperation = _IotMqtt_FindOperation( IOT_MQTT_PINGREQ, NULL );

                    if( pOperation != NULL )
                    {
                        pOperation->status = status;
                        _IotMqtt_Notify( pOperation );
                    }
                }

                break;

            default:

                /* If an unknown packet is received, stop processing pReceivedData. */
                IotLogError( "Unknown packet type %02x received.",
                             pNextPacket[ 0 ] );

                bytesProcessed = 1;
                status = IOT_MQTT_BAD_RESPONSE;

                break;
        }

        /* Check if a protocol violation was encountered. */
        if( ( bytesProcessed > 0 ) && ( status == IOT_MQTT_BAD_RESPONSE ) )
        {
            IotLogError( "MQTT protocol violation encountered. Closing network connection" );

            /* Clean up any previously allocated incoming PUBLISH operations. */
            while( pFirstPublish != NULL )
            {
                pLastPublish = pFirstPublish;
                pFirstPublish = pFirstPublish->pNextPublish;

                IotMqtt_FreeOperation( pLastPublish );
            }

            pLastPublish = NULL;

            /* Prevent the timer thread from running, then set the error flag. */
            IotMutex_Lock( &( pConnectionInfo->timerMutex ) );

            pConnectionInfo->disconnected = true;

            if( pConnectionInfo->network.disconnect != NULL )
            {
                pConnectionInfo->network.disconnect( 0, pConnectionInfo->network.pDisconnectContext );
            }
            else
            {
                IotLogWarn( "No disconnect function was set. Network connection not closed." );
            }

            IotMutex_Unlock( &( pConnectionInfo->timerMutex ) );

            return -1;
        }

        /* Check if a partial packet was encountered. */
        if( bytesProcessed == 0 )
        {
            break;
        }

        /* Move the "next packet" pointer and increment the number of bytes processed. */
        pNextPacket += bytesProcessed;
        totalBytesProcessed += bytesProcessed;

        /* Number of bytes processed should never exceed remainingDataLength. */
        IotMqtt_Assert( pNextPacket - totalBytesProcessed - offset == pReceivedData );
        IotMqtt_Assert( totalBytesProcessed <= remainingDataLength );
    }

    /* Only free pReceivedData if all bytes were processed and no PUBLISH messages
     * were in the data stream. */
    if( ( freeReceivedData != NULL ) &&
        ( totalBytesProcessed == remainingDataLength ) &&
        ( pFirstPublish == NULL ) )
    {
        IotMqtt_Assert( pLastPublish == NULL );

        freeReceivedData( ( void * ) pReceivedData );
    }

    /* Add all PUBLISH messages to the pending operations queue. */
    if( pLastPublish != NULL )
    {
        /* If all bytes of the receive buffer were processed, set the function
         * to free the receive buffer. */
        if( ( totalBytesProcessed == remainingDataLength ) && ( freeReceivedData != NULL ) )
        {
            pLastPublish->pReceivedData = pReceivedData;
            pLastPublish->freeReceivedData = freeReceivedData;
        }
        else
        {
            /* When some of the receive buffer is unprocessed, the receive buffer is
             * given back to the calling function. The MQTT library cannot guarantee
             * that the calling function will keep the receive buffer in scope;
             * therefore, data in the receive buffer must be copied for the MQTT
             * library's use. */
            for( pOperation = pFirstPublish; pOperation != NULL; pOperation = pOperation->pNextPublish )
            {
                /* Neither the buffer pointer nor the free function should be set. */
                IotMqtt_Assert( pOperation->pReceivedData == NULL );
                IotMqtt_Assert( pOperation->freeReceivedData == NULL );

                /* Allocate a new buffer to hold the topic name and payload. */
                pOperation->pReceivedData = IotMqtt_MallocMessage( pOperation->publishInfo.topicNameLength +
                                                                   pOperation->publishInfo.payloadLength );

                if( pOperation->pReceivedData != NULL )
                {
                    /* Copy the topic name and payload. */
                    ( void ) memcpy( ( void * ) pOperation->pReceivedData,
                                     pOperation->publishInfo.pTopicName,
                                     pOperation->publishInfo.topicNameLength );
                    ( void ) memcpy( ( uint8_t * ) ( pOperation->pReceivedData ) +
                                     pOperation->publishInfo.topicNameLength,
                                     pOperation->publishInfo.pPayload,
                                     pOperation->publishInfo.payloadLength );

                    /* Set the topic name and payload pointers into the new buffer.
                     * Also set the free function. */
                    pOperation->publishInfo.pTopicName = pOperation->pReceivedData;
                    pOperation->publishInfo.pPayload = ( uint8_t * ) ( pOperation->pReceivedData ) +
                                                       pOperation->publishInfo.topicNameLength;
                    pOperation->freeReceivedData = IotMqtt_FreeMessage;
                }
                else
                {
                    /* If a new buffer couldn't be allocated, clear the topic name and
                     * payload pointers so that this PUBLISH message will be ignored. */
                    IotLogWarn( "Failed to allocate memory for incoming PUBLISH message." );
                    pOperation->publishInfo.pTopicName = NULL;
                    pOperation->publishInfo.topicNameLength = 0;
                    pOperation->publishInfo.pPayload = NULL;
                    pOperation->publishInfo.payloadLength = 0;
                }
            }
        }

        if( _IotMqtt_ScheduleOperation( pFirstPublish,
                                        _IotMqtt_ProcessIncomingPublish ) != IOT_MQTT_SUCCESS )
        {
            IotLogWarn( "Failed to schedule incoming PUBLISH callback." );
        }
    }

    return ( int32_t ) totalBytesProcessed;
}

/*-----------------------------------------------------------*/

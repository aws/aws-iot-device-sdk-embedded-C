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

/* Error handling include. */
#include "private/iot_error.h"

/* MQTT internal include. */
#include "private/iot_mqtt_internal.h"

/* Platform layer includes. */
#include "platform/iot_threads.h"

/*-----------------------------------------------------------*/

/**
 * @brief Check if an incoming packet type is valid.
 *
 * @param[in] packetType The packet type to check.
 *
 * @return `true` if the packet type is valid; `false` otherwise.
 */
static bool _incomingPacketValid( uint8_t packetType );

/**
 * @brief Get an incoming MQTT packet from the network.
 *
 * @param[in] pNetworkConnection Network connection to use for receive, which
 * may be different from the network connection associated with the MQTT connection.
 * @param[in] pMqttConnection The associated MQTT connection.
 * @param[out] pIncomingPacket Output parameter for the incoming packet.
 *
 * @return `true` if a packet was successfully received; `false` otherwise.
 */
static bool _getIncomingPacket( void * pNetworkConnection,
                                const _mqttConnection_t * pMqttConnection,
                                _mqttPacket_t * pIncomingPacket );

/**
 * @brief Deserialize a packet received from the network.
 *
 * @param[in] pMqttConnection The associated MQTT connection.
 * @param[in] pIncomingPacket The packet received from the network.
 *
 * @return `true` if the incoming packet was successfully deserialized; `false`
 * otherwise.
 */
static bool _deserializeIncomingPacket( _mqttConnection_t * pMqttConnection,
                                        _mqttPacket_t * pIncomingPacket );

/**
 * @brief Send a PUBACK for a received QoS 1 PUBLISH packet.
 *
 * @param[in] pMqttConnection Which connection the PUBACK should be sent over.
 * @param[in] packetIdentifier Which packet identifier to include in PUBACK.
 */
static void _sendPuback( _mqttConnection_t * pMqttConnection,
                         uint16_t packetIdentifier );

/*-----------------------------------------------------------*/

static bool _incomingPacketValid( uint8_t packetType )
{
    bool status = true;

    /* Check packet type. Mask out lower bits to ignore flags. */
    switch( packetType & 0xf0 )
    {
        /* Valid incoming packet types. */
        case _MQTT_PACKET_TYPE_CONNACK:
        case _MQTT_PACKET_TYPE_PUBLISH:
        case _MQTT_PACKET_TYPE_PUBACK:
        case _MQTT_PACKET_TYPE_SUBACK:
        case _MQTT_PACKET_TYPE_UNSUBACK:
        case _MQTT_PACKET_TYPE_PINGRESP:
            break;

        /* Any other packet type is invalid. */
        default:
            status = false;
            break;
    }

    return status;
}

/*-----------------------------------------------------------*/

static bool _getIncomingPacket( void * pNetworkConnection,
                                const _mqttConnection_t * pMqttConnection,
                                _mqttPacket_t * pIncomingPacket )
{
    _IOT_FUNCTION_ENTRY( bool, true );
    size_t dataBytesRead = 0;

    /* Default functions for retrieving packet type and length. */
    uint8_t ( * getPacketType )( void *,
                                 const IotNetworkInterface_t * ) = _IotMqtt_GetPacketType;
    size_t ( * getRemainingLength )( void *,
                                     const IotNetworkInterface_t * ) = _IotMqtt_GetRemainingLength;

    /* No buffer for remaining data should be allocated. */
    IotMqtt_Assert( pIncomingPacket->pRemainingData == NULL );
    IotMqtt_Assert( pIncomingPacket->remainingLength == 0 );

    /* Choose packet type and length functions. */
    #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
        if( pMqttConnection->pSerializer != NULL )
        {
            if( pMqttConnection->pSerializer->getPacketType != NULL )
            {
                getPacketType = pMqttConnection->pSerializer->getPacketType;
            }
            else
            {
                _EMPTY_ELSE_MARKER;
            }

            if( pMqttConnection->pSerializer->getRemainingLength != NULL )
            {
                getRemainingLength = pMqttConnection->pSerializer->getRemainingLength;
            }
            else
            {
                _EMPTY_ELSE_MARKER;
            }
        }
        else
        {
            _EMPTY_ELSE_MARKER;
        }
    #endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */

    /* Read the packet type, which is the first byte available. */
    pIncomingPacket->type = getPacketType( pNetworkConnection,
                                           pMqttConnection->pNetworkInterface );

    /* Check that the incoming packet type is valid. */
    if( _incomingPacketValid( pIncomingPacket->type ) == false )
    {
        IotLogError( "(MQTT connection %p) Unknown packet type %02x received.",
                     pMqttConnection,
                     pIncomingPacket->type );

        _IOT_SET_AND_GOTO_CLEANUP( false );
    }
    else
    {
        _EMPTY_ELSE_MARKER;
    }

    /* Read the remaining length. */
    pIncomingPacket->remainingLength = getRemainingLength( pNetworkConnection,
                                                           pMqttConnection->pNetworkInterface );

    if( pIncomingPacket->remainingLength == _MQTT_REMAINING_LENGTH_INVALID )
    {
        _IOT_SET_AND_GOTO_CLEANUP( false );
    }
    else
    {
        _EMPTY_ELSE_MARKER;
    }

    /* Allocate a buffer for the remaining data and read the data. */
    if( pIncomingPacket->remainingLength > 0 )
    {
        pIncomingPacket->pRemainingData = IotMqtt_MallocMessage( pIncomingPacket->remainingLength );

        if( pIncomingPacket->pRemainingData == NULL )
        {
            _IOT_SET_AND_GOTO_CLEANUP( false );
        }
        else
        {
            _EMPTY_ELSE_MARKER;
        }

        dataBytesRead = pMqttConnection->pNetworkInterface->receive( pNetworkConnection,
                                                                     pIncomingPacket->pRemainingData,
                                                                     pIncomingPacket->remainingLength );

        if( dataBytesRead != pIncomingPacket->remainingLength )
        {
            _IOT_SET_AND_GOTO_CLEANUP( false );
        }
        else
        {
            _EMPTY_ELSE_MARKER;
        }
    }
    else
    {
        _EMPTY_ELSE_MARKER;
    }

    /* Clean up on error. */
    _IOT_FUNCTION_CLEANUP_BEGIN();

    if( status == false )
    {
        if( pIncomingPacket->pRemainingData != NULL )
        {
            IotMqtt_FreeMessage( pIncomingPacket->pRemainingData );
        }
        else
        {
            _EMPTY_ELSE_MARKER;
        }
    }
    else
    {
        _EMPTY_ELSE_MARKER;
    }

    _IOT_FUNCTION_CLEANUP_END();
}

/*-----------------------------------------------------------*/

static bool _deserializeIncomingPacket( _mqttConnection_t * pMqttConnection,
                                        _mqttPacket_t * pIncomingPacket )
{
    IotMqttError_t status = IOT_MQTT_STATUS_PENDING;
    _mqttOperation_t * pOperation = NULL;

    /* Deserializer function. */
    IotMqttError_t ( * deserialize )( _mqttPacket_t * ) = NULL;

    /* A buffer for remaining data must be allocated if remaining length is not 0. */
    IotMqtt_Assert( ( pIncomingPacket->remainingLength > 0 ) ==
                    ( pIncomingPacket->pRemainingData != NULL ) );

    /* Only valid packets should be given to this function. */
    IotMqtt_Assert( _incomingPacketValid( pIncomingPacket->type ) == true );

    /* Mask out the low bits of packet type to ignore flags. */
    switch( ( pIncomingPacket->type & 0xf0 ) )
    {
        case _MQTT_PACKET_TYPE_CONNACK:
            IotLogDebug( "(MQTT connection %p) CONNACK in data stream.", pMqttConnection );

            /* Choose CONNACK deserializer. */
            deserialize = _IotMqtt_DeserializeConnack;

            #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
                if( pMqttConnection->pSerializer != NULL )
                {
                    if( pMqttConnection->pSerializer->deserialize.connack != NULL )
                    {
                        deserialize = pMqttConnection->pSerializer->deserialize.connack;
                    }
                    else
                    {
                        _EMPTY_ELSE_MARKER;
                    }
                }
                else
                {
                    _EMPTY_ELSE_MARKER;
                }
            #endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */

            /* Deserialize CONNACK and notify of result. */
            status = deserialize( pIncomingPacket );
            pOperation = _IotMqtt_FindOperation( pMqttConnection,
                                                 IOT_MQTT_CONNECT,
                                                 NULL );

            if( pOperation != NULL )
            {
                pOperation->status = status;
                _IotMqtt_Notify( pOperation );
            }

            break;

        case _MQTT_PACKET_TYPE_PUBLISH:
            IotLogDebug( "(MQTT connection %p) PUBLISH in data stream.", pMqttConnection );

            /* Allocate memory to handle the incoming PUBLISH. */
            pOperation = IotMqtt_MallocOperation( sizeof( _mqttOperation_t ) );

            if( pOperation == NULL )
            {
                IotLogWarn( "Failed to allocate memory for incoming PUBLISH." );
                status = IOT_MQTT_NO_MEMORY;

                break;
            }

            /* Set the members of the incoming PUBLISH operation. */
            ( void ) memset( pOperation, 0x00, sizeof( _mqttOperation_t ) );
            pOperation->incomingPublish = true;
            pOperation->pMqttConnection = pMqttConnection;

            pIncomingPacket->pIncomingPublish = pOperation;

            /* Choose a PUBLISH deserializer. */
            deserialize = _IotMqtt_DeserializePublish;

            #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
                if( pMqttConnection->pSerializer != NULL )
                {
                    if( pMqttConnection->pSerializer->deserialize.publish != NULL )
                    {
                        deserialize = pMqttConnection->pSerializer->deserialize.publish;
                    }
                }
                else
                {
                    _EMPTY_ELSE_MARKER;
                }
            #endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */

            /* Deserialize incoming PUBLISH. */
            status = deserialize( pIncomingPacket );

            if( status == IOT_MQTT_SUCCESS )
            {
                /* Send a PUBACK for QoS 1 PUBLISH. */
                if( pOperation->publishInfo.qos == IOT_MQTT_QOS_1 )
                {
                    _sendPuback( pMqttConnection, pIncomingPacket->packetIdentifier );
                }
                else
                {
                    _EMPTY_ELSE_MARKER;
                }

                /* Transfer ownership of the received MQTT packet to the PUBLISH operation. */
                pOperation->pReceivedData = pIncomingPacket->pRemainingData;
                pIncomingPacket->pRemainingData = NULL;

                /* Schedule PUBLISH for callback invocation. */
                status = _IotMqtt_ScheduleOperation( pOperation, _IotMqtt_ProcessIncomingPublish, 0 );
            }

            /* Free PUBLISH operation on error. */
            if( status != IOT_MQTT_SUCCESS )
            {
                /* Check ownership of the received MQTT packet. */
                if( pOperation->pReceivedData != NULL )
                {
                    /* Retrieve the pointer MQTT packet pointer so it may be freed later. */
                    IotMqtt_Assert( pIncomingPacket->pRemainingData == NULL );
                    pIncomingPacket->pRemainingData = ( uint8_t * ) pOperation->pReceivedData;
                }
                else
                {
                    /* The received MQTT packet must be part of the incoming
                     * packet structure. */
                    IotMqtt_Assert( pIncomingPacket->pRemainingData != NULL );
                }

                IotMqtt_Assert( pOperation != NULL );
                IotMqtt_FreeOperation( pOperation );
            }

            break;

        case _MQTT_PACKET_TYPE_PUBACK:
            IotLogDebug( "(MQTT connection %p) PUBACK in data stream.", pMqttConnection );

            /* Choose PUBACK deserializer. */
            deserialize = _IotMqtt_DeserializePuback;

            #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
                if( pMqttConnection->pSerializer != NULL )
                {
                    if( pMqttConnection->pSerializer->deserialize.puback != NULL )
                    {
                        deserialize = pMqttConnection->pSerializer->deserialize.puback;
                    }
                    else
                    {
                        _EMPTY_ELSE_MARKER;
                    }
                }
                else
                {
                    _EMPTY_ELSE_MARKER;
                }
            #endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */

            /* Deserialize PUBACK and notify of result. */
            status = deserialize( pIncomingPacket );
            pOperation = _IotMqtt_FindOperation( pMqttConnection,
                                                 IOT_MQTT_PUBLISH_TO_SERVER,
                                                 &( pIncomingPacket->packetIdentifier ) );

            if( pOperation != NULL )
            {
                pOperation->status = status;
                _IotMqtt_Notify( pOperation );
            }

            break;

        case _MQTT_PACKET_TYPE_SUBACK:
            IotLogDebug( "(MQTT connection %p) SUBACK in data stream.", pMqttConnection );

            /* Choose SUBACK deserializer. */
            deserialize = _IotMqtt_DeserializeSuback;

            #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
                if( pMqttConnection->pSerializer != NULL )
                {
                    if( pMqttConnection->pSerializer->deserialize.suback != NULL )
                    {
                        deserialize = pMqttConnection->pSerializer->deserialize.suback;
                    }
                    else
                    {
                        _EMPTY_ELSE_MARKER;
                    }
                }
                else
                {
                    _EMPTY_ELSE_MARKER;
                }
            #endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */

            /* Deserialize SUBACK and notify of result. */
            status = deserialize( pIncomingPacket );
            pOperation = _IotMqtt_FindOperation( pMqttConnection,
                                                 IOT_MQTT_SUBSCRIBE,
                                                 &( pIncomingPacket->packetIdentifier ) );

            if( pOperation != NULL )
            {
                pOperation->status = status;
                _IotMqtt_Notify( pOperation );
            }

            break;

        case _MQTT_PACKET_TYPE_UNSUBACK:
            IotLogDebug( "(MQTT connection %p) UNSUBACK in data stream.", pMqttConnection );

            /* Choose UNSUBACK deserializer. */
            deserialize = _IotMqtt_DeserializeUnsuback;

            #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
                if( pMqttConnection->pSerializer != NULL )
                {
                    if( pMqttConnection->pSerializer->deserialize.unsuback != NULL )
                    {
                        deserialize = pMqttConnection->pSerializer->deserialize.unsuback;
                    }
                }
                else
                {
                    _EMPTY_ELSE_MARKER;
                }
            #endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */

            /* Deserialize UNSUBACK and notify of result. */
            status = deserialize( pIncomingPacket );
            pOperation = _IotMqtt_FindOperation( pMqttConnection,
                                                 IOT_MQTT_UNSUBSCRIBE,
                                                 &( pIncomingPacket->packetIdentifier ) );

            if( pOperation != NULL )
            {
                pOperation->status = status;
                _IotMqtt_Notify( pOperation );
            }

            break;

        default:
            /* The only remaining valid type is PINGRESP. */
            IotMqtt_Assert( pIncomingPacket->type == _MQTT_PACKET_TYPE_PINGRESP );
            IotLogDebug( "(MQTT connection %p) PINGRESP in data stream.", pMqttConnection );

            /* Choose PINGRESP deserializer. */
            deserialize = _IotMqtt_DeserializePingresp;

            #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
                if( pMqttConnection->pSerializer != NULL )
                {
                    if( pMqttConnection->pSerializer->deserialize.pingresp != NULL )
                    {
                        deserialize = pMqttConnection->pSerializer->deserialize.pingresp;
                    }
                }
                else
                {
                    _EMPTY_ELSE_MARKER;
                }
            #endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */

            /* Deserialize PINGRESP. */
            status = deserialize( pIncomingPacket );

            if( status == IOT_MQTT_SUCCESS )
            {
                IotMutex_Lock( &( pMqttConnection->referencesMutex ) );

                if( pMqttConnection->keepAliveFailure == false )
                {
                    IotLogWarn( "(MQTT connection %p) Unexpected PINGRESP received.",
                                pMqttConnection );
                }
                else
                {
                    IotLogDebug( "(MQTT connection %p) PINGRESP successfully parsed.",
                                 pMqttConnection );

                    pMqttConnection->keepAliveFailure = false;
                }

                IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );
            }

            break;
    }

    if( status != IOT_MQTT_SUCCESS )
    {
        IotLogError( "(MQTT connection %p) Packet parser status %s.",
                     pMqttConnection,
                     IotMqtt_strerror( status ) );
    }
    else
    {
        _EMPTY_ELSE_MARKER;
    }

    return( status == IOT_MQTT_SUCCESS );
}

/*-----------------------------------------------------------*/

static void _sendPuback( _mqttConnection_t * pMqttConnection,
                         uint16_t packetIdentifier )
{
    IotMqttError_t serializeStatus = IOT_MQTT_SUCCESS;
    uint8_t * pPuback = NULL;
    size_t pubackSize = 0, bytesSent = 0;

    /* Default PUBACK serializer and free packet functions. */
    IotMqttError_t ( * serializePuback )( uint16_t,
                                          uint8_t **,
                                          size_t * ) = _IotMqtt_SerializePuback;
    void ( * freePacket )( uint8_t * ) = _IotMqtt_FreePacket;

    /* Increment the reference count for the MQTT connection. */
    if( _IotMqtt_IncrementConnectionReferences( pMqttConnection ) == true )
    {
        IotLogDebug( "(MQTT connection %p) Sending PUBACK for received PUBLISH %hu.",
                     pMqttConnection,
                     packetIdentifier );

        /* Choose PUBACK serializer and free packet functions. */
        #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
            if( pMqttConnection->pSerializer != NULL )
            {
                if( pMqttConnection->pSerializer->serialize.puback != NULL )
                {
                    serializePuback = pMqttConnection->pSerializer->serialize.puback;
                }
                else
                {
                    _EMPTY_ELSE_MARKER;
                }
            }
            else
            {
                _EMPTY_ELSE_MARKER;
            }
        #endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */
        #if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1
            if( pMqttConnection->pSerializer != NULL )
            {
                if( pMqttConnection->pSerializer->freePacket != NULL )
                {
                    freePacket = pMqttConnection->pSerializer->freePacket;
                }
                else
                {
                    _EMPTY_ELSE_MARKER;
                }
            }
            else
            {
                _EMPTY_ELSE_MARKER;
            }
        #endif /* if IOT_MQTT_ENABLE_SERIALIZER_OVERRIDES == 1 */

        /* Generate a PUBACK packet from the packet identifier. */
        serializeStatus = serializePuback( packetIdentifier,
                                           &pPuback,
                                           &pubackSize );

        if( serializeStatus != IOT_MQTT_SUCCESS )
        {
            IotLogWarn( "(MQTT connection %p) Failed to generate PUBACK packet for "
                        "received PUBLISH %hu.",
                        pMqttConnection,
                        packetIdentifier );
        }
        else
        {
            bytesSent = pMqttConnection->pNetworkInterface->send( pMqttConnection->pNetworkConnection,
                                                                  pPuback,
                                                                  pubackSize );

            if( bytesSent != pubackSize )
            {
                IotLogWarn( "(MQTT connection %p) Failed to send PUBACK for received"
                            " PUBLISH %hu.",
                            pMqttConnection,
                            packetIdentifier );
            }
            else
            {
                IotLogDebug( "(MQTT connection %p) PUBACK for received PUBLISH %hu sent.",
                             pMqttConnection,
                             packetIdentifier );
            }

            freePacket( pPuback );
        }

        _IotMqtt_DecrementConnectionReferences( pMqttConnection );
    }
    else
    {
        IotLogWarn( "(MQTT connection %p) Connection is closed, PUBACK for received"
                    " PUBLISH %hu will not be sent.",
                    pMqttConnection,
                    packetIdentifier );
    }
}

/*-----------------------------------------------------------*/

bool _IotMqtt_GetNextByte( void * pNetworkConnection,
                           const IotNetworkInterface_t * pNetworkInterface,
                           uint8_t * pIncomingByte )
{
    bool status = false;
    uint8_t incomingByte = 0;
    size_t bytesReceived = 0;

    /* Attempt to read 1 byte. */
    bytesReceived = pNetworkInterface->receive( pNetworkConnection,
                                                &incomingByte,
                                                1 );

    /* Set the output parameter and return success if 1 byte was read. */
    if( bytesReceived == 1 )
    {
        *pIncomingByte = incomingByte;
        status = true;
    }
    else
    {
        /* Network receive must return 0 on failure. */
        IotMqtt_Assert( bytesReceived == 0 );
    }

    return status;
}

/*-----------------------------------------------------------*/

void _IotMqtt_CloseNetworkConnection( _mqttConnection_t * pMqttConnection )
{
    IotTaskPoolError_t taskPoolStatus = IOT_TASKPOOL_SUCCESS;
    IotNetworkError_t closeStatus = IOT_NETWORK_SUCCESS;

    /* Mark the MQTT connection as disconnected and the keep-alive as failed. */
    IotMutex_Lock( &( pMqttConnection->referencesMutex ) );
    pMqttConnection->disconnected = true;
    pMqttConnection->keepAliveFailure = true;

    if( pMqttConnection->keepAliveMs != 0 )
    {
        /* Keep-alive must have a PINGREQ allocated. */
        IotMqtt_Assert( pMqttConnection->pPingreqPacket != NULL );
        IotMqtt_Assert( pMqttConnection->pingreqPacketSize != 0 );

        /* PINGREQ provides a reference to the connection, so reference count must
         * be nonzero. */
        IotMqtt_Assert( pMqttConnection->references > 0 );

        /* Attempt to cancel the keep-alive job. */
        taskPoolStatus = IotTaskPool_TryCancel( IOT_SYSTEM_TASKPOOL,
                                                &( pMqttConnection->keepAliveJob ),
                                                NULL );

        /* If the keep-alive job was not canceled, it must be already executing.
         * Any other return value is invalid. */
        IotMqtt_Assert( ( taskPoolStatus == IOT_TASKPOOL_SUCCESS ) ||
                        ( taskPoolStatus == IOT_TASKPOOL_CANCEL_FAILED ) );

        /* Clean up keep-alive if its job was successfully canceled. Otherwise,
         * the executing keep-alive job will clean up itself. */
        if( taskPoolStatus == IOT_TASKPOOL_SUCCESS )
        {
            /* Clean up PINGREQ packet and job. */
            _IotMqtt_FreePacket( pMqttConnection->pPingreqPacket );

            /* Clear data about the keep-alive. */
            pMqttConnection->keepAliveMs = 0;
            pMqttConnection->pPingreqPacket = NULL;
            pMqttConnection->pingreqPacketSize = 0;

            /* Keep-alive is cleaned up; decrement reference count. Since this
             * function must be followed with a call to DISCONNECT, a check to
             * destroy the connection is not done here. */
            pMqttConnection->references--;

            IotLogDebug( "(MQTT connection %p) Keep-alive job canceled and cleaned up.",
                         pMqttConnection );
        }
        else
        {
            _EMPTY_ELSE_MARKER;
        }
    }
    else
    {
        _EMPTY_ELSE_MARKER;
    }

    IotMutex_Unlock( &( pMqttConnection->referencesMutex ) );

    /* Close the network connection regardless of whether an MQTT DISCONNECT
     * packet was sent. */
    if( pMqttConnection->pNetworkInterface->close != NULL )
    {
        closeStatus = pMqttConnection->pNetworkInterface->close( pMqttConnection->pNetworkConnection );

        if( closeStatus == IOT_NETWORK_SUCCESS )
        {
            IotLogInfo( "(MQTT connection %p) Network connection closed.", pMqttConnection );
        }
        else
        {
            IotLogWarn( "(MQTT connection %p) Failed to close network connection, error %d.",
                        pMqttConnection,
                        closeStatus );
        }
    }
    else
    {
        IotLogWarn( "(MQTT connection %p) No network close function was set. Network connection"
                    " not closed.", pMqttConnection );
    }
}

/*-----------------------------------------------------------*/

void IotMqtt_ReceiveCallback( void * pNetworkConnection,
                              void * pReceiveContext )
{
    bool status = true;
    _mqttPacket_t incomingPacket = { 0 };

    /* Cast context to correct type. */
    _mqttConnection_t * pMqttConnection = ( _mqttConnection_t * ) pReceiveContext;

    /* Read an MQTT packet from the network. */
    status = _getIncomingPacket( pNetworkConnection,
                                 pMqttConnection,
                                 &incomingPacket );

    if( status == true )
    {
        /* Deserialize the received packet. */
        status = _deserializeIncomingPacket( pMqttConnection,
                                             &incomingPacket );

        /* Free any buffers allocated for the MQTT packet. */
        if( incomingPacket.pRemainingData != NULL )
        {
            IotMqtt_FreeMessage( incomingPacket.pRemainingData );
        }
        else
        {
            _EMPTY_ELSE_MARKER;
        }
    }
    else
    {
        _EMPTY_ELSE_MARKER;
    }

    if( status == false )
    {
        IotLogError( "(MQTT connection %p) Error processing incoming data. Closing connection.",
                     pMqttConnection );

        _IotMqtt_CloseNetworkConnection( pMqttConnection );
    }
}

/*-----------------------------------------------------------*/

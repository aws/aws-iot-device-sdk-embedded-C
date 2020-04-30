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

#include <string.h>

#include "mqtt.h"

static int32_t sendPacket( MQTTContext_t * pContext,
                           const uint8_t * pOptionalBufferToSend,
                           size_t bytesToSend )
{
    const uint8_t * pIndex = pContext->networkBuffer.pBuffer;
    size_t bytesRemaining = bytesToSend;
    int32_t totalBytesSent = 0, bytesSent;

    /* If the optional buffer is not null send that instead of networkBuffer.
     * This is to support an optimization in publish to avoid copy of the
     * payload into networkBuffer.
     */
    if( pOptionalBufferToSend != NULL )
    {
        pIndex = pOptionalBufferToSend;
    }

    /* Record the time of transmission. */
    uint32_t sendTime = pContext->callbacks.getTime();

    /* Loop until the entire packet is sent. */
    while( bytesRemaining > 0 )
    {
        bytesSent = pContext->transportInterface.send( pContext->transportInterface.networkContext,
                                                       pIndex,
                                                       bytesRemaining );

        if( bytesSent > 0 )
        {
            bytesRemaining -= ( size_t ) bytesSent;
            totalBytesSent += bytesSent;
            pIndex += bytesSent;
        }
        else
        {
            totalBytesSent = -1;
            break;
        }
    }

    /* Update time of last transmission if the entire packet was successfully sent. */
    if( totalBytesSent > -1 )
    {
        pContext->lastPacketTime = sendTime;
    }

    return totalBytesSent;
}

/*-----------------------------------------------------------*/

void MQTT_Init( MQTTContext_t * const pContext,
                const MQTTTransportInterface_t * const pTransportInterface,
                const MQTTApplicationCallbacks_t * const pCallbacks,
                const MQTTFixedBuffer_t * const pNetworkBuffer )
{
    memset( pContext, 0x00, sizeof( MQTTContext_t ) );

    pContext->connectStatus = MQTTNotConnected;
    pContext->transportInterface = *pTransportInterface;
    pContext->callbacks = *pCallbacks;
    pContext->networkBuffer = *pNetworkBuffer;

    /* Zero is not a valid packet ID per MQTT spec. Start from 1. */
    pContext->nextPacketId = 1;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Connect( MQTTContext_t * const pContext,
                           const MQTTConnectInfo_t * const pConnectInfo,
                           const MQTTPublishInfo_t * const pWillInfo,
                           bool * const pSessionPresent )
{
    size_t remainingLength, packetSize;
    int32_t bytesSent;
    MQTTPacketInfo_t incomingPacket = { .type = ( ( uint8_t ) 0 ) };

    MQTTStatus_t status = MQTT_GetConnectPacketSize( pConnectInfo,
                                                     pWillInfo,
                                                     &remainingLength,
                                                     &packetSize );

    if( status == MQTTSuccess )
    {
        status = MQTT_SerializeConnect( pConnectInfo,
                                        pWillInfo,
                                        remainingLength,
                                        &( pContext->networkBuffer ) );
    }

    if( status == MQTTSuccess )
    {
        bytesSent = sendPacket( pContext, NULL, packetSize );

        if( bytesSent < 0 )
        {
            status = MQTTSendFailed;
        }
    }

    if( status == MQTTSuccess )
    {
        status = MQTT_GetIncomingPacket( pContext->transportInterface.recv,
                                         pContext->transportInterface.networkContext,
                                         &incomingPacket );
    }

    if( status == MQTTSuccess )
    {
        if( incomingPacket.type == MQTT_PACKET_TYPE_CONNACK )
        {
            status = MQTT_DeserializeAck( &incomingPacket, NULL, pSessionPresent );
        }
        else
        {
            status = MQTTBadResponse;
        }
    }

    if( status == MQTTSuccess )
    {
        pContext->connectStatus = MQTTConnected;
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Subscribe( MQTTContext_t * const pContext,
                             const MQTTSubscribeInfo_t * const pSubscriptionList,
                             size_t subscriptionCount )
{
    return MQTTSuccess;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Publish( MQTTContext_t * const pContext,
                           const MQTTPublishInfo_t * const pPublishInfo,
                           uint16_t packetId )
{
    size_t remainingLength = 0, packetSize = 0, headerSize = 0;
    int32_t bytesSent = 0;
    MQTTStatus_t status = MQTTSuccess;

    /* Validate arguments. */
    if( ( pContext == NULL ) || ( pPublishInfo == NULL ) )
    {
        status = MQTTBadParameter;
    }

    if( status == MQTTSuccess )
    {
        /* Get the remaining length and packet size.*/
        status = MQTT_GetPublishPacketSize( pPublishInfo,
                                            &remainingLength,
                                            &packetSize );
    }

    if( status == MQTTSuccess )
    {
        status = MQTT_SerializePublishHeader( pPublishInfo,
                                              packetId,
                                              remainingLength,
                                              &( pContext->networkBuffer ),
                                              &headerSize );
    }

    if( status == MQTTSuccess )
    {
        /* Send header first. */
        bytesSent = sendPacket( pContext, NULL, headerSize );

        if( bytesSent < 0 )
        {
            status = MQTTSendFailed;
        }
        /* Send Payload. */
        else
        {
            bytesSent = sendPacket( pContext,
                                    pPublishInfo->pPayload,
                                    pPublishInfo->payloadLength );

            if( bytesSent < 0 )
            {
                status = MQTTSendFailed;
            }
        }
    }

    /* TODO - Update the state machine with the packet ID. This will have to
     * be done once the state machine changes are available.*/

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Ping( MQTTContext_t * const pContext )
{
    return MQTTSuccess;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Unsubscribe( MQTTContext_t * const pContext,
                               const MQTTSubscribeInfo_t * const pSubscriptionList,
                               size_t subscriptionCount )
{
    return MQTTSuccess;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Disconnect( MQTTContext_t * const pContext )
{
    size_t packetSize;
    int32_t bytesSent;

    MQTTStatus_t status = MQTT_GetDisconnectPacketSize( &packetSize );

    if( status == MQTTSuccess )
    {
        status = MQTT_SerializeDisconnect( &( pContext->networkBuffer ) );
    }

    if( status == MQTTSuccess )
    {
        bytesSent = sendPacket( pContext, NULL, packetSize );

        if( bytesSent < 0 )
        {
            status = MQTTSendFailed;
        }
    }

    if( status == MQTTSuccess )
    {
        pContext->connectStatus = MQTTNotConnected;
    }

    return status;
}

/*-----------------------------------------------------------*/

MQTTStatus_t MQTT_Process( MQTTContext_t * const pContext,
                           uint32_t timeoutMs )
{
    return MQTTSuccess;
}

/*-----------------------------------------------------------*/

uint16_t MQTT_GetPacketId( MQTTContext_t * const pContext )
{
    uint16_t packetId = pContext->nextPacketId;

    pContext->nextPacketId++;

    if( pContext->nextPacketId == 0 )
    {
        pContext->nextPacketId = 1;
    }

    return packetId;
}

/*-----------------------------------------------------------*/

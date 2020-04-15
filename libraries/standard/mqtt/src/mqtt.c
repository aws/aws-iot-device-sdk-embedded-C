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

void MQTT_Init( MQTTContext_t * const pContext,
                const MQTTTransportInterface_t * const pTransportInterface,
                const MQTTApplicationCallbacks_t * const pCallbacks,
                const MQTTFixedBuffer_t * const pNetworkBuffer )
{
    memset( pContext, 0x00, sizeof( MQTTContext_t ) );

    pContext->connectStatus = MQTTNotConnected;
    pContext->pTransportInterface = pTransportInterface;
    pContext->pCallbacks = pCallbacks;
    pContext->pNetworkBuffer = pNetworkBuffer;

    /* Zero is not a valid packet ID per MQTT spec. Start from 1. */
    pContext->nextPacketId = 1;
}

MQTTStatus_t MQTT_Connect( MQTTContext_t * const pContext,
                           const MQTTConnectInfo_t * const pConnectInfo,
                           const MQTTPublishInfo_t * const pWillInfo,
                           bool * const pSessionPresent )
{
    size_t remainingLength, packetSize;
    int32_t bytesSent;
    uint32_t sendTime;
    MQTTPacketInfo_t incomingPacket;

    MQTTStatus_t status = MQTT_GetConnectPacketSize( pConnectInfo,
                                                     pWillInfo,
                                                     &remainingLength,
                                                     &packetSize );

    if( status == MQTTSuccess )
    {
        status = MQTT_SerializeConnect( pConnectInfo,
                                        pWillInfo,
                                        remainingLength,
                                        pContext->pNetworkBuffer );
    }

    if( status == MQTTSuccess )
    {
        sendTime = pContext->pCallbacks->getTime();

        bytesSent= pContext->pTransportInterface->send( pContext->pTransportInterface->networkContext,
                                                        pContext->pNetworkBuffer->pBuffer,
                                                        packetSize );

        if( ( bytesSent > 0 ) && ( ( size_t ) bytesSent == packetSize ) )
        {
            pContext->lastPacketTime = sendTime;
        }
        else
        {
            status = MQTTSendFailed;
        }
    }

    if( status == MQTTSuccess )
    {
        status = MQTT_GetIncomingPacket( pContext->pTransportInterface->recv,
                                         pContext->pTransportInterface->networkContext,
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

MQTTStatus_t MQTT_Subscribe( MQTTContext_t * const pContext,
                             const MQTTSubscribeInfo_t * const pSubscriptionList,
                             size_t subscriptionCount )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_Publish( MQTTContext_t * const pContext,
                           const MQTTPublishInfo_t * const pPublishInfo )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_Ping( MQTTContext_t * const pContext )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_Unsubscribe( MQTTContext_t * const pContext,
                               const MQTTSubscribeInfo_t * const pSubscriptionList,
                               size_t subscriptionCount )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_Disconnect( MQTTContext_t * const pContext )
{
    return MQTTSuccess;
}

MQTTStatus_t MQTT_Process( MQTTContext_t * const pContext,
                           uint32_t timeoutMs )
{
    return MQTTSuccess;
}

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

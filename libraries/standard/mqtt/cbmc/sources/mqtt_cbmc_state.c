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
#include <stdint.h>
#include <stdlib.h>
#include "mqtt_cbmc_state.h"
#include "mqtt.h"

void * mallocCanFail( size_t size )
{
    __CPROVER_assert( size < CBMC_MAX_OBJECT_SIZE, "mallocCanFail size is too big" );
    return nondet_bool() ? NULL : malloc( size );
}

MQTTPacketInfo_t * allocateMqttPacketInfo( MQTTPacketInfo_t * pPacketInfo )
{
    if( pPacketInfo == NULL )
    {
        pPacketInfo = mallocCanFail( sizeof( MQTTPacketInfo_t ) );
    }

    if( pPacketInfo != NULL )
    {
        __CPROVER_assume( pPacketInfo->remainingLength < CBMC_MAX_OBJECT_SIZE );
        pPacketInfo->pRemainingData = mallocCanFail( pPacketInfo->remainingLength );
    }

    return pPacketInfo;
}

bool isValidMqttPacketInfo( const MQTTPacketInfo_t * pPacketInfo )
{
    bool isValid = true;

    if( pPacketInfo != NULL )
    {
        isValid = pPacketInfo->remainingLength < CBMC_MAX_OBJECT_SIZE;
    }

    return isValid;
}

MQTTPublishInfo_t * allocateMqttPublishInfo( MQTTPublishInfo_t * pPublishInfo )
{
    if( pPublishInfo == NULL )
    {
        pPublishInfo = mallocCanFail( sizeof( MQTTPublishInfo_t ) );
    }

    if( pPublishInfo != NULL )
    {
        __CPROVER_assume( pPublishInfo->topicNameLength < CBMC_MAX_OBJECT_SIZE );
        pPublishInfo->pTopicName = mallocCanFail( pPublishInfo->topicNameLength );
        __CPROVER_assume( pPublishInfo->payloadLength < CBMC_MAX_OBJECT_SIZE );
        pPublishInfo->pPayload = mallocCanFail( pPublishInfo->payloadLength );
    }

    return pPublishInfo;
}

bool isValidMqttPublishInfo( const MQTTPublishInfo_t * pPublishInfo )
{
    bool isValid = true;

    if( pPublishInfo != NULL )
    {
        bool validQos = ( ( pPublishInfo->qos >= MQTTQoS0 ) ||
                          ( pPublishInfo->qos <= MQTTQoS2 ) );

        bool validTopicNameLength = pPublishInfo->topicNameLength < CBMC_MAX_OBJECT_SIZE;
        bool validPayloadLength = pPublishInfo->payloadLength < CBMC_MAX_OBJECT_SIZE;

        isValid = validQos && validTopicNameLength && validPayloadLength;
    }

    return isValid;
}

MQTTConnectInfo_t * allocateMqttConnectInfo( MQTTConnectInfo_t * pConnectInfo )
{
    if( pConnectInfo == NULL )
    {
        pConnectInfo = mallocCanFail( sizeof( MQTTConnectInfo_t ) );
    }

    if( pConnectInfo != NULL )
    {
        __CPROVER_assume( pConnectInfo->clientIdentifierLength < CBMC_MAX_OBJECT_SIZE );
        pConnectInfo->pClientIdentifier = mallocCanFail( pConnectInfo->clientIdentifierLength );
        __CPROVER_assume( pConnectInfo->userNameLength < CBMC_MAX_OBJECT_SIZE );
        pConnectInfo->pUserName = mallocCanFail( pConnectInfo->userNameLength );
        __CPROVER_assume( pConnectInfo->passwordLength < CBMC_MAX_OBJECT_SIZE );
        pConnectInfo->pPassword = mallocCanFail( pConnectInfo->passwordLength );
    }

    return pConnectInfo;
}

bool isValidMqttConnectInfo( const MQTTConnectInfo_t * pConnectInfo )
{
    bool isValid = true;

    if( pConnectInfo != NULL )
    {
        isValid &= ( pConnectInfo->clientIdentifierLength < CBMC_MAX_OBJECT_SIZE );
        isValid &= ( pConnectInfo->userNameLength < CBMC_MAX_OBJECT_SIZE );
        isValid &= ( pConnectInfo->passwordLength < CBMC_MAX_OBJECT_SIZE );
    }

    return isValid;
}

MQTTFixedBuffer_t * allocateMqttFixedBuffer( MQTTFixedBuffer_t * pBuffer )
{
    if( pBuffer == NULL )
    {
        pBuffer = mallocCanFail( sizeof( MQTTFixedBuffer_t ) );
    }

    if( pBuffer != NULL )
    {
        __CPROVER_assume( pBuffer->size < CBMC_MAX_OBJECT_SIZE );
        pBuffer->pBuffer = mallocCanFail( pBuffer->size );
    }

    return pBuffer;
}

bool isValidMqttFixedBuffer( const MQTTFixedBuffer_t * pBuffer )
{
    bool isValid = true;

    if( pBuffer != NULL )
    {
        isValid = pBuffer->size < CBMC_MAX_OBJECT_SIZE;
    }

    return isValid;
}

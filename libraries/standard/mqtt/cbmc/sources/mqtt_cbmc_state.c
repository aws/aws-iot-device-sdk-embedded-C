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

/* A default bound on the subscription count. Iterating over possibly SIZE_MAX
 * number of subscriptions does not add any value to the proofs. An application
 * can allocate memory for as many subscriptions as their system can handle.
 * The proofs verify that the code can handle the maximum topicFilterLength in
 * each subscription. */
#ifndef SUBSCRIPTION_COUNT_MAX
    #define SUBSCRIPTION_COUNT_MAX    1U
#endif

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
        isValid = isValid && ( pPublishInfo->topicNameLength < CBMC_MAX_OBJECT_SIZE );
        isValid = isValid && ( pPublishInfo->payloadLength < CBMC_MAX_OBJECT_SIZE );
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
        isValid = isValid && ( pConnectInfo->clientIdentifierLength < CBMC_MAX_OBJECT_SIZE );
        isValid = isValid && ( pConnectInfo->userNameLength < CBMC_MAX_OBJECT_SIZE );
        isValid = isValid && ( pConnectInfo->passwordLength < CBMC_MAX_OBJECT_SIZE );
    }

    return isValid;
}

MQTTFixedBuffer_t * allocateMqttFixedBuffer( MQTTFixedBuffer_t * pFixedBuffer )
{
    if( pFixedBuffer == NULL )
    {
        pFixedBuffer = mallocCanFail( sizeof( MQTTFixedBuffer_t ) );
    }

    if( pFixedBuffer != NULL )
    {
        __CPROVER_assume( pFixedBuffer->size < CBMC_MAX_OBJECT_SIZE );
        pFixedBuffer->pBuffer = mallocCanFail( pFixedBuffer->size );
    }

    return pFixedBuffer;
}

bool isValidMqttFixedBuffer( const MQTTFixedBuffer_t * pFixedBuffer )
{
    bool isValid = true;

    if( pFixedBuffer != NULL )
    {
        isValid = pFixedBuffer->size < CBMC_MAX_OBJECT_SIZE;
    }

    return isValid;
}

MQTTSubscribeInfo_t * allocateMqttSubscriptionList( MQTTSubscribeInfo_t * pSubscriptionList,
                                                    size_t subscriptionCount )
{
    if( pSubscriptionList == NULL )
    {
        __CPROVER_assume( sizeof( MQTTSubscribeInfo_t ) * subscriptionCount < CBMC_MAX_OBJECT_SIZE );
        pSubscriptionList = mallocCanFail( sizeof( MQTTSubscribeInfo_t ) * subscriptionCount );
    }

    if( pSubscriptionList != NULL )
    {
        for( int i = 0; i < subscriptionCount; i++ )
        {
            __CPROVER_assume( pSubscriptionList[ i ].topicFilterLength < CBMC_MAX_OBJECT_SIZE );
            pSubscriptionList[ i ].pTopicFilter = mallocCanFail( pSubscriptionList[ i ].topicFilterLength );
        }
    }

    return pSubscriptionList;
}

bool isValidMqttSubscriptionList( MQTTSubscribeInfo_t * pSubscriptionList,
                                  size_t subscriptionCount )
{
    bool isValid = true;

    if( pSubscriptionList != NULL )
    {
        for( int i = 0; i < subscriptionCount; i++ )
        {
            isValid = isValid && ( pSubscriptionList[ i ].topicFilterLength < CBMC_MAX_OBJECT_SIZE );
        }
    }

    return isValid;
}

MQTTContext_t * allocateMqttContext( MQTTContext_t * pContext )
{
    if( pContext == NULL )
    {
        pContext = mallocCanFail( sizeof( MQTTContext_t ) );
    }

    if( pContext != NULL )
    {
        /* The networkBuffer is the only field in the MQTTContext_t which has a
         * buffer of variable length. Since it is pat of the API contract to
         * call MQTT_Init first with a MQTTFixedBuffer_t, we do not need to
         * allocate one here. */
        /*__CPROVER_assume( pContext->networkBuffer.size < CBMC_MAX_OBJECT_SIZE ); */
        /*pContext->networkBuffer.pBuffer = mallocCanFail( pContext->networkBuffer.size ); */
    }

    return pContext;
}

bool isValidMqttContext( const MQTTContext_t * pContext )
{
    bool isValid = true;

    if( pContext != NULL )
    {
        isValid = pContext->networkBuffer.size < CBMC_MAX_OBJECT_SIZE;
    }

    return isValid;
}

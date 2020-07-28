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
#include "mqtt.h"
#include "mqtt_cbmc_state.h"
#include "network_interface_stubs.h"
#include "get_time_stub.h"
#include "event_callback_stub.h"

/* A default bound on the subscription count. Iterating over possibly SIZE_MAX
 * number of subscriptions does not add any value to the proofs. An application
 * can allocate memory for as many subscriptions as their system can handle.
 * The proofs verify that the code can handle the maximum topicFilterLength in
 * each subscription. */
#ifndef SUBSCRIPTION_COUNT_MAX
    #define SUBSCRIPTION_COUNT_MAX    1U
#endif

/* A default bound on the remainingLength in an incoming packet. This bound
 * is used for the MQTT_DeserializeAck() proof to limit the number of iterations
 * on a SUBACK packet's payload bytes. We do not need to iterate an unbounded
 * remaining length amount of bytes to verify memory safety in the dereferencing
 * the SUBACK payload's bytes. */
#ifndef REMAINING_LENGTH_MAX
    #define REMAINING_LENGTH_MAX    CBMC_MAX_OBJECT_SIZE
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
        __CPROVER_assert( REMAINING_LENGTH_MAX <= CBMC_MAX_OBJECT_SIZE,
                          "REMAINING_LENGTH_MAX size is too big" );
        __CPROVER_assume( pPacketInfo->remainingLength < REMAINING_LENGTH_MAX );
        pPacketInfo->pRemainingData = mallocCanFail( pPacketInfo->remainingLength );
    }

    return pPacketInfo;
}

bool isValidMqttPacketInfo( const MQTTPacketInfo_t * pPacketInfo )
{
    bool isValid = true;

    if( pPacketInfo != NULL )
    {
        __CPROVER_assert( REMAINING_LENGTH_MAX <= CBMC_MAX_OBJECT_SIZE,
                          "REMAINING_LENGTH_MAX size is too big" );
        isValid = pPacketInfo->remainingLength < REMAINING_LENGTH_MAX;
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
    TransportInterface_t * pTransportInterface;
    MQTTFixedBuffer_t * pNetworkBuffer;
    MQTTStatus_t status = MQTTSuccess;

    if( pContext == NULL )
    {
        pContext = mallocCanFail( sizeof( MQTTContext_t ) );
    }

    pTransportInterface = mallocCanFail( sizeof( TransportInterface_t ) );

    if( pTransportInterface != NULL )
    {
        /* The possibility that recv and send callbacks ar NULL is tested in the
         * MQTT_Init proof. MQTT_Init is required to be called before any other
         * function in mqtt.h. */
        pTransportInterface->recv = NetworkInterfaceReceiveStub;
        pTransportInterface->send = NetworkInterfaceSendStub;
    }

    pNetworkBuffer = allocateMqttFixedBuffer( NULL );
    __CPROVER_assume( isValidMqttFixedBuffer( pNetworkBuffer ) );

    /* It is part of the API contract to call MQTT_Init() with the MQTTContext_t
     * before any other function in mqtt.h. */
    if( pContext != NULL )
    {
        status = MQTT_Init( pContext,
                            pTransportInterface,
                            GetCurrentTimeStub,
                            EventCallbackStub,
                            pNetworkBuffer );
    }

    /* If the MQTTContext_t initialization failed, then set the context to NULL
     * so that function under harness will return immediately upon a NULL
     * parameter check. */
    if( status != MQTTSuccess )
    {
        pContext = NULL;
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

/*
 * IoT MQTT V2.1.0
 * Copyright (C) Amazon.com, Inc. or its affiliates.  All Rights Reserved.
 *
 * Permission is hereby granted, free of charge, to any person
 * obtaining a copy of this software and associated documentation
 * files (the "Software"), to deal in the Software without
 * restriction, including without limitation the rights to use, copy,
 * modify, merge, publish, distribute, sublicense, and/or sell copies
 * of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be
 * included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 * EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 * MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 * NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS
 * BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
 * ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
 * CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

/**
 * @file IotMqtt_ReceiveCallback_harness.c
 * @brief Implements the proof harness for IotMqtt_ReceiveCallback function.
 */

#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

#include "mqtt_state.h"

/****************************************************************
* A predicate asserting that an operation on the pending list with no
* retry has a job reference of 1.  This property is asserted by
* _IotMqtt_FindOperation.
*
* Notice that this predicate tests members of a union guaranteed to
* be valid only when the operation's incomingPublish is false.  This
* condition not tested by _IotMqtt_FindOperation and thus not tested
* by this predicate.
*
* This predicate is implemented using straight line code to avoid
* loop unwinding.  It assumes that the operation list has length at
* most 3.
****************************************************************/

bool pending_operation_has_valid_jobreference( IotLink_t * pElt )
{
    _mqttOperation_t * pOp = IotLink_Container( _mqttOperation_t, pElt, link );

    return IMPLIES( pOp->u.operation.periodic.retry.limit == 0,
                    pOp->u.operation.jobReference == 1 );
}

bool pending_operations_have_valid_jobreference( IotMqttConnection_t pConn )
{
    if( pConn == NULL )
    {
        return false;
    }

    IotLink_t * pHead = &pConn->pendingResponse;
    IotLink_t * pElt = pHead->pNext;
    bool status = true;

    if( pElt != pHead )
    {
        status = status && pending_operation_has_valid_jobreference( pElt );
        pElt = pElt->pNext;
    }

    if( pElt != pHead )
    {
        status = status && pending_operation_has_valid_jobreference( pElt );
        pElt = pElt->pNext;
    }

    if( pElt != pHead )
    {
        status = status && pending_operation_has_valid_jobreference( pElt );
        pElt = pElt->pNext;
    }

    status = status && pElt == pHead;

    return status;
}

/****************************************************************
* This proof works by splitting into cases based on incoming packet
* type.  There are six valid incoming packet types:
*
*     MQTT_PACKET_TYPE_CONNACK
*     MQTT_PACKET_TYPE_PUBLISH
*     MQTT_PACKET_TYPE_PUBACK
*     MQTT_PACKET_TYPE_SUBACK
*     MQTT_PACKET_TYPE_UNSUBACK
* and
*     MQTT_PACKET_TYPE_PINGRESP
*
* We split these cases into the first 5 and everything else by
* modifying the function that reads the byte from the network
* connection that includes the packet type.  This byte consists of 4
* bits giving the packet type and 4 bits giving the packet flags like
* quality of service.
****************************************************************/

uint8_t _IotMqtt_GetPacketType( IotNetworkConnection_t pNetworkConnection,
                                const IotNetworkInterface_t * pNetworkInterface )
{
    uint8_t byte;

    /* Top 4 bits are packet type, the bottom 4 bits are flags */
    uint8_t type = byte & 0xf0U;

    #ifdef CBMC_PACKET
        __CPROVER_assume( type == CBMC_PACKET );
        assert( type == MQTT_PACKET_TYPE_CONNACK ||
                type == MQTT_PACKET_TYPE_PUBLISH ||
                type == MQTT_PACKET_TYPE_PUBACK ||
                type == MQTT_PACKET_TYPE_SUBACK ||
                type == MQTT_PACKET_TYPE_UNSUBACK );
    #else
        __CPROVER_assume( type != MQTT_PACKET_TYPE_CONNACK &&
                          type != MQTT_PACKET_TYPE_PUBLISH &&
                          type != MQTT_PACKET_TYPE_PUBACK &&
                          type != MQTT_PACKET_TYPE_SUBACK &&
                          type != MQTT_PACKET_TYPE_UNSUBACK );
    #endif /* ifdef CBMC_PACKET */

    return byte;
}

/****************************************************************
* The proof harness
****************************************************************/

void harness()
{
    IotMqttConnection_t ReceiveContext = allocate_IotMqttConnection( NULL );

    __CPROVER_assume( ReceiveContext );
    ensure_IotMqttConnection_has_lists( ReceiveContext );
    __CPROVER_assume( valid_IotMqttConnection( ReceiveContext ) );

    __CPROVER_assume(
        pending_operations_have_valid_jobreference( ReceiveContext ) );

    /* There must be some operation waiting for an inbound ack */
    __CPROVER_assume( ReceiveContext->references > 0 );

    /* Disconnect callback function pointer points to our stub */
    __CPROVER_assume(
        MAYBE_STUBBED_USER_CALLBACK(
            ReceiveContext->disconnectCallback.function ) );

    /* Network interface method functions pointers point to our stubs */
    __CPROVER_assume(
        IS_STUBBED_NETWORKIF_RECEIVE(
            ReceiveContext->pNetworkInterface ) );
    __CPROVER_assume(
        MAYBE_STUBBED_NETWORKIF_CREATE(
            ReceiveContext->pNetworkInterface ) );
    __CPROVER_assume(
        MAYBE_STUBBED_NETWORKIF_CLOSE(
            ReceiveContext->pNetworkInterface ) );
    __CPROVER_assume(
        MAYBE_STUBBED_NETWORKIF_SEND(
            ReceiveContext->pNetworkInterface ) );
    __CPROVER_assume(
        MAYBE_STUBBED_NETWORKIF_SETRECEIVECALLBACK(
            ReceiveContext->pNetworkInterface ) );
    __CPROVER_assume(
        MAYBE_STUBBED_NETWORKIF_SETCLOSECALLBACK(
            ReceiveContext->pNetworkInterface ) );
    __CPROVER_assume(
        MAYBE_STUBBED_NETWORKIF_DESTROY(
            ReceiveContext->pNetworkInterface ) );

    IotMqtt_ReceiveCallback( ReceiveContext->pNetworkConnection,
                             ReceiveContext );
}

/****************************************************************/

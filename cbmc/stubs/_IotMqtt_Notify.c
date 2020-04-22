/*
 * IoT MQTT V2.1.0
 * Copyright (C) Amazon.com, Inc. or its affiliates.  All Rights Reserved.
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
 * @file _IotMqtt_Notify.c
 * @brief Implements a stub for _IotMqtt_Notify function.
 */

#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

/****************************************************************
* We abstract the Notify method by assuming it havocs subscription and
* operation lists.
*
* These functions are used to havoc the lists.  The lists are written
* and then never again read.  We model these updates by simply freeing
* the lists, and trusting CBMC to flag a use-after-free error if an
* element of the list is accessed.
****************************************************************/

void * invalid_pointer();

IotListDouble_t * destroy_subscription_list_element( IotListDouble_t * pElt )
{
    if( pElt == NULL )
    {
        return NULL;
    }

    IotListDouble_t * pNext = pElt->pNext;
    free( IotLink_Container( _mqttSubscription_t, pElt, link ) );
    return pNext;
}

void destroy_subscription_list( IotListDouble_t * pList )
{
    if( pList == NULL )
    {
        return;
    }

    /* Assuming lists are of length at most 3 */

    IotListDouble_t * pElt = pList->pNext;

    if( pElt != pList )
    {
        pElt = destroy_subscription_list_element( pElt );
    }

    if( pElt != pList )
    {
        pElt = destroy_subscription_list_element( pElt );
    }

    if( pElt != pList )
    {
        pElt = destroy_subscription_list_element( pElt );
    }

    pList->pNext = invalid_pointer();
    pList->pPrevious = invalid_pointer();
}

IotListDouble_t * destroy_operation_list_element( IotListDouble_t * pElt )
{
    if( pElt == NULL )
    {
        return NULL;
    }

    IotListDouble_t * pNext = pElt->pNext;
    free( IotLink_Container( struct _mqttOperation, pElt, link ) );
    return pNext;
}

void destroy_operation_list( IotListDouble_t * pList )
{
    if( pList == NULL )
    {
        return;
    }

    /* Assuming lists are of length at most 3 */

    IotListDouble_t * pElt = pList->pNext;

    if( pElt != pList )
    {
        pElt = destroy_operation_list_element( pElt );
    }

    if( pElt != pList )
    {
        pElt = destroy_operation_list_element( pElt );
    }

    if( pElt != pList )
    {
        pElt = destroy_operation_list_element( pElt );
    }

    pList->pNext = invalid_pointer();
    pList->pPrevious = invalid_pointer();
}

/****************************************************************
* Abstract the Notify method
*
* This abstraction assumes that the write set of Notify is just the
* subscription and operation lists in the connection, and it models
* Notify by simply havocing these lists.
****************************************************************/

void _IotMqtt_Notify( _mqttOperation_t * pOperation )
{
    destroy_subscription_list( &pOperation->pMqttConnection->subscriptionList );
    destroy_operation_list( &pOperation->pMqttConnection->pendingProcessing );
    destroy_operation_list( &pOperation->pMqttConnection->pendingResponse );
}

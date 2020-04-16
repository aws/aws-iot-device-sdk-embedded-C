#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

#include "mqtt_state.h"

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
*
* Note: We break coding conventions by placing this function at the
* head of the proof harness because it is the heart of the proof and
* explains what is going on.
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
    #endif

    return byte;
}

/****************************************************************
 * Type definitions used by the IoT List Double remove functions
 ****************************************************************/

typedef bool ( *MatchFunction_t )( const IotLink_t * const pOperationLink,
                                   void * pCompare );
typedef void ( *FreeElementFunction_t )( void * pData );

/****************************************************************
 * We assume the IoT List Double remove functions are memory safe.
 *
 * We abstract the list remove functions for performance reasons.  Our
 * abstraction replaces the original list with an unconstrained list.
 * Our abstraction proves that none of the elements on the original
 * list are accessed after the remove: We free all elements on the
 * original list, so that any later access will be caught as a
 * use-after-free error.
 ****************************************************************/

void IotListDouble_RemoveAllMatches( const IotListDouble_t * const pList,
                                     MatchFunction_t isMatch,
                                     void * pMatch,
                                     FreeElementFunction_t freeElement,
                                     size_t linkOffset )
{
    free_IotMqttSubscriptionList( pList );
    allocate_IotMqttSubscriptionList( pList, SUBSCRIPTION_COUNT_MAX - 1 );
}

/****************************************************************/

void IotListDouble_RemoveAll( const IotListDouble_t * const pList,
                              FreeElementFunction_t freeElement,
                              size_t linkOffset )
{
    free_IotMqttSubscriptionList( pList );
    allocate_IotMqttSubscriptionList( pList, SUBSCRIPTION_COUNT_MAX - 1 );
}

/****************************************************************
* We assume the TaskPool functions are memory safe.
*
* We abstract the task pool functions (we assume they have no side
* effects and return an unconstrained value), but there are some
* assertions in the code that the task pool functions return a
* constrained set of values.  We model these functions as simply
* returning one of those values.
****************************************************************/

IotTaskPoolError_t IotTaskPool_CreateJob( const IotTaskPoolRoutine_t userCallback,
                                          void * const pUserContext,
                                          IotTaskPoolJob_t * const pJob )
{
    /*
     * *_IotMqtt_ScheduleOperation says creating a new job should
     * never fail when parameters are valid.
     */
    return IOT_TASKPOOL_SUCCESS;
}

/****************************************************************/

IotTaskPoolError_t IotTaskPool_ScheduleDeferred( IotTaskPool_t * const pTaskPool,
                                                 IotTaskPoolJob_t * const pJob,
                                                 uint32_t timeMs )
{
    /*
     * *_IotMqtt_ScheduleOperation says a newly created job should
     * never be invalid or illegal.
     */
    IotTaskPoolError_t error;

    __CPROVER_assume( error != IOT_TASKPOOL_BAD_PARAMETER );
    __CPROVER_assume( error != IOT_TASKPOOL_ILLEGAL_OPERATION );
    return error;
}

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

    __CPROVER_assume( ReceiveContext->references > 0 );

    /* Disconnect callback */
    __CPROVER_assume(
        MAYBE_STUBBED_USER_CALLBACK(
            ReceiveContext->disconnectCallback.function ) );

    /* Network interface methods */
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

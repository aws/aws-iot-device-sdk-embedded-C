#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

#include "mqtt_state.h"

/****************************************************************/

void IotListDouble_RemoveAllMatches( const IotListDouble_t * const pList,
				     bool ( *isMatch )( const IotLink_t * const pOperationLink, void * pCompare ),
				     void * pMatch,
				     void ( *freeElement )( void * pData ),
				     size_t linkOffset )
{
  free_IotMqttSubscriptionList( pList );
  allocate_IotMqttSubscriptionList( pList, SUBSCRIPTION_COUNT_MAX-1 );
}

/****************************************************************/

/**
 * We abstract all functions related to concurrency and assume they are correct.
 * Thus, we add these stub to increase coverage.
 */
IotTaskPoolError_t IotTaskPool_CreateJob( IotTaskPoolRoutine_t userCallback,
                                          void * pUserContext,
                                          IotTaskPoolJobStorage_t * const pJobStorage,
                                          IotTaskPoolJob_t * const pJob )
{
  assert( userCallback != NULL );
  assert( pJobStorage != NULL );
  assert( pJob != NULL );

  /* _IotMqtt_ScheduleOperation asserts this */
  return IOT_TASKPOOL_SUCCESS;
}

IotTaskPoolError_t IotTaskPool_ScheduleDeferred( IotTaskPool_t taskPool,
                                                 IotTaskPoolJob_t job,
                                                 uint32_t timeMs )
{
  IotTaskPoolError_t error;

  /* _IotMqtt_ScheduleOperation asserts this */
  __CPROVER_assume(error != IOT_TASKPOOL_BAD_PARAMETER &&
                   error != IOT_TASKPOOL_ILLEGAL_OPERATION);
  return error;
}

/****************************************************************/

/**
 * _IotMqtt_NextPacketIdentifier calls Atomic_Add_u32, which receives
 * a volatile variable as input. Thus, CBMC will always consider that
 * Atomic_Add_u32 will operate over nondetermistic values and raises
 * a unsigned integer overflow failure. However, developers have reported
 * that the use of this overflow is part of the function implementation.
 * In order to mirror _IotMqtt_NextPacketIdentifier behaviour and avoid
 * spurious alarms, we stub out this function to always
 * return a nondetermistic odd value.
 */
uint16_t _IotMqtt_NextPacketIdentifier( void ) {
  uint16_t id;

  /* Packet identifiers will follow the sequence 1,3,5...65535,1,3,5... */
  __CPROVER_assume(id & 0x0001 == 1);

  return id;
}

/****************************************************************/


void harness()
{
  size_t subscriptionCount;
  __CPROVER_assume(subscriptionCount < SUBSCRIPTION_COUNT_MAX);

  IotMqttSubscription_t *subscriptionList = allocate_IotMqttSubscriptionArray(NULL, subscriptionCount);
  __CPROVER_assume(valid_IotMqttSubscriptionArray(subscriptionList, subscriptionCount));

  IotMqttConnection_t mqttConnection = allocate_IotMqttConnection(NULL);
  __CPROVER_assume(mqttConnection);
  ensure_IotMqttConnection_has_lists(mqttConnection);
  __CPROVER_assume(valid_IotMqttConnection(mqttConnection));
  __CPROVER_assume( IS_STUBBED_NETWORKIF_SEND( mqttConnection->pNetworkInterface ) );
  __CPROVER_assume( IS_STUBBED_NETWORKIF_DESTROY( mqttConnection->pNetworkInterface ) );

  uint32_t flags;
  IotMqttCallbackInfo_t callbackInfo;

  // output
  IotMqttOperation_t unsubscribeOperation;

  IotMqtt_UnsubscribeAsync(  mqttConnection,
			     subscriptionList,
			     subscriptionCount,
			     flags,
			     &callbackInfo,
			     &unsubscribeOperation );
}

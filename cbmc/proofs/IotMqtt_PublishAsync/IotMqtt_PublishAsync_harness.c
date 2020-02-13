#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>
#include <string.h>

#include "mqtt_state.h"

IotTaskPoolError_t IotTaskPool_CreateJob( IotTaskPoolRoutine_t userCallback,
                                          void * pUserContext,
                                          IotTaskPoolJobStorage_t * const pJobStorage,
                                          IotTaskPoolJob_t * const pJob )
{
  // _IotMqtt_ScheduleOperation asserts this
  return IOT_TASKPOOL_SUCCESS;
}

IotTaskPoolError_t IotTaskPool_ScheduleDeferred( IotTaskPool_t taskPool,
                                                 IotTaskPoolJob_t job,
                                                 uint32_t timeMs )
{
  IotTaskPoolError_t error;

  // _IotMqtt_ScheduleOperation asserts this
  __CPROVER_assume(IMPLIES(error != IOT_TASKPOOL_SUCCESS,
			   error != IOT_TASKPOOL_BAD_PARAMETER &&
			   error != IOT_TASKPOOL_ILLEGAL_OPERATION));
  return error;
}

uint16_t _IotMqtt_NextPacketIdentifier( void ) {
  uint16_t id;

  /* Packet identifiers will follow the sequence 1,3,5...65535,1,3,5... */
  __CPROVER_assume(id % 2 == 1);

  return id;
}

void harness()
{
  /* assume a valid MQTT connection */
  IotMqttConnection_t mqttConnection = allocate_IotMqttConnection(NULL);
  __CPROVER_assume(mqttConnection != NULL);
  __CPROVER_assume(mqttConnection->pNetworkInterface != NULL);
  __CPROVER_assume( IS_STUBBED_NETWORKIF_SEND( mqttConnection->pNetworkInterface ) );
  ensure_IotMqttConnection_has_lists(mqttConnection);
  __CPROVER_assume(valid_IotMqttConnection(mqttConnection));
 
  /* assume a valid publish info */
  IotMqttPublishInfo_t *pPublishInfo = allocate_IotMqttPublishInfo(NULL);
  __CPROVER_assume(valid_IotMqttPublishInfo(pPublishInfo));
  
  /* assume unconstrained inputs */
  uint32_t flags;
  IotMqttCallbackInfo_t callbackInfo;
  IotMqttOperation_t publishOperation;

  /* function under verification */
  IotMqtt_PublishAsync( mqttConnection, /* always assume a valid connection */
			nondet_bool() ? NULL : pPublishInfo,
			flags,
			nondet_bool() ? NULL: &callbackInfo,
			nondet_bool() ? NULL : &publishOperation );
}

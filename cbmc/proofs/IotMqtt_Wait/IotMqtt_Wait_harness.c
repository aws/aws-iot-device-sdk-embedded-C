#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>
#include <string.h>

#include "mqtt_state.h"

void harness()
{
  IotMqttConnection_t mqttConnection = allocate_IotMqttConnection(NULL);
  __CPROVER_assume(mqttConnection != NULL);
  __CPROVER_assume(mqttConnection->pNetworkInterface != NULL);
  __CPROVER_assume( IS_STUBBED_NETWORKIF_DESTROY( mqttConnection->pNetworkInterface ) );
  ensure_IotMqttConnection_has_lists(mqttConnection);
  __CPROVER_assume(valid_IotMqttConnection(mqttConnection));
  __CPROVER_assume(mqttConnection->references > 0);

  IotMqttOperation_t publishOperation = allocate_IotMqttOperation(NULL, mqttConnection);
  __CPROVER_assume(valid_IotMqttOperation(publishOperation));

  IotListDouble_Create( &( publishOperation->link ));
  
  if (nondet_bool())
  {
    IotListDouble_InsertHead( &( mqttConnection->pendingProcessing ), &( publishOperation->link ));
  }
  
  uint32_t timeoutMs;
  IotMqtt_Wait( nondet_bool() ? publishOperation : NULL, timeoutMs );
}


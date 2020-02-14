#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

void harness()
{
  IotMqttOperationType_t operation;
  const char *pMessage = IotMqtt_OperationType(operation);
  assert(pMessage != NULL);
}

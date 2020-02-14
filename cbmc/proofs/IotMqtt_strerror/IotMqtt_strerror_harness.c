#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

void harness()
{
  IotMqttError_t status;
  const char *pMessage = IotMqtt_strerror(status);
  assert(pMessage != NULL);
}

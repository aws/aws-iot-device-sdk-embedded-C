#include IOT_CONFIG_FILE
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

/*-----------------------------------------------------------*/

void harness()
{
  _mqttPacket_t Connack;
  Connack.pRemainingData = malloc(sizeof(uint8_t) * Connack.remainingLength);

  _IotMqtt_DeserializeConnack( &Connack );
}

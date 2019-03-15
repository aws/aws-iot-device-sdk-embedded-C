#include IOT_CONFIG_FILE
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

/*-----------------------------------------------------------*/

void harness()
{
  _mqttPacket_t Unsuback;
  Unsuback.pRemainingData = malloc(sizeof(uint8_t) * Unsuback.remainingLength);

  _IotMqtt_DeserializeUnsuback( &Unsuback );
}

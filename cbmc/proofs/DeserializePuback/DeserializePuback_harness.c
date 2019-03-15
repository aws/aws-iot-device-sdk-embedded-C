#include IOT_CONFIG_FILE
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

/*-----------------------------------------------------------*/

void harness()
{
  _mqttPacket_t Puback;
  Puback.pRemainingData = malloc(sizeof(uint8_t) * Puback.remainingLength);

  _IotMqtt_DeserializePuback( &Puback );
}

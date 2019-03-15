#include IOT_CONFIG_FILE
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

/*-----------------------------------------------------------*/

void harness()
{
  _mqttPacket_t Pingresp;
  Pingresp.pRemainingData = malloc(sizeof(uint8_t) * Pingresp.remainingLength);

  _IotMqtt_DeserializePingresp( &Pingresp );
}

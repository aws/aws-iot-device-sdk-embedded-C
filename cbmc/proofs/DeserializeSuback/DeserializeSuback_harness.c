#include IOT_CONFIG_FILE
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

/*-----------------------------------------------------------*/

void harness()
{
  _mqttPacket_t Suback;
  Suback.pRemainingData = malloc(sizeof(uint8_t) * Suback.remainingLength);

  __CPROVER_assume( Suback.remainingLength <= BUFFER_SIZE );

  _IotMqtt_DeserializeSuback( &Suback );
}

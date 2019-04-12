#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

/*-----------------------------------------------------------*/

void harness()
{
    _mqttPacket_t connack;

    connack.pRemainingData = malloc( sizeof( uint8_t ) * connack.remainingLength );

    _IotMqtt_DeserializeConnack( &connack );
}

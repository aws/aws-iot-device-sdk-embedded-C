#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

/*-----------------------------------------------------------*/

void harness()
{
    _mqttPacket_t unsuback;

    unsuback.pRemainingData = malloc( sizeof( uint8_t ) * unsuback.remainingLength );

    _IotMqtt_DeserializeUnsuback( &unsuback );
}

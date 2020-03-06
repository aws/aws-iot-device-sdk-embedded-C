#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

/*-----------------------------------------------------------*/

void harness()
{
    _mqttPacket_t puback;

    puback.pRemainingData = malloc( sizeof( uint8_t ) * puback.remainingLength );

    _IotMqtt_DeserializePuback( &puback );
}

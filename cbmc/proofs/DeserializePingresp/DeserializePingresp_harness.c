#include IOT_CONFIG_FILE
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

/*-----------------------------------------------------------*/

void harness()
{
    _mqttPacket_t pingresp;

    pingresp.pRemainingData = malloc( sizeof( uint8_t ) * pingresp.remainingLength );

    _IotMqtt_DeserializePingresp( &pingresp );
}

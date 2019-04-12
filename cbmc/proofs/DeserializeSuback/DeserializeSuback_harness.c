#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

/*-----------------------------------------------------------*/

void harness()
{
    _mqttPacket_t suback;

    suback.pRemainingData = malloc( sizeof( uint8_t ) * suback.remainingLength );

    __CPROVER_assume( suback.remainingLength <= BUFFER_SIZE );

    _IotMqtt_DeserializeSuback( &suback );
}

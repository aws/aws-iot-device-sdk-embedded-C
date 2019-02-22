#include IOT_CONFIG_FILE
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

/*-----------------------------------------------------------*/

void harness()
{
    size_t dataLength;
    uint8_t * pConnackStart = malloc( sizeof( uint8_t ) * dataLength );
    size_t bytesProcessed;

    _IotMqtt_DeserializeConnack( pConnackStart,
                                 dataLength,
                                 &bytesProcessed );
}

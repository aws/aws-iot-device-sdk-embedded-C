#include IOT_CONFIG_FILE
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

/*-----------------------------------------------------------*/

void harness()
{
    size_t dataLength;
    uint8_t * pPingrespStart = malloc( sizeof( uint8_t ) * dataLength );
    size_t bytesProcessed;

    _IotMqtt_DeserializePingresp( pPingrespStart,
                                  dataLength,
                                  &bytesProcessed );
}

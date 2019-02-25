#include IOT_CONFIG_FILE
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

/*-----------------------------------------------------------*/

void harness()
{
    size_t dataLength;
    uint8_t * pPubackStart = malloc( sizeof( uint8_t ) * dataLength );
    uint16_t packetIdentifier;
    size_t bytesProcessed;

    _IotMqtt_DeserializePuback( pPubackStart,
                                dataLength,
                                &packetIdentifier,
                                &bytesProcessed );
}

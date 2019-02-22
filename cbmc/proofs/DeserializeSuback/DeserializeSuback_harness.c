#include IOT_CONFIG_FILE
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

/*-----------------------------------------------------------*/

void harness()
{
    IotMqttConnection_t mqttConnection;
    size_t dataLength;
    uint8_t * pSubackStart = malloc( sizeof( uint8_t ) * dataLength );
    uint16_t packetIdentifier;
    size_t bytesProcessed;

    __CPROVER_assume( dataLength <= BUFFER_SIZE );

    _IotMqtt_DeserializeSuback( mqttConnection,
                                pSubackStart,
                                dataLength,
                                &packetIdentifier,
                                &bytesProcessed );
}

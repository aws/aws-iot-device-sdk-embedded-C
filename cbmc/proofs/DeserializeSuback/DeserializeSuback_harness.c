#include IOT_CONFIG_FILE
#include "private/aws_iot_mqtt_internal.h"

#include <stdlib.h>

/*-----------------------------------------------------------*/

void harness()
{
    AwsIotMqttConnection_t mqttConnection;
    size_t dataLength;
    uint8_t * pSubackStart = malloc( sizeof( uint8_t ) * dataLength );
    uint16_t packetIdentifier;
    size_t bytesProcessed;

    __CPROVER_assume( dataLength <= BUFFER_SIZE );

    AwsIotMqttInternal_DeserializeSuback( mqttConnection,
                                          pSubackStart,
                                          dataLength,
                                          &packetIdentifier,
                                          &bytesProcessed );
}

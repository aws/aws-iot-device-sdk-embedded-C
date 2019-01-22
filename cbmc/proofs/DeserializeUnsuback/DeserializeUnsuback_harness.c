#include IOT_CONFIG_FILE
#include "private/aws_iot_mqtt_internal.h"

#include <stdlib.h>

/*-----------------------------------------------------------*/

void harness()
{
    size_t dataLength;
    uint8_t * pUnsubackStart = malloc( sizeof( uint8_t ) * dataLength );
    uint16_t packetIdentifier;
    size_t bytesProcessed;

    AwsIotMqttInternal_DeserializeUnsuback( pUnsubackStart,
                                            dataLength,
                                            &packetIdentifier,
                                            &bytesProcessed );
}

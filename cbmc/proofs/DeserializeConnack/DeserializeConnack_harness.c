#include IOT_CONFIG_FILE
#include "private/aws_iot_mqtt_internal.h"

#include <stdlib.h>

/*-----------------------------------------------------------*/

void harness()
{
    size_t dataLength;
    uint8_t * pConnackStart = malloc( sizeof( uint8_t ) * dataLength );
    size_t bytesProcessed;

    AwsIotMqttInternal_DeserializeConnack( pConnackStart,
                                           dataLength,
                                           &bytesProcessed );
}

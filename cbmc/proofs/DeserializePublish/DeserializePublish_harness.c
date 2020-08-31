#include IOT_CONFIG_FILE
#include "private/aws_iot_mqtt_internal.h"

#include <stdlib.h>

/*-----------------------------------------------------------*/

void harness()
{
    size_t dataLength;
    uint8_t * pPublishStart = malloc( sizeof( uint8_t ) * dataLength );
    AwsIotMqttPublishInfo_t output;
    uint16_t packetIdentifier;
    size_t bytesProcessed;

    AwsIotMqttInternal_DeserializePublish( pPublishStart,
                                           dataLength,
                                           &output,
                                           &packetIdentifier,
                                           &bytesProcessed );
}

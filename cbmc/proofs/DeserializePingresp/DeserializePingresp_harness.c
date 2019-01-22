#include IOT_CONFIG_FILE
#include "private/aws_iot_mqtt_internal.h"

#include <stdlib.h>

void harness()
{
  size_t dataLength;
  uint8_t * pPingrespStart = malloc(sizeof(uint8_t) * dataLength);
  size_t BytesProcessed;

  AwsIotMqttInternal_DeserializePingresp( pPingrespStart,
					  dataLength,
					  &BytesProcessed );

}


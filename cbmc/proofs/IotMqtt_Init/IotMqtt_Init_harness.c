#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>
#include <string.h>

void harness()
{
    IotMqttError_t status = IotMqtt_Init();

    assert( status == IOT_MQTT_SUCCESS || status == IOT_MQTT_NOT_INITIALIZED );
}

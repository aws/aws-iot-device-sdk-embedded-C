#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

/*-----------------------------------------------------------*/

void harness()
{
    IotMqttPublishInfo_t publishInfo;

    publishInfo.pTopicName = malloc( publishInfo.topicNameLength );
    publishInfo.pPayload = malloc( publishInfo.payloadLength );

    _mqttOperation_t operation;
    operation.u.publish.publishInfo = publishInfo;

    _mqttPacket_t publish;
    publish.pRemainingData = malloc( sizeof( uint8_t ) * publish.remainingLength );
    publish.u.pIncomingPublish = &operation;


    _IotMqtt_DeserializePublish( &publish );
}

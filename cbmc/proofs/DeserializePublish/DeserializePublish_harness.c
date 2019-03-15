#include IOT_CONFIG_FILE
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>

/*-----------------------------------------------------------*/

void harness()
{
  IotMqttPublishInfo_t PublishInfo;
  PublishInfo.pTopicName = malloc(PublishInfo.topicNameLength);
  PublishInfo.pPayload = malloc(PublishInfo.payloadLength);

  _mqttOperation_t Operation;
  Operation.publishInfo = PublishInfo;

  _mqttPacket_t Publish;
  Publish.pRemainingData = malloc(sizeof(uint8_t) * Publish.remainingLength);
  Publish.pIncomingPublish = &Operation;


  _IotMqtt_DeserializePublish( &Publish );
}

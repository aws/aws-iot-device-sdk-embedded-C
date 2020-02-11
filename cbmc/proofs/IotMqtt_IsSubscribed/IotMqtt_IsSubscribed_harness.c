#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>
#include <string.h>

#include "mqtt_state.h"

/*

bool IotMqtt_IsSubscribed( IotMqttConnection_t mqttConnection,
                           const char * pTopicFilter,
                           uint16_t topicFilterLength,
                           IotMqttSubscription_t * pCurrentSubscription );

*/

void harness()
{
  IotMqttConnection_t mqttConnection = allocate_IotMqttConnection(NULL);
  __CPROVER_assume(mqttConnection);
  ensure_IotMqttConnection_has_lists(mqttConnection);
  __CPROVER_assume(valid_IotMqttConnection(mqttConnection));

  // Move to allocation and valid connection?
  allocate_IotMqttSubscriptionList(&(mqttConnection->subscriptionList), 1);
  __CPROVER_assume(valid_IotMqttSubscriptionList(&(mqttConnection->subscriptionList), 1));

  uint16_t topicFilterLength;
  __CPROVER_assume(topicFilterLength < TOPIC_LENGTH_MAX);

  char* TopicFilter = malloc_can_fail(topicFilterLength);

  IotMqttSubscription_t result;

  IotMqtt_IsSubscribed( nondet_bool() ? NULL : mqttConnection,
			TopicFilter,
			topicFilterLength,
                        nondet_boo() ? NULL : &result );
}

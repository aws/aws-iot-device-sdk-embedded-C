#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>
#include <string.h>

#include "mqtt_state.h"

void harness()
{
    IotMqttConnection_t mqttConnection = allocate_IotMqttConnection( NULL );

    __CPROVER_assume( mqttConnection );
    ensure_IotMqttConnection_has_lists( mqttConnection );
    __CPROVER_assume( valid_IotMqttConnection( mqttConnection ) );

    allocate_IotMqttSubscriptionList( &( mqttConnection->subscriptionList ), 1 );
    __CPROVER_assume( valid_IotMqttSubscriptionList( &( mqttConnection->subscriptionList ), 1 ) );

    uint16_t topicFilterLength;
    __CPROVER_assume( topicFilterLength < TOPIC_LENGTH_MAX );

    char * TopicFilter = malloc_can_fail( topicFilterLength );
    __CPROVER_assume( VALID_STRING( TopicFilter, topicFilterLength ) );

    IotMqttSubscription_t result;

    IotMqtt_IsSubscribed( mqttConnection,
                          nondet_bool() ? NULL : TopicFilter,
                          topicFilterLength,
                          nondet_bool() ? NULL : &result );
}

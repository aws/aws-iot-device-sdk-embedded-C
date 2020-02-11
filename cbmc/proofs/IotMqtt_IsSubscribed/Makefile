ENTRY=IotMqtt_IsSubscribed

ABSTRACTIONS += --remove-function-body IotLog_Generic

# Remove for coverage
ABSTRACTIONS += --remove-function-body _mqttSubscription_setUnsubscribe
ABSTRACTIONS += --remove-function-body _matchEndWildcards
ABSTRACTIONS += --remove-function-body _matchWildcards
ABSTRACTIONS += --remove-function-body _packetMatch
ABSTRACTIONS += --remove-function-body _topicFilterMatch


OBJS += $(ENTRY)_harness.goto
OBJS += $(MQTT)/cbmc/proofs/mqtt_state.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_api.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_subscription.goto

# One more than actual number of subscriptions
SUBSCRIPTION_COUNT_MAX=4
DEF += -DSUBSCRIPTION_COUNT_MAX=$(SUBSCRIPTION_COUNT_MAX)
OPERATION_COUNT_MAX=4
DEF += -DOPERATION_COUNT_MAX=$(OPERATION_COUNT_MAX)

# One more than actual length of topics
TOPIC_LENGTH_MAX=6
DEF += -DTOPIC_LENGTH_MAX=$(TOPIC_LENGTH_MAX)

# Should be 2*SUBSCRIPTION_COUNT_MAX-1
SUBSCRIPTION_LIST_MAX=6
DEF += -DSUBSCRIPTION_LIST_MAX=$(SUBSCRIPTION_LIST_MAX)

LOOP += allocate_IotMqttSubscriptionArray.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += valid_IotMqttSubscriptionArray.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += allocate_IotMqttSubscriptionList.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += valid_IotMqttSubscriptionList.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += valid_IotMqttOperationList.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += IotListDouble_FindFirstMatch\$$link1.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += strncmp.0:$(TOPIC_LENGTH_MAX)

UNWINDING += --unwind 1
UNWINDING += --unwindset '$(shell echo $(LOOP) | sed 's/ /,/g')'

include ../Makefile.common

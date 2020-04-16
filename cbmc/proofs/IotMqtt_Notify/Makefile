ENTRY=_IotMqtt_Notify

# We abstract all unreachable functions to improve coverage metrics
ABSTRACTIONS += --remove-function-body IotNetworkInterfaceClose

OBJS += $(ENTRY)_harness.goto
OBJS += $(MQTT)/cbmc/proofs/mqtt_state.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_api.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_operation.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_serialize.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_subscription.goto

# One more than actual number of subscriptions
SUBSCRIPTION_COUNT_MAX=4
DEF += -DSUBSCRIPTION_COUNT_MAX=$(SUBSCRIPTION_COUNT_MAX)

# One more than actual number of operations
OPERATION_COUNT_MAX=4
DEF += -DOPERATION_COUNT_MAX=$(OPERATION_COUNT_MAX)

# One more than actual length of topics
TOPIC_LENGTH_MAX=258
DEF += -DTOPIC_LENGTH_MAX=$(TOPIC_LENGTH_MAX)

# Enables CBMC stub for RemoveAllMatches function
DEF += -DCBMC_STUB_REMOVEALLMATCHES=1

LOOP += _matchWildcards.0:$(TOPIC_LENGTH_MAX)
LOOP += _topicFilterMatch.0:$(TOPIC_LENGTH_MAX)
LOOP += IotListDouble_RemoveAllMatches.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += IotListDouble_RemoveAllMatches$$link2.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += valid_IotMqttOperationList.0:$(OPERATION_COUNT_MAX)
LOOP += valid_IotMqttSubscriptionList.0:$(SUBSCRIPTION_COUNT_MAX)

UNWINDING += --unwind 1
UNWINDING += --unwindset '$(shell echo $(LOOP) | sed 's/ /,/g')'

include ../Makefile.common

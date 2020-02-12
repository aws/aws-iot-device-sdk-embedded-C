ENTRY=IotMqtt_Wait

ABSTRACTIONS += --remove-function-body IotNetworkInterfaceClose
ABSTRACTIONS += --remove-function-body IotLog_Generic
ABSTRACTIONS += --remove-function-body IotListDouble_Remove
ABSTRACTIONS += --remove-function-body _mqttOperation_tryDestroy
ABSTRACTIONS += --remove-function-body _mqttSubscription_setUnsubscribe
ABSTRACTIONS += --remove-function-body _mqttSubscription_tryDestroy
ABSTRACTIONS += --remove-function-body _IotMqtt_ProcessIncomingPublish
ABSTRACTIONS += --remove-function-body _mqttOperation_match
ABSTRACTIONS += --remove-function-body IotListDouble_Remove
ABSTRACTIONS += --remove-function-body _matchEndWildcards
ABSTRACTIONS += --remove-function-body _matchWildcards
ABSTRACTIONS += --remove-function-body _packetMatch
ABSTRACTIONS += --remove-function-body _topicFilterMatch
ABSTRACTIONS += --remove-function-body _topicMatch
ABSTRACTIONS += --remove-function-body IotListDouble_Remove
ABSTRACTIONS += --remove-function-body 'IotListDouble_Remove$$link3'

OBJS += $(ENTRY)_harness.goto
OBJS += $(MQTT)/cbmc/proofs/mqtt_state.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_api.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_operation.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_serialize.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_subscription.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_validate.goto

# One more than actual number of subscriptions
SUBSCRIPTION_COUNT_MAX=4
DEF += -DSUBSCRIPTION_COUNT_MAX=$(SUBSCRIPTION_COUNT_MAX)
OPERATION_COUNT_MAX=4
DEF += -DOPERATION_COUNT_MAX=$(OPERATION_COUNT_MAX)

# One more than actual length of topics
TOPIC_LENGTH_MAX=6
DEF += -DTOPIC_LENGTH_MAX=$(TOPIC_LENGTH_MAX)

LOOP += valid_IotMqttSubscriptionList.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += valid_IotMqttOperationList.0:$(SUBSCRIPTION_COUNT_MAX)

UNWINDING += --unwind 1
UNWINDING += --unwindset '$(shell echo $(LOOP) | sed 's/ /,/g')'

include ../Makefile.common

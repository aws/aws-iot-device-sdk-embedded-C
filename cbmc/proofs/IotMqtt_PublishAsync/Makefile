ENTRY=IotMqtt_PublishAsync

# We abstract all the log and concurrency related functions in this proof
# and assume their implementation is correct
ABSTRACTIONS += --remove-function-body IotLog_Generic
ABSTRACTIONS += --remove-function-body _IotMqtt_ProcessSend
ABSTRACTIONS += --remove-function-body _destroyMqttConnection

OBJS += $(ENTRY)_harness.goto
OBJS += $(MQTT)/cbmc/proofs/mqtt_state.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_api.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_helper.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_operation.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_serialize.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_validate.goto

# One more than actual number of subscriptions
SUBSCRIPTION_COUNT_MAX=4
DEF += -DSUBSCRIPTION_COUNT_MAX=$(SUBSCRIPTION_COUNT_MAX)

# One more than actual number of operations
OPERATION_COUNT_MAX=4
DEF += -DOPERATION_COUNT_MAX=$(OPERATION_COUNT_MAX)

UNWINDING += --unwindset IotListDouble_RemoveAllMatches.0:$(SUBSCRIPTION_COUNT_MAX)
UNWINDING += --unwindset valid_IotMqttSubscriptionList.0:$(SUBSCRIPTION_COUNT_MAX)
UNWINDING += --unwindset valid_IotMqttOperationList.0:$(OPERATION_COUNT_MAX)
UNWINDING += --unwindset _encodeRemainingLength.0:$(SUBSCRIPTION_COUNT_MAX)
UNWINDING += --unwind 1

include ../Makefile.common

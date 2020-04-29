ENTRY=IotMqtt_PublishAsync

# We abstract all the log and concurrency related functions in this proof
# and assume their implementation is correct
ABSTRACTIONS += --remove-function-body IotLog_Generic

# We also abstract unreachable functions to improve coverage metrics
ABSTRACTIONS += --remove-function-body IotNetworkInterfaceClose
ABSTRACTIONS += --remove-function-body IotNetworkInterfaceReceive

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

# Enables CBMC stub for RemoveAllMatches function
DEF += -DCBMC_STUB_REMOVEALLMATCHES=1

# Allow MQTT allocations to fail for coverage
DEF += -include mqtt_state.h
DEF += -DIotMqtt_MallocMessage=malloc_can_fail
DEF += -DIotMqtt_MallocOperation=malloc_can_fail

# The bound for _encodeRemainingLength is based on the maximum
# possible value for remainingLength, in this case, 2 * UINT16_MAX + 4
# (see _IotMqtt_PublishPacketSize). Thus, the bound is the number of
# times the function must divide the maximum remainingLength
# value by 128 until hits zero.
LOOP += _encodeRemainingLength.0:3
LOOP += IotListDouble_RemoveAllMatches.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += valid_IotMqttOperationList.0:$(OPERATION_COUNT_MAX)
LOOP += valid_IotMqttSubscriptionList.0:$(SUBSCRIPTION_COUNT_MAX)

UNWINDING += --unwind 1
UNWINDING += --unwindset '$(shell echo $(LOOP) | sed 's/ /,/g')'

include ../Makefile.common

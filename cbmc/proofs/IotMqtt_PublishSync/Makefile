ENTRY=IotMqtt_PublishSync

# We abstract all the log and concurrency related functions in this proof
# and assume their implementation is correct
ABSTRACTIONS += --remove-function-body IotLog_Generic

# We abstract this function because manual inspection demonstrates that it is unreachable
ABSTRACTIONS += --remove-function-body _IotMqtt_RemoveSubscriptionByPacket

# We also abstract unreachable functions to improve coverage metrics
ABSTRACTIONS += --remove-function-body _IotMqtt_ProcessIncomingPublish
ABSTRACTIONS += --remove-function-body IotNetworkInterfaceClose
ABSTRACTIONS += --remove-function-body IotNetworkInterfaceReceive

OBJS += $(ENTRY)_harness.goto
OBJS += $(MQTT)/cbmc/proofs/mqtt_state.goto
OBJS += $(MQTT)/cbmc/stubs/_IotMqtt_NextPacketIdentifier.goto
OBJS += $(MQTT)/cbmc/stubs/IotListDouble_RemoveAllMatches.goto
OBJS += $(MQTT)/cbmc/stubs/IotSemaphore.goto
OBJS += $(MQTT)/cbmc/stubs/IotTaskPool_CreateJob.goto
OBJS += $(MQTT)/cbmc/stubs/IotTaskPool_ScheduleDeferred.goto
OBJS += $(MQTT)/cbmc/stubs/IotTaskPool_TryCancel.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_api.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_helper.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_operation.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_serialize.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_subscription.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_validate.goto

# One more than actual number of subscriptions
SUBSCRIPTION_COUNT_MAX=4
DEF += -DSUBSCRIPTION_COUNT_MAX=$(SUBSCRIPTION_COUNT_MAX)

# One more than actual number of operations
OPERATION_COUNT_MAX=4
DEF += -DOPERATION_COUNT_MAX=$(OPERATION_COUNT_MAX)

# One more than actual length of topics
TOPIC_LENGTH_MAX=6
DEF += -DTOPIC_LENGTH_MAX=$(TOPIC_LENGTH_MAX)

# One more than actual length of payload
PAYLOAD_LENGTH_MAX=6
DEF += -DPAYLOAD_LENGTH_MAX=$(PAYLOAD_LENGTH_MAX)

# Enables CBMC stub for RemoveAllMatches function
DEF += -DCBMC_STUB_REMOVEALLMATCHES=1

# Allow MQTT allocations to fail for coverage
DEF += -include mqtt_state.h
DEF += -DIotMqtt_MallocMessage=malloc_can_fail
DEF += -DIotMqtt_MallocOperation=malloc_can_fail

LOOP += _encodeRemainingLength.0:$(PAYLOAD_LENGTH_MAX)
LOOP += _IotMqtt_InvokeSubscriptionCallback.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += _matchWildcards.0:$(TOPIC_LENGTH_MAX)
LOOP += _topicFilterMatch.0:$(TOPIC_LENGTH_MAX)
LOOP += IotListDouble_RemoveAllMatches.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += IotListDouble_RemoveAllMatches$$link2.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += valid_IotMqttOperationList.0:$(OPERATION_COUNT_MAX)
LOOP += valid_IotMqttSubscriptionList.0:$(SUBSCRIPTION_COUNT_MAX)

UNWINDING += --unwind 1
UNWINDING += --unwindset '$(shell echo $(LOOP) | sed 's/ /,/g')'

include ../Makefile.common

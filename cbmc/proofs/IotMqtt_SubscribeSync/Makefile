ENTRY=IotMqtt_SubscribeSync

# We abstract these functions because manual inspection demonstrates they are unreachable
ABSTRACTIONS += --remove-function-body _checkRetryLimit
ABSTRACTIONS += --remove-function-body _scheduleCallback
ABSTRACTIONS += --remove-function-body _scheduleNextRetry

# We abstract all unreachable functions to improve coverage metrics
ABSTRACTIONS += --remove-function-body _IotMqtt_ScheduleOperation
ABSTRACTIONS += --remove-function-body _IotMqtt_SerializeUnsubscribe
ABSTRACTIONS += --remove-function-body _IotMqtt_SerializeUnsubscribeCommon
ABSTRACTIONS += --remove-function-body _mqttOperation_match
ABSTRACTIONS += --remove-function-body _mqttOperation_tryDestroy
ABSTRACTIONS += --remove-function-body _mqttSubscription_setUnsubscribe
ABSTRACTIONS += --remove-function-body _mqttSubscription_tryDestroy
ABSTRACTIONS += --remove-function-body _packetMatch
ABSTRACTIONS += --remove-function-body _topicFilterMatch
ABSTRACTIONS += --remove-function-body IotMqtt_strerror
ABSTRACTIONS += --remove-function-body IotNetworkInterfaceClose
ABSTRACTIONS += --remove-function-body IotNetworkInterfaceReceive

OBJS += $(ENTRY)_harness.goto
OBJS += $(MQTT)/cbmc/proofs/mqtt_state.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_api.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_helper.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_operation.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_serialize.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_subscription.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_validate.goto

# One more than actual number of subscriptions in a subscription list
SUBSCRIPTION_COUNT_MAX=2
DEF += -DSUBSCRIPTION_COUNT_MAX=$(SUBSCRIPTION_COUNT_MAX)

# One more than actual number of operations in an operation list
OPERATION_COUNT_MAX=2
DEF += -DOPERATION_COUNT_MAX=$(OPERATION_COUNT_MAX)

# One more than actual length of topics
TOPIC_LENGTH_MAX=6
DEF += -DTOPIC_LENGTH_MAX=$(TOPIC_LENGTH_MAX)

# Should be 2*SUBSCRIPTION_COUNT_MAX-1
SUBSCRIPTION_LIST_MAX=3
DEF += -DSUBSCRIPTION_LIST_MAX=$(SUBSCRIPTION_LIST_MAX)

# Enables CBMC stub for RemoveAllMatches function
DEF += -DCBMC_STUB_REMOVEALLMATCHES=1

# These functions default to malloc. The CBMC model of malloc never fails,
# so we replace the CBMC model with a model that can fail to improve
# coverage and exercise more code
DEF += -include mqtt_state.h
DEF += -DIotMqtt_MallocMessage=malloc_can_fail
DEF += -DIotMqtt_MallocOperation=malloc_can_fail
DEF += -DIotMqtt_MallocSubscription=malloc_can_fail

LOOP += _IotMqtt_AddSubscriptions.0:$(SUBSCRIPTION_LIST_MAX)
LOOP += _IotMqtt_SerializeSubscribeCommon.0:$(SUBSCRIPTION_LIST_MAX)
LOOP += _IotMqtt_SubscriptionPacketSize.0:$(SUBSCRIPTION_LIST_MAX)
LOOP += _IotMqtt_ValidateSubscriptionList.0:$(SUBSCRIPTION_LIST_MAX)
LOOP += _validateSubscription.0:$(TOPIC_LENGTH_MAX)
LOOP += allocate_IotMqttSubscriptionArray.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += allocate_IotMqttSubscriptionList.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += IotListDouble_FindFirstMatch.0:$(SUBSCRIPTION_LIST_MAX)
LOOP += IotListDouble_FindFirstMatch\$$link1.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += IotListDouble_RemoveAllMatches.0:$(SUBSCRIPTION_LIST_MAX)
LOOP += IotListDouble_RemoveAllMatches\$$link1.0:$(SUBSCRIPTION_LIST_MAX)
LOOP += strncmp.0:$(TOPIC_LENGTH_MAX)
LOOP += valid_IotMqttOperationList.0:$(OPERATION_COUNT_MAX)
LOOP += valid_IotMqttSubscriptionArray.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += valid_IotMqttSubscriptionList.0:$(SUBSCRIPTION_COUNT_MAX)

UNWINDING += --unwind 1
UNWINDING += --unwindset '$(shell echo $(LOOP) | sed 's/ /,/g')'

include ../Makefile.common

ENTRY=IotMqtt_Connect

# We abstract these functions because manual inspection demonstrates they are unreachable
ABSTRACTIONS += --remove-function-body _checkRetryLimit
ABSTRACTIONS += --remove-function-body _IotMqtt_RemoveSubscriptionByPacket
ABSTRACTIONS += --remove-function-body _scheduleCallback
ABSTRACTIONS += --remove-function-body _scheduleNextRetry

# We abstract all unreachable functions to improve coverage metrics
ABSTRACTIONS += --remove-function-body _IotMqtt_NextPacketIdentifier
ABSTRACTIONS += --remove-function-body _IotMqtt_PublishSetDup
ABSTRACTIONS += --remove-function-body _IotMqtt_ScheduleOperation
ABSTRACTIONS += --remove-function-body _matchEndWildcards
ABSTRACTIONS += --remove-function-body _matchWildcards
ABSTRACTIONS += --remove-function-body _mqttOperation_match
ABSTRACTIONS += --remove-function-body _mqttSubscription_setUnsubscribe
ABSTRACTIONS += --remove-function-body _packetMatch
ABSTRACTIONS += --remove-function-body _topicFilterMatch
ABSTRACTIONS += --remove-function-body IotMutex_Create
ABSTRACTIONS += --remove-function-body IotNetworkInterfaceCloseCallback
ABSTRACTIONS += --remove-function-body IotNetworkInterfaceReceive
ABSTRACTIONS += --remove-function-body IotTaskPool_ScheduleDeferred
ABSTRACTIONS += --remove-function-body IotSemaphore_TimedWait

OBJS += $(ENTRY)_harness.goto
OBJS += $(MQTT)/cbmc/proofs/mqtt_state.goto
OBJS += $(MQTT)/cbmc/stubs/IotListDouble_RemoveAllMatches.goto
OBJS += $(MQTT)/cbmc/stubs/IotTaskPool_CreateJob.goto
OBJS += $(MQTT)/cbmc/stubs/IotTaskPool_TryCancel.goto
OBJS += $(MQTT)/cbmc/stubs/_IotMqtt_RemoveSubscriptionByTopicFilter.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_api.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_helper.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_operation.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_serialize.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_subscription.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_validate.goto

################################################################
# Proof assumptions

# This should be smaller than CLIENT_IDENTIFIER_LENGTH_MAX for coverage
AWS_IOT_MQTT_SERVER_MAX_CLIENTID_LENGTH=6
DEF += -DAWS_IOT_MQTT_SERVER_MAX_CLIENTID_LENGTH=$(AWS_IOT_MQTT_SERVER_MAX_CLIENTID_LENGTH)

# This should be smaller than SUBSCRIPTION_COUNT_MAX for coverage
AWS_IOT_MQTT_SERVER_MAX_TOPIC_FILTERS_PER_SUBSCRIBE=1
DEF += -DAWS_IOT_MQTT_SERVER_MAX_TOPIC_FILTERS_PER_SUBSCRIBE=$(AWS_IOT_MQTT_SERVER_MAX_TOPIC_FILTERS_PER_SUBSCRIBE)

# This should be smaller than TOPIC_LENGTH_MAX for coverage
AWS_IOT_MQTT_SERVER_MAX_TOPIC_LENGTH=2
DEF += -DAWS_IOT_MQTT_SERVER_MAX_TOPIC_LENGTH=$(AWS_IOT_MQTT_SERVER_MAX_TOPIC_LENGTH)

# One more than actual number of clientIdentifierLength
CLIENT_IDENTIFIER_LENGTH_MAX=8
DEF += -DCLIENT_IDENTIFIER_LENGTH_MAX=$(CLIENT_IDENTIFIER_LENGTH_MAX)

# This should be smaller than CLIENT_IDENTIFIER_LENGTH_MAX for coverage
MQTT_SERVER_MAX_CLIENTID_LENGTH=6
DEF += -DMQTT_SERVER_MAX_CLIENTID_LENGTH=$(MQTT_SERVER_MAX_CLIENTID_LENGTH)

# This should be smaller than PAYLOAD_LENGTH_MAX for coverage
MQTT_SERVER_MAX_LWT_PAYLOAD_LENGTH=2
DEF += -DMQTT_SERVER_MAX_LWT_PAYLOAD_LENGTH=$(MQTT_SERVER_MAX_LWT_PAYLOAD_LENGTH)

# One more than actual number of connectPacketSize
MQTT_PACKET_CONNECT_MAX_SIZE=50
DEF += -DMQTT_PACKET_CONNECT_MAX_SIZE=$(MQTT_PACKET_CONNECT_MAX_SIZE)

# One more than actual number of passwordLength
PASSWORD_LENGTH_MAX=3
DEF += -DPASSWORD_LENGTH_MAX=$(PASSWORD_LENGTH_MAX)

# One more than actual number of payloadLength
PAYLOAD_LENGTH_MAX=4
DEF += -DPAYLOAD_LENGTH_MAX=$(PAYLOAD_LENGTH_MAX)

# One more than actual number of subscriptions
SUBSCRIPTION_COUNT_MAX=3
DEF += -DSUBSCRIPTION_COUNT_MAX=$(SUBSCRIPTION_COUNT_MAX)

# Should be 2*SUBSCRIPTION_COUNT_MAX-1
SUBSCRIPTION_LIST_MAX=3
DEF += -DSUBSCRIPTION_LIST_MAX=$(SUBSCRIPTION_LIST_MAX)

# One more than actual length of topics
TOPIC_LENGTH_MAX=4
DEF += -DTOPIC_LENGTH_MAX=$(TOPIC_LENGTH_MAX)

# One more than actual number of topicNameLength
TOPIC_NAME_LENGTH_MAX=8
DEF += -DTOPIC_NAME_LENGTH_MAX=$(TOPIC_NAME_LENGTH_MAX)

# One more than actual number of userNameLength
USER_NAME_LENGTH_MAX=3
DEF += -DUSER_NAME_LENGTH_MAX=$(USER_NAME_LENGTH_MAX)

# Enables CBMC stub for RemoveAllMatches function
DEF += -DCBMC_STUB_REMOVEALLMATCHES=1

# Enables _IotMqtt_SerializePingreq to return a nondet status
DEF += -DCBMC_SERIALIZAPINGREQ_NONDET_RETURN=1

# Simulates background thread behavior in _sendConnectRequest
DEF += -DCBMC_BACKGROUND_THREAD_SIMULATION=1

# Allow MQTT allocations to fail for coverage
DEF += -include mqtt_state.h
DEF += -DIotMqtt_MallocMessage=malloc_can_fail
DEF += -DIotMqtt_MallocOperation=malloc_can_fail
DEF += -DIotMqtt_MallocSubscription=malloc_can_fail
DEF += -DIotMqtt_MallocConnection=malloc_can_fail

################################################################

LOOP += harness.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += allocate_IotMqttSubscriptionArray.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += valid_IotMqttSubscriptionArray.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += IotListDouble_FindFirstMatch.0:$(SUBSCRIPTION_LIST_MAX)
LOOP += IotListDouble_FindFirstMatch\$$link1.0:$(SUBSCRIPTION_LIST_MAX)
LOOP += IotListDouble_RemoveAllMatches.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += _IotMqtt_AddSubscriptions.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += _IotMqtt_AddSubscriptions.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += _IotMqtt_ValidateSubscriptionList.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += _encodeRemainingLength.0:$(TOPIC_LENGTH_MAX)
LOOP += strncmp.0:$(TOPIC_LENGTH_MAX)
LOOP += _validateSubscription.0:$(TOPIC_LENGTH_MAX)
LOOP += valid_IotMqttSubscriptionList.0:$(SUBSCRIPTION_COUNT_MAX)

UNWINDING += --unwind 1
UNWINDING += --unwindset '$(shell echo $(LOOP) | sed 's/ /,/g')'

include ../Makefile.common

ENTRY=IotMqtt_Disconnect

################################################################
# Proof assumptions

# Bound the number of subscriptions in a list (BOUND = MAX-1)
SUBSCRIPTION_COUNT_MAX=2
DEF += -DSUBSCRIPTION_COUNT_MAX=$(SUBSCRIPTION_COUNT_MAX)

# Bound the number of operations in a list (BOUND = MAX-1)
OPERATION_COUNT_MAX=2
DEF += -DOPERATION_COUNT_MAX=$(OPERATION_COUNT_MAX)

# Bound the length of subscription topics (BOUND = MAX-1)
TOPIC_LENGTH_MAX=8
DEF += -DTOPIC_LENGTH_MAX=$(TOPIC_LENGTH_MAX)

# A constant that should be 2*SUBSCRIPTION_COUNT_MAX-1
SUBSCRIPTION_LIST_MAX=3
DEF += -DSUBSCRIPTION_LIST_MAX=$(SUBSCRIPTION_LIST_MAX)

################################################################
# MQTT configuration constants modified for testing

# this should be smaller than topic_length_max for coverage
# _validateSubscription coverage at line 385
AWS_IOT_MQTT_SERVER_MAX_TOPIC_LENGTH=6
DEF += -DAWS_IOT_MQTT_SERVER_MAX_TOPIC_LENGTH=$(AWS_IOT_MQTT_SERVER_MAX_TOPIC_LENGTH)

# this should be smaller than topic_length_max for coverage
# _IotMqtt_SubscriptionPacketSize coverage at line 702
MQTT_MAX_REMAINING_LENGTH=6
DEF += -DMQTT_MAX_REMAINING_LENGTH=$(MQTT_MAX_REMAINING_LENGTH)

################################################################
# Function omitted from the proof
# See the proof harness for

ABSTRACTIONS += --remove-function-body IotLog_Generic

# Functions removed as manually proven to be unreachable
ABSTRACTIONS += --remove-function-body _IotMqtt_PublishSetDup
ABSTRACTIONS += --remove-function-body _IotMqtt_RemoveSubscriptionByPacket
ABSTRACTIONS += --remove-function-body _IotMqtt_ScheduleOperation
ABSTRACTIONS += --remove-function-body _checkRetryLimit
ABSTRACTIONS += --remove-function-body _completePendingSend
ABSTRACTIONS += --remove-function-body _scheduleCallback
ABSTRACTIONS += --remove-function-body _scheduleNextRetry

# Functions omitted for coverage
ABSTRACTIONS += --remove-function-body IotMqtt_ReceiveCallback
ABSTRACTIONS += --remove-function-body IotNetworkInterfaceReceive
ABSTRACTIONS += --remove-function-body _IotMqtt_DeserializeConnack
ABSTRACTIONS += --remove-function-body _IotMqtt_DeserializePuback
ABSTRACTIONS += --remove-function-body _IotMqtt_DeserializeSuback
ABSTRACTIONS += --remove-function-body _IotMqtt_DeserializeUnsuback
ABSTRACTIONS += --remove-function-body _matchEndWildcards
ABSTRACTIONS += --remove-function-body _matchWildcards
ABSTRACTIONS += --remove-function-body _mqttOperation_match
ABSTRACTIONS += --remove-function-body _mqttSubscription_setUnsubscribe
ABSTRACTIONS += --remove-function-body _packetMatch
ABSTRACTIONS += --remove-function-body _topicFilterMatch
ABSTRACTIONS += --remove-function-body _topicMatch

################################################################
# Stub out list remove functions.

DEF += -DCBMC_STUB_REMOVEALL=1
DEF += -DCBMC_STUB_REMOVEALLMATCHES=1

################################################################

OBJS += $(ENTRY)_harness.goto
OBJS += $(MQTT)/cbmc/proofs/mqtt_state.goto
OBJS += $(MQTT)/cbmc/stubs/IotListDouble_RemoveAll.goto
OBJS += $(MQTT)/cbmc/stubs/IotListDouble_RemoveAllMatches.goto
OBJS += $(MQTT)/cbmc/stubs/IotSemaphore.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_api.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_helper.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_operation.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_network.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_serialize.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_subscription.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_validate.goto

# allow mqtt mallocs to fail for coverage
DEF += -include mqtt_state.h
DEF += -DIotMqtt_MallocMessage=malloc_can_fail
DEF += -DIotMqtt_MallocOperation=malloc_can_fail

################################################################
# Loop unwinding

LOOP += valid_IotMqttOperationList.0:$(OPERATION_COUNT_MAX)
LOOP += valid_IotMqttSubscriptionList.0:$(SUBSCRIPTION_COUNT_MAX)

UNWINDING += --unwind 1

UNWINDING += --unwindset '$(shell echo $(LOOP) | sed 's/ /,/g')'

################################################################

include ../Makefile.common


ENTRY?=IotMqtt_ReceiveCallback

################################################################
# Proof works by case splitting by packet type
#
# The value of PACKET should be set on the make command line to one of
#   CONNACK
#   PUBLISH
#   PUBACK
#   SUBACK
#   UNSUBACK
# or should be left undefined to model any other packet type
#
# The proof is driving by running make in the six subdirectories.

ifdef PACKET
DEF += -DCBMC_PACKET=MQTT_PACKET_TYPE_$(PACKET)
endif

################################################################
# Proof assumptions

# Bound the number of subscriptions in a list (BOUND = MAX-1)
SUBSCRIPTION_COUNT_MAX=2
DEF += -DSUBSCRIPTION_COUNT_MAX=$(SUBSCRIPTION_COUNT_MAX)

# Bound the number of operations in a list (BOUND = MAX-1)
OPERATION_COUNT_MAX=2
DEF += -DOPERATION_COUNT_MAX=$(OPERATION_COUNT_MAX)

# Bound the length of subscription topics (BOUND = MAX-1)
TOPIC_LENGTH_MAX=6
DEF += -DTOPIC_LENGTH_MAX=$(TOPIC_LENGTH_MAX)

# Bound the remaining length of a packet (BOUND = MAX-1)
CBMC_REMAINING_LENGTH_BOUND=15
DEF += -DCBMC_REMAINING_LENGTH_BOUND=$(CBMC_REMAINING_LENGTH_BOUND)

# A constant that should be 2*SUBSCRIPTION_COUNT_MAX-1
SUBSCRIPTION_LIST_MAX=3
DEF += -DSUBSCRIPTION_LIST_MAX=$(SUBSCRIPTION_LIST_MAX)

################################################################
# Abstract the flush packet method

ABSTRACTIONS += --remove-function-body _flushPacket

################################################################
# Abstract list remove functions

DEF += -DCBMC_STUB_REMOVEALL=1
DEF += -DCBMC_STUB_REMOVEALLMATCHES=1

################################################################

OBJS += $(MQTT)/cbmc/proofs/$(ENTRY)/$(ENTRY)_harness.goto
OBJS += $(MQTT)/cbmc/proofs/mqtt_state.goto
OBJS += $(MQTT)/cbmc/stubs/_IotMqtt_Notify.goto
OBJS += $(MQTT)/cbmc/stubs/IotListDouble_RemoveAll.goto
OBJS += $(MQTT)/cbmc/stubs/IotListDouble_RemoveAllMatches.goto
OBJS += $(MQTT)/cbmc/stubs/IotTaskPool_CreateJob.goto
OBJS += $(MQTT)/cbmc/stubs/IotTaskPool_ScheduleDeferred.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_api.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_helper.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_network.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_operation.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_serialize.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_subscription.goto

# allow mqtt mallocs to fail for coverage
DEF += -include mqtt_state.h
DEF += -DIotMqtt_MallocMessage=malloc_can_fail
DEF += -DIotMqtt_MallocOperation=malloc_can_fail

################################################################
# Loop unwinding

LOOP += IotListDouble_FindFirstMatch.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += IotListDouble_FindFirstMatch\$$link1.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += IotListDouble_FindFirstMatch\$$link2.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += IotListDouble_FindFirstMatch\$$link3.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += IotListDouble_FindFirstMatch\$$link4.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += IotListDouble_FindFirstMatch\$$link5.0:$(SUBSCRIPTION_COUNT_MAX)

LOOP += _IotMqtt_GetRemainingLength.0:5
LOOP += _decodeSubackStatus.0:$(CBMC_REMAINING_LENGTH_BOUND)
LOOP += valid_IotMqttOperationList.0:$(OPERATION_COUNT_MAX)
LOOP += valid_IotMqttSubscriptionList.0:$(SUBSCRIPTION_COUNT_MAX)

UNWINDING += --unwind 1
UNWINDING += --unwindset '$(shell echo $(LOOP) | sed 's/ /,/g')'

################################################################

sinclude ../Makefile.common

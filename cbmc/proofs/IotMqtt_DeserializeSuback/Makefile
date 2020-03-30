ENTRY=_IotMqtt_DeserializeSuback

################################################################
# Proof assumptions

# Bound the number of subscriptions in a list (BOUND = MAX-1)
SUBSCRIPTION_COUNT_MAX=2
DEF += -DSUBSCRIPTION_COUNT_MAX=$(SUBSCRIPTION_COUNT_MAX)

# Bound the number of operations in a list (BOUND = MAX-1)
OPERATION_COUNT_MAX=2
DEF += -DOPERATION_COUNT_MAX=$(OPERATION_COUNT_MAX)

BUFFER_SIZE = 15
DEF += -DBUFFER_SIZE=$(BUFFER_SIZE)

################################################################
# Function omitted from the proof

# We abstract all the log and concurrency related functions in this
# proof and assume their implementation is correct
ABSTRACTIONS += --remove-function-body IotLog_Generic

# This define has the effect of removing RemoveAllMatches from the
# linear containers header so that our stub will be used.
DEF += -DCBMC_STUB_REMOVEALLMATCHES=1

################################################################
# Loop unwinding

LOOP += _decodeSubackStatus.0:$(BUFFER_SIZE)
LOOP += IotListDouble_FindFirstMatch.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += IotListDouble_RemoveAllMatches\$$link1.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += valid_IotMqttSubscriptionList.0:$(SUBSCRIPTION_COUNT_MAX)
LOOP += valid_IotMqttOperationList.0:$(OPERATION_COUNT_MAX)

UNWINDING += --unwind 1
UNWINDING += --unwindset '$(shell echo $(LOOP) | sed 's/ /,/g')'

################################################################

OBJS += $(ENTRY)_harness.goto
OBJS += $(MQTT)/cbmc/proofs/mqtt_state.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_serialize.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_subscription.goto

################################################################

include ../Makefile.common


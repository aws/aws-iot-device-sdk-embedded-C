METHOD=IotMqtt_Disconnect
ENTRY=harness

################################################################
# Proof assumptions

# Bound the number of subscriptions in a list (BOUND = MAX-1)
SUBSCRIPTION_COUNT_MAX=2
DEF += -DSUBSCRIPTION_COUNT_MAX=$(SUBSCRIPTION_COUNT_MAX)

# allow mqtt mallocs to fail for coverage
DEF += -include mqtt_state.h
DEF += -DIotMqtt_MallocMessage=malloc_can_fail
DEF += -DIotMqtt_MallocOperation=malloc_can_fail

################################################################

SRCDIR ?= $(abspath $(PROOFDIR)/../../..)

INC += \
	-I$(SRCDIR)/cbmc/proofs \
	-I$(SRCDIR)/demos \
	-I$(SRCDIR)/libraries/ \
	-I$(SRCDIR)/libraries/platform \
	-I$(SRCDIR)/libraries/standard/common/include \
	-I$(SRCDIR)/libraries/standard/mqtt/include \
	-I$(SRCDIR)/libraries/standard/mqtt/src \
	-I$(SRCDIR)/libraries/standard/mqtt/src/private \
	-I$(SRCDIR)/ports/common/include \

DEF += \
        -DIOT_SYSTEM_TYPES_FILE=\"$(SRCDIR)/ports/posix/include/iot_platform_types_posix.h\" \
        -Diotmqtt_EXPORTS \

COMPILE_FLAGS = -std=gnu99
LINK_FLAGS = -std=gnu99

NONDET_STATIC=--nondet-static

REMOVE_FUNCTION_BODY += IotLog_Generic
REMOVE_FUNCTION_BODY += _IotMqtt_PublishSetDup
REMOVE_FUNCTION_BODY += _IotMqtt_RemoveSubscriptionByPacket
REMOVE_FUNCTION_BODY += _IotMqtt_ScheduleOperation
REMOVE_FUNCTION_BODY += _checkRetryLimit
REMOVE_FUNCTION_BODY += _completePendingSend
REMOVE_FUNCTION_BODY += _scheduleCallback
REMOVE_FUNCTION_BODY += _scheduleNextRetry
REMOVE_FUNCTION_BODY += IotMqtt_ReceiveCallback
REMOVE_FUNCTION_BODY += IotNetworkInterfaceReceive
REMOVE_FUNCTION_BODY += _IotMqtt_DeserializeConnack
REMOVE_FUNCTION_BODY += _IotMqtt_DeserializePuback
REMOVE_FUNCTION_BODY += _IotMqtt_DeserializeSuback
REMOVE_FUNCTION_BODY += _IotMqtt_DeserializeUnsuback
REMOVE_FUNCTION_BODY += _matchEndWildcards
REMOVE_FUNCTION_BODY += _matchWildcards
REMOVE_FUNCTION_BODY += _mqttOperation_match
REMOVE_FUNCTION_BODY += _mqttSubscription_setUnsubscribe
REMOVE_FUNCTION_BODY += _packetMatch
REMOVE_FUNCTION_BODY += _topicFilterMatch
REMOVE_FUNCTION_BODY += _topicMatch


UNWINDSET += valid_IotMqttOperationList.0:$(OPERATION_COUNT_MAX)
UNWINDSET += valid_IotMqttSubscriptionList.0:$(SUBSCRIPTION_COUNT_MAX)

PROOF_SOURCES += $(PROOFDIR)/$(METHOD)_harness.c
PROOF_SOURCES += $(SRCDIR)/cbmc/proofs/mqtt_state.c
PROOF_SOURCES += $(SRCDIR)/cbmc/stubs/IotListDouble_RemoveAll.c
PROOF_SOURCES += $(SRCDIR)/cbmc/stubs/IotListDouble_RemoveAllMatches.c
PROOF_SOURCES += $(SRCDIR)/cbmc/stubs/IotSemaphore.c

PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/iot_mqtt_api.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/iot_mqtt_helper.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/iot_mqtt_operation.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/iot_mqtt_network.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/iot_mqtt_serialize.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/iot_mqtt_subscription.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/iot_mqtt_validate.c

DEFINES = $(DEF)

include ../Makefile.common

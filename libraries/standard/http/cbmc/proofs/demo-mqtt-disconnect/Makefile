HARNESS_FILE=IotMqtt_Disconnect_harness
HARNESS_ENTRY=harness

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
# Stub out list remove functions.

DEF += -DCBMC_STUB_REMOVEALL=1
DEF += -DCBMC_STUB_REMOVEALLMATCHES=1

# allow mqtt mallocs to fail for coverage
DEF += -include mqtt_state.h
DEF += -DIotMqtt_MallocMessage=malloc_can_fail
DEF += -DIotMqtt_MallocOperation=malloc_can_fail

################################################################

REMOVE_FUNCTION_BODY += IotLog_Generic
REMOVE_FUNCTION_BODY += IotMqtt_ReceiveCallback
REMOVE_FUNCTION_BODY += IotNetworkInterfaceReceive
REMOVE_FUNCTION_BODY += _IotMqtt_DeserializeConnack
REMOVE_FUNCTION_BODY += _IotMqtt_DeserializePuback
REMOVE_FUNCTION_BODY += _IotMqtt_DeserializeSuback
REMOVE_FUNCTION_BODY += _IotMqtt_DeserializeUnsuback
REMOVE_FUNCTION_BODY += _IotMqtt_PublishSetDup
REMOVE_FUNCTION_BODY += _IotMqtt_RemoveSubscriptionByPacket
REMOVE_FUNCTION_BODY += _IotMqtt_ScheduleOperation
REMOVE_FUNCTION_BODY += _checkRetryLimit
REMOVE_FUNCTION_BODY += _completePendingSend
REMOVE_FUNCTION_BODY += _matchEndWildcards
REMOVE_FUNCTION_BODY += _matchWildcards
REMOVE_FUNCTION_BODY += _mqttOperation_match
REMOVE_FUNCTION_BODY += _mqttSubscription_setUnsubscribe
REMOVE_FUNCTION_BODY += _packetMatch
REMOVE_FUNCTION_BODY += _scheduleCallback
REMOVE_FUNCTION_BODY += _scheduleNextRetry
REMOVE_FUNCTION_BODY += _topicFilterMatch
REMOVE_FUNCTION_BODY += _topicMatch


UNWINDSET += valid_IotMqttOperationList.0:$(OPERATION_COUNT_MAX)
UNWINDSET += valid_IotMqttSubscriptionList.0:$(SUBSCRIPTION_COUNT_MAX)

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/cbmc/proofs/mqtt_state.c
PROOF_SOURCES += $(SRCDIR)/cbmc/stubs/IotListDouble_RemoveAll.c
PROOF_SOURCES += $(SRCDIR)/cbmc/stubs/IotListDouble_RemoveAllMatches.c
PROOF_SOURCES += $(SRCDIR)/cbmc/stubs/IotSemaphore.c

PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/iot_mqtt_api.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/iot_mqtt_helper.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/iot_mqtt_network.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/iot_mqtt_operation.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/iot_mqtt_serialize.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/iot_mqtt_subscription.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/iot_mqtt_validate.c

DEFINES = $(DEF)

include ../Makefile.common

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

HARNESS_ENTRY=harness
HARNESS_FILE=MQTT_SerializeUnsubscribe_harness

# Bind the subscription count. Please see the default value in mqtt_cbmc_state.c
# for more information on this bound. This is set to 2 currently to have the proof
# run quickly.
SUBSCRIPTION_COUNT_MAX=2
DEFINES += -DSUBSCRIPTION_COUNT_MAX=$(SUBSCRIPTION_COUNT_MAX)
INCLUDES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET += allocateMqttSubscriptionList.0:$(SUBSCRIPTION_COUNT_MAX)
UNWINDSET += isValidMqttSubscriptionList.0:$(SUBSCRIPTION_COUNT_MAX)
UNWINDSET += __CPROVER_file_local_mqtt_lightweight_c_calculateSubscriptionPacketSize.0:$(SUBSCRIPTION_COUNT_MAX)
UNWINDSET += MQTT_SerializeUnsubscribe.0:$(SUBSCRIPTION_COUNT_MAX)
UNWINDSET += __CPROVER_file_local_mqtt_lightweight_c_encodeRemainingLength.0:4

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/libraries/standard/mqtt/cbmc/sources/mqtt_cbmc_state.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/mqtt_lightweight.c

include ../Makefile.common

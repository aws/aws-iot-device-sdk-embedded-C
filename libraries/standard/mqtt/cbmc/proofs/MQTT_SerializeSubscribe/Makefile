#
# Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
#
# Permission is hereby granted, free of charge, to any person obtaining a copy of
# this software and associated documentation files (the "Software"), to deal in
# the Software without restriction, including without limitation the rights to
# use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
# the Software, and to permit persons to whom the Software is furnished to do so,
# subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
# FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
# COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
# IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
# CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
#

HARNESS_ENTRY=harness
HARNESS_FILE=MQTT_SerializeSubscribe_harness

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
UNWINDSET += MQTT_SerializeSubscribe.0:$(SUBSCRIPTION_COUNT_MAX)
UNWINDSET += __CPROVER_file_local_mqtt_lightweight_c_encodeRemainingLength.0:4

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/libraries/standard/mqtt/cbmc/sources/mqtt_cbmc_state.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/mqtt_lightweight.c

include ../Makefile.common

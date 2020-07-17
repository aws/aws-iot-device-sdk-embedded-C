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
HARNESS_FILE=MQTT_ProcessLoop_harness

# Bound on the timeout in MQTT_ProcessLoop. This timeout is bounded because 
# memory saftey can be proven in a single iteration of the MQTT operations.
# Each iteration will try to receive a single packet in its entirey. If the 
# timeout is not reached, then another iteration will be performed unnecessarily
# duplicating the proof.
MQTT_PROCESS_LOOP_TIMEOUT=0
DEFINES += -DMQTT_PROCESS_LOOP_TIMEOUT=$(MQTT_PROCESS_LOOP_TIMEOUT)
INCLUDES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET += MQTT_ProcessLoop.0:2
UNWINDSET += __CPROVER_file_local_mqtt_c_discardPacket.0:2
UNWINDSET += __CPROVER_file_local_mqtt_c_recvExact.0:2
UNWINDSET += __CPROVER_file_local_mqtt_lightweight_c_getRemainingLength.0:5

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/libraries/standard/mqtt/cbmc/sources/mqtt_cbmc_state.c
PROOF_SOURCES += $(SRCDIR)/libraries/standard/mqtt/cbmc/stubs/network_interface_stubs.c
PROOF_SOURCES += $(SRCDIR)/libraries/standard/mqtt/cbmc/stubs/get_time_stub.c
PROOF_SOURCES += $(SRCDIR)/libraries/standard/mqtt/cbmc/stubs/event_callback_stub.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/mqtt.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/mqtt_lightweight.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/mqtt_state.c

include ../Makefile.common

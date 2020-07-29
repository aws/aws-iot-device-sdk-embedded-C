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
# memory saftey can be proven in a only a few iteration of the MQTT operations.
# Each iteration will try to receive a single packet in its entirey. With a time
# out of 2 we can get coverage of the entire function. Another iteration will
# performed unnecessarily duplicating of the proof.
MQTT_RECEIVE_TIMEOUT=3
# Please see libraries/standard/mqtt/cbmc/stubs/network_interface_subs.c for
# more information on MAX_NETWORK_SEND_TRIES.
MAX_NETWORK_SEND_TRIES=3
# Please see libraries/standard/mqtt/cbmc/include/mqtt_config.h for more
# information.
MQTT_STATE_ARRAY_MAX_COUNT=11
DEFINES += -DMQTT_RECEIVE_TIMEOUT=$(MQTT_RECEIVE_TIMEOUT)
DEFINES += -DMAX_NETWORK_SEND_TRIES=$(MAX_NETWORK_SEND_TRIES)
INCLUDES +=

# These functions have their memory saftey proven in other harnesses.
REMOVE_FUNCTION_BODY += MQTT_Ping
REMOVE_FUNCTION_BODY += MQTT_DeserializeAck
REMOVE_FUNCTION_BODY += MQTT_SerializeAck
# REMOVE_FUNCTION_BODY += _CPROVER_file_local_mqtt_c_handleKeepAlive

UNWINDSET += MQTT_ProcessLoop.0:$(MQTT_RECEIVE_TIMEOUT)
UNWINDSET += __CPROVER_file_local_mqtt_c_discardPacket.0:$(MQTT_RECEIVE_TIMEOUT)
UNWINDSET += __CPROVER_file_local_mqtt_c_recvExact.0:$(MQTT_RECEIVE_TIMEOUT)
# Unlike recvExact, sendPacket is not bounded by the timeout. The loop in
# sendPacket will continue until all the bytes are sent or a network error
# occurs. Please see NetworkInterfaceReceiveStub in
# libraries\standard\mqtt\cbmc\stubs\network_interface_stubs.c for more
# information.
UNWINDSET += __CPROVER_file_local_mqtt_c_sendPacket.0:$(MAX_NETWORK_SEND_TRIES)
# The getRemainingLength loop is unwound 5 times because getRemainingLength()
# divides a size_t variable by 128 until it reaches zero to stop the loop.
# log128(SIZE_MAX) = 4.571...
UNWINDSET += __CPROVER_file_local_mqtt_lightweight_c_getRemainingLength.0:5
# These loops will run for the maximum number of publishes pending
# acknowledgements plus one. This value is set in
# libraries/standard/mqtt/cbmc/include/mqtt_config.h.
UNWINDSET += __CPROVER_file_local_mqtt_state_c_addRecord.0:$(MQTT_STATE_ARRAY_MAX_COUNT)
UNWINDSET += __CPROVER_file_local_mqtt_state_c_findInRecord.0:$(MQTT_STATE_ARRAY_MAX_COUNT)

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/libraries/standard/mqtt/cbmc/sources/mqtt_cbmc_state.c
PROOF_SOURCES += $(SRCDIR)/libraries/standard/mqtt/cbmc/stubs/network_interface_stubs.c
PROOF_SOURCES += $(SRCDIR)/libraries/standard/mqtt/cbmc/stubs/get_time_stub.c
PROOF_SOURCES += $(SRCDIR)/libraries/standard/mqtt/cbmc/stubs/event_callback_stub.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/mqtt.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/mqtt_lightweight.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/mqtt_state.c

include ../Makefile.common

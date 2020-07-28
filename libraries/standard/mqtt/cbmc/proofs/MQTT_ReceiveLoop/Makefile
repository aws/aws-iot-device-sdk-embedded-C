# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

HARNESS_ENTRY=harness
HARNESS_FILE=MQTT_ReceiveLoop_harness

# Bound on the timeout in MQTT_ProcessLoop. This timeout is bounded because 
# memory saftey can be proven in a only a few iteration of the MQTT operations.
# Each iteration will try to receive a single packet in its entirety. With a time
# out of 2 we can get coverage of the entire function. Another iteration will 
# performed unnecessarily duplicating of the proof.
MQTT_RECEIVE_TIMEOUT=2
# Please see libraries/standard/mqtt/cbmc/stubs/network_interface_subs.c for
# more information on MAX_NETWORK_SEND_TRIES.
MAX_NETWORK_SEND_TRIES=3
DEFINES += -DMQTT_RECEIVE_TIMEOUT=$(MQTT_RECEIVE_TIMEOUT)
DEFINES += -DMAX_NETWORK_SEND_TRIES=$(MAX_NETWORK_SEND_TRIES)
INCLUDES +=

# These functions have their memory saftey proven in other harnesses.
REMOVE_FUNCTION_BODY += MQTT_Ping
REMOVE_FUNCTION_BODY += MQTT_DeserializeAck
REMOVE_FUNCTION_BODY += MQTT_SerializeAck


# The loops below are unwound once more than the timeout.
UNWINDSET += MQTT_ReceiveLoop.0:3
UNWINDSET += __CPROVER_file_local_mqtt_c_discardPacket.0:3
UNWINDSET += __CPROVER_file_local_mqtt_c_recvExact.0:3
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
# These loops will run for the maximum number of publishes pending acknowledgement.
# This is set in libraries/standard/mqtt/cbmc/include/mqtt_config.h.
UNWINDSET += __CPROVER_file_local_mqtt_state_c_addRecord.0:11
UNWINDSET += __CPROVER_file_local_mqtt_state_c_findInRecord.0:11

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/libraries/standard/mqtt/cbmc/sources/mqtt_cbmc_state.c
PROOF_SOURCES += $(SRCDIR)/libraries/standard/mqtt/cbmc/stubs/network_interface_stubs.c
PROOF_SOURCES += $(SRCDIR)/libraries/standard/mqtt/cbmc/stubs/get_time_stub.c
PROOF_SOURCES += $(SRCDIR)/libraries/standard/mqtt/cbmc/stubs/event_callback_stub.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/mqtt.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/mqtt_lightweight.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/mqtt_state.c

include ../Makefile.common

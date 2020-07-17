HARNESS_ENTRY=harness
HARNESS_FILE=MQTT_GetIncomingPacketTypeAndLength_harness

DEFINES +=
INCLUDES +=
REMOVE_FUNCTION_BODY +=
UNWINDSET += __CPROVER_file_local_mqtt_lightweight_c_getRemainingLength.0:5

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/libraries/standard/mqtt/cbmc/sources/mqtt_cbmc_state.c
PROOF_SOURCES += $(SRCDIR)/libraries/standard/mqtt/cbmc/stubs/network_interface_stubs.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/mqtt_lightweight.c

include ../Makefile.common

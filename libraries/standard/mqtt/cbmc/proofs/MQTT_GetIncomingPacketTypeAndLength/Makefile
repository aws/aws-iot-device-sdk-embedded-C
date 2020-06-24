HARNESS_ENTRY=harness
HARNESS_FILE=MQTT_GetIncomingPacketTypeAndLength_harness

DEFINES +=
INCLUDES += $(PROOFDIR)/../../include
REMOVE_FUNCTION_BODY +=
UNWINDSET += getRemainingLength.0:5

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(PROOFDIR)/../../sources/mqtt_cbmc_state.c
PROOF_SOURCES += $(PROOFDIR)/../../stubs/NetworkInterfaceReceiveStub.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/mqtt_lightweight.c

include ../Makefile.common

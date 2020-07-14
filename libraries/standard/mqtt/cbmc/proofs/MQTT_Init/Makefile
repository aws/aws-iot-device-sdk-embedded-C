HARNESS_ENTRY=harness
HARNESS_FILE=MQTT_Init_harness

DEFINES +=
INCLUDES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET +=

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(PROOFDIR)/../../sources/mqtt_cbmc_state.c
PROJECT_SOURCES += $(SRCDIR)/libraries/standard/mqtt/src/mqtt.c

include ../Makefile.common

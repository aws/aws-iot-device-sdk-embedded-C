HARNESS_ENTRY=harness
HARNESS_FILE=HTTPClient_AddHeader_harness

DEFINES +=
INCLUDES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET += strncmp.0:5

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c 
PROOF_SOURCES += $(PROOFDIR)/../../sources/http_cbmc_state.c

PROJECT_SOURCES += $(SRCDIR)/libraries/standard/http/src/http_client.c

include ../Makefile.common

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

HARNESS_ENTRY=harness
HARNESS_FILE=HTTPClient_AddRangeHeader_harness

DEFINES +=
INCLUDES +=

REMOVE_FUNCTION_BODY +=
# Maximum value of a 32 bit signed integer is 2,147,483,647, which is 10 digits.
UNWINDSET += strncmp.0:5
UNWINDSET += __CPROVER_file_local_http_client_c_convertInt32ToAscii.0:11
UNWINDSET += __CPROVER_file_local_http_client_c_convertInt32ToAscii.1:11

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(PROOFDIR)/../../sources/http_cbmc_state.c

PROJECT_SOURCES += $(SRCDIR)/libraries/standard/http/src/http_client.c

include ../Makefile.common

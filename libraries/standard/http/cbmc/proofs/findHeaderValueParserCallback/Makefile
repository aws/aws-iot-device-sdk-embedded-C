# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

HARNESS_ENTRY=harness
HARNESS_FILE=findHeaderValueParserCallback_harness

DEFINES +=
INCLUDES +=

REMOVE_FUNCTION_BODY +=
UNWINDSET +=

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(PROOFDIR)/../../sources/http_cbmc_state.c

PROJECT_SOURCES += $(SRCDIR)/libraries/standard/http/src/http_client.c

include ../Makefile.common

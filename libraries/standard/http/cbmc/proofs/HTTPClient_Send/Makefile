# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

HARNESS_ENTRY=harness
HARNESS_FILE=HTTPClient_Send_harness

DEFINES +=
INCLUDES +=

REMOVE_FUNCTION_BODY += httpParserOnHeadersCompleteCallback
REMOVE_FUNCTION_BODY += httpParserOnMessageBeginCallback
REMOVE_FUNCTION_BODY += httpParserOnMessageCompleteCallback
UNWINDSET += convertInt32ToAscii.0:11 convertInt32ToAscii.1:11 strncmp.0:5 sendHttpData.0:5 receiveAndParseHttpResponse.0:3

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(PROOFDIR)/../../sources/http_cbmc_state.c

PROJECT_SOURCES += $(SRCDIR)/libraries/standard/http/src/http_client.c

include ../Makefile.common

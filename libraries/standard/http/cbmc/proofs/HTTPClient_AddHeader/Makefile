# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

HARNESS_ENTRY=harness
HARNESS_FILE=HTTPClient_AddHeader_harness

DEFINES +=
INCLUDES +=

REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_findHeaderFieldParserCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_findHeaderValueParserCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_httpParserOnBodyCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_httpParserOnHeaderFieldCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_httpParserOnHeaderValueCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_httpParserOnStatusCallback

REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_httpParserOnHeadersCompleteCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_httpParserOnMessageBeginCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_httpParserOnMessageCompleteCallback

REMOVE_FUNCTION_BODY += memcpy

UNWINDSET += strncmp.0:5

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c 
PROOF_SOURCES += $(PROOFDIR)/../../sources/http_cbmc_state.c
PROOF_SOURCES += $(PROOFDIR)/../../stubs/memcpy.c

PROJECT_SOURCES += $(SRCDIR)/libraries/standard/http/src/http_client.c

include ../Makefile.common

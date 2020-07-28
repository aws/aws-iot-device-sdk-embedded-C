# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

HARNESS_ENTRY=harness
HARNESS_FILE=HTTPClient_Send_harness

DEFINES +=
INCLUDES +=

# We remove these function bodies so that they aren't categorized as possible
# function pointer targets, leading to faster execution time.
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_findHeaderFieldParserCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_findHeaderValueParserCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_httpParserOnBodyCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_httpParserOnHeaderFieldCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_httpParserOnHeaderValueCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_httpParserOnStatusCallback

REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_httpParserOnHeadersCompleteCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_httpParserOnMessageBeginCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_httpParserOnMessageCompleteCallback

UNWINDSET += __CPROVER_file_local_http_client_c_convertInt32ToAscii.0:11
UNWINDSET += __CPROVER_file_local_http_client_c_convertInt32ToAscii.1:11
UNWINDSET += __CPROVER_file_local_http_client_c_receiveAndParseHttpResponse.0:10
UNWINDSET += __CPROVER_file_local_http_client_c_sendHttpData.0:10
UNWINDSET += strncmp.0:5

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(PROOFDIR)/../../sources/http_cbmc_state.c
PROOF_SOURCES += $(PROOFDIR)/../../stubs/HTTPClient_Send_http_parser_execute.c
PROOF_SOURCES += $(PROOFDIR)/../../stubs/transport_interface_stubs.c

PROJECT_SOURCES += $(SRCDIR)/libraries/standard/http/src/http_client.c

include ../Makefile.common

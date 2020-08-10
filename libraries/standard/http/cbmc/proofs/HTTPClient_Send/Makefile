#
# Copyright (C) 2020 Amazon.com, Inc. or its affiliates.  All Rights Reserved.
#
# Permission is hereby granted, free of charge, to any person obtaining a copy of
# this software and associated documentation files (the "Software"), to deal in
# the Software without restriction, including without limitation the rights to
# use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
# the Software, and to permit persons to whom the Software is furnished to do so,
# subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
# FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR
# COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER
# IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
# CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
#

HARNESS_ENTRY=harness
HARNESS_FILE=HTTPClient_Send_harness

DEFINES +=
INCLUDES +=

# We remove these function bodies so that they aren't categorized as possible
# function pointer targets, leading to faster execution time.
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_findHeaderFieldParserCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_findHeaderValueParserCallback
# The memory safety of the http-parser callbacks are proven separately. The
# proofs for the functions below must have assumptions that are satisfied by the
# calling context in HTTPClient_Send.
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_httpParserOnBodyCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_httpParserOnHeaderFieldCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_httpParserOnHeaderValueCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_httpParserOnStatusCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_httpParserOnHeadersCompleteCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_httpParserOnMessageBeginCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_httpParserOnMessageCompleteCallback

# Remove any unused functions for http parser
REMOVE_FUNCTION_BODY += http_parser_init
REMOVE_FUNCTION_BODY += http_parser_set_max_header_size
REMOVE_FUNCTION_BODY += http_parser_settings_init

# There is a total of 10 digits in INT32_MAX. These loops are unwound once more
# than the total possible iterations in the int32_t to ASCII converation.
UNWINDSET += __CPROVER_file_local_http_client_c_convertInt32ToAscii.0:11
UNWINDSET += __CPROVER_file_local_http_client_c_convertInt32ToAscii.1:11
UNWINDSET += __CPROVER_file_local_http_client_c_receiveAndParseHttpResponse.0:10
UNWINDSET += __CPROVER_file_local_http_client_c_sendHttpData.0:10
UNWINDSET += strncmp.0:5

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/libraries/standard/http/cbmc/sources/http_cbmc_state.c
PROOF_SOURCES += $(SRCDIR)/libraries/standard/http/cbmc/stubs/HTTPClient_Send_http_parser_execute.c
PROOF_SOURCES += $(SRCDIR)/libraries/standard/http/cbmc/stubs/transport_interface_stubs.c

PROJECT_SOURCES += $(SRCDIR)/libraries/standard/http/src/http_client.c

include ../Makefile.common

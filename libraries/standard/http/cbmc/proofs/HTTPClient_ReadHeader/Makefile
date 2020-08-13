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
HARNESS_FILE=HTTPClient_ReadHeader_harness

DEFINES +=
INCLUDES +=

# The memory safety of the http-parser callbacks are proven separately.
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_findHeaderFieldParserCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_findHeaderValueParserCallback
REMOVE_FUNCTION_BODY += __CPROVER_file_local_http_client_c_findHeaderOnHeaderCompleteCallback

# Remove any unused functions for http parser
REMOVE_FUNCTION_BODY += http_parser_init
REMOVE_FUNCTION_BODY += http_parser_set_max_header_size
REMOVE_FUNCTION_BODY += http_parser_settings_init

UNWINDSET +=

PROOF_SOURCES += $(PROOFDIR)/$(HARNESS_FILE).c
PROOF_SOURCES += $(SRCDIR)/libraries/standard/http/cbmc/sources/http_cbmc_state.c
PROOF_SOURCES += $(SRCDIR)/libraries/standard/http/cbmc/stubs/HTTPClient_ReadHeader_http_parser_execute.c

PROJECT_SOURCES += $(SRCDIR)/libraries/standard/http/src/http_client.c


include ../Makefile.common

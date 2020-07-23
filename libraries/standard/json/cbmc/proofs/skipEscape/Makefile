# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

HARNESS_FILE=skipEscape_harness

CBMC_MAX_BUFSIZE=14

UNWINDSET += skipEscape.0:$(CBMC_MAX_BUFSIZE)
UNWINDSET += skipHexEscape.0:$(CBMC_MAX_BUFSIZE)

include ../Makefile-json.common

$(PROOFDIR)/json.c: $(SRCDIR)/libraries/standard/json/src/json.c
	sed 's/^static //' $< > $@

# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

HARNESS_FILE=JSON_Validate_harness

CBMC_MAX_BUFSIZE=14

UNWINDSET += JSON_Validate.0:$(CBMC_MAX_BUFSIZE)

include ../Makefile-json.common

$(PROOFDIR)/json.c: $(SRCDIR)/libraries/standard/json/src/json.c
	sed -E '1s/^/#include "glue.h" /; s/^static //; s/(bool_|JSONStatus_t|void) skip(AnyLiteral|Collection|Number|Space|String)\b/&_/' $< > $@

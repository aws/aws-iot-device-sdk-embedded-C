# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

HARNESS_FILE=skipCollection_harness

CBMC_MAX_BUFSIZE=8

DEFINES += -DJSON_MAX_DEPTH='( $(CBMC_MAX_BUFSIZE) - 2 )'

REMOVE_FUNCTION_BODY += strnEq
UNWINDSET += skipCollection.0:$(CBMC_MAX_BUFSIZE)
UNWINDSET += skipArrayScalars.0:$(CBMC_MAX_BUFSIZE)
UNWINDSET += skipObjectScalars.0:$(CBMC_MAX_BUFSIZE)

include ../Makefile-json.common

$(PROOFDIR)/json.c: $(SRCDIR)/libraries/standard/json/src/json.c
	sed -E '1s/^/#include "glue.h" /; s/^static //; s/(bool_|void) skip(AnyLiteral|Number|Space|SpaceAndComma|String)\b/&_/' $< > $@

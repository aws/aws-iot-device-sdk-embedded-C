# Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

HARNESS_FILE=JSON_Search_harness

CBMC_MAX_BUFSIZE=8
CBMC_MAX_QUERYKEYLENGTH=10

REMOVE_FUNCTION_BODY += strnEq
UNWINDSET += JSON_Search.0:$(CBMC_MAX_QUERYKEYLENGTH)
UNWINDSET += JSON_Search.1:$(CBMC_MAX_QUERYKEYLENGTH)
UNWINDSET += search.0:$(CBMC_MAX_BUFSIZE)
UNWINDSET += nextKeyValuePair.0:$(CBMC_MAX_BUFSIZE)

PROOF_SOURCES += $(PROOF_STUB)/skipGeneric.c
PROOF_SOURCES += $(PROOF_STUB)/skipAnyScalar.c
PROOF_SOURCES += $(PROOF_STUB)/skipCollection.c
PROOF_SOURCES += $(PROOF_STUB)/skipSpace.c
PROOF_SOURCES += $(PROOF_STUB)/skipSpaceAndComma.c
PROOF_SOURCES += $(PROOF_STUB)/skipString.c

include ../Makefile-json.common

$(PROOFDIR)/json.c: $(SRCDIR)/libraries/standard/json/src/json.c
	sed -E '1s/^/#include "json_annex.h" /; s/^static //; s/(bool_|void|JSONStatus_t) skip(AnyScalar|Collection|Space|SpaceAndComma|String)\b/&_/' $< > $@

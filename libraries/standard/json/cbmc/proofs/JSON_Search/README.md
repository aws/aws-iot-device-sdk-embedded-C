JSON_Search proof
==============

This directory contains a memory safety proof for JSON_Search.

The proof runs in 15 minutes on a t3.medium.  It provides complete coverage of:
* JSON_Search()
* nextKeyValuePair()
* search()

For this proof, the following functions are replaced with mocks.
These functions have separate proofs.
* skipAnyScalar()
* skipCollection()
* skipSpace()
* skipSpaceAndComma()
* skipString()

To run the proof.
* Add cbmc, goto-cc, goto-instrument, goto-analyzer, and cbmc-viewer
  to your path.
* Run "make".
* Open html/index.html in a web browser.

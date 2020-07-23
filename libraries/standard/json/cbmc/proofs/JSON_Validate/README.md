JSON_Validate proof
==============

This directory contains a memory safety proof for JSON_Validate.

For this proof, the following functions are replaced with mocks.
These functions have separate proofs.
* skipAnyLiteral()
* skipCollection()
* skipNumber()
* skipString()

To run the proof.
* Add cbmc, goto-cc, goto-instrument, goto-analyzer, and cbmc-viewer
  to your path.
* Run "make".
* Open html/index.html in a web browser.

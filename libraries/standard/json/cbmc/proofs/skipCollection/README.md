skipCollection proof
==============

This directory contains a memory safety proof for skipCollection.

This function requires non-NULL arguments and a buffer with length > 0.
The proof runs in 5 minutes on a t3.medium.  It provides complete coverage of:
* skipAnyScalar()
* skipArrayScalars()
* skipCollection()
* skipObjectScalars()
* skipScalars()

For this proof, the following functions are replaced with mocks.
These functions have separate proofs.
* skipAnyLiteral()
* skipNumber()
* skipSpace()
* skipSpaceAndComma()
* skipString()

To run the proof.
* Add cbmc, goto-cc, goto-instrument, goto-analyzer, and cbmc-viewer
  to your path.
* Run "make".
* Open html/index.html in a web browser.

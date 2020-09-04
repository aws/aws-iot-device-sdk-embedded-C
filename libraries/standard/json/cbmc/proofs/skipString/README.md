skipString proof
==============

This directory contains a memory safety proof for skipString.

This function requires non-NULL arguments and a buffer with length > 0.
The proof runs in a few seconds and provides complete coverage of
skipString().

For this proof, skipEscape() and skipUTF8() are replaced with mocks.
These functions have separate proofs.

To run the proof.
* Add cbmc, goto-cc, goto-instrument, goto-analyzer, and cbmc-viewer
  to your path.
* Run "make".
* Open html/index.html in a web browser.

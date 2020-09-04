skipEscape proof
==============

This directory contains a memory safety proof for skipEscape.

This function requires non-NULL arguments and a buffer with length > 0.
The proof runs in a few seconds and provides complete coverage of:
* hexToInt()
* skipEscape()
* skipHexEscape()

To run the proof.
* Add cbmc, goto-cc, goto-instrument, goto-analyzer, and cbmc-viewer
  to your path.
* Run "make".
* Open html/index.html in a web browser.

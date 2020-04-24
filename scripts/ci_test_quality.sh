#!/bin/sh

# Travis CI uses this script to test code quality.

# Exit on any nonzero return code.
set -e

# Get the list of files to check. Only check library files and exclude tests.
# Run complexity with a threshold of 8.
find ../libraries/ \( -name '*.c' ! -name *tests*.c \) -type f | \
xargs complexity --scores --threshold=8 #--horrid-threshold=8

#!/bin/sh

# Travis CI uses this script to set up the test environment on macOS.

# Set compiler options for macOS. Silence field initializer warnings.
export COMPILER_OPTIONS="-Wall -Wextra -Wno-missing-field-initializers"

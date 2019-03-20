#!/bin/sh

# Travis CI uses this script to run the general test scripts.
# This script is invoked from the build directory, so all helper scripts have a relative
# path from the build directory.

# Exit on any nonzero return code.
set -e

# Run test coverage script only for commit builds.
if [ "$TRAVIS_PULL_REQUEST" = "false" ]; then
    echo "Nothing to do right now."
fi

#!/bin/sh

# Travis CI uses this script to set up the test environment on macOS.

# Install and start Mosquitto for MQTT pull request builds.
if [ "$TRAVIS_PULL_REQUEST" != "false" ]; then
    brew install mosquitto
    brew services start mosquitto
fi

# Set compiler options for macOS. Silence field initializer warnings.
export COMPILER_OPTIONS="-Wall -Wextra -Wno-missing-field-initializers"

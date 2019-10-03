#!/bin/sh

# Travis CI uses this script to set up the test environment on macOS.

# Homebrew updates take a while on CI.
export HOMEBREW_NO_AUTO_UPDATE=1

# Install and start Mosquitto for MQTT pull request builds.
if [ "$TRAVIS_PULL_REQUEST" != "false" ] && [ "$RUN_TEST" = "mqtt" ]; then
    brew install mosquitto
    brew services start mosquitto
fi

# Set compiler options for macOS. Silence field initializer warnings.
export COMPILER_OPTIONS="-Wall -Wextra -Wno-missing-field-initializers"

#!/bin/sh

# Travis CI uses this script to set up the test environment on Linux.

# Update repositories.
sudo apt-get update

# Install OpenSSL if needed.
if [ "$NETWORK_STACK" = "openssl" ]; then
    sudo apt-get install -y libssl-dev;
fi

# Set up for pull request builds.
if [ "$TRAVIS_PULL_REQUEST" != "false" ]; then
    # Install Mosquitto for MQTT pull request builds.
    if [ "$RUN_TEST" = "mqtt" ]; then
        sudo apt-get install -y mosquitto;
    fi

    # Install graphviz for documentation builds.
    if [ "$RUN_TEST" = "doc" ]; then
        sudo apt-get install -y graphviz;
    fi

    # Install util-linux and spell for spelling checks.
    if [ "$RUN_TEST" = "spelling" ]; then
        sudo apt-get -y install util-linux    # for gnu getopt
        sudo apt-get -y install spell         # for spell
    fi

    # Install complexity for complexity checks.
    if [ "$RUN_TEST" = "quality" ]; then
        sudo apt-get -y install complexity
    fi
# Set up for coverage builds.
else
    # Install dependencies for Jobs tests.
    # Coverage needs these too since it runs the Jobs tests.
    if [ "$RUN_TEST" = "jobs" ] || [ "$RUN_TEST" = "coverage" ]; then
        sudo apt-get install -y python3-setuptools python3-pip athena-jot;
        pip3 install --user wheel;
        pip3 install --user awscli;
    fi
    
    # Install dependencies for Provisioning tests.
    if [ "$RUN_TEST" = "provisioning" ]; then
        # Install pip for awscli, and install a json parser utility, jq and its dependencies.
        sudo apt-get install -y python3-setuptools python3-pip jq;
        pip3 install --user awscli;
    fi

    # Install dependencies for coverage builds.
    if [ "$RUN_TEST" = "coverage" ]; then
        sudo apt-get install -y lcov;
    fi
fi

# Set default compiler options for Linux. Individual test scripts may override this.
export COMPILER_OPTIONS="-Wall -Wextra -fsanitize=thread"

#!/bin/bash
# This script should detect the OS, then download and run the relevant installer for that OS
set -e

unameOut="$(uname -s)"
case "${unameOut}" in
    Linux*)     machine=Linux;;
    Darwin*)    machine=Mac;;
    CYGWIN*)    machine=Cygwin;;
    MINGW*)     machine=MinGw;;
    *)          machine="UNKNOWN:${unameOut}"
esac

mac_func() {
    echo "Installing Tunnelmole for Mac OS X"
    curl -O https://tunnelmole.com/sh/install-mac.sh && bash install-mac.sh
}

linux_func() {
    echo "Installing Tunnelmole for Linux"
    curl -O https://tunnelmole.com/sh/install-linux.sh && bash install-linux.sh
}

if [ "${machine}" == "Linux" ]; then
    linux_func
elif [ "${machine}" == "Mac" ]; then
    mac_func
fi

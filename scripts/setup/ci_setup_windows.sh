#!/bin/sh

# Travis CI uses this script to set up the test environment on Windows.

# Location of MSBuild.exe in the test environment
MSBUILD_PATH="/c/Program Files (x86)/Microsoft Visual Studio/2017/BuildTools/MSBuild/15.0/Bin"
export PATH=$PATH:$MSBUILD_PATH

# Use default compiler options for windows.
export COMPILER_OPTIONS=""

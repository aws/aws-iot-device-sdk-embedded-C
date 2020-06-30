#!/bin/bash

function usage {
    cat <<USAGE
Usage: $0 [files...]

A script to run complexity in CI. This is needed to avoid issues with
exit codes.

USAGE
}

if [ $# -eq 0 ] ; then
    usage
    exit 1
fi

complexity --scores --threshold=9 --horrid-threshold=8 $@

# When no functions are scored (i.e. below the threshold) complexity has an
# exit code of 5. The "horrid-threshold" value will cause the program to exit
# with a different code. Other non-zero values indicate a failure of some type.
if [ "$?" = "5" ] ; then
    exit 0
else
    exit $?
fi

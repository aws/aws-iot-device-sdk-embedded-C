#!/bin/bash

function usage {
    cat <<USAGE
Usage: $0 [files...]

An script to run complexity in CI. This is needed to avoid issues with
exit codes.

USAGE
}

if [ $# -eq 0 ] ; then
    usage
    exit 1
fi

complexity --scores --threshold=9 --horrid-threshold=8 $@

if [ "$?" = "5" ] ; then
    exit 0
else
    exit $?
fi

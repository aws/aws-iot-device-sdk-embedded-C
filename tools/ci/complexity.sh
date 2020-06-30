#!/bin/bash

function usage {
    cat <<USAGE
Usage: $0 [files...]

A script to run complexity in CI. This is needed to avoid issues with
exit codes.

USAGE
}

# If there are no arguments, we get a cryptic message from complexity.
if [ $# -eq 0 ] ; then
    usage
    exit 1
fi


# Explicitly check that complexity exists.
which complexity > /dev/null
if [ $? -ne 0 ] ; then
    echo "complexity not found"
    exit 1
fi

# Run complexity. The `--threshold` option prints functions with a cylcomatic
# complexity greater than or equal to the value. The `--horrid-threshold` makes
# the program exit with a non-zero exit code if a function is strictly greater
# than the value.
complexity --scores --threshold=9 --horrid-threshold=8 $@

# When no functions are scored (i.e. below the threshold) complexity has an
# exit code of 5. The "horrid-threshold" value will cause the program to exit
# with a different code. Other non-zero values indicate a failure of some type.
if [ $? -eq 5 ] ; then
    exit 0
else
    exit $?
fi

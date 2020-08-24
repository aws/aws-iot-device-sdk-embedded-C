#!/bin/bash
#
# Extract comments from C/C++ files
#
set -e
set -f

function usage () {
    echo "Extract comments from C/C++ files"
    echo ""
    echo "usage: "${0##*/}" file-list"
    exit 1
}

if [ $# -lt 1 ]
then
	usage $0
fi

if [ $1 = "-h" ] || [ $1 == "--help" ]
then
    usage $0
fi

while test $# -gt 0
do
    if [ ! -f $1 ]
    then
        echo $0": '"$1"' is not a file." 2>/dev/null
        exit 1
    fi
#
# Extract all words from C/C++ language comments; add line
# numbers to aid in searching.
#
# NOTE: This has some limitations.  For example, it prints
# non-comment text at the beginning of a comment line.
#
    nl -ba $1 | awk '/\/\// {print $0}; /\/\*/ {comment=1}; {if(comment) print $0}; /\*\// {comment=0}'
    shift
done

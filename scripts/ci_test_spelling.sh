#!/bin/sh

# Check arguments when running locally. If running on CI, install dependencies.
if [ -z "$TRAVIS_PULL_REQUEST" ]; then
    if [ $# -ne 1 ]; then
        echo "Usage: ${0##*/} sdk_root_directory"
        exit 1
    fi

    # Change to SDK root directory.
    cd $1
else
    set -ev
    cd ..                                 # change to SDK root directory
fi
PATH=$PATH:$PWD/scripts

# Check for find-unknown-comment-words.
command -v find-unknown-comment-words > /dev/null || { echo "Can't find spellcheck script, exiting."; exit 1; }

STATUS=
#
# Check spelling in all directories with a 'lexicon.txt' file.
#
for lexfile in `find . -name lexicon.txt`
do
    dir=${lexfile%/lexicon.txt}
    find-unknown-comment-words --directory $dir
    if [ $? -ne "0" ]
    then
        STATUS=1
    fi
done

if [ $STATUS"" = "1" ]
then
    exit 1
fi

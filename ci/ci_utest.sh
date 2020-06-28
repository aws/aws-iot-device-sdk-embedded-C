#!/bin/bash

rm -fr build/
mkdir build

cmake -S . -B build/ -DBUILD_TESTS=1 -G "Unix Makefiles"

# Gather all the make targets and select unit tests. They have utest in the name.
make help -C build/ | grep utest | tr -d '. ' | xargs make -C build/

for t in build/bin/tests/*
do
    echo "= $( basename $t ) ="
    ./$t

done


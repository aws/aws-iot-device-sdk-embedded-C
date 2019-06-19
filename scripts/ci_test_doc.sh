#!/bin/sh

# Check arguments when running locally. If running on CI, install the correct
# version of doxygen.
if [ -z "$TRAVIS_PULL_REQUEST" ]; then
    if [ $# -ne 1 ]; then
        echo "Usage: ./generate_doc.sh sdk_root_directory"
        exit 1
    fi

    # Change to SDK root directory.
    cd $1
else
    set -ev
    wget -O doxygen_source.tar.gz https://downloads.sourceforge.net/project/doxygen/rel-1.8.14/doxygen-1.8.14.src.tar.gz
    tar xf doxygen_source.tar.gz
    cmake doxygen-1.8.14 -DCMAKE_CXX_FLAGS="-w"
    make -j2
    sudo make install
    cd ..
fi

# Check for doxygen.
command -v doxygen > /dev/null || { echo "Doxygen not found. Exiting."; exit 1; }

# Create tag directory if needed.
mkdir -p doc/tag

# Doxygen must be run twice: once to generate tags and once more to link tags.
i=0; while [ $i -le 1 ]; do
    # Run for each library config file.
    for file in doc/config/*; do
        # Ignore directories.
        if [ -d $file ]; then
            continue
        fi

        # Ignore xml files.
        if [ ${file##*.} = "xml" ]; then
            continue
        fi

        # Ignore the common configuration file.
        if [ $file = "doc/config/common" ]; then
            continue
        fi

        # Generate Doxygen tags first. Once tags are generated, generate documentation.
        if [ $i -eq 0 ]; then
            echo "Generating Doxygen tags for $file..."
            doxygen $file 2> /dev/null
        else
            echo "Generating documentation for $file..."

            # Redirect errors to file when running under Travis CI.
            if [ -z "$TRAVIS" ]; then
                doxygen $file
            else
                doxygen $file 2>>doxygen_warnings.txt
            fi
        fi
    done

    i=$(($i+1));
done

echo "Documentation written to doc/output"

# Print any doxygen errors or warnings and exit with a nonzero value.
if [ -s doxygen_warnings.txt ]; then
    cat doxygen_warnings.txt
    exit 1
fi

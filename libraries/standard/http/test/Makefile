# the path to be indexed (default: ..)
# Directory indexing includes subdirectories.
SOURCE = ../src

# arguments given to the compiler (default: see the included file)
#CFLAGS = std=c99 -Wall -fprofile-arcs -ftest-coverage -O0 -ggdb

# include directories given to the compiler (default: none)
INCLUDE = ../include

# the default goal (default: help)
# Set to build or test as desired.
.DEFAULT_GOAL := test

# names of unit test programs
# Values based on test source file names will be dynamically added.
#TESTS = 

# functions to dump into separate source files
# Values based on test source file names will be dynamically added.
#FUNCTIONS = a_private_func

# Changes to the above variables should remain above this include.
include Mock4thewin.mk

# additional dependencies for all tests
$(TESTS): common.h

# additional dependency for a specific test
#api_func.c: a_private_func.c
HTTPClient_AddHeader.c: _addHeader.c _isNullParam.c

CSDK_ROOT = ../../../..

# the path to be indexed (default: ..)
# Directory indexing includes subdirectories.
SOURCE = ../src

# Show extra warnings.
CFLAGS += -Wextra

# arguments given to the compiler (default: see the included file)
#CFLAGS = std=c99 -Wall -fprofile-arcs -ftest-coverage -O0 -ggdb

# include directories given to the compiler (default: none)
INCLUDE = . \
		  ../include \
		  ../src \
		  $(CSDK_ROOT)/platform/include \
		  ../../utilities/include

# the default goal (default: help)
# Set to build or test as desired.
.DEFAULT_GOAL := test

# names of unit test programs
# Values based on test source file names will be dynamically added.
#TESTS = 

# functions to dump into separate source files
# Values based on test source file names will be dynamically added.
FUNCTIONS = _convertInt32ToAscii \
			_addHeader \
            _sendHttpHeaders \
			_sendHttpBody \
			_receiveHttpResponse \
			_receiveAndParseHttpResponse \
			_HTTPClient_InitializeParsingContext \
			_HTTPClient_ParseResponse \
			_getFinalResponseStatus

# Changes to the above variables should remain above this include.
include Mock4thewin.mk

# additional dependencies for all tests
$(TESTS): $(CSDK_ROOT)/platform/posix/iot_clock_posix.o $(CSDK_ROOT)/platform/posix/iot_logging.o

# additional dependency for a specific test
HTTPClient_AddHeader.c: _addHeader.c
HTTPClient_AddRangeHeader.c: _addHeader.c _convertInt32ToAscii.c
HTTPClient_Send.c: _sendHttpHeaders.c \
				   _sendHttpBody.c \
				   _receiveHttpResponse.c \
				   _receiveAndParseHttpResponse.c \
				   _HTTPClient_InitializeParsingContext.c \
				   _HTTPClient_ParseResponse.c \
				   _getFinalResponseStatus.c \

# additional header dependencies for all tests
COMMON = common.h

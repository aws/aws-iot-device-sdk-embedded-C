CSDK_ROOT = ../../../..

# the path to be indexed (default: ..)
# Directory indexing includes subdirectories.
SOURCE = ../src

# Show extra warnings.
CFLAGS += -Wextra -O0 -ggdb

# arguments given to the compiler (default: see the included file)
#CFLAGS = std=c99 -Wall -fprofile-arcs -ftest-coverage -O0 -ggdb

# include directories given to the compiler (default: none)
INCLUDE = . \
		  ../include \
		  ../src \
		  $(CSDK_ROOT)/platform/include \
		  ../../utilities/include \
		  ../third_party

# the default goal (default: help)
# Set to build or test as desired.
.DEFAULT_GOAL := test

# names of unit test programs
# Values based on test source file names will be dynamically added.
#TESTS = 

# functions to dump into separate source files
# Values based on test source file names will be dynamically added.
FUNCTIONS = addHeader \
			writeRequestLine \
			convertInt32ToAscii \
            sendHttpHeaders \
			sendHttpBody \
			receiveHttpResponse \
			receiveAndParseHttpResponse \
			HTTPClient_InitializeParsingContext \
			HTTPClient_ParseResponse \
			getFinalResponseStatus \
			HTTPClient_strerror \
			findHeaderFieldParserCallback \
			findHeaderValueParserCallback \
			findHeaderOnHeaderCompleteCallback \
			findHeaderInResponse 

# Changes to the above variables should remain above this include.
include Mock4thewin.mk

# additional dependencies for all tests
$(TESTS): $(CSDK_ROOT)/platform/posix/iot_clock_posix.o $(CSDK_ROOT)/platform/posix/iot_logging.o

# additional dependency for a specific test
HTTPClient_AddHeader.c: addHeader.c
HTTPClient_AddRangeHeader.c: addHeader.c convertInt32ToAscii.c
HTTPClient_Send.c: sendHttpHeaders.c \
				   sendHttpBody.c \
				   receiveHttpResponse.c \
				   receiveAndParseHttpResponse.c \
				   HTTPClient_InitializeParsingContext.c \
				   HTTPClient_ParseResponse.c \
				   getFinalResponseStatus.c
HTTPClient_InitializeRequestHeaders.c: writeRequestLine.c addHeader.c
HTTPClient_ReadHeader.c: HTTPClient_strerror.c \
						 findHeaderFieldParserCallback.c \
						 findHeaderValueParserCallback.c \
						 findHeaderOnHeaderCompleteCallback.c \
						 findHeaderInResponse.c 

# additional header dependencies for all tests
COMMON = common.h

CC = gcc

CSDK_ROOT = ../../..

INCLUDE_DIRS = -I . \
               -I $(CSDK_ROOT)/libraries/standard/http/include \
			   -I $(CSDK_ROOT)/platform/include \
			   -I $(CSDK_ROOT)/libraries/standard/utilities/include

SRC_FILES = http_demo_plaintext.c \
            $(shell find $(CSDK_ROOT)/libraries/standard/http/src -name '*.c') \
			$(CSDK_ROOT)/platform/posix/iot_clock_posix.o \
			$(CSDK_ROOT)/platform/posix/iot_logging.o

FLAGS = -g -O0 -Wall -Wextra -Wpedantic -fprofile-arcs

all:
	$(CC) $(FLAGS) $(INCLUDE_DIRS) $(SRC_FILES) -o http_demo_plaintext

clean:
	rm http_demo_plaintext

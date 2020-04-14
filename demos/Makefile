CC = clang

INCLUDE_DIRS = -I . \
               -I ../libraries/standard/common/include \
               -I ../libraries/standard/mqtt/include

SRC_FILES = $(shell find . -name '*.c') \
            $(shell find ../libraries/standard/mqtt/src -name '*.c')

FLAGS = -g -O0 -Weverything -Wno-padded

all:
	$(CC) $(FLAGS) $(INCLUDE_DIRS) $(SRC_FILES) -o mqtt_demo

clean:
	rm mqtt_demo

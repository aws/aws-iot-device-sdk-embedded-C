CC = gcc

INCLUDE_DIRS = -I ../libraries/standard/mqtt/include \
               -I ../platform/include \
               -I mqtt/mqtt_demo_plaintext

SRC_FILES = $(shell find mqtt/mqtt_demo_plaintext -name '*.c') \
            $(shell find ../libraries/standard/mqtt/src -name '*.c')

FLAGS = -g -O0 -Wall -Wextra -Wpedantic

all:
	$(CC) $(FLAGS) $(INCLUDE_DIRS) $(SRC_FILES) -o mqtt_demo

clean:
	rm mqtt_demo

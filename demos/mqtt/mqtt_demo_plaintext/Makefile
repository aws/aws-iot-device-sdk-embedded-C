CC = gcc

INCLUDE_DIRS = -I . \
               -I ../../../libraries/standard/mqtt/include

SRC_FILES = mqtt_demo_plaintext.c \
            $(shell find ../../../libraries/standard/mqtt/src -name '*.c')

FLAGS = -g -O0 -Wall -Wextra -Wpedantic

all:
	$(CC) $(FLAGS) $(INCLUDE_DIRS) $(SRC_FILES) -o mqtt_demo_plaintext

clean:
	rm mqtt_demo

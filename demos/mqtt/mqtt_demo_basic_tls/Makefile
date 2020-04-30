CC = gcc

INCLUDE_DIRS = -I . \
               -I ../../../libraries/standard/mqtt/include

SRC_FILES = mqtt_demo_basic_tls.c \
            $(shell find ../../../libraries/standard/mqtt/src -name '*.c')

FLAGS = -g -O0 -Wall -Wextra -Wpedantic
LINK_FLAGS = -lssl -lcrypto

all:
	$(CC) $(FLAGS) $(INCLUDE_DIRS) $(SRC_FILES) -o mqtt_demo_basic_tls $(LINK_FLAGS)

clean:
	rm mqtt_demo_basic_tls

ENTRY=IotMqtt_Init

ABSTRACTIONS += --remove-function-body IotLog_Generic
ABSTRACTIONS += --remove-function-body Iot_EnterCritical
ABSTRACTIONS += --remove-function-body Iot_ExitCritical

OBJS += $(ENTRY)_harness.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_api.goto

UNWINDING += --unwind 1

default: report

# Use the generic implementations of atomic operations.
# Using the gcc atomic intrinsics causes coverage computation to fail.
# Define the generic flag here, and replace *_gcc.h with *_generic.h below.
DEF += -DIOT_ATOMIC_GENERIC=1

install_atomic:
	mv $(MQTT)/ports/common/include/atomic/iot_atomic_gcc.h $(MQTT)/ports/common/include/atomic/iot_atomic_gcc_disable.h
	cp $(MQTT)/ports/common/include/atomic/iot_atomic_generic.h \
	   $(MQTT)/ports/common/include/atomic/iot_atomic_gcc.h

uninstall_atomic:
	rm $(MQTT)/ports/common/include/atomic/iot_atomic_gcc.h \
	mv $(MQTT)/ports/common/include/atomic/iot_atomic_gcc_disable.h $(MQTT)/ports/common/include/atomic/iot_atomic_gcc.h 

.PHONY: install_atomic uninstall_atomic

include ../Makefile.common

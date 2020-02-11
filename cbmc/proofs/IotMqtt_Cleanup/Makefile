ENTRY=IotMqtt_Cleanup

ABSTRACTIONS += --remove-function-body IotLog_Generic

OBJS += $(ENTRY)_harness.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_api.goto

UNWINDING += --unwind 1

include ../Makefile.common

ENTRY=IotMqtt_Init

ABSTRACTIONS += --remove-function-body IotLog_Generic
ABSTRACTIONS += --remove-function-body Iot_EnterCritical
ABSTRACTIONS += --remove-function-body Iot_ExitCritical

OBJS += $(ENTRY)_harness.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_api.goto

UNWINDING += --unwind 1

include ../Makefile.common

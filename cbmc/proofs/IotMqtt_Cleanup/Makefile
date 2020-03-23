ENTRY=IotMqtt_Cleanup

# We abstract all the log and concurrency related functions in this proof
# and assume their implementation is correct
ABSTRACTIONS += --remove-function-body IotLog_Generic

OBJS += $(ENTRY)_harness.goto
OBJS += $(MQTT)/libraries/standard/mqtt/src/iot_mqtt_api.goto

UNWINDING += --unwind 1

include ../Makefile.common

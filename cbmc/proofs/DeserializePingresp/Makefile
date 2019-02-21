ENTRY=DeserializePingresp

ABSTRACTIONS = \
	--remove-function-body IotLog_Generic \

OBJS = \
	$(ENTRY)_harness.goto \
	$(MQTT)/lib/source/mqtt/iot_mqtt_serialize.goto \

include ../Makefile.common

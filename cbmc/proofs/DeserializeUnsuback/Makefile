ENTRY=DeserializeUnsuback

ABSTRACTIONS = \
	--remove-function-body IotLog_Generic \

OBJS = \
	$(ENTRY)_harness.goto \
	$(MQTT)/libraries/standard/mqtt/src/iot_mqtt_serialize.goto \

include ../Makefile.common

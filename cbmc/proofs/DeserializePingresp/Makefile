ENTRY=DeserializePingresp

ABSTRACTIONS = \
	--remove-function-body AwsIotLogGeneric \

OBJS = \
	$(ENTRY)_harness.goto \
	$(MQTT)/lib/source/mqtt/aws_iot_mqtt_serialize.goto \

include ../Makefile.common

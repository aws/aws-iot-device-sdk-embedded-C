ENTRY=DeserializeSuback

BUFFER_SIZE = 100

ABSTRACTIONS = \
	--remove-function-body IotLog_Generic \
	--remove-function-body _IotMqtt_RemoveSubscriptionByPacket \

UNWINDING = \
	--unwindset _decodeSubackStatus.0:$(BUFFER_SIZE) \

OBJS = \
	$(ENTRY)_harness.goto \
	$(MQTT)/libraries/standard/mqtt/src/iot_mqtt_subscription.goto \
	$(MQTT)/libraries/standard/mqtt/src/iot_mqtt_serialize.goto \

DEF = -DBUFFER_SIZE=$(BUFFER_SIZE)

include ../Makefile.common

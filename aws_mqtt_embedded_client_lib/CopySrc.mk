MQTTPacket := $(call copy, $(pwd)/MQTTPacket/src,$(brazil.build.dir)/MQTTPacket/src)

MQTTClient := $(call copy, $(pwd)/MQTTClient/src,$(brazil.build.dir)/MQTTClient/src)

MQTTClientC := $(call copy, $(pwd)/MQTTClient-C/src,$(brazil.build.dir)/MQTTClient-C/src)

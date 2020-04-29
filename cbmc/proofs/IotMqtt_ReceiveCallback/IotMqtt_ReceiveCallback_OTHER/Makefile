# Leave PACKET undefined for the OTHER case.
#PACKET=

# Note: We should be able to abstract all of the functions below, but
# symbolic execution wants _deserializePublishPacket for the OTHER
# case.  The constraint solver is able to prove that the function is
# unreachable in the OTHER case.

ENTRY=IotMqtt_ReceiveCallback
MQTT = $(abspath ../../../..)

################################################################
# Functions made unreachable by the case split

ABSTRACTIONS += --remove-function-body _IotMqtt_DeserializeConnack
ABSTRACTIONS += --remove-function-body _IotMqtt_DeserializePuback
ABSTRACTIONS += --remove-function-body _IotMqtt_DeserializeSuback
ABSTRACTIONS += --remove-function-body _IotMqtt_DeserializeUnsuback

ABSTRACTIONS += --remove-function-body _deserializeAck
ABSTRACTIONS += --remove-function-body _deserializePublishPacket

################################################################
# Functions the solver can prove are unreachable

ABSTRACTIONS += --remove-function-body IotNetworkInterfaceDestroy
ABSTRACTIONS += --remove-function-body IotNetworkInterfaceSend
ABSTRACTIONS += --remove-function-body _matchEndWildcards
ABSTRACTIONS += --remove-function-body _matchWildcards
ABSTRACTIONS += --remove-function-body _mqttOperation_match
ABSTRACTIONS += --remove-function-body _mqttSubscription_setUnsubscribe
ABSTRACTIONS += --remove-function-body _packetMatch
ABSTRACTIONS += --remove-function-body _topicFilterMatch
ABSTRACTIONS += --remove-function-body _topicMatch

include ../Makefile
include ../../Makefile.common

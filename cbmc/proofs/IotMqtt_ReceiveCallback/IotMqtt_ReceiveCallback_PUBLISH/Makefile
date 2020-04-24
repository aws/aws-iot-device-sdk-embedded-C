PACKET=PUBLISH

ENTRY=IotMqtt_ReceiveCallback
MQTT = $(abspath ../../../..)

################################################################
# Functions made unreachable by the case split

ABSTRACTIONS += --remove-function-body _IotMqtt_DeserializeConnack
ABSTRACTIONS += --remove-function-body _IotMqtt_DeserializePuback
ABSTRACTIONS += --remove-function-body _IotMqtt_DeserializeSuback
ABSTRACTIONS += --remove-function-body _IotMqtt_DeserializeUnsuback

ABSTRACTIONS += --remove-function-body _deserializeAck
ABSTRACTIONS += --remove-function-body _deserializePingResp

################################################################
# Functions the solver can prove are unreachable

ABSTRACTIONS += --remove-function-body Atomic_CompareAndSwap_u32
ABSTRACTIONS += --remove-function-body Atomic_CompareAndSwap_u32
ABSTRACTIONS += --remove-function-body IotListDouble_FindFirstMatch
ABSTRACTIONS += --remove-function-body IotNetworkInterfaceDestroy
ABSTRACTIONS += --remove-function-body IotNetworkInterfaceSend
ABSTRACTIONS += --remove-function-body _IotMqtt_DeserializePingresp
ABSTRACTIONS += --remove-function-body _IotMqtt_FindOperation
ABSTRACTIONS += --remove-function-body _IotMqtt_Notify
ABSTRACTIONS += --remove-function-body _matchEndWildcards
ABSTRACTIONS += --remove-function-body _matchWildcards
ABSTRACTIONS += --remove-function-body _mqttOperation_match
ABSTRACTIONS += --remove-function-body _mqttSubscription_setUnsubscribe
ABSTRACTIONS += --remove-function-body _packetMatch
ABSTRACTIONS += --remove-function-body _topicFilterMatch
ABSTRACTIONS += --remove-function-body _topicMatch
ABSTRACTIONS += --remove-function-body destroy_operation_list
ABSTRACTIONS += --remove-function-body destroy_operation_list_element
ABSTRACTIONS += --remove-function-body destroy_subscription_list
ABSTRACTIONS += --remove-function-body destroy_subscription_list_element

include ../Makefile
include ../../Makefile.common

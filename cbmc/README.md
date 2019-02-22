# MQTT memory safety proofs

This directory contains CBMC proofs of memory safety of MQTT entry points. [CBMC](http://www.cprover.org/cbmc/) is a bounded model checker for C available from the GitHub [repository](https://github.com/diffblue/cbmc). Each proof is in a separate subdirectory of proofs:

* DeserializeConnack: _IotMqtt_DeserializeConnack is memory safe assuming:
  * We abstract the IotLog_Generic logging function
* DeserializePingresp: _IotMqtt_DeserializePingresp is memory safe assuming:
  * We abstract the IotLog_Generic logging function
* DeserializePuback: _IotMqtt_DeserializePuback is memory safe assuming:
  * We abstract the IotLog_Generic logging function
* DeserializePublish: _IotMqtt_DeserializePublish is memory safe assuming:
  * We abstract the IotLog_Generic logging function
* DeserializeSuback: _IotMqtt_DeserializeSuback is memory safe assuming:
  * We abstract the IotLog_Generic logging function
  * We abstract the _IotMqtt_RemoveSubscriptionByPacket function
  * We bound the length of the buffer being parsed
* DeserializeUnsuback: _IotMqtt_DeserializeUnsuback is memory safe assuming:
  * We abstract the IotLog_Generic logging function

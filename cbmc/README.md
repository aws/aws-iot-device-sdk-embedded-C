# MQTT memory safety proofs

This directory contains CBMC proofs of memory safety of MQTT entry points. [CBMC](http://www.cprover.org/cbmc/) is a bounded model checker for C available from the GitHub [repository](https://github.com/diffblue/cbmc). Each proof is in a separate subdirectory of proofs:

* DeserializeConnack: AwsIotMqttInternal_DeserializeConnack is memory safe assuming:
  * We abstract the AwsIotLogGeneric logging function
* DeserializePingresp: AwsIotMqttInternal_DeserializePingresp is memory safe assuming:
  * We abstract the AwsIotLogGeneric logging function
* DeserializePuback: AwsIotMqttInternal_DeserializePuback is memory safe assuming:
  * We abstract the AwsIotLogGeneric logging function
* DeserializePublish: AwsIotMqttInternal_DeserializePublish is memory safe assuming:
  * We abstract the AwsIotLogGeneric logging function
* DeserializeSuback: AwsIotMqttInternal_DeserializeSuback is memory safe assuming:
  * We abstract the AwsIotLogGeneric logging function
  * We abstract the AwsIotMqttInternal_RemoveSubscriptionByPacket function
  * We bound the length of the buffer being parsed
* DeserializeUnsuback: AwsIotMqttInternal_DeserializeUnsuback is memory safe assuming:
  * We abstract the AwsIotLogGeneric logging function



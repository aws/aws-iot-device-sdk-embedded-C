# Memory safety proof for IotMqtt_PublishAsync

This proof harness attains 94% code coverage.  The following comments explain
why the uncovered lines of code are unreachable code.

Some functions contain unreachable blocks of code:

* `_IotMqtt_SerializeConnectCommon`

    * `_validatePublish` eliminates that possibility of `QoS == IOT_MQTT_QOS_2`

* `_scheduleNextRetry`

    * `pOperation->u.operation.periodic.retry.count <
       pOperation->u.operation.periodic.retry.limit`

* `_IotMqtt_DestroyOperation`

    * Notify calls `DestroyOperation` with a linked operation

* `_IotMqtt_RemainingLengthEncodedSize`

    * This function never reaches `length > 2097152U`

* `_IotMqtt_ProcessSend`

    * `pOperation->u.operation.periodic.retry.limit` always 0
    * `pOperation->u.operation.type != IOT_MQTT_DISCONNECT`
    * `_completePendingSend` always return `destroyOperation == false`

* `_IotMqtt_PublishPacketSize`

    * This function never reaches `pPublishInfo->payloadLength > payloadLimit`

* `_IotMqtt_SerializePublish`

    * `_IotMqtt_PublishPacketSize` never returns false, because
       `pPublishInfo->payloadLength` is always smaller than `payloadLimit`

* `_IotMqtt_PublishSetDup`

    * `pPacketIdentifierHigh != NULL`

* `_validatePublishPayload`

    * This function never reaches `payloadLength > maximumPayloadLength`

* `_checkRetryLimit`

    * `pOperation->u.operation.periodic.retry.count <
       pOperation->u.operation.periodic.retry.limit`
    *  `pOperation->u.operation.periodic.retry.count != 1U`

* `_IotMqtt_DecrementOperationReferences`

    * `cancelJob == false`

* `_IotMqtt_Notify`

    * `pOperation->u.operation.type != IOT_MQTT_SUBSCRIBE`

* `IotMqtt_OperationType`

    * Always returns `IOT_MQTT_PUBLISH_TO_SERVER`

Some functions are simply unreachable:

* `_IotMqtt_RemoveSubscriptionByPacket`

    * Unreachable: Only function call in from an unreachable block of
	`_IotMqtt_Notify`

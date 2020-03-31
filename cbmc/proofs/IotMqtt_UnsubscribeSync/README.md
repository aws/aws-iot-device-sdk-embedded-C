This is a memory safety proof for IotMqtt_UnsubscribeAsync.

This proof attains 88% code coverage.  The following comments explain
why the uncovered lines of code are unreachable code.

Some functions contain unreachable blocks of code:

* libraries/standard/common/include/iot_linear_containers.h IotListDouble_FindFirstMatch

  * Always called with a nonnull match predicate

* libraries/standard/mqtt/src/iot_mqtt_api.c IotMqtt_OperationType

  * Always called with UNSUBSCRIBE operation type

* libraries/standard/mqtt/src/iot_mqtt_api.c IotMqtt_Wait

  * Wait is called with a good operation in a connected state.

* libraries/standard/mqtt/src/iot_mqtt_api.c IotMqtt_strerror

  * Called with only a subset of error codes.

* libraries/standard/mqtt/src/iot_mqtt_api.c \_sendMqttMessage

  * A synchronous operation is a blocking operation

* libraries/standard/mqtt/src/iot_mqtt_api.c \_subscriptionCommon

  * Always called with UNSUBSCRIBE operation type

* libraries/standard/mqtt/src/iot_mqtt_api.c \_subscriptionCommonSetup

  * Always called with UNSUBSCRIBE operation type

* libraries/standard/mqtt/src/iot_mqtt_api.c \_waitForOperation

  * Always called with UNSUBSCRIBE operation type

* libraries/standard/mqtt/src/iot_mqtt_helper.c \_IotMqtt_RemainingLengthEncodedSize

  * Proof assumption: Proof bounds on number and size of subscription topics limits the
	outbound packet to less than 128 bytes.

* libraries/standard/mqtt/src/iot_mqtt_helper.c \_IotMqtt_SubscriptionPacketSize

  * Always called with UNSUBSCRIBE operation type

* libraries/standard/mqtt/src/iot_mqtt_helper.c \_encodeRemainingLength

  * Proof assumption: Proof bounds on number and size of subscription topics limits the
	outbound packet to less than 128 bytes.

* libraries/standard/mqtt/src/iot_mqtt_operation.c \_IotMqtt_CreateOperation

  * Waitable operation has no callback

* libraries/standard/mqtt/src/iot_mqtt_operation.c \_IotMqtt_DecrementOperationReferences

  * TODO: TryCancel always fails

* libraries/standard/mqtt/src/iot_mqtt_operation.c \_IotMqtt_DestroyOperation

  * Always called with a linked operation

* libraries/standard/mqtt/src/iot_mqtt_operation.c \_IotMqtt_Notify

  * TODO

* libraries/standard/mqtt/src/iot_mqtt_operation.c \_IotMqtt_ProcessSend

  * Always called with a UNSUBSCRIBE operation

* libraries/standard/mqtt/src/iot_mqtt_operation.c \_completePendingSend

  * The operation.periodic.retry union member is not valid for UNSUBSCRIBE.

* libraries/standard/mqtt/src/iot_mqtt_operation.c \_initializeOperation

  * Sync operation is always waitable.

* libraries/standard/mqtt/src/iot_mqtt_subscription.c \_topicMatch

  * Always called with exactMatchOnly == true

* libraries/standard/mqtt/src/iot_mqtt_validate.c \_IotMqtt_ValidateOperation

  * Operation is nonnull and waitable.

* libraries/standard/mqtt/src/iot_mqtt_validate.c \_validateListSize

  * Proof assumption: list of topics to unsubscribe is nonempty

* libraries/standard/mqtt/src/iot_mqtt_validate.c \_validateString

  * Proof assumption: length of topic filter is always positive.

* libraries/standard/mqtt/src/iot_mqtt_validate.c \_validateSubscription

  * Always called with UNSUBSCRIBE operation type.

Some functions are simply unreachable:

* libraries/standard/mqtt/src/iot_mqtt_operation.c \_IotMqtt_ScheduleOperation

  * Unreachable: Only function calls are from unreachable
    scheduleCallback, unreachable scheduleNextRetry, and an
    unreachable block of sendMqttMessage.

* libraries/standard/mqtt/src/iot_mqtt_operation.c \_checkRetryLimit

  * Unreachable: Only function call is in an unreachable block of code
	in ProcessSend.

* libraries/standard/mqtt/src/iot_mqtt_operation.c \_scheduleCallback

  * Unreachable: Only function call is from Notify, but waitable
    operations have no callbacks.

* libraries/standard/mqtt/src/iot_mqtt_operation.c \_scheduleNextRetry

  * Unreachable: Only function call is in an unreachable block of code
	in completePendingSend

* libraries/standard/mqtt/src/iot_mqtt_serialize.c \_IotMqtt_PublishSetDup

  * Unreachable: Only function call in from unreachable checkRetryLimit

* libraries/standard/mqtt/src/iot_mqtt_subscription.c \_IotMqtt_RemoveSubscriptionByPacket

  * Unreachable: Only function call in from an unreachable block of
	subscriptionCommon


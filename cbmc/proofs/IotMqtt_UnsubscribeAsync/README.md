This is a memory safety proof for IotMqtt_UnsubscribeAsync.

This proof attains 91% code coverage.  The following comments explain
why the uncovered lines of code are unreachable code.

Some functions contain unreachable blocks of code:

* libraries/standard/common/include/iot_linear_containers.h
  IotListDouble_FindFirstMatch

  * Always called with a nonnull match predicate

* libraries/standard/mqtt/src/iot_mqtt_api.c IotMqtt_OperationType

  * Always called with UNSUBSCRIBE operation type

* libraries/standard/mqtt/src/iot_mqtt_api.c \_subscriptionCommon

  * Always called with UNSUBSCRIBE operation type

* libraries/standard/mqtt/src/iot_mqtt_api.c \_subscriptionCommonSetup

  * Always called with a nonnull operation reference

* libraries/standard/mqtt/src/iot_mqtt_helper.c
  \_IotMqtt_RemainingLengthEncodedSize

  * Proof assumption: Proof bounds on number and size of subscription topics limits the
	outbound packet to less than 128 bytes.

* libraries/standard/mqtt/src/iot_mqtt_helper.c
  \_IotMqtt_SubscriptionPacketSize

  * Always called with UNSUBSCRIBE operation type

* libraries/standard/mqtt/src/iot_mqtt_helper.c \_encodeRemainingLength

  * Proof assumption: Proof bounds on number and size of subscription topics limits the
	outbound packet to less than 128 bytes.

* libraries/standard/mqtt/src/iot_mqtt_operation.c
  \_IotMqtt_CreateOperation

  * pOperation is null if status is not SUCCESS.  This is because 1)
	status is initialized to SUCCESS and is left untouched when operation
	allocation succeeds (returns a nonnull value), and 2) status is set
	to SUCCESS by \_initializeOperation because \_initializeOperation
	always returns SUCCESS because an asynchronous operation is
	unwaitable, so initialization can't fail.

* libraries/standard/mqtt/src/iot_mqtt_operation.c
  \_IotMqtt_DecrementOperationReferences

  * Always called with cancelJob false.

* libraries/standard/mqtt/src/iot_mqtt_operation.c
  \_IotMqtt_DestroyOperation

  * Notify calls DestroyOperation with a linked, unwaitable
	(asynchronous) SUBSCRIBE operation.

* libraries/standard/mqtt/src/iot_mqtt_operation.c \_IotMqtt_Notify

  * ProcessSend calls Notify with an unwaitable (asynchronous) SUBSCRIBE
	operation.

* libraries/standard/mqtt/src/iot_mqtt_operation.c \_IotMqtt_ProcessSend

  * ProcessSsend is called with an UNSUBSCRIBE operation

* libraries/standard/mqtt/src/iot_mqtt_operation.c \_completePendingSend

  * Always called with an unwaitable (asynchronous) and nonPUBLISH
	(UNSUBSCRIBE) operation

* libraries/standard/mqtt/src/iot_mqtt_operation.c \_initializeOperation

  * Always called with an unwaitable (asynchronous) operation

* libraries/standard/mqtt/src/iot_mqtt_subscription.c \_topicMatch

  * Always called with exactMatchOnly == true

* libraries/standard/mqtt/src/iot_mqtt_validate.c \_validateListSize

  * Proof assumption: list of topics to unsubscribe is nonempty

* libraries/standard/mqtt/src/iot_mqtt_validate.c \_validateString

  * Proof assumption: length of topic filter is always positive.

* libraries/standard/mqtt/src/iot_mqtt_validate.c \_validateSubscription

  * Always called with UNSUBSCRIBE operation type.

Some functions are simply unreachable:

* libraries/standard/mqtt/src/iot_mqtt_operation.c \_checkRetryLimit

  * Unreachable: Only function call is in an unreachable block of code
	in ProcessSend.

* libraries/standard/mqtt/src/iot_mqtt_operation.c \_scheduleNextRetry

  * Unreachable: Only function call is in an unreachable block of code
	in completePendingSend

* libraries/standard/mqtt/src/iot_mqtt_subscription.c
  \_IotMqtt_RemoveSubscriptionByPacket

  * Unreachable: Only function call in from an unreachable block of
	subscriptionCommon


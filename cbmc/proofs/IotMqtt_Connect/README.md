# Memory safety proof for IotMqtt_Connect

This proof harness attains 92% code coverage.  The following comments explain
why the uncovered lines of code are unreachable code.

Some functions contain unreachable blocks of code:

* `_IotMqtt_SerializeConnectCommon`

    * `_validatePublish` eliminates that possibility of `QoS == IOT_MQTT_QOS_2`

* `IotListDouble_FindFirstMatch`

    * Always called with a nonnull isMatch parameter

* `_topicMatch`

    * `_IotMqtt_AddSubscriptions` sets `pParam->exactMatchOnly == true`,
     so `_topicFilterMatch` is never called

* `_encodeUserNameAndMetrics`

    * At this point `pConnectInfo->userNameLength` is smaller
    than `(UINT16_MAX - AWS_IOT_METRICS_USERNAME_LENGTH)`

* `_validatePublish`

    * Always called with a nonnull pPublishInfo parameter

* `_IotMqtt_DestroyOperation`

    * Notify calls `DestroyOperation` with a linked operation

* `_IotMqtt_IncrementConnectionReferences`

    * `pMqttConnection->disconnected` is false

* `_encodeRemainingLength`

    * `remainingLength` is smaller than 128 (higher sizes lead
      to way higher verification time)

* `_IotMqtt_DecrementOperationReferences`

    * `IotTaskPool_TryCancel` always return bad parameter,
    because we do not create a TaskPool job.

* `_initializeOperation`

    * The operation is always waitable

* `_IotMqtt_CreateOperation`

    * `pMqttConnection->disconnected` is true; therefore,
      `_IotMqtt_IncrementConnectionReferences` always return false

* `_completePendingSend`

    * `pOperation->u.operation.periodic.retry.limit` always 0

* `_IotMqtt_ProcessSend`

    * `pOperation->u.operation.periodic.retry.limit` always 0
    * `pOperation->u.operation.type != IOT_MQTT_DISCONNECT`
    * Operation is always waitable
    * `_completePendingSend` always return `destroyOperation == false`

* `IotMqtt_Wait`

    * operation is always initialized at this point
    * all parameters are valid
    * `pMqttConnection->disconnected == false`

* `_IotMqtt_DecrementConnectionReferences`

    * `pMqttConnection->references` is always different than zero, so the
       connection won't be destroyed
    * `destroyConnection == false` -> `pMqttConnection->references always != 0`

* `_waitForOperation`

    * `operation->u.operation.type != IOT_MQTT_SUBSCRIBE`

* `IotMqtt_strerror`

    * Never returns the following messages: `IOT_MQTT_SUCCESS`,
      `IOT_MQTT_INIT_FAILED`, `IOT_MQTT_BAD_RESPONSE`, `IOT_MQTT_SERVER_REFUSED`,
      `IOT_MQTT_RETRY_NO_RESPONSE`, and `default`

* `_validateListSize`

    * Always called with a nonnull list parameter
    * List size different than zero

* `_IotMqtt_ValidateOperation`

    * Always called with a nonnull operation parameter
    * Operation is waitable

* `_IotMqtt_RemainingLengthEncodedSize`

    * If length is too big, proof takes more than an hour to complete,
      so we consider small bounds here (i.e. `length < 128U`)

* `_IotMqtt_Notify`

    * `pOperation->u.operation.type != IOT_MQTT_SUBSCRIBE`
    * Operation is waitable
    * At this point, `status == IOT_MQTT_SCHEDULING_ERROR`
    * `_IotMqtt_DecrementOperationReferences` always returns false and
      the operation is not destroyed

* `IotMqtt_OperationType`

    * Always returns `IOT_MQTT_CONNECT`


Some functions are simply unreachable:

* `_IotMqtt_RemoveSubscriptionByPacket`

    * Unreachable: Only function call in from an unreachable block of
	`_IotMqtt_Notify`

* `_checkRetryLimit`

    * Unreachable: Only function call is in an unreachable block of code
	in `ProcessSend`

* `_scheduleCallback`

    * Unreachable: Only function call in from an unreachable block of
  	`_IotMqtt_Notify`

* `_scheduleNextRetry`

    * Unreachable: Only function call is in an unreachable block of code
	in `completePendingSend`


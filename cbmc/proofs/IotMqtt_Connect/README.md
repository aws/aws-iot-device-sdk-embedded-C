# Memory safety proof for IotMqtt_Connect

This proof harness attains 92% code coverage.  The following comments explain
why the uncovered lines of code are unreachable code.

Some functions contain unreachable blocks of code:

* libraries/standard/mqtt/src/iot_mqtt_helper.c
  \_IotMqtt_SerializeConnectCommon
  * _validatePublish eliminates that possibility of QoS == IOT_MQTT_QOS_2

* libraries/standard/common/include/iot_linear_containers.h
  IotListDouble_FindFirstMatch	
  * Always called with a nonnull isMatch parameter

* libraries/standard/mqtt/src/iot_mqtt_subscription.c
  \_topicMatch
  * _IotMqtt_AddSubscriptions sets pParam->exactMatchOnly == true, so _topicFilterMatch is never called

* libraries/standard/mqtt/src/iot_mqtt_helper.c
  \_encodeUserNameAndMetrics
  * At this point pConnectInfo->userNameLength is smaller than (UINT16_MAX - AWS_IOT_METRICS_USERNAME_LENGTH)

* libraries/standard/mqtt/src/iot_mqtt_validate.c
  \_validatePublish
  * Always called with a nonnull pPublishInfo parameter

* libraries/standard/mqtt/src/iot_mqtt_operation.c
  \_IotMqtt_DestroyOperation
  * Notify calls DestroyOperation with a linked operation.

* libraries/standard/mqtt/src/iot_mqtt_api.c
  \_IotMqtt_IncrementConnectionReferences
  * pMqttConnection->disconnected is false

* libraries/standard/mqtt/src/iot_mqtt_helper.c
  \_encodeRemainingLength
  * remainingLength is smaller than 128 (higher sizes lead to way higher verification time)

* libraries/standard/mqtt/src/iot_mqtt_operation.c
  \_IotMqtt_DecrementOperationReferences
  * IotTaskPool_TryCancel always return bad parameter, because we do not create a TaskPool job.

* libraries/standard/mqtt/src/iot_mqtt_operation.c
  \_initializeOperation
  * The operation is always waitable

* libraries/standard/mqtt/src/iot_mqtt_operation.c
  \_IotMqtt_CreateOperation
  * pMqttConnection->disconnected is true; therefore, _IotMqtt_IncrementConnectionReferences always return false

* libraries/standard/mqtt/src/iot_mqtt_api.c
  \_createKeepAliveOperation
  * _getMqttPingreqSerializer always return IOT_MQTT_SUCCESS

* libraries/standard/mqtt/src/iot_mqtt_operation.c
  \_completePendingSend
  * pOperation->u.operation.periodic.retry.limit always 0

* libraries/standard/mqtt/src/iot_mqtt_operation.c
  \_IotMqtt_ProcessSend
  * pOperation->u.operation.periodic.retry.limit always 0
  * pOperation->u.operation.type != IOT_MQTT_DISCONNECT
  * operation is always waitable
  * _completePendingSend always return destroyOperation == false

* libraries/standard/mqtt/src/iot_mqtt_api.c
  \IotMqtt_Wait
  * operation is always initialized at this point
  * all parameters are valid
  * pMqttConnection->disconnected == false

* libraries/standard/mqtt/src/iot_mqtt_api.c
  \_IotMqtt_DecrementConnectionReferences
  * pMqttConnection->references always != 0, so the connection won't be destroyed
  * destroyConnection == false, because pMqttConnection->references always != 0

* libraries/standard/mqtt/src/iot_mqtt_api.c
  \_waitForOperation

  * operation->u.operation.type != IOT_MQTT_SUBSCRIBE

* libraries/standard/mqtt/src/iot_mqtt_api.c
  IotMqtt_strerror

  * Never returns the following messages: IOT_MQTT_SUCCESS, IOT_MQTT_INIT_FAILED, IOT_MQTT_BAD_RESPONSE, IOT_MQTT_SERVER_REFUSED, IOT_MQTT_RETRY_NO_RESPONSE, and default

* libraries/standard/mqtt/src/iot_mqtt_validate.c
  \_validateListSize

  * Always called with a nonnull list parameter
  * list size != 0

* libraries/standard/mqtt/src/iot_mqtt_validate.c
  \_IotMqtt_ValidateOperation

  * Always called with a nonnull operation parameter
  * operation is waitable

* libraries/standard/mqtt/src/iot_mqtt_helper.c
  \_IotMqtt_RemainingLengthEncodedSize

	* if length is too big, proof takes more than an hour to complete, so we consider small bounds here (i.e. length < 128U)
					
* libraries/standard/mqtt/src/iot_mqtt_operation.c
  \_IotMqtt_Notify

  * pOperation->u.operation.type != IOT_MQTT_SUBSCRIBE
  * operation is waitable
  * at this point status is always status == IOT_MQTT_SCHEDULING_ERROR
  * \_IotMqtt_DecrementOperationReferences always return false and the operation is not destroyed

* libraries/standard/mqtt/src/iot_mqtt_api.c
  IotMqtt_OperationType

  * always return IOT_MQTT_CONNECT


Some functions are simply unreachable:

* libraries/standard/mqtt/src/iot_mqtt_subscription.c
  \_IotMqtt_RemoveSubscriptionByPacket

  * Unreachable: Only function call in from an unreachable block of
	_IotMqtt_Notify

* libraries/standard/mqtt/src/iot_mqtt_operation.c \_checkRetryLimit

  * Unreachable: Only function call is in an unreachable block of code
	in ProcessSend.

* libraries/standard/mqtt/src/iot_mqtt_operation.c \_scheduleCallback

  * Unreachable: Only function call in from an unreachable block of
  	_IotMqtt_Notify

* libraries/standard/mqtt/src/iot_mqtt_operation.c \_scheduleNextRetry

  * Unreachable: Only function call is in an unreachable block of code
	in completePendingSend


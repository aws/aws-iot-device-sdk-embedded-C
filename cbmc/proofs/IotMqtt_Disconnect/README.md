This is a memory safety proof for IotMqtt_Disconnect.

This proof attains 86% code coverage.  The following comments explain
why the uncovered lines of code are unreachable code.

Unreachable code blocks within functions:

* `_IotMqtt_CreateOperation`

	* Called from `IotMqtt_Disconnect`
		* Called with pCallbackInfo == NULL

* `_initializeOperation`

	* Called from `_IotMqtt_CreateOperation` <- `IotMqtt_Disconnect`
		* waitable: Disconnect calls CreateOperation with waitable flag

* `_IotMqtt_DestroyOperation`

	* Called from `IotMqtt_Wait` <- `IotMqtt_Disconnect`
		* operation linked: Disconnected called CreateOperation that linked the operation
		* operation mqttpacket defined: Checked by Disconnect assertion
	* Called from `_IotMqtt_Notify` <- `_IotMqtt_ProcessSend` <- `IotMqtt_Disconnect`
		* Called from dead code block
	* Called from `_IotMqtt_ProcessSend` <- `IotMqtt_Disconnect`
		* Called from dead code block

* `IotMqtt_Wait`

	* Called from `IotMqtt_Disconnect`
		* checkInit == true: checked by disconnect
		* ValidateOperation == true: operation is nonnull and waitable
		* connection->disconnected == false: Disconnect would set status to pending and not call wait.

* `_destroyMqttConnection`

	* Called from `_IotMqtt_DecrementConnectionReferences` but only
      when reference has been decremented to 0.
		* The uncovered block is guarded by the conditional keepalive!=0.
		* A valid connection has references > 0 and references > 1
          when keepalive!=0 (the ping request operation references
          it).
		* So a path with keepalive!=0 has references set to >=2,
		  Disconnect calls CreateOperation (for the Disconnect packet)
		  that increments references to >=3, and Disconnect calls Wait
		  that call Destroy Operation (for the Disconnect packet) that
		  decrements references to >=2.
	    * There are only remaining decrements:
		  Disconnect calls DecrementConnectionReferences and
		  CloseNetworkConnection.
		* Both decrements are required to get reference to 0,
		  but the decrement in CloseNetworkConnection also sets keepalive=0.
		* Thus it is impossible to invoke destroyMqttConnection (with
          references=0) and execute this block of code (with
          keepalive!=0).

* `_IotMqtt_ProcessSend`

	* Called from `IotMqtt_Disconnect`
		* retry limit == 0: checked in disconnect
		* operation type == disconnect: In disconnect, processsend called => status == success => type set to disconnect

* `_IotMqtt_DecrementOperationReferences`

	* Called from `IotMqtt_Wait` <- `IotMqtt_Disconnect`
		* Called with canceljob == false
	* Called from `_IotMqtt_Notify` <- `_IotMqtt_ProcessSend` <- `IotMqtt_Disconnect`
		* Called with canceljob == false
	* Called from `_completePendingSend` <- `_IotMqtt_ProcessSend` <- `IotMqtt_Disconnect`
		* Called with canceljob == false
	* Called from `_waitForOperation` <- `IotMqtt_Wait` <- `IotMqtt_Disconnect`
		* Called from dead code

* `_IotMqtt_ValidateOperation`

	* Called from `IotMqtt_Wait` <- `IotMqtt_Disconnect`
		* operation is nonnull and waitable (checked by disconnect)

* `_IotMqtt_Notify`

	* Called from `_IotMqtt_ProcessSend` <- `IotMqtt_Disconnect`
		* operation type set to disconnect by disconnect
		* operation created as waitable by disconnect
		* status initialized to error and unchanged

* `IotMqtt_OperationType`

	* Called only with `DISCONNECT` operation type

* `_waitForOperation`

	* Called from `IotMqtt_Wait` <- `IotMqtt_Disconnect`
		* packet type != subscribe

* `IotMqtt_strerror`

	* Called only with `NETWORK_ERROR` and `SUCCESS`

Unreachable functions

* `_IotMqtt_ScheduleOperation`

	* Called from `_scheduleCallback` <- `_IotMqtt_Notify` <- `_IotMqtt_ProcessSend` <- `IotMqtt_Disconnect`
		* Called from unreachable function
	* Called from `_scheduleNextRetry` <- `_completePendingSend` <- `_IotMqtt_ProcessSend` <- `IotMqtt_Disconnect`
		* Called from unreachable function

* `_checkRetryLimit`

	* Called from `_IotMqtt_ProcessSend` <- `IotMqtt_Disconnect`
		* Called from dead code block

* `_completePendingSend`

	* Called from `_IotMqtt_ProcessSend` <- `IotMqtt_Disconnect`
		* Called from dead code block

* `_scheduleCallback`

	* Called from `_IotMqtt_Notify` <- `_IotMqtt_ProcessSend` <- `IotMqtt_Disconnect`
		* Called from dead code block

* `_scheduleNextRetry`

	* Called from `_completePendingSend` <- `_IotMqtt_ProcessSend` <- `IotMqtt_Disconnect`
		* Called from unreachable function

* `_IotMqtt_PublishSetDup`

	* Called from `_checkRetryLimit` <- `_IotMqtt_ProcessSend` <- `IotMqtt_Disconnect`
		* Called from unreachable function

* `_IotMqtt_RemoveSubscriptionByPacket`

	* Called from `_IotMqtt_Notify` <- `_IotMqtt_ProcessSend` <- `IotMqtt_Disconnect`
		* Called from dead code block
	* Called from `_waitForOperation` <- `IotMqtt_Wait` <- `IotMqtt_Disconnect`
		* Called from dead code block

Modeling code whose coverage is irrelevant:

* `IotSemaphore_TimedWait`
* `_IotMqtt_NextPacketIdentifier`

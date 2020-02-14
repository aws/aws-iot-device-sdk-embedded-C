#include "iot_config.h"
#include "private/iot_mqtt_internal.h"

#include <stdlib.h>
#include <string.h>

void harness()
{
  /*
   * The code specification says that IotMqtt_Cleanup must be
   * called after IotMqtt_Init, since it is supposed to undo
   * anything that IotMqtt_Init does. Both IotMqtt_Cleanup and
   * IotMqtt_Init basically update the status of the same global
   * variable _initCalled. This variable is declared as volatile,
   * so CBMC will always treat it as non-deterministic.
   * Thus, even if we called IotMqtt_Init first, it does not make
   * a significant impact in this proof harness. However, since
   * the developers may change the implementation of both
   * functions in the future, we should keep both functions in the proof.
   */
  IotMqtt_Init();
  IotMqtt_Cleanup();
}

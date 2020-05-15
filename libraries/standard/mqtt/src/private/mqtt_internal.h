#ifndef MQTT_INTERNAL_H_
#define MQTT_INTERNAL_H_

#include "mqtt_config.h"

#ifndef LogError
    #define LogError( message )
#endif

#ifndef LogErrorWithArgs
    #define LogErrorWithArgs( formatAndStrings )
#endif

#ifndef LogWarn
    #define LogWarn( message )
#endif

#ifndef LogWarnWithArgs
    #define LogWarnWithArgs( formatAndStrings )
#endif

#ifndef LogInfo
    #define LogInfo( message )
#endif

#ifndef LogInfoWithArgs
    #define LogInfoWithArgs( formatAndStrings )
#endif

#ifndef LogDebug
    #define LogDebug( message )
#endif

#ifndef LogDebugWithArgs
    #define LogDebugWithArgs( formatAndStrings )
#endif

#endif /* ifndef MQTT_INTERNAL_H_ */

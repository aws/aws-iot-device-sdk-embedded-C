# Include filepaths for source and include.
include(filePaths.cmake)

# MQTT library target.
add_library( iotmqtt
             ${MQTT_SOURCES}
             include/mqtt.h
             include/mqtt_lightweight.h )

# MQTT public include path.
target_include_directories( iotmqtt PUBLIC ${MQTT_INCLUDE_PUBLIC_DIRS} )

# Link required libraries.
#target_link_libraries( iotmqtt PRIVATE iotbase )

# Link Unity test framework when building tests.
#if( ${IOT_BUILD_TESTS} )
#    target_link_libraries( iotmqtt PRIVATE unity )
#endif()

# Organization of MQTT in folders.
set_property( TARGET iotmqtt PROPERTY FOLDER libraries/standard )
source_group( include FILES include/mqtt.h )
source_group( src FILES ${MQTT_SOURCES} )

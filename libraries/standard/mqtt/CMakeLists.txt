# Include filepaths for source and include.
include( mqttFilePaths.cmake )

# MQTT library target.
add_library( mqtt
             ${MQTT_SOURCES} )

# MQTT public include path.
target_include_directories( mqtt PUBLIC ${MQTT_INCLUDE_PUBLIC_DIRS} )

# MQTT private include path.
target_include_directories( mqtt PRIVATE ${MQTT_INCLUDE_PRIVATE_DIRS} 
                                         ${LOGGING_INCLUDE_DIRS} )

# Organization of MQTT in IDE projects.
set_target_properties( mqtt PROPERTIES FOLDER libraries/standard )
source_group( include FILES include/mqtt.h include/mqtt_lightweight.h include/mqtt_state.h )
source_group( src FILES ${MQTT_SOURCES} )
source_group( src\\private FILES src/private/mqtt_internal.h )

if(BUILD_TESTS)
    add_subdirectory( utest )
endif()

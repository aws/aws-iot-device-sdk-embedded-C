# Common libraries source files.
add_library( iotcommon SHARED
             iot_common.c
             iot_json_utils.c
             iot_logging.c
             iot_taskpool.c
             static_memory/iot_static_memory_common.c
             static_memory/iot_static_memory_taskpool.c
             static_memory/iot_static_memory_mqtt.c
             static_memory/aws_iot_static_memory_shadow.c )

# Library version.
set_target_properties( iotcommon PROPERTIES VERSION ${PROJECT_VERSION} )

# Link required libraries.
target_link_libraries( iotcommon iotplatform )

# Link Unity test framework when building tests.
if( ${IOT_BUILD_TESTS} )
    target_link_libraries( iotcommon unity )
endif()

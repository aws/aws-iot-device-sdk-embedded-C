# Common libraries source files.
add_library( iotcommon
             iot_init.c
             iot_logging.c
             iot_static_memory_common.c
             iot_taskpool.c
             iot_taskpool_static_memory.c )

# Library version.
set_target_properties( iotcommon PROPERTIES VERSION ${PROJECT_VERSION} )

# Link required libraries.
target_link_libraries( iotcommon iotplatform )

# Link Unity test framework when building tests.
if( ${IOT_BUILD_TESTS} )
    target_link_libraries( iotcommon unity )
endif()

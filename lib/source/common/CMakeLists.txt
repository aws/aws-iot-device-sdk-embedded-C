# Common libraries source files.
set( COMMON_SOURCES
     iot_init.c
     iot_logging.c
     iot_static_memory_common.c
     iot_taskpool.c
     iot_taskpool_static_memory.c )

# Lists of common header files. These are only used for directory organization
# (not for build).
set( COMMON_PUBLIC_HEADERS
     ${PROJECT_SOURCE_DIR}/lib/include/iot_init.h
     ${PROJECT_SOURCE_DIR}/lib/include/iot_linear_containers.h
     ${PROJECT_SOURCE_DIR}/lib/include/iot_logging_setup.h
     ${PROJECT_SOURCE_DIR}/lib/include/iot_taskpool.h )
set( COMMON_PRIVATE_HEADERS
     ${PROJECT_SOURCE_DIR}/lib/include/private/iot_error.h
     ${PROJECT_SOURCE_DIR}/lib/include/private/iot_logging.h
     ${PROJECT_SOURCE_DIR}/lib/include/private/iot_static_memory.h
     ${PROJECT_SOURCE_DIR}/lib/include/private/iot_taskpool_internal.h )
set( COMMON_TYPES_HEADERS
     ${PROJECT_SOURCE_DIR}/lib/include/types/iot_taskpool_types.h )

# Common library target.
add_library( iotcommon
             ${COMMON_SOURCES} ${COMMON_PUBLIC_HEADERS} ${COMMON_PRIVATE_HEADERS} ${COMMON_TYPES_HEADERS} )

# Link required libraries.
target_link_libraries( iotcommon iotplatform )

# Link Unity test framework when building tests.
if( ${IOT_BUILD_TESTS} )
    target_link_libraries( iotcommon unity )
endif()

# Organization of common libraries in folders.
set_property( TARGET iotcommon PROPERTY FOLDER "lib" )
source_group( include FILES ${COMMON_PUBLIC_HEADERS} )
source_group( include\\private FILES ${COMMON_PRIVATE_HEADERS} )
source_group( include\\types FILES ${COMMON_TYPES_HEADERS} )
source_group( source FILES ${COMMON_SOURCES} )

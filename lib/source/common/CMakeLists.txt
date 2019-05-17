# Common libraries source files.
set( COMMON_SOURCES
     ${PROJECT_SOURCE_DIR}/lib/source/common/iot_init.c
     ${PROJECT_SOURCE_DIR}/lib/source/common/iot_logging.c
     ${PROJECT_SOURCE_DIR}/lib/source/common/iot_static_memory_common.c
     ${PROJECT_SOURCE_DIR}/lib/source/common/iot_taskpool.c
     ${PROJECT_SOURCE_DIR}/lib/source/common/iot_taskpool_static_memory.c
     PARENT_SCOPE )

# Lists of common header files. These are only used for directory organization
# (not for build).
set( COMMON_PUBLIC_HEADERS
     ${PROJECT_SOURCE_DIR}/lib/include/iot_init.h
     ${PROJECT_SOURCE_DIR}/lib/include/iot_linear_containers.h
     ${PROJECT_SOURCE_DIR}/lib/include/iot_logging_setup.h
     ${PROJECT_SOURCE_DIR}/lib/include/iot_taskpool.h
     PARENT_SCOPE )
set( COMMON_PRIVATE_HEADERS
     ${PROJECT_SOURCE_DIR}/lib/include/private/iot_error.h
     ${PROJECT_SOURCE_DIR}/lib/include/private/iot_logging.h
     ${PROJECT_SOURCE_DIR}/lib/include/private/iot_static_memory.h
     ${PROJECT_SOURCE_DIR}/lib/include/private/iot_taskpool_internal.h
     PARENT_SCOPE )
set( COMMON_TYPES_HEADERS
     ${PROJECT_SOURCE_DIR}/lib/include/types/iot_taskpool_types.h
     PARENT_SCOPE )

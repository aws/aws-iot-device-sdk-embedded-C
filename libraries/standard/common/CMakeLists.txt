# Common libraries source files.
set( COMMON_SOURCES
     src/iot_init.c
     src/iot_logging.c
     src/iot_static_memory_common.c
     src/iot_taskpool.c
     src/iot_taskpool_static_memory.c )

# Lists of common header files. These are only used for directory organization.
set( COMMON_PUBLIC_HEADERS
     include/iot_error.h
     include/iot_init.h
     include/iot_linear_containers.h
     include/iot_logging.h
     include/iot_logging_setup.h
     include/iot_static_memory.h
     include/iot_taskpool.h )
set( COMMON_PRIVATE_HEADERS
     src/private/iot_taskpool_internal.h )
set( COMMON_TYPES_HEADERS
     include/types/iot_taskpool_types.h )

# List of the platform public headers.
set( PLATFORM_INTERFACE_DIRECTORY ${PROJECT_SOURCE_DIR}/libraries/platform )
set( PORTS_DIRECTORY ${PROJECT_SOURCE_DIR}/ports )

set( PLATFORM_INTERFACE_HEADERS
     ${PLATFORM_INTERFACE_DIRECTORY}/iot_clock.h
     ${PLATFORM_INTERFACE_DIRECTORY}/iot_metrics.h
     ${PLATFORM_INTERFACE_DIRECTORY}/iot_network.h
     ${PLATFORM_INTERFACE_DIRECTORY}/iot_threads.h )
set( PLATFORM_TYPES_HEADER
     ${PLATFORM_INTERFACE_DIRECTORY}/types/iot_platform_types.h )
set( PLATFORM_COMMON_HEADERS
     ${PORTS_DIRECTORY}/common/include/iot_atomic.h
     ${PORTS_DIRECTORY}/common/include/iot_network_metrics.h )

# Include the CMake file for this port.
include( ${PROJECT_SOURCE_DIR}/ports/${IOT_PLATFORM_NAME}/${IOT_PLATFORM_NAME}.cmake )

# The port CMake file must specify the types header and the platform sources.
if( NOT DEFINED PORT_TYPES_HEADER )
    message( FATAL_ERROR "Port CMake file did not set PORT_TYPES_HEADER." )
endif()

if( NOT DEFINED PLATFORM_SOURCES )
    message( FATAL_ERROR "Port CMake file did not set PLATFORM_SOURCES." )
endif()

# iotbase library target. This is a combination of the platform port and the
# common libraries.
add_library( iotbase
             ${CONFIG_HEADER_PATH}/iot_config.h
             ${COMMON_SOURCES}
             ${COMMON_PUBLIC_HEADERS}
             ${COMMON_PRIVATE_HEADERS}
             ${COMMON_TYPES_HEADERS}
             ${PLATFORM_INTERFACE_HEADERS}
             ${PLATFORM_TYPES_HEADER}
             ${PLATFORM_COMMON_HEADERS}
             ${PLATFORM_SOURCES}
             ${PORT_TYPES_HEADER} )

# Set the types header for the port.
target_compile_definitions( iotbase PUBLIC -DIOT_SYSTEM_TYPES_FILE="${PORT_TYPES_HEADER}" )

# Specify if OpenSSL is being used in a compiler define.
if( ${IOT_NETWORK_USE_OPENSSL} )
    target_compile_definitions( iotbase PUBLIC -DIOT_NETWORK_USE_OPENSSL=1 )
endif()

# Set the include directories for the common and platform libraries.
target_include_directories( iotbase
                            PUBLIC
                            ${CONFIG_HEADER_PATH}
                            ${PLATFORM_INTERFACE_DIRECTORY}/..
                            ${PLATFORM_INTERFACE_DIRECTORY}
                            ${PORTS_DIRECTORY}/common/include
                            include/ )

# Link any dependencies required by this port.
target_link_libraries( iotbase PRIVATE ${PLATFORM_DEPENDENCIES} )

if( ${IOT_BUILD_TESTS} )
    target_link_libraries( iotbase PRIVATE unity )
endif()

# Organization of iotbase in folders.
set_property( TARGET iotbase PROPERTY FOLDER libraries/standard )
source_group( "" FILES ${CONFIG_HEADER_PATH}/iot_config.h )
source_group( common\\include FILES ${COMMON_PUBLIC_HEADERS} )
source_group( common\\include\\types FILES ${COMMON_TYPES_HEADERS} )
source_group( common\\src FILES ${COMMON_SOURCES} )
source_group( common\\src\\private FILES ${COMMON_PRIVATE_HEADERS} )
source_group( platform\\include FILES ${PLATFORM_INTERFACE_HEADERS} ${PLATFORM_COMMON_HEADERS} )
source_group( platform\\include\\types FILES ${PLATFORM_TYPES_HEADER} ${PORT_TYPES_HEADER} )
source_group( platform\\src FILES ${PLATFORM_SOURCES} )

# Install the library with public headers.
install(TARGETS iotbase
        LIBRARY
        DESTINATION lib
        ARCHIVE
        DESTINATION lib)

install(FILES ${COMMON_PUBLIC_HEADERS}
        DESTINATION include/aws_iot/)

install(FILES ${COMMON_TYPES_HEADERS}
        DESTINATION include/aws_iot/)

# Build the test executable if needed.
if( ${IOT_BUILD_TESTS} )
    # Common unit test sources.
    set( COMMON_UNIT_TEST_SOURCES
         test/unit/iot_tests_linear_containers.c
         test/unit/iot_tests_taskpool.c
         test/unit/iot_tests_atomic.c )

    # Common tests executable.
    add_executable( iot_tests_common
                    ${COMMON_UNIT_TEST_SOURCES}
                    test/iot_tests_common.c
                    ${IOT_TEST_APP_SOURCE}
                    ${CONFIG_HEADER_PATH}/iot_config.h )

    # Define the test to run.
    target_compile_definitions( iot_tests_common PRIVATE
                                -DRunTests=RunCommonTests )

    # The tests use internal headers. Add the include path for internal headers.
    target_include_directories( iot_tests_common PRIVATE src )

    # Common tests library dependencies.
    target_link_libraries( iot_tests_common PRIVATE iotbase unity )

    # Organization of common tests in folders.
    set_property( TARGET iot_tests_common PROPERTY FOLDER tests )
    source_group( unit FILES ${COMMON_UNIT_TEST_SOURCES} )
    source_group( "" FILES ${IOT_TEST_APP_SOURCE} test/iot_tests_common.c )
endif()

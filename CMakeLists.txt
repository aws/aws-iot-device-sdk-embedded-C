# Project information.
cmake_minimum_required( VERSION 3.5.0 )
project( AwsIotDeviceSdkEmbeddedC
         VERSION 4.0.0
         LANGUAGES C )

# Allow the project to be organized into folders.
set_property( GLOBAL PROPERTY USE_FOLDERS ON )

# Use C99.
set( CMAKE_C_STANDARD 99 )
set( CMAKE_C_STANDARD_REQUIRED ON )

# Do not allow in-source build.
if( ${PROJECT_SOURCE_DIR} STREQUAL ${PROJECT_BINARY_DIR} )
    message( FATAL_ERROR "In-source build is not allowed. Please build in a separate directory, such as ${PROJECT_SOURCE_DIR}/build." )
endif()

# Configure options to always show in CMake GUI.
option( IOT_ATOMIC_USE_PORT
        "Set this to ON to use a custom atomic port. When OFF, the build system will choose an atomic port."
        OFF )
option( IOT_BUILD_TESTS
        "Set this to ON to build both demo and test executables. When OFF, only demo executables are built."
        OFF )
option( IOT_BUILD_CLONE_SUBMODULES
        "Set this to ON to automatically clone any required Git submodules. When OFF, submodules must be manually cloned."
        ON )

# Unity test framework does not export the correct symbols for DLLs.
# Do not allow allow shared libraries to be built when building tests on Windows.
if( ${IOT_BUILD_TESTS} AND ${CMAKE_SYSTEM_NAME} STREQUAL "Windows" )
    set( ALLOW_SHARED_LIBRARIES OFF )
else()
    set( ALLOW_SHARED_LIBRARIES ON )
endif()

include( CMakeDependentOption )
CMAKE_DEPENDENT_OPTION( BUILD_SHARED_LIBS
                        "Set this to ON to build all libraries as shared libraries. When OFF, libraries build as static libraries."
                        ON "${ALLOW_SHARED_LIBRARIES}"
                        OFF )

# Set the platform named based on the host OS if not defined.
if( NOT DEFINED IOT_PLATFORM_NAME )
    if( ${CMAKE_SYSTEM_NAME} STREQUAL "Linux" )
        set( IOT_PLATFORM_NAME "posix" CACHE STRING "Port to use for building the SDK." )

        # Provide an option to use the OpenSSL network abstraction on Linux.
        option( IOT_NETWORK_USE_OPENSSL
                "Set this to ON to use a network abstraction implemented on OpenSSL. When OFF, the mbed TLS network abstraction is used."
                OFF )
    elseif( ${CMAKE_SYSTEM_NAME} STREQUAL "Windows" )
        set( IOT_PLATFORM_NAME "win32" CACHE STRING "Port to use for building the SDK." )

        # Export all symbols when building Windows DLLs.
        if( ${BUILD_SHARED_LIBS} )
            set( CMAKE_WINDOWS_EXPORT_ALL_SYMBOLS
                 TRUE CACHE BOOL
                 "Export all symbols for Windows DLLs. This option must by enabled."
                 FORCE )
        endif()
    endif()
endif()

if( ${IOT_NETWORK_USE_OPENSSL} )
    add_definitions( -DIOT_NETWORK_USE_OPENSSL=1 )
endif()

# Validate the platform name.
if( NOT DEFINED IOT_PLATFORM_NAME )
    message( FATAL_ERROR "IOT_PLATFORM_NAME was not set and could not be automatically determined." )
endif()

if( NOT EXISTS ${PROJECT_SOURCE_DIR}/platform/ports/${IOT_PLATFORM_NAME} )
    message( FATAL_ERROR "A port for ${IOT_PLATFORM_NAME} does not exist in platform/ports." )
endif()

# Set output directories.
set( CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin )
set( CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib )

# Platform types file.
include_directories( ${PROJECT_SOURCE_DIR}/platform/ports/${IOT_PLATFORM_NAME}/types )
add_definitions( -DIOT_SYSTEM_TYPES_FILE="iot_platform_types_${IOT_PLATFORM_NAME}.h" )

# SDK include paths.
include_directories( ${PROJECT_SOURCE_DIR}/lib/include
                     ${PROJECT_SOURCE_DIR}/platform/include )

# Demo include path. Always required because the tests also build the demos.
include_directories( ${PROJECT_SOURCE_DIR}/demos/include )

# Set additional include paths for demos and tests.
if( ${IOT_BUILD_TESTS} )
    # Define the constant to enable test access.
    add_definitions( -DIOT_BUILD_TESTS=1 )

    # Test include paths.
    include_directories( ${PROJECT_SOURCE_DIR}/tests
                         tests/mqtt/access )

    # Build unity test framework.
    add_subdirectory( third_party/unity )
else()
    include_directories( ${PROJECT_SOURCE_DIR}/demos )
endif()

# Use a custom atomic port if the CMake option is set.
if( ${IOT_ATOMIC_USE_PORT} )
    add_definitions( -DIOT_ATOMIC_USE_PORT=1 )
endif()

# Platform headers.
set( PLATFORM_INTERFACE_HEADERS
     ${CMAKE_SOURCE_DIR}/lib/include/platform/iot_clock.h
     ${CMAKE_SOURCE_DIR}/lib/include/platform/iot_metrics.h
     ${CMAKE_SOURCE_DIR}/lib/include/platform/iot_network.h
     ${CMAKE_SOURCE_DIR}/lib/include/platform/iot_threads.h )

set( PLATFORM_TYPES_HEADERS
     ${CMAKE_SOURCE_DIR}/lib/include/types/iot_platform_types.h
     ${CMAKE_SOURCE_DIR}/platform/ports/${IOT_PLATFORM_NAME}/types/iot_platform_types_${IOT_PLATFORM_NAME}.h )

set( PLATFORM_COMMON_HEADERS
     ${CMAKE_SOURCE_DIR}/platform/include/iot_atomic.h
     ${CMAKE_SOURCE_DIR}/platform/include/iot_network_metrics.h )

# Platform libraries.
add_subdirectory( platform/ports/${IOT_PLATFORM_NAME} )

# Common libraries (linear containers, logging, etc.)
add_subdirectory( lib/source/common )

# The sources of the common libraries and platform layer will be built into a
# single library that is used as a dependency by other libraries.
add_library( iotbase
             ${PLATFORM_INTERFACE_HEADERS}
             ${PLATFORM_TYPES_HEADERS}
             ${PLATFORM_COMMON_HEADERS}
             ${COMMON_PUBLIC_HEADERS}
             ${COMMON_PRIVATE_HEADERS}
             ${COMMON_TYPES_HEADERS} )

# Link required libraries.
target_link_libraries( iotbase PRIVATE iotplatform iotcommon )

if( ${IOT_BUILD_TESTS} )
    target_link_libraries( iotbase PRIVATE unity )
endif()

# Organization of iotbase in folders.
source_group( platform\\interface FILES ${PLATFORM_INTERFACE_HEADERS} )
source_group( platform\\include FILES ${PLATFORM_COMMON_HEADERS} )
source_group( platform\\include\\types FILES ${PLATFORM_TYPES_HEADERS} )
source_group( platform\\source FILES ${PLATFORM_SOURCES} )
source_group( common\\include FILES ${COMMON_PUBLIC_HEADERS} )
source_group( common\\include\\private FILES ${COMMON_PRIVATE_HEADERS} )
source_group( common\\include\\types FILES ${COMMON_TYPES_HEADERS} )
source_group( common\\source\\aws_iot FILES ${AWS_IOT_COMMON_SOURCES} )
source_group( common\\source FILES ${COMMON_SOURCES} )

# MQTT library.
add_subdirectory( lib/source/mqtt )

# Shadow library.
add_subdirectory( lib/source/shadow )

# Serializer library.
add_subdirectory( lib/source/serializer )

# Defender library.
add_subdirectory( lib/source/defender )

# Jobs library.
add_subdirectory( lib/source/jobs )

# TinyCBOR library (third-party).
add_subdirectory( third_party/tinycbor )

# mbed TLS library (third-party).
add_subdirectory( third_party/mbedtls )

# Build demo executable.
add_subdirectory( demos/app )

# Test executables.
if( ${IOT_BUILD_TESTS} )
    add_subdirectory( tests/ )
endif()

# Set startup projects in Visual Studio.
if( ${IOT_BUILD_TESTS} )
    set_property( DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR} PROPERTY VS_STARTUP_PROJECT iot_tests_mqtt )
else()
    set_property( DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR} PROPERTY VS_STARTUP_PROJECT iot_demo_mqtt )
endif()

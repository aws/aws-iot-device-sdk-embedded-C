# Project information.
cmake_minimum_required( VERSION 3.5.0 )
project( AwsIotDeviceSdkC
         VERSION 4.0.0
         LANGUAGES C )

# Use C99.
set( CMAKE_C_STANDARD 99 )
set( CMAKE_C_STANDARD_REQUIRED ON )

# Do not allow in-source build.
if( ${PROJECT_SOURCE_DIR} STREQUAL ${PROJECT_BINARY_DIR} )
    message( FATAL_ERROR "In-source build is not allowed. Please build in a separate directory, such as ${PROJECT_SOURCE_DIR}/build." )
endif()

# Configure options to always show in CMake GUI.
option( BUILD_SHARED_LIBS
        "Set this to ON to build all libraries as shared libraries. When OFF, libraries build as static libraries."
        ON )
option( IOT_ATOMIC_USE_PORT
        "Set this to ON to use a custom atomic port. When OFF, the build system will choose an atomic port."
        OFF )
option( IOT_BUILD_TESTS
        "Set this to ON to build both demo and test executables. When OFF, only demo executables are built."
        OFF )
option( IOT_BUILD_CLONE_SUBMODULES
        "Set this to ON to automatically clone any required Git submodules. When OFF, submodules must be manually cloned."
        ON )

# Check for system support.
list( APPEND SUPPORTED_SYSTEMS "Linux" )

if( NOT ${CMAKE_SYSTEM_NAME} IN_LIST SUPPORTED_SYSTEMS )
    message( FATAL_ERROR "Unsupported system: ${CMAKE_SYSTEM_NAME}. Currently supported systems are: ${SUPPORTED_SYSTEMS}." )
endif()

# Set output directories.
set( CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin )
set( CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib )

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

# Platform libraries.
if( ${CMAKE_SYSTEM_NAME} STREQUAL "Linux" )
    # Provide an option to use the OpenSSL network abstraction on Linux.
    option( IOT_NETWORK_USE_OPENSSL
            "Set this to ON to use a network abstraction implemented on OpenSSL. When OFF, the mbed TLS network abstraction is used."
            OFF )

    if( ${IOT_NETWORK_USE_OPENSSL} )
        add_definitions( -DIOT_NETWORK_USE_OPENSSL=1 )
    endif()

    add_definitions( -DIOT_SYSTEM_TYPES_FILE="posix/iot_platform_types_posix.h" )
    add_subdirectory( platform/source/posix )
endif()

# Common libraries (linear containers, logging, etc.)
add_subdirectory( lib/source/common )

# MQTT library.
add_subdirectory( lib/source/mqtt )

# Shadow library.
add_subdirectory( lib/source/shadow )

# Serializer library.
add_subdirectory( lib/source/serializer )

# Defender library.
add_subdirectory( lib/source/defender )

# TinyCBOR library (third-party).
add_subdirectory( third_party/tinycbor )

# mbed TLS library (third-party).
add_subdirectory( third_party/mbedtls )

# Determine the demo executable to build based on system.
if( ${CMAKE_SYSTEM_NAME} STREQUAL "Linux" )
    add_subdirectory( demos/app/posix )
endif()

# Test executables.
if( ${IOT_BUILD_TESTS} )
    add_subdirectory( tests/ )
endif()

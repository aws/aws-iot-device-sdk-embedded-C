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
set( ALLOW_SHARED_LIBRARIES ON )

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
    else()
        message( FATAL_ERROR "${CMAKE_SYSTEM_NAME} is not a supported platform." )
    endif()
endif()

# Validate the platform name.
if( NOT DEFINED IOT_PLATFORM_NAME )
    message( FATAL_ERROR "IOT_PLATFORM_NAME was not set and could not be automatically determined." )
endif()

if( NOT EXISTS ${PROJECT_SOURCE_DIR}/ports/${IOT_PLATFORM_NAME} )
    message( FATAL_ERROR "A port for ${IOT_PLATFORM_NAME} does not exist." )
endif()

# Set output directories.
set( CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin )
set( CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib )

# Set the path to the config header.
if( ${IOT_BUILD_TESTS} )
    set( CONFIG_HEADER_PATH ${PROJECT_SOURCE_DIR}/tests )
    set( IOT_TEST_APP_SOURCE ${PROJECT_SOURCE_DIR}/tests/iot_tests.c )
else()
    set( CONFIG_HEADER_PATH ${PROJECT_SOURCE_DIR}/demos )
endif()

# Build Unity test framework when building tests.
if( ${IOT_BUILD_TESTS} )
    add_subdirectory( third_party/unity )
endif()

# Build the demos.
add_subdirectory( demos )

# Common libraries and platform port. This creates the iotbase library target.
add_subdirectory( libraries/standard/common )

# MQTT library.
add_subdirectory( libraries/standard/mqtt )

# Serializer library.
add_subdirectory( libraries/standard/serializer )

# AWS IoT common libraries.
add_subdirectory( libraries/aws/common )

# AWS IoT Shadow library.
add_subdirectory( libraries/aws/shadow )

# AWS IoT Jobs library.
add_subdirectory( libraries/aws/jobs )

# AWS IoT Device Defender library.
add_subdirectory( libraries/aws/defender )

# Onboarding library.
add_subdirectory( libraries/aws/onboarding )

# TinyCBOR library (third-party).
add_subdirectory( third_party/tinycbor )

# mbed TLS library (third-party).
if( NOT IOT_NETWORK_USE_OPENSSL )
    add_subdirectory( third_party/mbedtls )
endif()

# Set startup projects in Visual Studio.
if( ${IOT_BUILD_TESTS} )
    set_property( DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR} PROPERTY VS_STARTUP_PROJECT iot_tests_mqtt )
else()
    set_property( DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR} PROPERTY VS_STARTUP_PROJECT iot_demo_mqtt )
endif()

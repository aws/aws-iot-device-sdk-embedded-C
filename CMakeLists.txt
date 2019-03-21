# Project information.
cmake_minimum_required( VERSION 3.5.0 )
project( AwsIotDeviceSdkC
         VERSION 4.0.0
         LANGUAGES C )
add_definitions( -DIOT_SDK_VERSION="${PROJECT_VERSION}" )

# Use C99.
set( CMAKE_C_STANDARD 99 )
set( CMAKE_C_STANDARD_REQUIRED ON )

# Do not allow in-source build.
if( ${PROJECT_SOURCE_DIR} STREQUAL ${PROJECT_BINARY_DIR} )
    message( FATAL_ERROR "In-source build is not allowed. Please build in a separate directory, such as ${PROJECT_SOURCE_DIR}/build." )
endif()

# Check for system support.
list( APPEND SUPPORTED_SYSTEMS "Linux" )

if( NOT ${CMAKE_SYSTEM_NAME} IN_LIST SUPPORTED_SYSTEMS )
    message( FATAL_ERROR "Unsupported system: ${CMAKE_SYSTEM_NAME}. Currently supported systems are: ${SUPPORTED_SYSTEMS}." )
endif()

# Log compiler information
message("Compiler ID: ${CMAKE_C_COMPILER_ID}")
message("Compiler version: ${CMAKE_C_COMPILER_VERSION}")

# Set output directories.
set( CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin )
set( CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib )

# Atomic headers.
# If GCC --
# for version <4.7.0, __sync_* shall be called.
# for version >= 4.7.0, __atomic_* shall be called. 
# We only implemented atomic with __atomic_*. 
if( CMAKE_C_COMPILER_ID STREQUAL GNU AND ( CMAKE_C_COMPILER_VERSION VERSION_GREATER 4.7 OR CMAKE_C_COMPILER_VERSION VERSION_EQUAL 4.7 ) )
    add_definitions( -DCOMPILER_OPTION_GCC_ATOMIC_BUILTIN=1 )
endif()

# If Clang --
# Clang supports GCC's __atomic_* built-in functions since 3.1 release. 
if( CMAKE_C_COMPILER_ID STREQUAL Clang AND ( CMAKE_C_COMPILER_VERSION VERSION_GREATER 3.1 OR CMAKE_C_COMPILER_VERSION VERSION_EQUAL 3.1 ) )
    add_definitions( -DCOMPILER_OPTION_GCC_ATOMIC_BUILTIN=1 )
endif()

# SDK include paths.
include_directories( ${PROJECT_SOURCE_DIR}/lib/include
                     ${PROJECT_SOURCE_DIR}/platform/include
                     ${PROJECT_SOURCE_DIR}/third_party/include )

# Demo include path.
include_directories( ${PROJECT_SOURCE_DIR}/demos )

# Use either the demo or test configuration file.
if( ${IOT_BUILD_TESTS} )
    # Tests include directories.
    include_directories( ${PROJECT_SOURCE_DIR}/tests
                         tests/unity
                         tests/unity/fixture
                         tests/mqtt/access )

    # Tests config file.
    add_definitions( -DIOT_CONFIG_FILE="iot_tests_config.h" )

    # Build unity test framework.
    add_subdirectory( tests/unity )
else()
    add_definitions( -DIOT_CONFIG_FILE="iot_demo_config.h" )
endif()

# Platform libraries.
if( ${CMAKE_SYSTEM_NAME} STREQUAL "Linux" )
    add_definitions( -DIOT_SYSTEM_TYPES_FILE="posix/iot_platform_types_posix.h" )
    add_subdirectory( platform/source/posix )
endif()

# Thrid party libraries (tinycbor).
add_subdirectory( third_party/tinycbor )

# Common libraries (linear containers, logging, etc.)
add_subdirectory( lib/source/common )

# MQTT library.
add_subdirectory( lib/source/mqtt )

# Shadow library.
add_subdirectory( lib/source/shadow )

# Metrics library.
add_subdirectory( lib/source/metrics )

# Serializer library.
add_subdirectory( lib/source/serializer )

# Defender library.
add_subdirectory( lib/source/defender )

# Demo executables.
if( ${CMAKE_SYSTEM_NAME} STREQUAL "Linux" )
    add_subdirectory( demos/posix )
endif()

# Test executables.
if( ${IOT_BUILD_TESTS} )
    add_subdirectory( tests/ )
endif()

# Project information.
cmake_minimum_required( VERSION 3.5.0 )
project( AwsIotDeviceSdkEmbeddedC
         VERSION 4.0.1
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

# Import global configurations.
include("tools/cmake/filePaths.cmake")

# Configure options to always show in CMake GUI.
option( ATOMIC_USE_PORT
        "Set this to ON to use a custom atomic port. When OFF, the build system will choose an atomic port."
        OFF )
option( BUILD_TESTS
        "Set this to ON to build both demo and test executables. When OFF, only demo executables are built."
        ON )
option( BUILD_CLONE_SUBMODULES
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
if( NOT DEFINED _PLATFORM_NAME )
    if( ${CMAKE_SYSTEM_NAME} STREQUAL "Linux" )
        set( PLATFORM_NAME "posix" CACHE STRING "Port to use for building the SDK." )
    else()
        message( FATAL_ERROR "${CMAKE_SYSTEM_NAME} is not a supported platform." )
    endif()
endif()

# Validate the platform name.
if( NOT DEFINED PLATFORM_NAME )
    message( FATAL_ERROR "PLATFORM_NAME was not set and could not be automatically determined." )
endif()

# Set output directories.
set( CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin )
set( CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib )
set( CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib )

# Set the path to the config header.
if( ${BUILD_TESTS} )
    include("${ROOT_DIR}/tools/cmock/create_test.cmake")

    include_directories("${3RDPARTY_DIR}/CMock/vendor/unity/src/"
                        "${3RDPARTY_DIR}/CMock/vendor/unity/extras/fixture/src"
                        "${3RDPARTY_DIR}/CMock/vendor/unity/extras/memory/src"
                        "${3RDPARTY_DIR}/CMock/src"
            )
    link_directories("${CMAKE_BINARY_DIR}/lib"
            )

    add_library(cmock STATIC
            "${ROOT_DIR}/libraries/3rdparty/CMock/src/cmock.c"
            )

    set_target_properties(cmock PROPERTIES
            ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib
            POSITION_INDEPENDENT_CODE ON
            COMPILE_FLAGS "-Og"
            )

    add_library(unity STATIC
            "${3RDPARTY_DIR}/CMock/vendor/unity/src/unity.c"
            "${3RDPARTY_DIR}/CMock/vendor/unity/extras/fixture/src/unity_fixture.c"
            "${3RDPARTY_DIR}/CMock/vendor/unity/extras/memory/src/unity_memory.c"
            )
    set_target_properties(unity PROPERTIES
            ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib
            POSITION_INDEPENDENT_CODE ON
            )

    target_include_directories(cmock PUBLIC
            ${ROOT_DIR}/libraries/3rdparty/CMock/src
            ${ROOT_DIR}/libraries/3rdparty/CMock/vendor/unity/src/
            ${ROOT_DIR}/libraries/3rdparty/CMock/examples
            )
    target_link_libraries(cmock unity)

    add_custom_target(coverage
            COMMAND make && ${CMAKE_COMMAND} -P ${CMAKE_SOURCE_DIR}/tools/cmock/coverage.cmake
            DEPENDS http_utest cmock unity
            WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
            )
endif()

# Add libraries.
add_subdirectory( libraries )

# Build the demos.
add_subdirectory( demos )

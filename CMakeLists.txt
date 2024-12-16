# Project information.
cmake_minimum_required( VERSION 3.2.0 )
project( AwsIotDeviceSdkEmbeddedC
         VERSION 202412.00
         LANGUAGES C CXX )

# Allow the project to be organized into folders.
set_property( GLOBAL PROPERTY USE_FOLDERS ON )

# Use C90 if not specified.
if( NOT DEFINED CMAKE_C_STANDARD )
    set( CMAKE_C_STANDARD 90 )
endif()
if( NOT DEFINED CMAKE_C_STANDARD_REQUIRED )
    set( CMAKE_C_STANDARD_REQUIRED ON )
endif()

# Do not allow in-source build.
if( ${PROJECT_SOURCE_DIR} STREQUAL ${PROJECT_BINARY_DIR} )
    message( FATAL_ERROR "In-source build is not allowed. Please build in a separate directory, such as ${PROJECT_SOURCE_DIR}/build." )
endif()

# Set global path variables.
get_filename_component(__root_dir "${CMAKE_CURRENT_LIST_DIR}" ABSOLUTE)
set(ROOT_DIR ${__root_dir} CACHE INTERNAL "C SDK source root.")
set(DEMOS_DIR "${ROOT_DIR}/demos" CACHE INTERNAL "C SDK demos root.")
set(SYSTEM_TEST_DIR "${ROOT_DIR}/integration-test" CACHE INTERNAL "C SDK integration tests root.")
set(PLATFORM_DIR "${ROOT_DIR}/platform" CACHE INTERNAL "C SDK platform root.")
set(MODULES_DIR "${ROOT_DIR}/libraries" CACHE INTERNAL "C SDK modules root.")
set(3RDPARTY_DIR "${MODULES_DIR}/3rdparty" CACHE INTERNAL "3rdparty libraries root.")

include( "demos/logging-stack/logging.cmake" )

# Configure options to always show in CMake GUI.
option( BUILD_TESTS
        "Set this to ON to build test executables."
        OFF )
option( BUILD_DEMOS
        "Set this to ON to build demo executables."
        ON )
option( BUILD_CLONE_SUBMODULES
        "Set this to ON to automatically clone any required Git submodules. When OFF, submodules must be manually cloned."
        ON )
option( DOWNLOAD_CERTS
        "Set this to ON to automatically download certificates needed to run the demo. When OFF, certificates must be manually downloaded."
        ON )
option( INSTALL_PLATFORM_ABSTRACTIONS
        "Set this to ON to install POSIX platform abstractions that are used together with the C-SDK libraries in the demos."
        ON )
option( INSTALL_TO_SYSTEM
        "Set this to ON to install libraries and headers to the default system path (e.g. /usr/local/lib, /usr/local/include)."
        OFF )

# Unity test framework does not export the correct symbols for DLLs.
set( ALLOW_SHARED_LIBRARIES ON )

include( CMakeDependentOption )
CMAKE_DEPENDENT_OPTION( BUILD_SHARED_LIBS
                        "Set this to ON to build all libraries as shared libraries. When OFF, libraries build as static libraries."
                        ON "${ALLOW_SHARED_LIBRARIES}"
                        OFF )

# Set output directories.
set( CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin )
set( CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib )
set( CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib )

# Set prefix to PWD if any path flags are relative.
# PWD is set to the path where you run the cmake command.
if(DEFINED ENV{PWD})
    if(ROOT_CA_CERT_PATH AND NOT IS_ABSOLUTE ${ROOT_CA_CERT_PATH})
        set(ROOT_CA_CERT_PATH "$ENV{PWD}/${ROOT_CA_CERT_PATH}")
    endif()
    if(CLIENT_CERT_PATH AND NOT IS_ABSOLUTE ${CLIENT_CERT_PATH})
        set(CLIENT_CERT_PATH "$ENV{PWD}/${CLIENT_CERT_PATH}")
    endif()
    if(CLIENT_PRIVATE_KEY_PATH AND NOT IS_ABSOLUTE ${CLIENT_PRIVATE_KEY_PATH})
        set(CLIENT_PRIVATE_KEY_PATH "$ENV{PWD}/${CLIENT_PRIVATE_KEY_PATH}")
    endif()
endif()

# Build the tests if flag enabled.
if(BUILD_TESTS)
    enable_testing()
    include(${ROOT_DIR}/tools/cmock/cmock_dependencies.cmake)
endif()

include(GNUInstallDirs)

# Try installing to /opt if the directory exists, or use the home directory otherwise.
# One may turn on the INSTALL_TO_SYSTEM option to have it installed to the
# default system path for headers and libraries.

# Set the install directory for header files.
if(INSTALL_TO_SYSTEM)
    set(CSDK_HEADER_INSTALL_PATH "${CMAKE_INSTALL_INCLUDEDIR}/aws")
else()
    if(NOT DEFINED CSDK_HEADER_INSTALL_PATH)
        set(CSDK_HEADER_INSTALL_PATH "${ROOT_DIR}/project/include")
    endif()
endif()
install(DIRECTORY DESTINATION ${CSDK_HEADER_INSTALL_PATH})
# Set the install directory for shared libraries.
if(INSTALL_TO_SYSTEM)
    set(CSDK_LIB_INSTALL_PATH "${CMAKE_INSTALL_LIBDIR}")
else()
    if(NOT DEFINED CSDK_LIB_INSTALL_PATH)
        set(CSDK_LIB_INSTALL_PATH "${ROOT_DIR}/project/lib")
    endif()
endif()
install(DIRECTORY DESTINATION ${CSDK_LIB_INSTALL_PATH})

# Find thread library.
set(THREADS_PREFER_PTHREAD_FLAG ON)
find_package(Threads)

# Add libraries.
add_subdirectory( libraries )

# Add platform.
add_subdirectory( platform )

# Create the `install` target by including this file.
include( tools/cmake/install.cmake )
# Define any shared CMake utility functions.
include( tools/cmake/utility.cmake )

# Make THING_NAME an alias for CLIENT_IDENTIFIER
set_alias( "CLIENT_IDENTIFIER" ALIASES "THING_NAME" )

if(BUILD_TESTS)
    # Add build configuration for integration tests.
    add_subdirectory( integration-test )
endif()
if(BUILD_DEMOS)
    # Add build configuration for demos.
    add_subdirectory( demos )
endif()

if(DOWNLOAD_CERTS)
    if(BUILD_TESTS)
        set(CERT_DOWNLOAD_DIR ${SYSTEM_TEST_DIR}/certificates)
    else()
        set(CERT_DOWNLOAD_DIR ${DEMOS_DIR}/certificates)
    endif()
    set(CERT_DOWNLOAD_DIR ${DEMOS_DIR}/certificates)
    file(MAKE_DIRECTORY ${CERT_DOWNLOAD_DIR})
    # Download the Amazon Root CA certificate.
    message( "Downloading the Amazon Root CA certificate..." )
    execute_process(
        COMMAND curl --url https://www.amazontrust.com/repository/AmazonRootCA1.pem
        -o ${CERT_DOWNLOAD_DIR}/AmazonRootCA1.crt
    )
    # Copy certificates to the build directory.
    file(COPY "${CERT_DOWNLOAD_DIR}"
      DESTINATION ${CMAKE_RUNTIME_OUTPUT_DIRECTORY})
    if(BUILD_TESTS)
        file(COPY "${CERT_DOWNLOAD_DIR}"
             DESTINATION ${CMAKE_RUNTIME_OUTPUT_DIRECTORY}/tests)
    endif()
endif()

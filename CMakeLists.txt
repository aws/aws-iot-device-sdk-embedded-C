# Project information.
cmake_minimum_required( VERSION 3.13.0 )
project( AwsIotDeviceSdkEmbeddedC
         VERSION 4.0.2
         LANGUAGES C )

# Allow the project to be organized into folders.
set_property( GLOBAL PROPERTY USE_FOLDERS ON )

# Use C90.
set( CMAKE_C_STANDARD 90 )
set( CMAKE_C_STANDARD_REQUIRED ON )

# Do not allow in-source build.
if( ${PROJECT_SOURCE_DIR} STREQUAL ${PROJECT_BINARY_DIR} )
    message( FATAL_ERROR "In-source build is not allowed. Please build in a separate directory, such as ${PROJECT_SOURCE_DIR}/build." )
endif()

# Set global path variables.
get_filename_component(__root_dir "${CMAKE_CURRENT_LIST_DIR}" ABSOLUTE)
set(ROOT_DIR ${__root_dir} CACHE INTERNAL "C SDK source root.")
set(DEMOS_DIR "${ROOT_DIR}/demos" CACHE INTERNAL "C SDK demos root.")
set(PLATFORM_DIR "${ROOT_DIR}/platform" CACHE INTERNAL "C SDK platform root.")
set(MODULES_DIR "${ROOT_DIR}/libraries" CACHE INTERNAL "C SDK modules root.")
set(3RDPARTY_DIR "${MODULES_DIR}/3rdparty" CACHE INTERNAL "3rdparty libraries root.")

include( "demos/logging-stack/logging.cmake" )

# Configure options to always show in CMake GUI.
option( BUILD_TESTS
        "Set this to ON to build both demo and test executables. When OFF, only demo executables are built."
        OFF )
option( BUILD_CLONE_SUBMODULES
        "Set this to ON to automatically clone any required Git submodules. When OFF, submodules must be manually cloned."
        ON )
option( DOWNLOAD_CERTS
        "Set this to ON to automatically download certificates needed to run the demo. When OFF, certificates must be manually downloaded." 
        ON )

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

# Add libraries.
add_subdirectory( libraries )

# Add platform.
add_subdirectory( platform )

# Build the demos.
add_subdirectory( demos )

# Build the tests if flag enabled.
if(${BUILD_TESTS})
    enable_testing()
    # Check if the CMock source directory exists.	
    if( NOT EXISTS ${3RDPARTY_DIR}/CMock/src )	
        # Attempt to clone CMock.	
        if( ${BUILD_CLONE_SUBMODULES} )	
            find_package( Git REQUIRED )	

            message( "Cloning submodule CMock." )	
            execute_process( COMMAND ${GIT_EXECUTABLE} submodule update --init --recursive libraries/3rdparty/CMock	
                                WORKING_DIRECTORY ${PROJECT_SOURCE_DIR}	
                                RESULT_VARIABLE CMOCK_CLONE_RESULT )	

            if( NOT ${CMOCK_CLONE_RESULT} STREQUAL "0" )	
                message( FATAL_ERROR "Failed to clone CMock submodule." )	
            endif()	
        else()	
            message( FATAL_ERROR "The required submodule CMock does not exist. Either clone it manually, or set BUILD_CLONE_SUBMODULES to 1 to automatically clone it during build." )	
        endif()	
    endif()

    include("${ROOT_DIR}/tools/cmock/create_test.cmake")

    include_directories("${3RDPARTY_DIR}/CMock/vendor/unity/src/"
                    "${3RDPARTY_DIR}/CMock/vendor/unity/extras/fixture/src"
                    "${3RDPARTY_DIR}/CMock/vendor/unity/extras/memory/src"
                    "${3RDPARTY_DIR}/CMock/src"
        )
    link_directories("${CMAKE_BINARY_DIR}/lib"
        )

    # Create a list for each unit test target
    set(utest_targets 
            http_utest mqtt_utest 
            mqtt_lightweight_utest mqtt_state_utest 
            http_send_utest sockets_utest)

    # Add a target for running coverage on tests.
    add_custom_target(coverage
        COMMAND ${CMAKE_COMMAND} -DROOT_DIR=${ROOT_DIR}
        -P ${CMAKE_SOURCE_DIR}/tools/cmock/coverage.cmake
        DEPENDS cmock unity ${utest_targets}
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    )
endif()

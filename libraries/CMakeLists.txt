# Configuration for CMock if testing is enabled.
if( ${BUILD_TESTS} )
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

    # Include the 3rdparty CMakeLists.txt for CMock build configuration.
    add_subdirectory(${3RDPARTY_DIR})

    # Add a target for running coverage on tests.
    add_custom_target(coverage
        COMMAND ${CMAKE_COMMAND} -P ${CMAKE_SOURCE_DIR}/tools/cmock/coverage.cmake
        DEPENDS cmock unity http_utest mqtt_utest mqtt_lightweight_utest mqtt_state_utest http_send_utest
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
    )
endif()
            
# Add all CMakeLists.txts in the standard folder.
file(GLOB standard_modules "${MODULES_DIR}/standard/*")
foreach(module IN LISTS standard_modules )
    if(IS_DIRECTORY "${module}" AND EXISTS "${module}/CMakeLists.txt")
        add_subdirectory(${module})
    endif()
endforeach()
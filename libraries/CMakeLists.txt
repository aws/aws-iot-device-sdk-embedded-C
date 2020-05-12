
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
            COMMAND ${CMAKE_COMMAND} -P ${CMAKE_SOURCE_DIR}/tools/cmock/coverage.cmake
            DEPENDS cmock unity http_utest mqtt_utest
            WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
            )
endif()

# Add standard modules
file(GLOB standard_modules "${MODULES_DIR}/standard/*")
foreach(module IN LISTS standard_modules)
    if(IS_DIRECTORY "${module}" AND EXISTS "${module}/CMakeLists.txt")
        add_subdirectory(${module})
    endif()
endforeach()

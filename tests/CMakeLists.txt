message("building linux specific Unit Test port")
set(CMAKE_INSTALL_RPATH_USE_LINK_PATH TRUE)
set_property(GLOBAL PROPERTY TARGET_SUPPORTS_SHARED_LIBS TRUE)
set (CMAKE_MODULE_PATH ${CMAKE_SOURCE_DIR}/tools/cmock)

include(create_test)
include_directories(
        "${CMAKE_CURRENT_LIST_DIR}/config_files"
        "${CMAKE_CURRENT_LIST_DIR}/utils"
        "${ROOT_DIR}/libraries/c_sdk/standard/common/include/private"
        "${ROOT_DIR}/freertos_kernel/include"
        "${ROOT_DIR}/libraries/3rdparty/tracealyzer_recorder/Include"
        "${ROOT_DIR}/libraries/3rdparty/CMock/vendor/unity/src/"
        "${ROOT_DIR}/libraries/3rdparty/CMock/src"
        )
link_directories("${CMAKE_BINARY_DIR}/lib"
        )

add_library(cmock  STATIC
        ${ROOT_DIR}/libraries/3rdparty/CMock/src/cmock.c
        )

set_target_properties(cmock PROPERTIES
        ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib
        POSITION_INDEPENDENT_CODE ON
        COMPILE_FLAGS "-Og"
        )

add_library(unity STATIC
        ${ROOT_DIR}/libraries/3rdparty/CMock/vendor/unity/src/unity.c
        )
set_target_properties(unity PROPERTIES
        ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib
        POSITION_INDEPENDENT_CODE ON
        )

target_include_directories(cmock PUBLIC
        ${ROOT_DIR}/libraries/3rdparty/CMock/src
        )
target_link_libraries(cmock libunity.a)

add_custom_target(coverage
        COMMAND ${CMAKE_COMMAND} -P ${CMAKE_SOURCE_DIR}/tools/cmock/coverage.cmake
        DEPENDS http_utest cmock unity
        WORKING_DIRECTORY ${CMAKE_BINARY_DIR}
        )

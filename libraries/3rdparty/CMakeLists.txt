# Build Configuration for CMock and Unity libraries.
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

# jsmn
add_library(jsmn INTERFACE IMPORTED GLOBAL)
target_sources(jsmn
    INTERFACE
    "${3RDPARTY_DIR}/jsmn/jsmn.h"
    "${3RDPARTY_DIR}/jsmn/jsmn.c"
)
target_include_directories(jsmn
    SYSTEM INTERFACE
    "${3RDPARTY_DIR}/jsmn"
)

# tinycbor
add_library(tinycbor INTERFACE IMPORTED GLOBAL)
target_sources(tinycbor
    INTERFACE
    "${3RDPARTY_DIR}/tinycbor/src/cborpretty.c"
    "${3RDPARTY_DIR}/tinycbor/src/cborpretty_stdio.c"
    "${3RDPARTY_DIR}/tinycbor/src/cborencoder.c"
    "${3RDPARTY_DIR}/tinycbor/src/cborencoder_close_container_checked.c"
    "${3RDPARTY_DIR}/tinycbor/src/cborerrorstrings.c"
    "${3RDPARTY_DIR}/tinycbor/src/cborparser.c"
    "${3RDPARTY_DIR}/tinycbor/src/cborparser_dup_string.c"
)
target_include_directories(tinycbor
    SYSTEM INTERFACE
    "${3RDPARTY_DIR}/tinycbor/src"
)

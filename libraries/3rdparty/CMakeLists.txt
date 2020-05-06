# -------------------------------------------------------------------------------------------------
# 3rdparty libraries
# -------------------------------------------------------------------------------------------------
# unity - test framework
if(EXISTS "${3RDPARTY_DIR}/unity")
    add_library(3rdparty::unity INTERFACE IMPORTED GLOBAL)
    target_sources(
        3rdparty::unity INTERFACE
        "${3RDPARTY_DIR}/unity/src/unity.c"
        "${3RDPARTY_DIR}/unity/src/unity.h"
        "${3RDPARTY_DIR}/unity/src/unity_internals.h"
        "${3RDPARTY_DIR}/unity/extras/fixture/src/unity_fixture.c"
        "${3RDPARTY_DIR}/unity/extras/fixture/src/unity_fixture.h"
        "${3RDPARTY_DIR}/unity/extras/fixture/src/unity_fixture_internals.h"
        "${3RDPARTY_DIR}/unity/extras/fixture/src/unity_fixture_malloc_overrides.h"
    )
    target_include_directories(
        3rdparty::unity INTERFACE
        "${3RDPARTY_DIR}/unity/src"
        "${3RDPARTY_DIR}/unity/examples"
        "${3RDPARTY_DIR}/unity/extras/fixture/src"
    )
    target_compile_definitions(3rdparty::unity INTERFACE UNITY_INCLUDE_CONFIG_H)
endif()

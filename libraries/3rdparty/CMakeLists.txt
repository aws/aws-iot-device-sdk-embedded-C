if(${BUILD_TESTS})
    if( NOT EXISTS ${3RDPARTY_DIR}/CMock/.git )
        # Attempt to clone submodule.
        if( ${BUILD_CLONE_SUBMODULES} )
            clone_library( ${submodule_dir} 0 )
        else()
            message( FATAL_ERROR "A required submodule does not exist. Either clone it manually, or set BUILD_CLONE_SUBMODULES to 1 to automatically clone it during build." )
        endif()
    endif()

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
endif()

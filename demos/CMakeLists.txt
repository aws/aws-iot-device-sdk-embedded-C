# Include each subdirectory that has a CMakeLists.txt file in it
file(GLOB demo_dirs "${DEMOS_DIR}/*/*")
foreach(demo_dir IN LISTS demo_dirs)
    if(IS_DIRECTORY "${demo_dir}" AND EXISTS "${demo_dir}/CMakeLists.txt")
        get_filename_component( DEMO_EXE_NAME ${demo_dir} NAME )
        add_subdirectory(${demo_dir})
    endif()
endforeach()

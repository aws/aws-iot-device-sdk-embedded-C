# Include filepaths for source and include.
include(filePaths.cmake)

if(BUILD_TESTS)
    add_subdirectory(utest)
endif()

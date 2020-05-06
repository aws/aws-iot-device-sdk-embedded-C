# Include filepaths for source and include.
include(filePaths.cmake)

if(IOT_BUILD_TESTS)
    add_subdirectory(utest)
endif()

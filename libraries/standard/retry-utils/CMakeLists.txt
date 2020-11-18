# Include file path configuration for retry utils library.
include(retryUtilsFilePaths.cmake)

# Library target for retry utils.
add_library( retry_utils
               ${RETRY_UTILS_SOURCES} )

target_include_directories( retry_utils
                              PUBLIC
                                ${RETRY_UTILS_INCLUDE_PUBLIC_DIRS} )

# Include unit tests.
if(BUILD_TESTS)
    add_subdirectory(${CMAKE_CURRENT_LIST_DIR}/utest)
endif()

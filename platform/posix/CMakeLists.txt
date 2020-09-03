# Include filepaths for source and include.
include(posixFilePaths.cmake)

# Create target for POSIX implementation of reconnect logic.
add_library( clock_posix 
               "clock_posix.c" )

target_include_directories( clock_posix 
                              PRIVATE 
                                ${PLATFORM_DIR}/include )

# Create target for POSIX implementation of retry logic.
add_library( retry_utils_posix 
               ${RETRY_SOURCES} )

target_include_directories( retry_utils_posix 
                              PUBLIC 
                                ${RETRY_INCLUDE_PUBLIC_DIRS}
                                ${LOGGING_INCLUDE_DIRS} )

if(BUILD_TESTS)
  add_subdirectory(utest)
endif()

# Add the transport targets
add_subdirectory( ${CMAKE_CURRENT_LIST_DIR}/transport )

# Include filepaths for source and include.
include(posixFilePaths.cmake)

# Create target for POSIX implementation of reconnect logic.
add_library( clock_posix
               "clock_posix.c" )

target_include_directories( clock_posix
                              PRIVATE
                                ${PLATFORM_DIR}/include )

if(BUILD_TESTS)
  add_subdirectory(utest)
endif()

# Add the transport targets
add_subdirectory( ${CMAKE_CURRENT_LIST_DIR}/transport )

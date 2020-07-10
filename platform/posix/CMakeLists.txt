# Create target for POSIX implementation of reconnect logic.
add_library( clock_posix 
               "clock_posix.c" )

target_include_directories( clock_posix 
                              PRIVATE 
                                ${PLATFORM_DIR}/include )

# Add the transport targets
add_subdirectory( ${CMAKE_CURRENT_LIST_DIR}/transport )

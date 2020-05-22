# Logging target.
add_library( logging 
             ${CMAKE_CURRENT_LIST_DIR}/posix/clock_posix.c )

# Logging target include path. 
target_include_directories( logging 
                            PUBLIC 
                                ${CMAKE_CURRENT_LIST_DIR}/include
                                ${MODULES_DIR}/demos/logging-stack )

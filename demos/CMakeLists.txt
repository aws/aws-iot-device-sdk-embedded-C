# Common application source files.
set( DEMO_APP_SOURCES
     app/iot_demo.c
     app/iot_demo_arguments.c )

# Common demo header files.
set( DEMO_COMMON_HEADERS
     include/iot_clock.h
     include/iot_logging.h )

# List all the demo functions, source files, and library dependencies here.
#
# The list order matters: Each demo must be at the same index in each list.
# For example, if the MQTT demo function is at DEMO_MAIN_FUNCTIONS[0], then
# the MQTT demo source must be at DEMO_SOURCES[0] and the MQTT library must
# be at DEMO_LIBRARY_DEPENDENCY[0].
#
# If a demo has multiple dependencies, place a semicolon-separated list in
# DEMO_LIBRARY_DEPENDENCY. The semicolon itself must be escaped as \\\;

# Create demo sources by listing directories in cwd
set( DEMO_LIBARY_NAMES
     "mqtt" )

set( DEMO_LIBRARY_DEPENDENCIES
     iotmqtt )

# Get the list length to iterate over it. Since CMake indexes from 0, subtract
# 1 for the iteration range.
list( LENGTH DEMO_LIBRARY_DEPENDENCIES DEMO_LIBRARY_COUNT )
math( EXPR DEMO_LIBRARY_COUNT "${DEMO_LIBRARY_COUNT}-1" )

foreach( i RANGE ${DEMO_LIBRARY_COUNT} )
    list( GET DEMO_LIBARY_NAMES ${i} CURRENT_NAME )
    list( GET DEMO_LIBRARY_DEPENDENCIES ${i} CURRENT_DEPENDENCY )
    # Include submodules
    file(GLOB demo_dirs "${DEMOS_DIR}/${CURRENT_NAME}/*")
    foreach(demo_dir IN LISTS demo_dirs)
        if(IS_DIRECTORY "${demo_dir}" AND EXISTS "${demo_dir}/CMakeLists.txt")
            add_subdirectory( demo_dir )
            message("${demo_dir}")
        endif()
    endforeach()

endforeach()

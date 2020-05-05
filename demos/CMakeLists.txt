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

# Get the list length to iterate over it. Since CMake indexes from 0, subtract
# 1 for the iteration range.
list( LENGTH DEMO_LIBRARY_DEPENDENCIES DEMO_LIBRARY_COUNT )
math( EXPR DEMO_LIBRARY_COUNT "${DEMO_LIBRARY_COUNT}-1" )

set( CONFIG_HEADER config.h )

file(GLOB demo_dirs "${DEMOS_DIR}/*/*")
foreach(demo_dir IN LISTS demo_dirs)
    if(IS_DIRECTORY "${demo_dir}" AND EXISTS "${demo_dir}/CMakeLists.txt")
    get_filename_component( DEMO_EXE_NAME ${demo_dir} NAME )
        add_subdirectory(${demo_dir})
        # Add the demo executable.
        #add_executable( ${DEMO_EXE_NAME}
        #                "${DEMO_EXE_NAME}.c"
        #                ${CONFIG_HEADER} )
        #target_link_libraries( ${DEMO_EXE_NAME} PRIVATE ${CURRENT_DEPENDENCY} )
    endif()
endforeach()

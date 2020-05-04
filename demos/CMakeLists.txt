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
    # Create executables from submodules
    file(GLOB afr_demos "${AFR_DEMOS_DIR}/*")
    foreach(demo IN LISTS afr_demos)
        if(IS_DIRECTORY "${demo}" AND EXISTS "${demo}/CMakeLists.txt")
            afr_add_subdirectory("${demo}")
        endif()
    endforeach()

    file(GLOB children RELATIVE ${})
    # Read the demo function, source, and dependency from each list.
    list( GET DEMO_MAIN_FUNCTIONS ${i} CURRENT_DEMO_FUNCTION )
    list( GET DEMO_SOURCES ${i} CURRENT_DEMO_SOURCE )
    list( GET DEMO_LIBRARY_DEPENDENCY ${i} CURRENT_DEMO_LIBRARY )

    # Get the name of the demo executable. This is the name of the demo source
    # without the .c file extension.
    get_filename_component( DEMO_EXE_NAME ${CURRENT_DEMO_SOURCE} NAME_WE )

    # Add the demo executable.
    add_executable( ${DEMO_EXE_NAME}
                    ${CURRENT_DEMO_SOURCE}
                    ${DEMO_APP_SOURCES}
                    ${DEMO_COMMON_HEADERS}
                    ${CONFIG_HEADER} )

    # Set the demo function to run.
    target_compile_definitions( ${DEMO_EXE_NAME}
                                PRIVATE RunDemo=${CURRENT_DEMO_FUNCTION} )

    # Set additional defines when testing the demos.
    if( ${IOT_BUILD_TESTS} )
        target_compile_definitions( ${DEMO_EXE_NAME} PRIVATE
                                    IOT_TEST_DEMO=1 )
    endif()

    # Add the include path for the demo application.
    target_include_directories( ${DEMO_EXE_NAME} PRIVATE include )

    # Link iotbase. All demos require this.
    target_link_libraries( ${DEMO_EXE_NAME} PRIVATE iotbase )

    # Link the unique dependency of each demo.
    target_link_libraries( ${DEMO_EXE_NAME} PRIVATE ${CURRENT_DEMO_LIBRARY} )

    # When building tests, link the Unity test framework.
    if( ${IOT_BUILD_TESTS} )
        target_link_libraries( ${DEMO_EXE_NAME} PRIVATE unity )
    endif()

    # Organize the demo into folders.
    set_property( TARGET ${DEMO_EXE_NAME} PROPERTY FOLDER demos )
    source_group( app FILES ${DEMO_APP_SOURCES} )
    source_group( include FILES ${DEMO_COMMON_HEADERS} )
    source_group( src FILES ${CURRENT_DEMO_SOURCE} )
    source_group( "" FILES ${CONFIG_HEADER} )
endforeach()

# Add build configuration for all 3rd party modules.
add_subdirectory(${3RDPARTY_DIR})

# Macro utility to clone the coreMQTT submodule.
macro( clone_mqtt )
        find_package( Git REQUIRED )
        message( "Cloning submodule coreMQTT." )
        execute_process( COMMAND rm -rf ${MODULES_DIR}/standard/coreMQTT
                         COMMAND ${GIT_EXECUTABLE} submodule update --init --recursive libraries/standard/coreMQTT
                         WORKING_DIRECTORY ${ROOT_DIR}
                         RESULT_VARIABLE MQTT_CLONE_RESULT )

        if( NOT ${MQTT_CLONE_RESULT} STREQUAL "0" )
                message( FATAL_ERROR "Failed to clone coreMQTT submodule." )
        endif()
endmacro()

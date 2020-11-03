# Add build configuration for all 3rd party modules.
add_subdirectory(${3RDPARTY_DIR})

# Macro utility to clone the coreMQTT submodule.
macro( clone_library submodule_dir )
        find_package( Git REQUIRED )
        execute_process( COMMAND rm -rf ${submodule_dir}
                         COMMAND ${GIT_EXECUTABLE} submodule update --init --recursive ${submodule_dir}
                         WORKING_DIRECTORY ${ROOT_DIR}
                         RESULT_VARIABLE LIB_CLONE_RESULT )

        if( NOT ${LIB_CLONE_RESULT} STREQUAL "0" )
                message( FATAL_ERROR "Failed to clone submodule." )
        endif()
endmacro()

set(SUBMODULE_DIRS
      ${MODULES_DIR}/standard/coreHTTP
      ${MODULES_DIR}/standard/coreJSON
      ${MODULES_DIR}/standard/coreMQTT
      ${MODULES_DIR}/aws/device-defender-for-aws-iot-embedded-sdk
      ${MODULES_DIR}/aws/device-shadow-for-aws-iot-embedded-sdk
      ${MODULES_DIR}/aws/jobs-for-aws-iot-embedded-sdk )

foreach(submodule_dir IN ITEMS ${SUBMODULE_DIRS})
    if( NOT EXISTS ${submodule_dir}/.git )
        # Attempt to clone submodule.
        if( ${BUILD_CLONE_SUBMODULES} )
            clone_library( ${submodule_dir} )
        else()
            message( FATAL_ERROR "A required submodule does not exist. Either clone it manually, or set BUILD_CLONE_SUBMODULES to 1 to automatically clone it during build." )
        endif()
    endif()
endforeach()

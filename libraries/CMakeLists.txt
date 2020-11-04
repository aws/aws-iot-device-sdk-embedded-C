# Macro utility to clone a library and source-related submodules.
macro( clone_path path )
    find_package( Git REQUIRED )
    # Attempt to clone submodules.
    if( ${BUILD_CLONE_SUBMODULES} )
        execute_process( COMMAND ${GIT_EXECUTABLE} submodule update --init --recursive -- ${path}
                         WORKING_DIRECTORY ${ROOT_DIR}
                         RESULT_VARIABLE LIB_CLONE_RESULT )
        if( NOT ${LIB_CLONE_RESULT} STREQUAL "0" )
            message( FATAL_ERROR "Failed to clone submodules." )
        endif()
    endif()
endmacro()

clone_path( ${MODULES_DIR} )

set( LIBRARY_SUBMODULES
       ${MODULES_DIR}/standard/coreHTTP
       ${MODULES_DIR}/standard/coreJSON
       ${MODULES_DIR}/standard/coreMQTT
       ${MODULES_DIR}/aws/device-defender-for-aws-iot-embedded-sdk
       ${MODULES_DIR}/aws/device-shadow-for-aws-iot-embedded-sdk
       ${MODULES_DIR}/aws/jobs-for-aws-iot-embedded-sdk )

foreach(submodule_dir IN ITEMS ${LIBRARY_SUBMODULES})
    if( NOT EXISTS ${submodule_dir}/.git )
        message( FATAL_ERROR "The required submodule {} does not exist. Either clone it manually, or set BUILD_CLONE_SUBMODULES to 1 to automatically clone it during build." )
    endif()
endforeach()

# Add build configuration for all 3rd party modules.
add_subdirectory(${3RDPARTY_DIR})

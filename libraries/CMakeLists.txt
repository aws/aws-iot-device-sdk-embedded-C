# Add build configuration for all 3rd party modules.
add_subdirectory(${3RDPARTY_DIR})

# Macro utility to clone a library and source-related submodules.
macro( clone_library submodule_dir clone_source )
    find_package( Git REQUIRED )
    execute_process( COMMAND rm -rf ${submodule_dir}
                        COMMAND ${GIT_EXECUTABLE} submodule update --init ${submodule_dir}
                        WORKING_DIRECTORY ${ROOT_DIR}
                        RESULT_VARIABLE LIB_CLONE_RESULT )
    if( NOT ${LIB_CLONE_RESULT} STREQUAL "0" )
        message( FATAL_ERROR "Failed to clone submodule ${submodule_dir}." )
    endif()
    if(${clone_source})
        # Sources may have submodules like from the depedency directory
        execute_process( COMMAND ${GIT_EXECUTABLE} submodule update --init -- source
                            WORKING_DIRECTORY ${submodule_dir}
                            RESULT_VARIABLE LIB_CLONE_RESULT )
        if( NOT ${LIB_CLONE_RESULT} STREQUAL "0" )
            message( FATAL_ERROR "Failed to submodules from sources." )
        endif()
    endif()
endmacro()

set( LIBRARY_SUBMODULES
       ${MODULES_DIR}/standard/coreHTTP
       ${MODULES_DIR}/standard/coreJSON
       ${MODULES_DIR}/standard/coreMQTT
       ${MODULES_DIR}/aws/device-defender-for-aws-iot-embedded-sdk
       ${MODULES_DIR}/aws/device-shadow-for-aws-iot-embedded-sdk
       ${MODULES_DIR}/aws/jobs-for-aws-iot-embedded-sdk )

foreach(submodule_dir IN ITEMS ${LIBRARY_SUBMODULES})
    if( NOT EXISTS ${submodule_dir}/.git )
        # Attempt to clone submodule.
        if( ${BUILD_CLONE_SUBMODULES} )
            clone_library( ${submodule_dir} 1 )
        else()
            message( FATAL_ERROR "A required submodule does not exist. Either clone it manually, or set BUILD_CLONE_SUBMODULES to 1 to automatically clone it during build." )
        endif()
    endif()
endforeach()

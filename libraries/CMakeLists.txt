# Macro utility to clone a library and source-related submodules.
macro( clone_path path )
    # Attempt to clone submodules.
    if( ${BUILD_CLONE_SUBMODULES} )
        find_package( Git REQUIRED )
        execute_process( COMMAND ${GIT_EXECUTABLE} submodule update --init --recursive ${ARGV1} -- ${path}
                         WORKING_DIRECTORY ${ROOT_DIR}
                         RESULT_VARIABLE LIB_CLONE_RESULT )
        if( NOT ${LIB_CLONE_RESULT} STREQUAL "0" )
            message( FATAL_ERROR "Failed to clone submodules." )
        endif()
    endif()
endmacro()

# Clone the submodules only if this is a Git repo.
if( EXISTS ${ROOT_DIR}/.git )
    clone_path( ${MODULES_DIR} )
    clone_path( ${MODULES_DIR}/standard/corePKCS11 "--checkout" )
endif()

# Add build configuration for all 3rd party modules.
add_subdirectory(${3RDPARTY_DIR})

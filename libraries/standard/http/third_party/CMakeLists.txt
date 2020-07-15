# Check if the http_parser source directory exists.
if( NOT EXISTS ${CMAKE_CURRENT_LIST_DIR}/http_parser/http_parser.c )
    # Attempt to clone http_parser.
    if( ${BUILD_CLONE_SUBMODULES} )
        find_package( Git REQUIRED )

        message( "Cloning submodule http_parser." )
        execute_process( COMMAND ${GIT_EXECUTABLE} submodule update --init --recursive http_parser
                        WORKING_DIRECTORY ${CMAKE_CURRENT_LIST_DIR}
                        RESULT_VARIABLE HTTP_PARSER_CLONE_RESULT )

        if( NOT ${HTTP_PARSER_CLONE_RESULT} STREQUAL "0" )
            message( FATAL_ERROR "Failed to clone http_parser submodule." )
        endif()
    else()
        message( FATAL_ERROR "The required submodule http_parser does not exist. Either clone it manually, or set BUILD_CLONE_SUBMODULES to 1 to automatically clone it during build." )
    endif()
endif()

# http_parser library target.
add_library( http_parser
             ${CMAKE_CURRENT_LIST_DIR}/http_parser/http_parser.c )

# http_parser public include path.
target_include_directories( http_parser PUBLIC 
                                        ${CMAKE_CURRENT_LIST_DIR}/http_parser )

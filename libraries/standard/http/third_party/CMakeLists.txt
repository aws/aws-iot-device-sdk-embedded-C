# http_parser library target.
add_library( http_parser
             ${CMAKE_CURRENT_LIST_DIR}/http_parser/http_parser.c )

# http_parser public include path.
target_include_directories( http_parser PUBLIC 
                                        ${CMAKE_CURRENT_LIST_DIR}/http_parser )

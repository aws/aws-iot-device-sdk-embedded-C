# Include filepaths for source and include.
include(httpFilePaths.cmake)

# Add http_parser submodule to HTTP client library.
add_subdirectory( third_party )

# HTTP library target.
add_library( http
             ${HTTP_SOURCES} )

# HTTP public include path.
target_include_directories( http PUBLIC ${HTTP_INCLUDE_PUBLIC_DIRS}
                                        ${LOGGING_INCLUDE_DIRS}
                                        ${CMAKE_CURRENT_LIST_DIR}/utest )

# HTTP private include path.
target_include_directories( http PRIVATE ${HTTP_INCLUDE_PRIVATE_DIRS} )

# Link http_parser to http target.
target_link_libraries( http PRIVATE http_parser )

# Organization of HTTP in IDE projects.
set_target_properties( http PROPERTIES FOLDER libraries/standard )
source_group( include FILES include/http_client.h )
source_group( src FILES ${HTTP_SOURCES} )
source_group( src\\private FILES src/private/http_internal.h )

if(BUILD_TESTS)
    add_subdirectory(utest)
endif()

# Include filepaths for source and include.
include(filePaths.cmake)

# HTTP library target.
add_library( http
             ${HTTP_SOURCES} )

# HTTP public include path.
target_include_directories( http PUBLIC ${HTTP_INCLUDE_PUBLIC_DIRS} )

# HTTP private include path.
target_include_directories( http PRIVATE ${HTTP_INCLUDE_PRIVATE_DIRS} )

# Organization of HTTP in IDE projects.
set_target_properties( http PROPERTIES FOLDER libraries/standard )
source_group( include FILES include/http_client.h )
source_group( src FILES ${HTTP_SOURCES} )
source_group( src\\private FILES src/private/http_internal.h src/private/http_client_parse.h )

if(BUILD_TESTS)
    add_subdirectory(utest)
endif()

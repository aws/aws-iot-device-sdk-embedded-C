# Include filepaths for source and include.
include(filePaths.cmake)

# HTTP library target.
add_library( iothttp
             ${HTTP_SOURCES}
             include/http_client.h )

# HTTP public include path.
target_include_directories( iothttp PUBLIC ${HTTP_INCLUDE_PUBLIC_DIRS} )

# Organization of HTTP in folders.
set_property( TARGET iothttp PROPERTY FOLDER libraries/standard )
source_group( include FILES include/http_client.h )
source_group( src FILES ${HTTP_SOURCES} )

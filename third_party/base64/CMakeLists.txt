# Tinycbor library source files.
add_library( base64 SHARED
             base64.c )

# Library version.
set_target_properties( base64 PROPERTIES VERSION ${PROJECT_VERSION} )
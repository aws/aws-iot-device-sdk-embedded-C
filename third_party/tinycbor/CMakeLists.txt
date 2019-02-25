# Tinycbor library source files.
add_library( tinycbor SHARED
             cborencoder.c
             cborencoder_close_container_checked.c
             cborerrorstrings.c
             cborparser.c 
             cborparser_dup_string.c
             cborpretty.c )

# Library version.
set_target_properties( tinycbor PROPERTIES VERSION ${PROJECT_VERSION} )
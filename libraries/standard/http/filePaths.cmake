# This file is to add source files and include directories
# into variables so that it can be reused from different repositories
# in their Cmake based build system by including this file.
#
# Files specific to the repository such as test runner, platform tests
# are not added to the variables.

# HTTP library source files.
set( HTTP_SOURCES
     src/http_client.c
     src/http_client_parse.c )

# HTTP library Include directories.
set( HTTP_INCLUDE_PUBLIC_DIRS
     include )

# HTTP test include directories.
set( HTTP_TEST_INCLUDE_PRIVATE_DIRS
     src )

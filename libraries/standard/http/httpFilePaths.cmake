# This file is to add source files and include directories
# into variables so that it can be reused from different repositories
# in their Cmake based build system by including this file.
#
# Files specific to the repository such as test runner, platform tests
# are not added to the variables.

# HTTP library source files.
set( HTTP_SOURCES
     ${MODULES_DIR}/standard/http/src/http_client.c )

# HTTP library Public Include directories.
set( HTTP_INCLUDE_PUBLIC_DIRS
     ${MODULES_DIR}/standard/http/include
     ${PLATFORM_DIR}/include )

# HTTP library Private Include directories.
set( HTTP_INCLUDE_PRIVATE_DIRS
     ${MODULES_DIR}/standard/http/src
     ${MODULES_DIR}/standard/http/third_party/http_parser )

# HTTP library Include directories for Tests.
set( HTTP_TEST_INCLUDE_DIRS
     ${MODULES_DIR}/standard/http/third_party/http_parser )

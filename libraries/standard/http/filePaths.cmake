# This file is to add source files and include directories
# into variables so that it can be reused from different repositories
# in their Cmake based build system by including this file.
#
# Files specific to the repository such as test runner, platform tests
# are not added to the variables.

# HTTP library source files.
set( HTTP_SOURCES
     ${MODULES_DIR}/standard/http/src/http_client.c
     ${MODULES_DIR}/standard/http/src/http_client_parse.c )

# HTTP library Public Include directories.
set( HTTP_INCLUDE_PUBLIC_DIRS
     ${MODULES_DIR}/standard/http/include
     ${MODULES_DIR}/standard/utilities/include
      )

# HTTP library Private Include directories.
set( HTTP_INCLUDE_PRIVATE_DIRS
     ${MODULES_DIR}/standard/http/src
      )

# HTTP test include directories.
set( HTTP_TEST_INCLUDE_PRIVATE_DIRS
     ${MODULES_DIR}/standard/http/src/private
     ${MODULES_DIR}/standard/http/third_party
      )

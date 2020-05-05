# This file is to add source files and include directories
# into variables so that it can be reused from different repositories
# in their Cmake based build system by including this file.
#
# Files specific to the repository such as test runner, platform tests
# are not added to the variables.

set( DEMO_NAME "mqtt_demo_basic_tls" )

# Sources.
set( MQTT_DEMO_BASIC_TLS_SOURCES
     "${DEMO_NAME}.c" )

# Include public directories.
set( MQTT_DEMO_BASIC_TLS_INCLUDE_PUBLIC_DIRS
     ${CMAKE_CURRENT_LIST_DIR} )

# Libraries.
set( MQTT_DEMO_BASIC_TLS_LIBRARIES
     iotmqtt
     OpenSSL::Crypto
     OpenSSL::SSL )

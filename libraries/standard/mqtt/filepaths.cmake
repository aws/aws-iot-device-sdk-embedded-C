# This file is to add source files and include directories
# into variables so that it can be reused from different repositories
# in their Cmake based build system by including this file.
#
# Files specific to the repository such as test runner, platform tests
# are not added to the variables.

# MQTT library source files.
set( MQTT_SOURCES
     src/mqtt.c
     src/mqtt_lightweight.c )

# MQTT library Include directories.
set( MQTT_INCLUDE_PUBLIC_DIRS
     include )

# MQTT test include directories.
set( MQTT_TEST_INCLUDE_PRIVATE_DIRS
     src )

# Serializer library source files.
add_library( iotmetrics SHARED
             iot_metrics.c )

# Library version.
set_target_properties( iotmetrics PROPERTIES VERSION ${PROJECT_VERSION} )

# Link required libraries.
target_link_libraries( iotmetrics iotplatform )
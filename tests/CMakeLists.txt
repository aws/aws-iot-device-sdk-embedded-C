# Tests are currently only supported on Linux.
if( NOT ${CMAKE_SYSTEM_NAME} STREQUAL "Linux" )
    message( FATAL_ERROR "Currently, tests must run on Linux. Detected system: ${CMAKE_SYSTEM_NAME}." )
endif()

# Common tests.
add_subdirectory( common )

# MQTT tests.
add_subdirectory( mqtt )

# Shadow tests.
add_subdirectory( shadow )

# Serializer tests.
add_subdirectory( serializer )

# Defender tests.
add_subdirectory( defender )

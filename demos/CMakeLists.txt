# Set the platform named based on the host OS if not defined.
if( NOT DEFINED PLATFORM_NAME )
    if( ${CMAKE_SYSTEM_NAME} STREQUAL "Linux" )
        set( PLATFORM_NAME "posix" CACHE STRING "Port to use for building the SDK." )
    else()
        message( FATAL_ERROR "${CMAKE_SYSTEM_NAME} is not a supported platform." )
    endif()
endif()

# Include each subdirectory that has a CMakeLists.txt file in it
file(GLOB demo_dirs "${DEMOS_DIR}/*/*")
foreach(demo_dir IN LISTS demo_dirs)
    if(IS_DIRECTORY "${demo_dir}" AND EXISTS "${demo_dir}/CMakeLists.txt")
        get_filename_component( DEMO_EXE_NAME ${demo_dir} NAME )
        add_subdirectory(${demo_dir})
    endif()
endforeach()

# Replace macro definition if defined
if(AWS_IOT_ENDPOINT AND CLIENT_CERT_PATH AND CLIENT_PRIVATE_KEY_PATH)
    set_target_properties(http_demo_mutual_auth mqtt_demo_mutual_auth 
                            PROPERTIES COMPILE_DEFINITIONS 
                            "AWS_IOT_ENDPOINT;CLIENT_CERT_PATH;CLIENT_PRIVATE_KEY_PATH")
endif()

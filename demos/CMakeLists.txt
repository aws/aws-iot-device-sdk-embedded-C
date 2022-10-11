# Set the platform named based on the host OS if not defined.
if( NOT DEFINED PLATFORM_NAME )
    if( ${CMAKE_SYSTEM_NAME} STREQUAL "Linux" )
        set( PLATFORM_NAME "posix" CACHE STRING "Port to use for building the SDK." )
    else()
        message( FATAL_ERROR "${CMAKE_SYSTEM_NAME} is not a supported platform." )
    endif()
else()
    set( PLATFORM_NAME ${PLATFORM_NAME} CACHE STRING "Port to use for building the SDK." )
endif()

set(AWS_DEMO_INCLUDE_DIRS ${CMAKE_CURRENT_LIST_DIR}/include)

# Include each subdirectory that has a CMakeLists.txt file in it
file(GLOB demo_dirs "${DEMOS_DIR}/*/*")
foreach(demo_dir IN LISTS demo_dirs)
    if(IS_DIRECTORY "${demo_dir}" AND EXISTS "${demo_dir}/CMakeLists.txt")
        add_subdirectory(${demo_dir})
    endif()
endforeach()

# Check for function fork
check_symbol_exists(fork "unistd.h" HAVE_FORK)

# Filter demos based on what packages or library exist.
if(${LIB_RT} STREQUAL "LIB_RT-NOTFOUND")
    set(librt_demos
            "http_demo_s3_download_multithreaded"
            "ota_demo_core_http"
            "ota_demo_core_mqtt"
    )
    message( WARNING "rt library could not be found. Demos that use it will be excluded from the default target." )
    foreach(demo_name ${librt_demos})
        set_target_properties(${demo_name} PROPERTIES EXCLUDE_FROM_ALL true)
    endforeach()
endif()
if(NOT ${OpenSSL_FOUND})
    set(openssl_demos
            "defender_demo"
            "http_demo_basic_tls"
            "http_demo_mutual_auth"
            "http_demo_s3_download"
            "http_demo_s3_download_multithreaded"
            "http_demo_s3_upload"
            "mqtt_demo_basic_tls"
            "mqtt_demo_mutual_auth"
            "mqtt_demo_subscription_manager"
            "ota_demo_core_http"
            "ota_demo_core_mqtt"
            "shadow_demo_main"
            "greengrass_demo_local_auth"
    )
    message( WARNING "OpenSSL library could not be found. Demos that use it will be excluded from the default target." )
    foreach(demo_name ${openssl_demos})
        set_target_properties(${demo_name} PROPERTIES EXCLUDE_FROM_ALL true)
    endforeach()
endif()
if(NOT ${Threads_FOUND})
    set(thread_demos
            "ota_demo_core_http"
            "ota_demo_core_mqtt"
    )
    message( WARNING "Threads library could not be found. Demos that use it will be excluded from the default target." )
    foreach(demo_name ${thread_demos})
        set_target_properties(${demo_name} PROPERTIES EXCLUDE_FROM_ALL true)
    endforeach()
endif()
if(NOT HAVE_FORK)
    set(fork_demos
            "http_demo_s3_download_multithreaded"
            "jobs_demo_mosquitto"
    )
    message( WARNING "fork() could not be found. Demos that use it will be excluded from the default target." )
    foreach(demo_name ${fork_demos})
        set_target_properties(${demo_name} PROPERTIES EXCLUDE_FROM_ALL true)
    endforeach()
endif()

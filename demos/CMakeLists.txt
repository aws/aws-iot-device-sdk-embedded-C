# Set the platform named based on the host OS if not defined.
if( NOT DEFINED PLATFORM_NAME )
    if( ${CMAKE_SYSTEM_NAME} STREQUAL "Linux" )
        set( PLATFORM_NAME "posix" CACHE STRING "Port to use for building the SDK." )
    else()
        message( FATAL_ERROR "${CMAKE_SYSTEM_NAME} is not a supported platform." )
    endif()
endif()

# This function will add a demo target to the list of default targets
# if all AWS Credentials are defined.
function(check_aws_credentials demo_name)
    if(AWS_IOT_ENDPOINT AND CLIENT_CERT_PATH AND CLIENT_PRIVATE_KEY_PATH)
        target_compile_definitions(
            ${demo_name} PRIVATE
                AWS_IOT_ENDPOINT="${AWS_IOT_ENDPOINT}"
                CLIENT_CERT_PATH="${CLIENT_CERT_PATH}"
                CLIENT_PRIVATE_KEY_PATH="${CLIENT_PRIVATE_KEY_PATH}"
        )
        set(CMAKE_REQUIRED_DEFINITIONS -DAWS_IOT_ENDPOINT -DCLIENT_CERT_PATH -DCLIENT_PRIVATE_KEY_PATH)
    endif()

    set(FILES_TO_CHECK "demo_config.h")
    list(APPEND CMAKE_REQUIRED_INCLUDES "${CMAKE_CURRENT_LIST_DIR};${LOGGING_INCLUDE_DIRS}")
    unset(HAVE_AWS_ENDPOINT CACHE)
    unset(HAVE_CLIENT_CERT CACHE)
    unset(HAVE_PRIVATE_KEY CACHE)
    check_symbol_exists(AWS_IOT_ENDPOINT ${FILES_TO_CHECK} HAVE_AWS_ENDPOINT)
    check_symbol_exists(CLIENT_CERT_PATH ${FILES_TO_CHECK} HAVE_CLIENT_CERT)
    check_symbol_exists(CLIENT_PRIVATE_KEY_PATH ${FILES_TO_CHECK} HAVE_PRIVATE_KEY)
    
    if(NOT(HAVE_AWS_ENDPOINT AND HAVE_CLIENT_CERT AND HAVE_PRIVATE_KEY))
        message("To run ${demo_name}, define AWS_IOT_ENDPOINT, CLIENT_CERT_PATH, CLIENT_PRIVATE_KEY_PATH in ${demo_name}/demo_config.h.")
        set_target_properties(${demo_name} PROPERTIES EXCLUDE_FROM_ALL true)
    endif()
endfunction()

# Include each subdirectory that has a CMakeLists.txt file in it
file(GLOB demo_dirs "${DEMOS_DIR}/*/*")
foreach(demo_dir IN LISTS demo_dirs)
    if(IS_DIRECTORY "${demo_dir}" AND EXISTS "${demo_dir}/CMakeLists.txt")
        get_filename_component( DEMO_EXE_NAME ${demo_dir} NAME )
        add_subdirectory(${demo_dir})
    endif()
endforeach()

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
    set(REQUIRED_AWS_DEFINES
            "AWS_IOT_ENDPOINT"
            "CLIENT_CERT_PATH"
            "CLIENT_PRIVATE_KEY_PATH"
        )
    set(THING_NAME_DEMOS
            "THING_NAME"
        )
    if(";${THING_NAME_DEMOS};" MATCHES ";${demo_name};")
        list(APPEND REQUIRED_AWS_DEFINES "THING_NAME")
    endif()
    foreach(aws_define IN LISTS REQUIRED_AWS_DEFINES)
        if(DEFINED ${aws_define})
            target_compile_definitions(
                ${demo_name} PRIVATE
                    ${aws_define}="${${aws_define}}"
            )
            list(APPEND CMAKE_REQUIRED_DEFINITIONS -D${aws_define})
        endif()
    endforeach()

    # Check if demo_config.h has those macros defined.
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
        return()
    else()
        if(";${THING_NAME_DEMOS};" MATCHES ";${demo_name};")
            unset(HAVE_THING_NAME CACHE)
            check_symbol_exists(THING_NAME "demo_config.h" HAVE_THING_NAME)
            if(NOT HAVE_THING_NAME)
                message("To run ${demo_name}, define THING_NAME in ${demo_name}/demo_config.h.")
                set_target_properties(${demo_name} PROPERTIES EXCLUDE_FROM_ALL true)
                return()
            endif()
        endif()
    endif()

    message("All required macros for ${demo_name} were found - Adding to default target.")
endfunction()

function(set_macro_definitions)
    set(multiValueArgs TARGETS REQUIRED OPTIONAL FILES_TO_CHECK)
    cmake_parse_arguments(MACRO_DEFINITIONS "" "" "${multiValueArgs}" ${ARGN})
    if(NOT DEFINED MACRO_DEFINITIONS_TARGETS)
        message("At least one target is required when setting macro definitions through CMake.")
        return()
    endif()
    if(NOT DEFINED MACRO_DEFINITIONS_FILES_TO_CHECK)
        set(MACRO_DEFINITIONS_FILES_TO_CHECK "demo_config.h")
    endif()
    set(CMAKE_REQUIRED_DEFINITIONS "")
    foreach(application_target ${MACRO_DEFINITIONS_TARGETS})
        if(DEFINED MACRO_DEFINITIONS_OPTIONAL)
            foreach(optional_macro_definition ${MACRO_DEFINITIONS_OPTIONAL})
                if(DEFINED ${optional_macro_definition})
                    target_compile_definitions(
                        ${application_target} PRIVATE
                            ${optional_macro_definition}="${${optional_macro_definition}}"
                    )
                endif()
            endforeach()
        endif()
        if(DEFINED MACRO_DEFINITIONS_REQUIRED)
            foreach(required_macro_definition ${MACRO_DEFINITIONS_REQUIRED})
                if(DEFINED ${required_macro_definition})
                    target_compile_definitions(
                        ${application_target} PRIVATE
                            ${required_macro_definition}="${${required_macro_definition}}"
                    )
                    list(APPEND CMAKE_REQUIRED_DEFINITIONS -D${required_macro_definition})
                endif()
                # Check if MACRO_DEFINITIONS_FILES_TO_CHECK has the required macros defined already.
                # Note: Need to use includes from demo
                list(APPEND CMAKE_REQUIRED_INCLUDES "${CMAKE_CURRENT_LIST_DIR};${LOGGING_INCLUDE_DIRS}")
                unset(HAVE_${required_macro_definition} CACHE)
                check_symbol_exists(${required_macro_definition} ${FILES_TO_CHECK} HAVE_${required_macro_definition})
            endforeach()
        endif()
        # Print the error when certain required macros are not defined
    endforeach()
    if(MACRO_DEFINITIONS_REQUIRED)

    endif()
endfunction()

# This function will add a demo target to the list of default targets
# if pre-signed GET and PUT URLs are defined.
function(check_presigned_urls demo_name)
    if(S3_PRESIGNED_GET_URL)
        target_compile_definitions(
            ${demo_name} PRIVATE
                S3_PRESIGNED_GET_URL="${S3_PRESIGNED_GET_URL}"
        )
        list(APPEND CMAKE_REQUIRED_DEFINITIONS -DS3_PRESIGNED_GET_URL)
    endif()

    if(S3_PRESIGNED_PUT_URL)
        target_compile_definitions(
            ${demo_name} PRIVATE
                S3_PRESIGNED_PUT_URL="${S3_PRESIGNED_PUT_URL}"
        )
        list(APPEND CMAKE_REQUIRED_DEFINITIONS -DS3_PRESIGNED_PUT_URL)
    endif()

    set(UPLOAD_DEMOS "http_demo_s3_upload")
    set(DOWNLOAD_DEMOS "http_demo_s3_download" "http_demo_s3_download_multithreaded")
    set(FILES_TO_CHECK "demo_config.h")
    list(APPEND CMAKE_REQUIRED_INCLUDES "${CMAKE_CURRENT_LIST_DIR};${LOGGING_INCLUDE_DIRS}")
    unset(HAVE_S3_PRESIGNED_GET_URL CACHE)
    unset(HAVE_S3_PRESIGNED_PUT_URL CACHE)
    check_symbol_exists(S3_PRESIGNED_GET_URL ${FILES_TO_CHECK} HAVE_S3_PRESIGNED_GET_URL)
    check_symbol_exists(S3_PRESIGNED_PUT_URL ${FILES_TO_CHECK} HAVE_S3_PRESIGNED_PUT_URL)

    if( ";${UPLOAD_DEMOS};" MATCHES ";${demo_name};" )
        if( NOT(HAVE_S3_PRESIGNED_GET_URL AND HAVE_S3_PRESIGNED_PUT_URL) )
            message("To run ${demo_name}, define S3_PRESIGNED_GET_URL and S3_PRESIGNED_PUT_URL in ${demo_name}/demo_config.h.")
            set_target_properties(${demo_name} PROPERTIES EXCLUDE_FROM_ALL true)
        else()
            message("All required macros for ${demo_name} were found - Adding to default target.")
        endif()
    endif()

    if( ";${DOWNLOAD_DEMOS};" MATCHES ";${demo_name};" )
        if( NOT(HAVE_S3_PRESIGNED_GET_URL) )
            message("To run ${demo_name}, define S3_PRESIGNED_GET_URL in ${demo_name}/demo_config.h.")
            set_target_properties(${demo_name} PROPERTIES EXCLUDE_FROM_ALL true)
        else()
            message("All required macros for ${demo_name} were found - Adding to default target.")
        endif()
    endif()
endfunction()

# Include each subdirectory that has a CMakeLists.txt file in it
file(GLOB demo_dirs "${DEMOS_DIR}/*/*")
foreach(demo_dir IN LISTS demo_dirs)
    if(IS_DIRECTORY "${demo_dir}" AND EXISTS "${demo_dir}/CMakeLists.txt")
        add_subdirectory(${demo_dir})
    endif()
endforeach()

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

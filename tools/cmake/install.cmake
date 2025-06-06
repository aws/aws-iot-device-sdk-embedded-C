# Creates an install target to allow users to include CSDK as a set of shared libraries

set(FILEPATH_LOCATIONS
        ${MODULES_DIR}/aws/device-defender-for-aws-iot-embedded-sdk/defenderFilePaths.cmake
        ${MODULES_DIR}/aws/device-shadow-for-aws-iot-embedded-sdk/shadowFilePaths.cmake
        ${MODULES_DIR}/aws/jobs-for-aws-iot-embedded-sdk/jobsFilePaths.cmake
        ${MODULES_DIR}/standard/backoffAlgorithm/backoffAlgorithmFilePaths.cmake
        ${MODULES_DIR}/standard/coreHTTP/httpFilePaths.cmake
        ${MODULES_DIR}/standard/coreJSON/jsonFilePaths.cmake
        ${MODULES_DIR}/standard/coreMQTT/mqttFilePaths.cmake
        ${MODULES_DIR}/standard/corePKCS11/pkcsFilePaths.cmake
        ${PLATFORM_DIR}/posix/posixFilePaths.cmake
    )

# Include filePaths of all libraries
foreach(filepath ${FILEPATH_LOCATIONS})
    include(${filepath})
endforeach()

# Each filePath defines a set of variables that are prefixed with the name of the
# library and end with the type of source or include directory e.g. MQTT_SERIALIZER_SOURCES.
set(LIBRARY_PREFIXES
        "DEFENDER"
        "SHADOW"
        "JSON"
        "JOBS"
        "BACKOFF_ALGORITHM"
        "HTTP"
        "MQTT"
        "PKCS")

set(COREPKCS11_LOCATION "${MODULES_DIR}/standard/corePKCS11")
set(CORE_PKCS11_3RDPARTY_LOCATION "${COREPKCS11_LOCATION}/source/dependency/3rdparty")

# Define any extra sources or includes outside the standard, making sure to use the same prefix.
set(MQTT_EXTRA_SOURCES
        ${MQTT_SERIALIZER_SOURCES})
set(PKCS_EXTRA_SOURCES
        "${COREPKCS11_LOCATION}/source/portable/os/posix/core_pkcs11_pal.c"
        "${COREPKCS11_LOCATION}/source/portable/os/core_pkcs11_pal_utils.c"
        "${CORE_PKCS11_3RDPARTY_LOCATION}/mbedtls_utils/mbedtls_utils.c")
set(PKCS_EXTRA_INCLUDE_PRIVATE_DIRS
    PRIVATE
        "${CORE_PKCS11_3RDPARTY_LOCATION}/mbedtls_utils"
        "${COREPKCS11_LOCATION}/source/portable/os")

# Define any extra library dependencies, making sure to use the same prefix

if(NOT DEFINED INSTALL_LIBS)
    set(INSTALL_LIBS ${LIBRARY_PREFIXES})
endif()

foreach(library_prefix ${LIBRARY_PREFIXES})
    # Check if prefix is in list of libraries to be installed.
    list (FIND INSTALL_LIBS ${library_prefix} _index)
    # Create the library target.
    if(DEFINED "${library_prefix}_SOURCES" AND ${_index} GREATER -1)
        string(TOLOWER "aws_iot_${library_prefix}" library_name)
        add_library("${library_name}"
        ${${library_prefix}_EXTRA_SOURCES}
        ${${library_prefix}_SOURCES})

        if(${library_prefix} STREQUAL "JOBS")
            target_include_directories("${library_name}" PUBLIC ${JSON_INCLUDE_PUBLIC_DIRS})
            target_link_libraries("${library_name}" PRIVATE aws_iot_json)
        endif()
    else()
        continue()
    endif()

    # Add any extra includes defined for the library.
    if(DEFINED "${library_prefix}_EXTRA_INCLUDE_PUBLIC_DIRS")
        target_include_directories("${library_name}"
                        PUBLIC ${${library_prefix}_EXTRA_INCLUDE_PUBLIC_DIRS})
    endif()
    if(DEFINED "${library_prefix}_EXTRA_INCLUDE_PRIVATE_DIRS")
        target_include_directories("${library_name}"
                        PRIVATE ${${library_prefix}_EXTRA_INCLUDE_PRIVATE_DIRS})
    endif()

    # Link library dependencies
    if(DEFINED "${library_prefix}_LIBRARY_DEPENDENCIES")
        message( STATUS "Linking libraries for ${library_prefix}: ${${library_prefix}_LIBRARY_DEPENDENCIES}" )
        target_link_libraries("${library_name}" PRIVATE "${${library_prefix}_LIBRARY_DEPENDENCIES}" )
    endif()

    # Allow a path to a custom config header to be passed through a CMake flag.
    set(config_prefix "${library_prefix}")
    if(DEFINED "${config_prefix}_CUSTOM_CONFIG_DIR")
        target_include_directories("${library_name}"
                                    PRIVATE ${${config_prefix}_CUSTOM_CONFIG_DIR})
    else()
        target_compile_definitions("${library_name}" PRIVATE -D${config_prefix}_DO_NOT_USE_CUSTOM_CONFIG)
        # PKCS11 requires a config so include the one from the demos by default.
        if(${config_prefix} STREQUAL "PKCS")
            target_include_directories("${library_name}" PRIVATE
                                        ${DEMOS_DIR}/pkcs11/common/include
                                        ${LOGGING_INCLUDE_DIRS})
            target_link_libraries("${library_name}" PRIVATE mbedtls )
        endif()
    endif()

    # Add public include directories to library target.
    if(DEFINED "${library_prefix}_INCLUDE_PUBLIC_DIRS")
        target_include_directories("${library_name}"
                                    PUBLIC ${${library_prefix}_INCLUDE_PUBLIC_DIRS})
        foreach(library_public_dir ${${library_prefix}_INCLUDE_PUBLIC_DIRS})
            install(DIRECTORY ${library_public_dir}/ DESTINATION ${CSDK_HEADER_INSTALL_PATH}
                    FILES_MATCHING PATTERN "*.h"
                    PATTERN "*private*" EXCLUDE)
        endforeach()
    endif()

    # Add private include directories to library target.
    if(DEFINED "${library_prefix}_INCLUDE_PRIVATE_DIRS")
        target_include_directories("${library_name}"
                                    PRIVATE ${${library_prefix}_INCLUDE_PRIVATE_DIRS})
    endif()

    # Install the library target and support both static archive and shared library builds.
    install(TARGETS "${library_name}"
            LIBRARY DESTINATION "${CSDK_LIB_INSTALL_PATH}"
            ARCHIVE DESTINATION "${CSDK_LIB_INSTALL_PATH}")
endforeach()

# Install platform abstractions as shared libraries if enabled.
if(INSTALL_PLATFORM_ABSTRACTIONS)
    set(PLATFORM_DIRECTORIES
            ${COMMON_TRANSPORT_INCLUDE_PUBLIC_DIRS})
    foreach(platform_dir ${PLATFORM_DIRECTORIES})
        install(DIRECTORY ${platform_dir}/ DESTINATION ${CSDK_HEADER_INSTALL_PATH}
                FILES_MATCHING PATTERN "*.h"
                PATTERN "*private*" EXCLUDE)
    endforeach()
endif()

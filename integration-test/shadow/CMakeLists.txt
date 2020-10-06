project ("shadow system test")
cmake_minimum_required (VERSION 3.2.0)

# Include MQTT library's source and header path variables.
include("${CMAKE_SOURCE_DIR}/libraries/standard/coreMQTT/mqttFilePaths.cmake")

include("${CMAKE_SOURCE_DIR}/libraries/aws/device-shadow-for-aws-iot-embedded-sdk/shadowFilePaths.cmake")

# ====================  Define your project name (edit) ========================
set(project_name "shadow_system")

# ================= Create the library under test here (edit) ==================

# list the files you would like to test here
list(APPEND real_source_files
            ${SHADOW_SOURCES}
            ${MQTT_SOURCES}
            ${MQTT_SERIALIZER_SOURCES}
        )
# list the directories the module under test includes
list(APPEND real_include_directories
            .
            ${SHADOW_INCLUDE_PUBLIC_DIRS}
            ${MQTT_INCLUDE_PUBLIC_DIRS}
            ${LOGGING_INCLUDE_DIRS}
            ${CMAKE_CURRENT_LIST_DIR}
        )

# =====================  Create UnitTest Code here (edit)  =====================

# list the directories your test needs to include
list(APPEND test_include_directories
            .
            ${SHADOW_INCLUDE_PUBLIC_DIRS}
            ${MQTT_INCLUDE_PUBLIC_DIRS}
            ${LOGGING_INCLUDE_DIRS}
        )

# =============================  (end edit)  ===================================
set(real_name "${project_name}_real")

create_real_library(${real_name}
                    "${real_source_files}"
                    "${real_include_directories}"
                    # Empty mock name as create_real_library needs the 4th argument.
                    ""
        )

list(APPEND stest_link_list
            lib${real_name}.a
        )

list(APPEND stest_dep_list
            ${real_name}
            clock_posix
            openssl_posix
        )

set(stest_name "${project_name}_test")
set(stest_source "${project_name}_test.c")
create_test(${stest_name}
            ${stest_source}
            "${stest_link_list}"
            "${stest_dep_list}"
            "${test_include_directories}"
        )

# Set preprocessor defines for test if configured in build.
if(BROKER_ENDPOINT)
    target_compile_definitions(
        ${stest_name} PRIVATE
            AWS_IOT_ENDPOINT="${BROKER_ENDPOINT}"
    )
endif()
if(ROOT_CA_CERT_PATH)
    target_compile_definitions(
        ${stest_name} PRIVATE
            ROOT_CA_CERT_PATH="${ROOT_CA_CERT_PATH}"
    )
endif()
if(CLIENT_CERT_PATH)
    target_compile_definitions(
        ${stest_name} PRIVATE
        CLIENT_CERT_PATH="${CLIENT_CERT_PATH}"
    )
endif()
if(CLIENT_PRIVATE_KEY_PATH)
    target_compile_definitions(
        ${stest_name} PRIVATE
        CLIENT_PRIVATE_KEY_PATH="${CLIENT_PRIVATE_KEY_PATH}"
    )
endif()

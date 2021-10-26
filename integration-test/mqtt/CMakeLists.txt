project ("mqtt system test")
cmake_minimum_required (VERSION 3.2.0)

# Include MQTT library's source and header path variables.
include("${CMAKE_SOURCE_DIR}/libraries/standard/coreMQTT/mqttFilePaths.cmake")

# ====================  Define your project name (edit) ========================
set(project_name "mqtt_system")

# ================= Create the library under test here (edit) ==================

# list the files you would like to test here
list(APPEND real_source_files
            ${MQTT_SOURCES}
            ${MQTT_SERIALIZER_SOURCES}
        )
# list the directories the module under test includes
list(APPEND real_include_directories
            .
            ${MQTT_INCLUDE_PUBLIC_DIRS}
            ${LOGGING_INCLUDE_DIRS}
        )

# =====================  Create UnitTest Code here (edit)  =====================

# list the directories your test needs to include
list(APPEND test_include_directories
            .
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
            USE_CUSTOM_RUNNER 1
        )

# Separate test target when testing against an IoT Core broker
create_test(aws_iot_${stest_name}
            ${stest_source}
            "${stest_link_list}"
            "${stest_dep_list}"
            "${test_include_directories}"
            USE_CUSTOM_RUNNER 1
        )

set_macro_definitions(TARGETS ${stest_name} aws_iot_${stest_name}
                      REQUIRED
                        "ROOT_CA_CERT_PATH"
                        "CLIENT_CERT_PATH"
                        "CLIENT_PRIVATE_KEY_PATH"
                        "CLIENT_IDENTIFIER"
                        "BROKER_ENDPOINT"
                        "BROKER_PORT"
                      FILES_TO_CHECK
                        "test_config.h")

# aws_iot_mqtt_system_test will always test against IoT Core
target_compile_definitions(aws_iot_${stest_name} PUBLIC -DTEST_AGAINST_IOT_CORE=1)

if(${TEST_AGAINST_IOT_CORE})
    target_compile_definitions(${stest_name} PUBLIC -DTEST_AGAINST_IOT_CORE=1)
endif()

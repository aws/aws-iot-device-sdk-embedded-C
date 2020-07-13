set(src_dir "${CMAKE_CURRENT_LIST_DIR}/src")
set(inc_dir "${CMAKE_CURRENT_LIST_DIR}/include")
set(test_dir "${CMAKE_CURRENT_LIST_DIR}/test")

add_library(ota
    "${inc_dir}/aws_iot_ota_agent.h"
    "${inc_dir}/aws_iot_ota_types.h"
    "${src_dir}/aws_iot_ota_agent_internal.h"
    "${src_dir}/aws_iot_ota_agent.c"
    "${src_dir}/aws_iot_ota_interface.c"
    "${src_dir}/aws_iot_ota_interface.h"
    "${src_dir}/aws_iot_ota_pal.h"
)

target_include_directories(ota
    PUBLIC "${inc_dir}"
    PRIVATE "${src_dir}"
)

target_link_libraries(ota
    PRIVATE ota_mqtt ota_http ota_pal jsmn
)

# Link to this INTERFACE target to enable the MQTT backend.
add_library(ota_mqtt INTERFACE)
target_sources(ota_mqtt
    INTERFACE
    "${src_dir}/mqtt/aws_iot_ota_cbor_internal.h"
    "${src_dir}/mqtt/aws_iot_ota_cbor.c"
    "${src_dir}/mqtt/aws_iot_ota_cbor.h"
    "${src_dir}/mqtt/aws_iot_ota_mqtt.c"
    "${src_dir}/mqtt/aws_iot_ota_mqtt.h"
)
target_link_libraries(ota_mqtt INTERFACE mqtt tinycbor)

# Link to this INTERFACE target to enable the HTTP backend.
add_library(ota_http INTERFACE)
target_sources(ota_http
    INTERFACE
    "${src_dir}/http/aws_iot_ota_http.c"
    "${src_dir}/http/aws_iot_ota_http.h"
)
target_link_libraries(ota_http INTERFACE http)

# TODO, add ota_pal target for Linux

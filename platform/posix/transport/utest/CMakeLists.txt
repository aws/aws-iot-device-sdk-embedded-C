include(${PLATFORM_DIR}/posix/posixFilePaths.cmake)
project ("transport unit test")
cmake_minimum_required (VERSION 3.2.0)

# CMock does not have a built-in C parser.
# https://github.com/ThrowTheSwitch/CMock/issues/71
# Therefore, header files need to be preprocessed before mocks are generated.

# ====================  Define your project name (edit) ========================
set(project_name "transport")

# =====================  Create your mock here  (edit)  ========================

# list the files to mock here
list(APPEND mock_list
            /usr/include/arpa/inet.h
            /usr/include/x86_64-linux-gnu/sys/socket.h
            /usr/include/netdb.h
            /usr/include/x86_64-linux-gnu/sys/poll.h
            ${CMAKE_CURRENT_LIST_DIR}/mocks/unistd_api.h
            ${CMAKE_CURRENT_LIST_DIR}/mocks/openssl_api.h
            ${CMAKE_CURRENT_LIST_DIR}/mocks/stdio_api.h
            ${PLATFORM_DIR}/posix/transport/include/sockets_posix.h
        )
# list the directories your mocks need
list(APPEND mock_include_list
            ${LOGGING_INCLUDE_DIRS}
            ${PLATFORM_DIR}/include
            ${MODULES_DIR}/standard/coreMQTT/source/interface
        )
#list the definitions of your mocks to control what to be included
list(APPEND mock_define_list
            ""
        )

# ================= Create the library under test here (edit) ==================

# list the files you would like to test here
list(APPEND real_source_files
            ${SOCKETS_SOURCES}
        )
# list the directories the module under test includes
list(APPEND real_include_directories
            .
            ${COMMON_TRANSPORT_INCLUDE_PUBLIC_DIRS}
            ${LOGGING_INCLUDE_DIRS}
            ${MODULES_DIR}/standard/coreMQTT/source/interface
        )

# =====================  Create UnitTest Code here (edit)  =====================

# list the directories your test needs to include
list(APPEND test_include_directories
            .
            ${COMMON_TRANSPORT_INCLUDE_PUBLIC_DIRS}
            ${LOGGING_INCLUDE_DIRS}
            /usr/include/arpa
            /usr/include/x86_64-linux-gnu/sys
            ${OPENSSL_INCLUDE_DIR}
            mocks
        )

# =============================  (end edit)  ===================================

set(mock_name "transport_mock")
set(real_name "sockets_real")

create_mock_list(${mock_name}
                "${mock_list}"
                "${ROOT_DIR}/tools/cmock/transport.yml"
                "${mock_include_list}"
                "${mock_define_list}"
        )

create_real_library(${real_name}
                    "${real_source_files}"
                    "${real_include_directories}"
                    "${mock_name}"
        )

list(APPEND utest_link_list
            lib${real_name}.a
            -l${mock_name}
        )

list(APPEND utest_dep_list
            ${real_name}
        )

set(utest_name "sockets_utest")
set(utest_source "sockets_utest.c")
create_test(${utest_name}
            ${utest_source}
            "${utest_link_list}"
            "${utest_dep_list}"
            "${test_include_directories}"
        )

# list the files you would like to test here
set(real_source_files
        ${OPENSSL_TRANSPORT_SOURCES}
        )
set(real_name "openssl_real")

create_real_library(${real_name}
                    "${real_source_files}"
                    "${real_include_directories}"
                    "${mock_name}"
        )

set(utest_link_list
        lib${real_name}.a
        -l${mock_name}
        )

set(utest_dep_list
        ${real_name}
        )

set(utest_name "openssl_utest")
set(utest_source "openssl_utest.c")
create_test(${utest_name}
            ${utest_source}
            "${utest_link_list}"
            "${utest_dep_list}"
            "${test_include_directories}"
        )

# list the files you would like to test here
set(real_source_files
        ${PLAINTEXT_TRANSPORT_SOURCES}
        )
set(real_name "plaintext_real")

create_real_library(${real_name}
                    "${real_source_files}"
                    "${real_include_directories}"
                    "${mock_name}"
        )

set(utest_link_list
        lib${real_name}.a
        -l${mock_name}
        )

set(utest_dep_list
        ${real_name}
        )

set(utest_name "plaintext_utest")
set(utest_source "plaintext_utest.c")
create_test(${utest_name}
           ${utest_source}
           "${utest_link_list}"
           "${utest_dep_list}"
           "${test_include_directories}"
        )

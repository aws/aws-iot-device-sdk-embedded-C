include("../jsonFilePaths.cmake")
project ("json unit test")

# ====================  Define your project name (edit) ========================
set(project_name "json")

# =====================  Create your mock here  (edit)  ========================
# ================= Create the library under test here (edit) ==================

# list the files you would like to test here
list(APPEND real_source_files
            ${JSON_SOURCES}
        )
# list the directories the module under test includes
list(APPEND real_include_directories
            ${JSON_INCLUDE_PUBLIC_DIRS}
        )

# =====================  Create UnitTest Code here (edit)  =====================

# list the directories your test needs to include
list(APPEND test_include_directories
            ${JSON_INCLUDE_PUBLIC_DIRS}
        )

# =============================  (end edit)  ===================================

set(real_name "${project_name}_real")

create_real_library(${real_name}
                    "${real_source_files}"
                    "${real_include_directories}"
                    "${mock_name}"
        )

list(APPEND utest_link_list
            lib${real_name}.a
        )

list(APPEND utest_dep_list
            ${real_name}
        )

set(utest_name "${project_name}_utest")
set(utest_source "${project_name}_utest.c")
create_test(${utest_name}
            ${utest_source}
            "${utest_link_list}"
            "${utest_dep_list}"
            "${test_include_directories}"
        )

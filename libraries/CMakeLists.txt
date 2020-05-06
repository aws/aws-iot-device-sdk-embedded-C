# Add standard modules
file(GLOB standard_modules "${MODULES_DIR}/standard/*")
foreach(module IN LISTS standard_modules)
    if(IS_DIRECTORY "${module}" AND EXISTS "${module}/CMakeLists.txt")
        add_subdirectory(${module})
    endif()
endforeach()

# Add 3rdparty modules
add_subdirectory(${3RDPARTY_DIR})

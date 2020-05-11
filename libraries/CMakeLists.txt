# Add standard modules
file(GLOB standard_modules "${ROOT_DIR}/libraries/standard/*")
foreach(module IN LISTS standard_modules)
    if(IS_DIRECTORY "${module}" AND EXISTS "${module}/CMakeLists.txt")
        add_subdirectory(${module})
    endif()
endforeach()

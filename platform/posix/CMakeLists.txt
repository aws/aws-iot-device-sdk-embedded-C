# Include filepaths for source and include.
include(posixFilePaths.cmake)

# Create target for POSIX implementation of reconnect logic.
add_library( clock_posix
               "clock_posix.c" )

target_include_directories( clock_posix
                              PUBLIC
                                ${PLATFORM_DIR}/include )

# Install clock abstraction as library of both static archive and shared type.
if(INSTALL_PLATFORM_ABSTRACTIONS)
    install(TARGETS
      clock_posix
      LIBRARY DESTINATION "${CSDK_LIB_INSTALL_PATH}"
      ARCHIVE DESTINATION "${CSDK_LIB_INSTALL_PATH}"
      )
endif()

# Add the transport targets
add_subdirectory( ${CMAKE_CURRENT_LIST_DIR}/transport )

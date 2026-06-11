file(CONFIGURE OUTPUT ${CMAKE_BINARY_DIR}/temp/empty_init.c CONTENT "")
add_library(initialize OBJECT ${CMAKE_BINARY_DIR}/temp/empty_init.c)

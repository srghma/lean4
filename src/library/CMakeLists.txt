file(CONFIGURE OUTPUT ${CMAKE_CURRENT_BINARY_DIR}/empty.c CONTENT "")
add_library(
  library
  OBJECT
  ${CMAKE_CURRENT_BINARY_DIR}/empty.c
)

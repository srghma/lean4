if(GMP_INCLUDE_DIR AND GMP_LIBRARIES)
  set(GMP_FIND_QUIETLY TRUE)
endif()

find_path(GMP_INCLUDE_DIR NAMES gmp.h)
find_library(GMP_LIBRARIES NAMES gmp libgmp mpir REQUIRED)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(GMP DEFAULT_MSG GMP_INCLUDE_DIR GMP_LIBRARIES)
mark_as_advanced(GMP_INCLUDE_DIR GMP_LIBRARIES)

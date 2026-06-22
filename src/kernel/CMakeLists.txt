add_library(
  kernel
  OBJECT
  inductive.cpp
  type_checker.cpp
)
# Note: initialize_type_checker/finalize_type_checker are provided by Rust (kernel_type_checker.rs).
# type_checker.cpp provides lean_cxx_add_* bridges still used for quot/mutual/inductive.
# The C++ globals are initialized via initialize_cxx_type_checker_globals() called from Rust init.
if(GMP_INCLUDE_DIR)
  target_compile_options(kernel PRIVATE -isystem ${GMP_INCLUDE_DIR})
endif()

TODO:
1. how to run shell.cpp test?
1. When shell.cpp runs?
1. learn LakeMain.lean

traceCls
dbg_trace "msg with {interpolations}"; val
dbgTraceVal val

src/CMakeLists.txt
553:add_subdirectory(initialize) -> "lib/constr lib/comp" lib/print ran kern util
  #include "runtime/stackinfo.h"
  #include "runtime/thread.h"
  #include "runtime/init_module.h"
  #include "util/init_module.h"
  #include "util/io.h"
  #include "kernel/init_module.h"
  #include "library/constructions/init_module.h"
  #include "library/compiler/init_module.h"
  #
  #include "library/init_module.h"
  #include "library/print.h"
  #include "initialize/init.h"

  lean_initialize
  lean::io_mark_end_initialization

  save_stack_info();
  initialize_util_module();
    initialize_runtime_module();
      initialize_alloc();
      initialize_debug();
      initialize_object();
      initialize_io();
      initialize_thread();
      initialize_mutex();
      initialize_process();
      initialize_stack_overflow();
    initialize_ascii();
    initialize_name();
    initialize_name_generator();
    initialize_options();

  uint8_t builtin = 1;
  // Initializing the core libs explicitly is necessary because of references to them other than
  // via `import`, such as:
  // * calling exported Lean functions from C++
  // * calling into native code of the current module from a previous stage when `prefer_native`
  //   is set
  consume_io_result(initialize_Init(builtin, io_mk_world()));
  consume_io_result(initialize_Std(builtin, io_mk_world()));
  consume_io_result(initialize_Lean(builtin, io_mk_world()));
  initialize_kernel_module();
  init_default_print_fn();
  initialize_library_core_module();
  initialize_library_module();
  initialize_compiler_module();
  initialize_constructions_module();


554:add_subdirectory(shell)
595:  add_subdirectory(runtime)
601:  add_subdirectory(util)
603:  add_subdirectory(kernel)
605:  add_subdirectory(library)
607:  add_subdirectory(library/constructions)
609:  add_subdirectory(library/compiler)

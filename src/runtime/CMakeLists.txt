set(
  RUNTIME_OBJS
  thread.cpp
  mpz_helpers.cpp
  object.cpp
  exception.cpp
  compact.cpp
  io.cpp
)

set_source_files_properties(object.cpp PROPERTIES COMPILE_DEFINITIONS "LEAN_RUST_OBJECT_PANIC;LEAN_RUST_OBJECT_SIZE;LEAN_RUST_OBJECT_ARRAY;LEAN_RUST_OBJECT_RC;LEAN_RUST_OBJECT_NAT_INT;LEAN_RUST_OBJECT_STRING;LEAN_RUST_OBJECT_NAME;LEAN_RUST_OBJECT_CTOR_RUNTIME;LEAN_RUST_OBJECT_EXTERNAL_RUNTIME;LEAN_RUST_OBJECT_EXTERNAL_CLASS;LEAN_RUST_OBJECT_TASK_HARDWARE;LEAN_RUST_OBJECT_TASK_NUM_THREADS;LEAN_RUST_OBJECT_TASK_PURE;LEAN_RUST_OBJECT_TASK_IOSTATE")
set_source_files_properties(thread.cpp PROPERTIES COMPILE_DEFINITIONS "LEAN_RUST_THREAD_INIT;LEAN_RUST_THREAD_LEAN_RUN_MAIN")

find_program(CARGO_EXECUTABLE cargo REQUIRED)

if(CMAKE_BUILD_TYPE STREQUAL "Debug")
  set(LEAN_RUST_CARGO_ARGS)
  set(LEAN_RUST_PROFILE_DIR debug)
else()
  set(LEAN_RUST_CARGO_ARGS --release)
  set(LEAN_RUST_PROFILE_DIR release)
endif()
set(LEAN_RUST_HAS_ADDRESS_SANITIZER 0)
if(CMAKE_CXX_FLAGS MATCHES "fsanitize=address" OR LEAN_EXTRA_CXX_FLAGS MATCHES "fsanitize=address")
  set(LEAN_RUST_HAS_ADDRESS_SANITIZER 1)
endif()
if(STAGE EQUAL 0)
  set(LEAN_RUST_IS_STAGE0 1)
else()
  set(LEAN_RUST_IS_STAGE0 0)
endif()

set(LEAN_RUNTIME_RUST_ARCHIVE ${CMAKE_BINARY_DIR}/rust/${LEAN_RUST_PROFILE_DIR}/liblean_runtime.a)
set(LEAN_RUNTIME_RUST_DEPS_ARCHIVE ${CMAKE_BINARY_DIR}/rust/${LEAN_RUST_PROFILE_DIR}/liblean_runtime_deps.a)
set(LEAN_RUNTIME_RUST_OBJECT_DIR ${CMAKE_CURRENT_BINARY_DIR}/rust/lean_runtime)
set(LEAN_RUNTIME_RUST_OBJECT ${LEAN_RUNTIME_RUST_OBJECT_DIR}/lean_runtime.o)
add_custom_command(
  OUTPUT ${LEAN_RUNTIME_RUST_OBJECT} ${LEAN_RUNTIME_RUST_DEPS_ARCHIVE}
  COMMAND
    ${CMAKE_COMMAND} -E env
    CARGO_TARGET_DIR=${CMAKE_BINARY_DIR}/rust
    LEAN_RUST_GITHASH=${GIT_SHA1}
    LEAN_RUST_BUILD_TYPE=${CMAKE_BUILD_TYPE}
    LEAN_RUST_HAS_LLVM=$<IF:$<BOOL:${LLVM}>,1,0>
    LEAN_RUST_HAS_ADDRESS_SANITIZER=${LEAN_RUST_HAS_ADDRESS_SANITIZER}
    LEAN_RUST_HAS_MIMALLOC=$<IF:$<BOOL:${USE_MIMALLOC}>,1,0>
    LEAN_RUST_SMALL_ALLOCATOR=$<IF:$<BOOL:${SMALL_ALLOCATOR}>,1,0>
    LEAN_RUST_USE_GMP=$<IF:$<BOOL:${USE_GMP}>,1,0>
    LEAN_RUST_MULTI_THREAD=$<IF:$<BOOL:${MULTI_THREAD}>,1,0>
    LEAN_RUST_LAZY_RC=$<IF:$<BOOL:${LAZY_RC}>,1,0>
    LEAN_RUST_DEBUG=$<IF:$<CONFIG:Debug>,1,$<IF:$<CONFIG:RelWithAssert>,1,0>>
    LEAN_RUST_LEANC_EXTRA_CC_FLAGS=${LEANC_EXTRA_CC_FLAGS}
    LEAN_RUST_LEANC_INTERNAL_FLAGS=${LEANC_INTERNAL_FLAGS}
    LEAN_RUST_LEANC_STATIC_LINKER_FLAGS=${LEANC_STATIC_LINKER_FLAGS}
    LEAN_RUST_LEANC_SHARED_LINKER_FLAGS=${LEANC_SHARED_LINKER_FLAGS}
    LEAN_RUST_LEAN_EXTRA_LINKER_FLAGS=${LEAN_EXTRA_LINKER_FLAGS}
    LEAN_RUST_LEAN_EXTRA_LINKER_FLAGS_WITHOUT_RUST_ARCHIVE=${LEAN_EXTRA_LINKER_FLAGS_WITHOUT_RUST_ARCHIVE}
    LEAN_RUST_LEANC_INTERNAL_LINKER_FLAGS=${LEANC_INTERNAL_LINKER_FLAGS}
    LEAN_RUST_LEANRT_INITIAL_EXEC_ARCHIVE=${CMAKE_BINARY_DIR}/runtime/libleanrt_initial-exec.a
    LEAN_RUST_IS_STAGE0=${LEAN_RUST_IS_STAGE0}
    ${CARGO_EXECUTABLE} build --manifest-path ${LEAN_SOURCE_DIR}/rust/Cargo.toml --package lean_runtime --features export-runtime-ffi ${LEAN_RUST_CARGO_ARGS}
  COMMAND ${CMAKE_COMMAND} -E rm -rf ${LEAN_RUNTIME_RUST_OBJECT_DIR}
  COMMAND ${CMAKE_COMMAND} -E make_directory ${LEAN_RUNTIME_RUST_OBJECT_DIR}
  COMMAND
    bash -ec
    "cd '${LEAN_RUNTIME_RUST_OBJECT_DIR}' && obj=`'${CMAKE_AR}' t '${LEAN_RUNTIME_RUST_ARCHIVE}' | grep '^lean_runtime-.*\\.o$' | head -n 1` && cp '${LEAN_RUNTIME_RUST_ARCHIVE}' '${LEAN_RUNTIME_RUST_DEPS_ARCHIVE}' && '${CMAKE_AR}' x '${LEAN_RUNTIME_RUST_ARCHIVE}' \"$obj\" && '${CMAKE_AR}' d '${LEAN_RUNTIME_RUST_DEPS_ARCHIVE}' \"$obj\" && mv \"$obj\" lean_runtime.o"
  DEPENDS
    ${LEAN_SOURCE_DIR}/rust/Cargo.toml
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/Cargo.toml
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/build.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/lib.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/library_constants.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/library_dynlib.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_apply.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_debug.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_dns.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_event_loop.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_libuv.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_mpn.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_mutex.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_net_addr.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_signal.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_stack_overflow.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_stack_info.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_interrupt.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_system.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_process.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_tcp.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_timer.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_udp.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_alloc.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_memory.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_object_panic.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_object_size.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_object_array.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_object_rc.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_sharecommon.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_thread.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_once.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_float.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_mpz.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_object_nat_int.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_object_string.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_object_name.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_io_fs.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_io_ref.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_io_error.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_io_handle.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_io_task.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_io_stream.rs
  VERBATIM
)
add_custom_target(lean_runtime_rust DEPENDS ${LEAN_RUNTIME_RUST_OBJECT})
list(APPEND RUNTIME_OBJS ${LEAN_RUNTIME_RUST_OBJECT})
if(USE_MIMALLOC)
  list(APPEND RUNTIME_OBJS ${LEAN_BINARY_DIR}/../mimalloc/src/mimalloc/src/static.c)
  # Lean code includes it as `lean/mimalloc.h` but for compiling `static.c` itself, add original dir
  include_directories(${LEAN_BINARY_DIR}/../mimalloc/src/mimalloc/include)
  # make all symbols visible, always build with optimizations as otherwise Lean becomes too slow
  set(MIMALLOC_FLAGS "-DMI_SHARED_LIB -DMI_SHARED_LIB_EXPORT -O3 -DNDEBUG -DMI_WIN_NOREDIRECT -DMI_SECURE=${LEAN_MI_SECURE} -Wno-unused-function")
  if(CMAKE_CXX_COMPILER_ID MATCHES "AppleClang|Clang")
    string(APPEND MIMALLOC_FLAGS " -Wno-deprecated")
  endif()
  set_source_files_properties(
    ${LEAN_BINARY_DIR}/../mimalloc/src/mimalloc/src/static.c
    PROPERTIES
      # (C flags are incomplete, compile as C++ instead like everything else)
      LANGUAGE CXX
      COMPILE_FLAGS ${MIMALLOC_FLAGS}
  )
endif()

add_library(leanrt_initial-exec STATIC ${RUNTIME_OBJS})
set_target_properties(leanrt_initial-exec PROPERTIES ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR})
add_dependencies(leanrt_initial-exec lean_runtime_rust)
target_link_libraries(leanrt_initial-exec PUBLIC ${LEAN_RUNTIME_RUST_ARCHIVE})

# The above library, like all other C++ code, is built using `-ftls-model=initial-exec`, which is necessary for linking it into `leanshared`,
# but introduces a measurable overhead while accessing the thread-local variable `g_heap` when allocating and deallocating. Therefore we compile
# the runtime again with the more restrictive `local-exec` and use it when linking Lean code statically, i.e. not against `leanshared`.
add_library(leanrt STATIC ${RUNTIME_OBJS})
set_target_properties(leanrt PROPERTIES ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_ARCHIVE_OUTPUT_DIRECTORY})
add_dependencies(leanrt lean_runtime_rust)
target_link_libraries(leanrt PUBLIC ${LEAN_RUNTIME_RUST_ARCHIVE})
if(NOT MSVC)
  target_compile_options(leanrt PRIVATE -ftls-model=local-exec)
endif()
# We do not export Lean symbols when statically linking on Windows.
if(CMAKE_SYSTEM_NAME MATCHES "Windows")
  target_compile_options(leanrt PRIVATE -ULEAN_EXPORTING)
endif()

if(LLVM)
  if(NOT CMAKE_CXX_COMPILER_ID MATCHES "Clang")
    message(
      FATAL_ERROR
      "building 'lean.h.bc', need CMAKE_CXX_COMPILER_ID to match Clang to build LLVM bitcode file of Lean runtime."
    )
  endif()
  file(READ "${CMAKE_CURRENT_SOURCE_DIR}/../include/lean/lean.h" LEAN_H)
  # generate LLVM IR for `static inline` definitions in lean.h for the LLVM backend
  string(REPLACE "static inline" "__attribute__((always_inline))" LEAN_H "${LEAN_H}")
  # drop '#pragma once' in .c file to avoid warning
  string(REPLACE "#pragma once" "" LEAN_H "${LEAN_H}")
  file(WRITE "${CMAKE_CURRENT_BINARY_DIR}/lean_inlines.c" "${LEAN_H}")
  message("Generating LLVM bitcode file for Lean runtime at '${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/lean.h.bc'")
  add_custom_command(
    OUTPUT ${CMAKE_ARCHIVE_OUTPUT_DIRECTORY}/lean.h.bc
    DEPENDS ${RUNTIME_OBJS} ${CMAKE_CURRENT_BINARY_DIR}/lean_inlines.c
    COMMAND
      bash -ec
      "${CMAKE_BINARY_DIR}/leanc.sh ${LEANC_OPTS} -I$<JOIN:$<TARGET_PROPERTY:leanrt_initial-exec,INCLUDE_DIRECTORIES>, -I> -c ${CMAKE_CURRENT_BINARY_DIR}/lean_inlines.c -emit-llvm -o ${CMAKE_ARCHIVE_OUTPUT_DIRECTORY}/lean.h.bc"
    VERBATIM
  )
  add_custom_target(runtime_bc DEPENDS ${CMAKE_ARCHIVE_OUTPUT_DIRECTORY}/lean.h.bc)
endif()

set(RUNTIME_OBJS)

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

set(LEAN_RUNTIME_RUST_RLIB ${CMAKE_BINARY_DIR}/rust/${LEAN_RUST_PROFILE_DIR}/liblean_runtime.rlib)
add_custom_command(
  OUTPUT ${LEAN_RUNTIME_RUST_RLIB}
  COMMAND
    ${CMAKE_COMMAND} -E env
    CARGO_TARGET_DIR=${CMAKE_BINARY_DIR}/rust
    RUSTFLAGS=-Dwarnings
    LEAN_RUST_GITHASH=${GIT_SHA1}
    LEAN_RUST_BUILD_TYPE=${CMAKE_BUILD_TYPE}
    LEAN_RUST_VERSION_STRING=${LEAN_VERSION_STRING}
    LEAN_RUST_MANUAL_ROOT=${LEAN_MANUAL_ROOT}
    LEAN_RUST_HAS_LLVM=$<IF:$<BOOL:${LLVM}>,1,0>
    LEAN_RUST_HAS_ADDRESS_SANITIZER=${LEAN_RUST_HAS_ADDRESS_SANITIZER}
    LEAN_RUST_USE_GMP=$<IF:$<BOOL:${USE_GMP}>,1,0>
    LEAN_RUST_MULTI_THREAD=$<IF:$<BOOL:${MULTI_THREAD}>,1,0>
    LEAN_RUST_DEBUG=$<IF:$<CONFIG:Debug>,1,$<IF:$<CONFIG:RelWithAssert>,1,0>>
    LEAN_RUST_LEANC_EXTRA_CC_FLAGS=${LEANC_EXTRA_CC_FLAGS}
    LEAN_RUST_LEANC_INTERNAL_FLAGS=${LEANC_INTERNAL_FLAGS}
    LEAN_RUST_LEANC_STATIC_LINKER_FLAGS=${LEANC_STATIC_LINKER_FLAGS}
    LEAN_RUST_LEANC_SHARED_LINKER_FLAGS=${LEANC_SHARED_LINKER_FLAGS}
    LEAN_RUST_LEAN_EXTRA_LINKER_FLAGS=${LEAN_EXTRA_LINKER_FLAGS}
    LEAN_RUST_LEAN_EXTRA_LINKER_FLAGS_WITHOUT_RUST_ARCHIVE=${LEAN_EXTRA_LINKER_FLAGS_WITHOUT_RUST_ARCHIVE}
    LEAN_RUST_LEANC_INTERNAL_LINKER_FLAGS=${LEANC_INTERNAL_LINKER_FLAGS}
    LEAN_RUST_IS_STAGE0=${LEAN_RUST_IS_STAGE0}
    ${CARGO_EXECUTABLE} build --manifest-path ${LEAN_SOURCE_DIR}/rust/Cargo.toml --package lean_runtime ${LEAN_RUST_CARGO_ARGS}
  DEPENDS
    ${LEAN_SOURCE_DIR}/rust/Cargo.toml
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/Cargo.toml
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/build.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/lib.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/library_constants.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/library_util.rs
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
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_exception.rs
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
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_object_task.rs
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
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/kernel_abstract.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/library_expr_lt.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/library_time_task.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/library_print.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_compact.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/runtime_compact_writer.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/kernel_replace_fn.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/kernel_expr_eq_fn.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/kernel_for_each_fn.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/kernel_level.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/kernel_expr.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/kernel_instantiate.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/kernel_environment.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/kernel_type_checker.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/library_instantiate_mvars.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/library_module.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/library_elab_environment.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/library_ir_interpreter.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/library_llvm.rs
    ${LEAN_SOURCE_DIR}/rust/lean_runtime/src/kernel_num.rs
  VERBATIM
)
add_custom_target(lean_runtime_rust DEPENDS ${LEAN_RUNTIME_RUST_RLIB})
add_custom_target(leanrt_initial-exec DEPENDS lean_runtime_rust)
add_custom_target(leanrt DEPENDS lean_runtime_rust)

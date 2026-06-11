# Integration steps for runtime_compact.rs, runtime_io.rs, io_shims.cpp, compact_shims.cpp

## Files to add to the repo

1. `src/rust/lean_runtime/src/runtime_compact.rs`
   — Replace or create; exposes the three `lean_compacted_region_*` functions.

2. `src/rust/lean_runtime/src/runtime_io.rs`
   — New file; provides all `lean_io_*`, `lean_st_*`, and `lean_runtime_*` functions
     that were in `runtime/io.cpp`.

3. `src/runtime/compact_shims.cpp`
   — Thin C wrappers for object_compactor / compacted_region C++ types.

4. `src/runtime/io_shims.cpp`
   — Thin C wrappers for all C++ things runtime_io.rs can't call directly:
     atomic<object*>, MK_THREAD_LOCAL_GET, uv_fs_* helpers, platform
     realpath/app_path/rename, ICU timezone funcs, lock/unlock, etc.

## lib.rs additions (after existing includes)

```rust
include!("runtime_compact.rs");
include!("runtime_io.rs");
```

## src/runtime/CMakeLists.txt changes

```cmake
set(RUNTIME_OBJS
  thread.cpp
  mpz.cpp
  object.cpp
  exception.cpp
  compact.cpp        # keep until compact_shims.cpp covers all symbols
  # io.cpp           # REMOVED — replaced by runtime_io.rs + io_shims.cpp
  alloc.cpp          # or alloc_shims.cpp if that port is complete
  compact_shims.cpp  # ADD
  io_shims.cpp       # ADD
  object_shims.cpp   # already there
  ...
)
```

## Symbols removed from io.cpp (guard with #ifndef LEAN_RUST_IO or delete)

All `extern "C" LEAN_EXPORT` functions whose Rust replacements are in runtime_io.rs:

  lean_io_result_show_error
  lean_decode_io_error
  lean_decode_uv_error
  lean_get_stdin, lean_get_stdout, lean_get_stderr
  lean_get_set_stdin, lean_get_set_stdout, lean_get_set_stderr
  lean_chmod
  lean_io_prim_handle_mk
  lean_io_prim_handle_is_tty, lean_io_prim_handle_is_eof
  lean_io_prim_handle_flush, lean_io_prim_handle_rewind, lean_io_prim_handle_truncate
  lean_io_prim_handle_read, lean_io_prim_handle_write
  lean_io_prim_handle_get_line, lean_io_prim_handle_put_str
  lean_io_prim_handle_lock, lean_io_prim_handle_try_lock, lean_io_prim_handle_unlock
  lean_io_get_random_bytes
  lean_io_realpath
  lean_io_read_dir
  lean_io_metadata, lean_io_symlink_metadata
  lean_io_create_dir, lean_io_remove_dir, lean_io_rename, lean_io_hard_link
  lean_io_remove_file
  lean_io_app_path, lean_io_current_dir
  lean_io_create_tempfile, lean_io_create_tempdir
  lean_st_mk_ref, lean_st_ref_get, lean_st_ref_take, lean_st_ref_set, lean_st_ref_swap
  lean_st_ref_ptr_eq
  lean_io_as_task, lean_io_map_task, lean_io_bind_task
  lean_io_check_canceled, lean_io_cancel, lean_io_get_task_state
  lean_io_wait, lean_io_wait_any
  lean_io_exit, lean_io_force_exit
  lean_runtime_mark_multi_threaded, lean_runtime_mark_persistent
  lean_runtime_forget
  lean_option_get_or_block
  lean_windows_get_next_transition, lean_get_windows_local_timezone_id_at
  initialize_io, finalize_io

## Symbols removed from compact.cpp (guard or delete)

  lean_compacted_region_is_memory_mapped
  lean_compacted_region_size
  lean_compacted_region_free

## Notes on io_shims.cpp

Several shims forward to existing io.cpp functions (lean_io_prim_handle_lock_impl,
lean_io_prim_handle_mk, etc.). Until io.cpp is fully removed, rename those
C++ functions to *_impl variants so both the Rust wrapper and the C++ body coexist.
The simplest approach: in io.cpp rename the function bodies to lean_*_impl and
have lean_io_shim_*.cpp call them. Then runtime_io.rs exports the lean_* names.

Alternatively, remove io.cpp entirely and inline the body of lock/tryLock/unlock
directly in io_shims.cpp (they're < 20 lines each).

use leanh_l1::datatypes::{LeanObject, LeanScalarArray, LeanStringObject};
// Generated stub file for Lean FFI imports
// Source: src/Init/System/IO.lean

pub fn lean_io_timeit(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_timeit");
}

pub fn lean_io_allocprof(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_allocprof");
}

pub fn lean_io_initializing() -> bool {
    todo!("Stub for lean_io_initializing");
}

pub fn lean_io_as_task(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_as_task");
}

pub fn lean_io_map_task(
    _: *mut LeanObject,
    _: *mut LeanObject,
    _: *mut LeanObject,
    _: bool,
) -> *mut LeanObject {
    todo!("Stub for lean_io_map_task");
}

pub fn lean_io_bind_task(
    _: *mut LeanObject,
    _: *mut LeanObject,
    _: *mut LeanObject,
    _: bool,
) -> *mut LeanObject {
    todo!("Stub for lean_io_bind_task");
}

pub fn lean_io_mono_ms_now() -> *mut LeanObject {
    todo!("Stub for lean_io_mono_ms_now");
}

pub fn lean_io_mono_nanos_now() -> *mut LeanObject {
    todo!("Stub for lean_io_mono_nanos_now");
}

pub fn lean_io_get_random_bytes(_: usize) -> *mut LeanObject {
    todo!("Stub for lean_io_get_random_bytes");
}

pub fn lean_io_check_canceled() -> bool {
    todo!("Stub for lean_io_check_canceled");
}

pub fn lean_io_cancel(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_cancel");
}

pub fn lean_io_get_task_state(_: *mut LeanObject) -> u8 {
    todo!("Stub for lean_io_get_task_state");
}

pub fn lean_io_wait(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_wait");
}

pub fn lean_io_wait_any(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_wait_any");
}

pub fn lean_io_get_num_heartbeats() -> *mut LeanObject {
    todo!("Stub for lean_io_get_num_heartbeats");
}

pub fn lean_io_set_heartbeats(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_set_heartbeats");
}

pub fn lean_get_stdin() -> *mut LeanObject {
    todo!("Stub for lean_get_stdin");
}

pub fn lean_get_stdout() -> *mut LeanObject {
    todo!("Stub for lean_get_stdout");
}

pub fn lean_get_stderr() -> *mut LeanObject {
    todo!("Stub for lean_get_stderr");
}

pub fn lean_get_set_stdin(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_get_set_stdin");
}

pub fn lean_get_set_stdout(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_get_set_stdout");
}

pub fn lean_get_set_stderr(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_get_set_stderr");
}

pub fn lean_io_prim_handle_mk(_: *mut LeanObject, _: u8) -> *mut LeanObject {
    todo!("Stub for lean_io_prim_handle_mk");
}

pub fn lean_io_prim_handle_lock(_: *mut LeanObject, _: bool) -> *mut LeanObject {
    todo!("Stub for lean_io_prim_handle_lock");
}

pub fn lean_io_prim_handle_try_lock(_: *mut LeanObject, _: bool) -> *mut LeanObject {
    todo!("Stub for lean_io_prim_handle_try_lock");
}

pub fn lean_io_prim_handle_unlock(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_prim_handle_unlock");
}

pub unsafe fn lean_io_prim_handle_is_tty(h: *mut LeanObject) -> bool {
    unsafe {
        leanh_l1_initializers::r#priv::lean_io_prim_handle_is_tty::lean_io_prim_handle_is_tty(h)
    }
}

pub fn lean_io_prim_handle_flush(h: *mut LeanObject) -> *mut LeanObject {
    unsafe {
        leanh_l1_initializers::r#priv::lean_io_prim_handle_flush::lean_io_prim_handle_flush(h)
    }
}

pub fn lean_io_prim_handle_rewind(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_prim_handle_rewind");
}

pub fn lean_io_prim_handle_truncate(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_prim_handle_truncate");
}

pub fn lean_io_prim_handle_read(h: *mut LeanObject, nbytes: usize) -> *mut LeanObject {
    unsafe {
        leanh_l1_initializers::r#priv::lean_io_prim_handle_read::lean_io_prim_handle_read(h, nbytes)
    }
}

pub fn lean_io_prim_handle_write(h: *mut LeanObject, s: *mut LeanObject) -> *mut LeanObject {
    unsafe {
        leanh_l1_initializers::r#priv::lean_io_prim_handle_write::lean_io_prim_handle_write(h, s)
    }
}

pub fn lean_io_prim_handle_get_line(h: *mut LeanObject) -> *mut LeanObject {
    unsafe {
        leanh_l1_initializers::r#priv::lean_io_prim_handle_get_line::lean_io_prim_handle_get_line(h)
    }
}

pub fn lean_io_prim_handle_put_str(h: *mut LeanObject, s: *mut LeanObject) -> *mut LeanObject {
    unsafe {
        leanh_l1_initializers::r#priv::lean_io_prim_handle_put_str::lean_io_prim_handle_put_str(
            h, s,
        )
    }
}

pub fn lean_io_realpath(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_realpath");
}

pub fn lean_io_remove_file(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_remove_file");
}

pub fn lean_io_remove_dir(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_remove_dir");
}

pub fn lean_io_create_dir(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_create_dir");
}

pub fn lean_io_rename(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_rename");
}

pub fn lean_io_hard_link(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_hard_link");
}

pub fn lean_io_create_tempfile() -> *mut LeanObject {
    todo!("Stub for lean_io_create_tempfile");
}

pub fn lean_io_create_tempdir() -> *mut LeanObject {
    todo!("Stub for lean_io_create_tempdir");
}

pub fn lean_io_getenv(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_getenv");
}

pub fn lean_io_app_path() -> *mut LeanObject {
    todo!("Stub for lean_io_app_path");
}

pub fn lean_io_current_dir() -> *mut LeanObject {
    todo!("Stub for lean_io_current_dir");
}

pub fn lean_io_read_dir(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_read_dir");
}

pub fn lean_io_metadata(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_metadata");
}

pub fn lean_io_symlink_metadata(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_symlink_metadata");
}

pub fn lean_io_process_get_current_dir() -> *mut LeanObject {
    todo!("Stub for lean_io_process_get_current_dir");
}

pub fn lean_io_process_set_current_dir(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_process_set_current_dir");
}

pub fn lean_io_process_get_pid() -> u32 {
    todo!("Stub for lean_io_process_get_pid");
}

pub fn lean_io_process_spawn(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_process_spawn");
}

pub fn lean_io_process_child_wait(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_process_child_wait");
}

pub fn lean_io_process_child_try_wait(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_process_child_try_wait");
}

pub fn lean_io_process_child_kill(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_process_child_kill");
}

pub fn lean_io_process_child_take_stdin(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_process_child_take_stdin");
}

pub fn lean_io_process_child_pid(_: *mut LeanObject, _: *mut LeanObject) -> u32 {
    todo!("Stub for lean_io_process_child_pid");
}

pub fn lean_io_exit(_: u8) -> *mut LeanObject {
    todo!("Stub for lean_io_exit");
}

pub fn lean_io_force_exit(_: u8) -> *mut LeanObject {
    todo!("Stub for lean_io_force_exit");
}

pub fn lean_io_get_tid() -> u64 {
    todo!("Stub for lean_io_get_tid");
}

pub fn lean_chmod(_: *mut LeanObject, _: u32) -> *mut LeanObject {
    todo!("Stub for lean_chmod");
}

pub fn lean_runtime_mark_multi_threaded(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_runtime_mark_multi_threaded");
}

pub fn lean_runtime_mark_persistent(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_runtime_mark_persistent");
}

pub fn lean_runtime_forget(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_runtime_forget");
}

pub fn lean_runtime_hold(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_runtime_hold");
}

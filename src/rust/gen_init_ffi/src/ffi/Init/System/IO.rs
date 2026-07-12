use leanh_l1::datatypes::{LeanObject, LeanTaskImp, LeanTaskState};
use leanh_l1::emitted::lean_alloc_closure::lean_alloc_closure;
use leanh_l1::emitted::lean_closure_set::lean_closure_set;
use leanh_l1::emitted::lean_dec::lean_dec;
use leanh_l1::emitted::lean_io_mark_end_initialization::INITIALIZING;
use leanh_l1::emitted::lean_io_result_mk_ok::lean_io_result_mk_ok;
use leanh_l1::emitted::lean_mk_string::lean_mk_string;
use leanh_l1::emitted::lean_unbox::lean_unbox;
use leanh_l1::runtime_object_task::p1_get_task_manager::get_task_manager;
use leanh_l1::runtime_object_task::scoped_current_task::current_task;
use leanh_l1::todo_import_from_lean::lean_io_eprintln::lean_io_eprintln;
use leanh_l1_initializers::r#priv::lean_alloc_sarray::lean_alloc_sarray;
use leanh_l1_initializers::r#priv::lean_errno::lean_errno;
use leanh_l1_initializers::r#priv::lean_io_result_mk_error::lean_io_result_mk_error;
use leanh_l1_initializers::r#priv::lean_sarray_cptr::lean_sarray_cptr;
use leanh_l1_initializers::r#priv::lean_sarray_set_size::lean_sarray_set_size;
use leanh_l1_initializers::runtime_io_error::lean_decode_io_error::lean_decode_io_error;
use std::ffi::{CStr, c_void};
use std::io::{self, Write};
use std::sync::OnceLock;
use std::sync::atomic::Ordering;
use std::time::Instant;
// Generated stub file for Lean FFI imports
// Source: src/Init/System/IO.lean

pub unsafe fn lean_io_timeit(msg: *mut LeanObject, fn_obj: *mut LeanObject) -> *mut LeanObject {
    let start = Instant::now();
    let result = lean_apply_1(fn_obj, lean_box(0));
    let elapsed = start.elapsed().as_secs_f64();

    let prefix = CStr::from_ptr(lean_string_cstr(msg)).to_string_lossy();
    let mut stderr = io::stderr().lock();
    let _ = if elapsed < 1.0 {
        stderr.write_fmt(format_args!("{prefix} {:.3}ms\n", elapsed * 1000.0))
    } else {
        stderr.write_fmt(format_args!("{prefix} {:.3}s\n", elapsed))
    };
    result
}

pub unsafe fn lean_io_allocprof(msg: *mut LeanObject, fn_obj: *mut LeanObject) -> *mut LeanObject {
    let label = CStr::from_ptr(lean_string_cstr(msg)).to_string_lossy();
    let result = lean_apply_1(fn_obj, lean_box(0));
    let output = std::ffi::CString::new(format!(
        "{label}\nAllocation profiling data is not available, compile lean using `-D RUNTIME_STATS=ON`\n"
    ))
    .expect("allocation profiler output has no NUL");
    let print_result = lean_io_eprintln(lean_mk_string(output.as_ptr()));
    lean_dec(print_result);
    result
}

pub fn lean_io_initializing() -> bool {
    INITIALIZING.load(Ordering::Relaxed)
}

pub unsafe fn lean_io_as_task(act: *mut LeanObject, prio: *mut LeanObject) -> *mut LeanObject {
    let c = lean_alloc_closure(lean_io_as_task_fn as *mut c_void, 2, 1);
    lean_closure_set(c, 0, act);
    lean_task_spawn_core(c, lean_unbox(prio) as core::ffi::c_uint, true)
}

pub unsafe fn lean_io_map_task(
    f: *mut LeanObject,
    t: *mut LeanObject,
    prio: *mut LeanObject,
    sync: bool,
) -> *mut LeanObject {
    let c = lean_alloc_closure(lean_io_bind_task_fn as *mut c_void, 2, 1);
    lean_closure_set(c, 0, f);
    lean_task_map_core(c, t, lean_unbox(prio) as core::ffi::c_uint, sync, true)
}

pub unsafe fn lean_io_bind_task(
    t: *mut LeanObject,
    f: *mut LeanObject,
    prio: *mut LeanObject,
    sync: bool,
) -> *mut LeanObject {
    let c = lean_alloc_closure(lean_io_bind_task_fn as *mut c_void, 2, 1);
    lean_closure_set(c, 0, f);
    lean_task_bind_core(t, c, lean_unbox(prio) as core::ffi::c_uint, sync, true)
}

pub unsafe fn lean_io_mono_ms_now() -> *mut LeanObject {
    static START: OnceLock<Instant> = OnceLock::new();
    let start = START.get_or_init(Instant::now);
    lean_uint64_to_nat(start.elapsed().as_millis() as u64)
}

pub unsafe fn lean_io_mono_nanos_now() -> *mut LeanObject {
    static START: OnceLock<Instant> = OnceLock::new();
    let start = START.get_or_init(Instant::now);
    lean_uint64_to_nat(start.elapsed().as_nanos() as u64)
}

pub unsafe fn lean_io_get_random_bytes(nbytes: usize) -> *mut LeanObject {
    if nbytes == 0 {
        return lean_io_result_mk_ok(lean_alloc_sarray(1, 0, 0));
    }
    if lean_alloc_sarray_would_overflow(1, nbytes) {
        return lean_io_result_mk_error(lean_decode_io_error(libc::ENOMEM, core::ptr::null_mut()));
    }

    let res = lean_alloc_sarray(1, 0, nbytes);
    let mut remain = nbytes;
    let mut dst = lean_sarray_cptr(res).cast_mut();

    {
        let random_path = c"/dev/urandom";
        let fd = libc::open(random_path.as_ptr(), libc::O_RDONLY | libc::O_CLOEXEC);
        if fd < 0 {
            lean_dec(res);
            let fname = lean_mk_string(random_path.as_ptr());
            return lean_io_result_mk_error(lean_decode_io_error(lean_errno(), fname));
        }

        while remain > 0 {
            let read_size = remain;

            let nread = libc::read(fd, dst.cast(), read_size);
            if nread < 0 {
                if lean_errno() != libc::EINTR {
                    let err = lean_errno();
                    libc::close(fd);
                    lean_dec(res);
                    return lean_io_result_mk_error(lean_decode_io_error(
                        err,
                        core::ptr::null_mut(),
                    ));
                }
            } else {
                remain -= nread as usize;
                dst = dst.add(nread as usize);
            }
        }
        libc::close(fd);
    }

    lean_sarray_set_size(res, nbytes);
    lean_io_result_mk_ok(res)
}

pub use leanh_l1_initializers::r#priv::lean_alloc_sarray_would_overflow::lean_alloc_sarray_would_overflow;

pub fn lean_io_check_canceled() -> bool {
    let ct = current_task();
    if ct.is_null() {
        return false;
    }
    unsafe {
        let imp = (*ct).m_imp as *mut LeanTaskImp;
        debug_assert!(!imp.is_null());
        if (*imp).m_canceled {
            return true;
        }
    }
    get_task_manager()
        .map(|tm| is_shutting_down(&tm))
        .unwrap_or(false)
}

pub fn lean_io_cancel(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_cancel");
}

pub fn lean_io_get_task_state(_: *mut LeanObject) -> LeanTaskState {
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

use leanh_l1::emitted::lean_box::lean_box;
use leanh_l1::r#priv::lean_string_cstr::lean_string_cstr;
use leanh_l1::runtime_apply::lean_apply_1;
pub use leanh_l1_initializers::r#priv::lean_io_prim_handle_flush::lean_io_prim_handle_flush;
pub use leanh_l1_initializers::r#priv::lean_io_prim_handle_is_tty::lean_io_prim_handle_is_tty;

pub fn lean_io_prim_handle_rewind(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_prim_handle_rewind");
}

pub fn lean_io_prim_handle_truncate(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_io_prim_handle_truncate");
}

pub use leanh_l1_initializers::r#priv::lean_io_prim_handle_read::lean_io_prim_handle_read;

pub use leanh_l1_initializers::r#priv::lean_io_prim_handle_write::lean_io_prim_handle_write;

pub use leanh_l1_initializers::r#priv::lean_io_prim_handle_get_line::lean_io_prim_handle_get_line;

pub use leanh_l1_initializers::r#priv::lean_io_prim_handle_put_str::lean_io_prim_handle_put_str;

use crate::r#priv::is_shutting_down::is_shutting_down;
use crate::r#priv::lean_io_as_task_fn::lean_io_as_task_fn;
use crate::r#priv::lean_io_bind_task_fn::lean_io_bind_task_fn;
use crate::r#priv::lean_task_bind_core::lean_task_bind_core;
use crate::r#priv::lean_task_map_core::lean_task_map_core;
use crate::r#priv::lean_task_spawn_core::lean_task_spawn_core;
use crate::r#priv::uint_family::lean_uint64_to_nat;

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

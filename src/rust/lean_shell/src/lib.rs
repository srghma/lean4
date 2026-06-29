/*
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
*/

use core::ffi::{c_char, c_int, c_uint};
use runtime::{
    lean_box, lean_dec, lean_finalize, lean_inc, lean_initialize, lean_io_error_to_string_rust,
    lean_io_result_get_error, lean_io_result_get_value, lean_io_result_is_ok, lean_mk_string,
    lean_runtime_mk_cnstr, lean_string_cstr, lean_unbox, LeanObject,
};
use std::ffi::{CStr, CString};
use std::io::{self, Write};
use std::slice;

fn multi_thread() -> bool {
    option_env!("LEAN_RUST_MULTI_THREAD") == Some("1")
}

fn debug_build() -> bool {
    option_env!("LEAN_RUST_DEBUG") == Some("1")
}

use runtime::lean_enable_initializer_execution;
use runtime::lean_finalize_task_manager;
use runtime::lean_init_search_path;
use runtime::lean_init_task_manager_using;
use runtime::lean_io_mark_end_initialization;
use runtime::lean_shell_main;
use runtime::lean_shell_options_get_num_threads;
use runtime::lean_shell_options_get_profiler;
use runtime::lean_shell_options_get_run;
use runtime::lean_shell_options_mk;
use runtime::lean_shell_options_process;

struct TaskManagerGuard;

impl Drop for TaskManagerGuard {
    fn drop(&mut self) {
        unsafe { lean_finalize_task_manager() }
    }
}

struct LeanInitializerGuard;

impl Drop for LeanInitializerGuard {
    fn drop(&mut self) {
        unsafe { lean_finalize() }
    }
}

#[derive(Copy, Clone)]
enum ArgMode {
    None,
    Required,
    Optional,
}

fn long_option(name: &str) -> Option<(c_char, ArgMode)> {
    let candidates = [
        ("version", b'v' as c_char, ArgMode::None, true),
        ("help", b'h' as c_char, ArgMode::None, true),
        ("githash", b'g' as c_char, ArgMode::None, true),
        ("short-version", b'V' as c_char, ArgMode::None, true),
        ("run", b'r' as c_char, ArgMode::None, true),
        ("o", b'o' as c_char, ArgMode::Optional, true),
        ("i", b'i' as c_char, ArgMode::Optional, true),
        ("stdin", b'I' as c_char, ArgMode::None, true),
        ("root", b'R' as c_char, ArgMode::Required, true),
        ("memory", b'M' as c_char, ArgMode::Required, true),
        ("trust", b't' as c_char, ArgMode::Required, true),
        ("profile", b'P' as c_char, ArgMode::None, true),
        ("stats", b'a' as c_char, ArgMode::None, true),
        ("quiet", b'q' as c_char, ArgMode::None, true),
        ("deps", b'd' as c_char, ArgMode::None, true),
        ("src-deps", b'O' as c_char, ArgMode::None, true),
        ("deps-json", b'N' as c_char, ArgMode::None, true),
        ("timeout", b'T' as c_char, ArgMode::Optional, true),
        ("c", b'c' as c_char, ArgMode::Optional, true),
        ("bc", b'b' as c_char, ArgMode::Optional, true),
        ("features", b'f' as c_char, ArgMode::None, true),
        ("exitOnPanic", b'e' as c_char, ArgMode::None, true),
        ("plugin", b'p' as c_char, ArgMode::Required, true),
        ("load-dynlib", b'l' as c_char, ArgMode::Required, true),
        ("setup", b'u' as c_char, ArgMode::Required, true),
        ("error", b'E' as c_char, ArgMode::Required, true),
        ("json", b'J' as c_char, ArgMode::None, true),
        ("print-prefix", b'x' as c_char, ArgMode::None, true),
        ("print-libdir", b'L' as c_char, ArgMode::None, true),
        ("debug", b'B' as c_char, ArgMode::Required, debug_build()),
        ("threads", b'j' as c_char, ArgMode::Required, multi_thread()),
        ("tstack", b's' as c_char, ArgMode::Required, multi_thread()),
        ("server", b'S' as c_char, ArgMode::None, multi_thread()),
        ("worker", b'W' as c_char, ArgMode::None, multi_thread()),
    ];
    let mut exact = None;
    let mut prefix = None;
    for (candidate, ch, mode, enabled) in candidates {
        if !enabled {
            continue;
        }
        if candidate == name {
            exact = Some((ch, mode));
            break;
        }
        if candidate.starts_with(name) {
            if prefix.is_some() {
                return None;
            }
            prefix = Some((ch, mode));
        }
    }
    exact.or(prefix)
}

fn short_option(ch: char) -> Option<ArgMode> {
    Some(match ch {
        'v' | 'h' | 'g' | 'V' | 'r' | 'I' | 'P' | 'a' | 'q' | 'd' | 'O' | 'N' | 'f' | 'e' | 'J'
        | 'x' | 'L' => ArgMode::None,
        'o' | 'i' | 'T' | 'c' | 'b' | 'R' | 'M' | 't' | 'p' | 'l' | 'u' | 'E' | 'D' => {
            ArgMode::Required
        }
        'B' if debug_build() => ArgMode::Required,
        'j' | 's' | 'S' | 'W' if multi_thread() => {
            if ch == 'j' || ch == 's' {
                ArgMode::Required
            } else {
                ArgMode::None
            }
        }
        _ => return None,
    })
}

unsafe fn make_opt_arg(value: Option<&CStr>) -> *mut LeanObject {
    match value {
        Some(text) => {
            let string = lean_mk_string(text.as_ptr());
            let mut fields = [string];
            lean_runtime_mk_cnstr(1, 1, fields.as_mut_ptr(), 0)
        }
        None => lean_box(0),
    }
}

unsafe fn print_io_error(prefix: Option<&str>, err: *mut LeanObject) {
    let msg = lean_io_error_to_string_rust(err);
    let text = CStr::from_ptr(lean_string_cstr(msg));
    let mut stderr = io::stderr().lock();
    if let Some(prefix) = prefix {
        let _ = stderr.write_all(prefix.as_bytes());
    }
    let _ = stderr.write_all(text.to_bytes());
    let _ = stderr.write_all(b"\n");
    lean_dec(msg);
}

unsafe fn handle_io_result(prefix: Option<&str>, result: *mut LeanObject) -> bool {
    if lean_io_result_is_ok(result) {
        lean_dec(result);
        true
    } else {
        let err = lean_io_result_get_error(result);
        lean_inc(err);
        lean_dec(result);
        print_io_error(prefix, err);
        lean_dec(err);
        false
    }
}

unsafe fn init_search_path() -> bool {
    handle_io_result(Some("error: "), lean_init_search_path())
}

unsafe fn enable_initializer_execution() -> bool {
    handle_io_result(Some("error: "), lean_enable_initializer_execution())
}

unsafe fn parse_and_process_options(
    argc: c_int,
    argv: *mut *mut c_char,
    mut shell_opts: *mut LeanObject,
) -> Result<(*mut LeanObject, Vec<*mut c_char>), c_int> {
    let args = slice::from_raw_parts(argv, argc as usize);
    let mut idx = 1usize;
    let mut positional = Vec::new();

    while idx < args.len() {
        let raw = args[idx];
        if raw.is_null() {
            break;
        }
        let token = CStr::from_ptr(raw);
        let bytes = token.to_bytes();
        if bytes.is_empty() || bytes[0] != b'-' {
            positional.push(raw);
            idx += 1;
            continue;
        }
        if bytes == b"--" {
            idx += 1;
            positional.extend(args[idx..].iter().copied().filter(|p| !p.is_null()));
            break;
        }

        let mut opt_char: c_char;
        let mut opt_arg: Option<&CStr> = None;
        let opt_arg_storage: Option<CString>;
        let mut consumed_extra = 0usize;

        if bytes.len() >= 2 && bytes[1] == b'-' {
            let payload = &bytes[2..];
            let (name_bytes, arg_bytes) = match payload.iter().position(|&b| b == b'=') {
                Some(pos) => (&payload[..pos], Some(&payload[pos + 1..])),
                None => (payload, None),
            };
            let name = match std::str::from_utf8(name_bytes) {
                Ok(name) => name,
                Err(_) => {
                    opt_char = 0;
                    shell_opts = process_option(shell_opts, opt_char, None)?;
                    if get_run(shell_opts) {
                        positional.clear();
                        positional.extend(args[idx + 1..].iter().copied().filter(|p| !p.is_null()));
                        break;
                    }
                    idx += 1;
                    continue;
                }
            };
            if let Some((ch, mode)) = long_option(name) {
                opt_char = ch;
                match (mode, arg_bytes) {
                    (ArgMode::None, _) => {}
                    (ArgMode::Required, Some(arg)) => {
                        opt_arg_storage = Some(CString::new(arg).expect("argv contains NUL"));
                        opt_arg = Some(opt_arg_storage.as_ref().unwrap().as_c_str());
                    }
                    (ArgMode::Required, None) => {
                        if idx + 1 < args.len() {
                            opt_arg = Some(CStr::from_ptr(args[idx + 1]));
                            consumed_extra = 1;
                        }
                    }
                    (ArgMode::Optional, Some(arg)) => {
                        opt_arg_storage = Some(CString::new(arg).expect("argv contains NUL"));
                        opt_arg = Some(opt_arg_storage.as_ref().unwrap().as_c_str());
                    }
                    (ArgMode::Optional, None) => {}
                }
            } else {
                opt_char = 0;
            }
        } else {
            let ch = bytes[1] as c_char;
            opt_char = ch;
            if let Some(mode) = short_option(bytes[1] as char) {
                match mode {
                    ArgMode::None => {}
                    ArgMode::Required => {
                        if bytes.len() > 2 {
                            opt_arg_storage =
                                Some(CString::new(&bytes[2..]).expect("argv contains NUL"));
                            opt_arg = Some(opt_arg_storage.as_ref().unwrap().as_c_str());
                        } else if idx + 1 < args.len() {
                            opt_arg = Some(CStr::from_ptr(args[idx + 1]));
                            consumed_extra = 1;
                        }
                    }
                    ArgMode::Optional => {}
                }
            } else {
                opt_char = 0;
            }
        }

        let next = process_option(shell_opts, opt_char, opt_arg)?;
        shell_opts = next;
        if get_run(shell_opts) {
            let start = idx + 1 + consumed_extra;
            positional.clear();
            positional.extend(args[start..].iter().copied().filter(|p| !p.is_null()));
            break;
        }
        idx += 1 + consumed_extra;
    }

    Ok((shell_opts, positional))
}

unsafe fn process_option(
    shell_opts: *mut LeanObject,
    opt: c_char,
    opt_arg: Option<&CStr>,
) -> Result<*mut LeanObject, c_int> {
    let opt_arg_obj = make_opt_arg(opt_arg);
    let result = lean_shell_options_process(shell_opts, opt as c_uint, opt_arg_obj);
    if lean_io_result_is_ok(result) {
        let next = lean_io_result_get_value(result);
        lean_inc(next);
        lean_dec(result);
        Ok(next)
    } else {
        let code = lean_unbox(lean_io_result_get_error(result)) as c_int;
        lean_dec(result);
        Err(code)
    }
}

unsafe fn get_run(shell_opts: *mut LeanObject) -> bool {
    lean_inc(shell_opts);
    let run = lean_shell_options_get_run(shell_opts) != 0;
    run
}

unsafe fn get_profiler(shell_opts: *mut LeanObject) -> bool {
    lean_inc(shell_opts);
    lean_shell_options_get_profiler(shell_opts) != 0
}

unsafe fn get_num_threads(shell_opts: *mut LeanObject) -> c_uint {
    lean_inc(shell_opts);
    lean_shell_options_get_num_threads(shell_opts)
}

unsafe fn make_args_list(argc: c_int, argv: *mut *mut c_char) -> *mut LeanObject {
    let args = slice::from_raw_parts(argv, argc as usize);
    let mut list = lean_box(0);
    for raw in args.iter().rev() {
        let text = lean_mk_string(*raw);
        let mut fields = [text, list];
        list = lean_runtime_mk_cnstr(1, 2, fields.as_mut_ptr(), 0);
    }
    list
}

fn main_impl(argc: c_int, argv: *mut *mut c_char) -> c_int {
    unsafe {
        lean_initialize();
        let _init_guard = LeanInitializerGuard;

        if !init_search_path() {
            return 1;
        }
        if !enable_initializer_execution() {
            return 1;
        }

        let shell_opts = lean_shell_options_mk(lean_box(0));
        let (shell_opts, positional_args) = match parse_and_process_options(argc, argv, shell_opts)
        {
            Ok(v) => v,
            Err(code) => return code,
        };

        lean_io_mark_end_initialization();

        let _profiling = get_profiler(shell_opts);
        let num_threads = get_num_threads(shell_opts);

        lean_init_task_manager_using(num_threads);
        let _task_manager_guard = TaskManagerGuard;

        let args = make_args_list(
            positional_args.len() as c_int,
            positional_args.as_ptr() as *mut *mut c_char,
        );
        let result = lean_shell_main(args, shell_opts);
        if lean_io_result_is_ok(result) {
            let rc = lean_unbox(lean_io_result_get_value(result)) as c_int;
            lean_dec(result);
            rc
        } else {
            let err = lean_io_result_get_error(result);
            lean_inc(err);
            lean_dec(result);
            print_io_error(None, err);
            lean_dec(err);
            1
        }
    }
}

pub fn main(argc: c_int, argv: *mut *mut c_char) -> c_int {
    main_impl(argc, argv)
}

pub(crate) fn lean_main(argc: c_int, argv: *mut *mut c_char) -> c_int {
    main_impl(argc, argv)
}

use leanh::LeanObject;
use runtime::leanh_extra as leanh;
// Generated stub file for Lean FFI imports
// Source: src/Init/Core.lean

pub unsafe fn lean_mk_thunk(closure: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_mk_thunk(closure) }
}

pub fn lean_task_pure(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_task_pure");
}

pub fn lean_task_get_own(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_task_get_own");
}

pub unsafe fn lean_thunk_pure(value: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_thunk_pure(value) }
}

pub unsafe fn lean_thunk_get_own(thunk: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_thunk_get_own(thunk) }
}

pub fn lean_task_spawn(_: *mut LeanObject, _: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_task_spawn");
}

pub fn lean_task_map(
    _: *mut LeanObject,
    _: *mut LeanObject,
    _: *mut LeanObject,
    _: u8,
) -> *mut LeanObject {
    todo!("Stub for lean_task_map");
}

pub fn lean_task_bind(
    _: *mut LeanObject,
    _: *mut LeanObject,
    _: *mut LeanObject,
    _: u8,
) -> *mut LeanObject {
    todo!("Stub for lean_task_bind");
}

pub fn lean_strict_or(a: u8, b: u8) -> u8 {
    ((a != 0) || (b != 0)) as u8
}

pub fn lean_strict_and(a: u8, b: u8) -> u8 {
    ((a != 0) && (b != 0)) as u8
}
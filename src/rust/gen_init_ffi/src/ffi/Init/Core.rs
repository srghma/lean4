use leanh::LeanObject;
use leanh_l1::datatypes::{LeanObject, LeanScalarArray, LeanStringObject};
// Generated stub file for Lean FFI imports
// Source: src/Init/Core.lean
use leanh_l1::runtime_object_task::lean_task_get_own::lean_task_get_own as leanh_l1_lean_task_get_own;

pub unsafe fn lean_mk_thunk(closure: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh::lean_mk_thunk(closure) }
}

pub fn lean_task_pure(_: *mut LeanObject) -> *mut LeanObject {
    todo!("Stub for lean_task_pure");
}

pub fn lean_task_get_own(t: *mut LeanObject) -> *mut LeanObject {
    unsafe { leanh_l1_lean_task_get_own(t) }
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

pub fn lean_strict_or(a: bool, b: bool) -> bool {
    a || b
}

pub fn lean_strict_and(a: bool, b: bool) -> bool {
    a && b
}

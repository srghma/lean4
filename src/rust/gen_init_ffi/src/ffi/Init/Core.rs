use std::sync::atomic::AtomicPtr;

use leanh_l1::{
    datatypes::{LeanObject, LeanObjectTag, LeanTaskObject, LeanThunkObject},
    emitted::{lean_inc::lean_inc, lean_unbox::lean_unbox},
    r#priv::lean_alloc_small_object::lean_alloc_small_object,
};

use crate::r#priv::{
    lean_task_bind_core::lean_task_bind_core, lean_task_map_core::lean_task_map_core,
    lean_task_spawn_core::lean_task_spawn_core, lean_thunk_get::lean_thunk_get,
    set_task_header_st::set_task_header_st,
};
// Generated stub file for Lean FFI imports
// Source: src/Init/Core.lean

#[inline]
pub unsafe fn lean_mk_thunk(closure: *mut LeanObject) -> *mut LeanObject {
    let o =
        lean_alloc_small_object(core::mem::size_of::<LeanThunkObject>()) as *mut LeanThunkObject;
    (*o).m_header.rc = 1;
    (*o).m_header.tag = LeanObjectTag::Thunk.as_u8();
    (*o).m_header.other = 0;
    (*o).m_header.cs_size = 0;
    (*o).m_value = AtomicPtr::new(core::ptr::null_mut());
    (*o).m_closure = AtomicPtr::new(closure);
    o as *mut LeanObject
}

#[inline]
pub unsafe fn lean_task_pure(value: *mut LeanObject) -> *mut LeanObject {
    let o = lean_alloc_small_object(core::mem::size_of::<LeanTaskObject>()) as *mut LeanTaskObject;
    set_task_header_st(o as *mut LeanObject);
    (*o).m_value = AtomicPtr::new(value);
    (*o).m_imp = core::ptr::null_mut();
    o as *mut LeanObject
}

pub use leanh_l1::runtime_object_task::lean_task_get_own::lean_task_get_own;

#[inline]
pub unsafe fn lean_thunk_pure(value: *mut LeanObject) -> *mut LeanObject {
    let o =
        lean_alloc_small_object(core::mem::size_of::<LeanThunkObject>()) as *mut LeanThunkObject;
    (*o).m_header.rc = 1;
    (*o).m_header.tag = LeanObjectTag::Thunk.as_u8();
    (*o).m_header.other = 0;
    (*o).m_header.cs_size = 0;
    (*o).m_value = AtomicPtr::new(value);
    (*o).m_closure = AtomicPtr::new(core::ptr::null_mut());
    o as *mut LeanObject
}

#[inline]
pub unsafe fn lean_thunk_get_own(thunk: *mut LeanObject) -> *mut LeanObject {
    let value = lean_thunk_get(thunk);
    lean_inc(value);
    value
}

#[inline]
pub unsafe fn lean_task_spawn(c: *mut LeanObject, prio: *mut LeanObject) -> *mut LeanObject {
    lean_task_spawn_core(c, lean_unbox(prio) as u32, false)
}

#[inline]
pub unsafe fn lean_task_map(
    f: *mut LeanObject,
    t: *mut LeanObject,
    prio: *mut LeanObject,
    sync: bool,
) -> *mut LeanObject {
    lean_task_map_core(f, t, lean_unbox(prio) as u32, sync, false)
}

#[inline]
pub unsafe fn lean_task_bind(
    t: *mut LeanObject,
    f: *mut LeanObject,
    prio: *mut LeanObject,
    sync: bool,
) -> *mut LeanObject {
    lean_task_bind_core(t, f, lean_unbox(prio) as u32, sync, false)
}

#[inline]
pub fn lean_strict_or(a: bool, b: bool) -> bool {
    a || b
}

#[inline]
pub fn lean_strict_and(a: bool, b: bool) -> bool {
    a && b
}

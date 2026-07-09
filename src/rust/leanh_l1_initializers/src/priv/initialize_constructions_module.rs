use leanh_l1::{
    datatypes::{LeanExternalObject, LeanObject, Size},
    emitted::{
        lean_box::lean_box, lean_inc::lean_inc, lean_mark_persistent::lean_mark_persistent,
        lean_mk_string::lean_mk_string,
    },
};
use std::{ffi::c_void, ptr};

use crate::todo_import_from_lean::lean_name_mk_string::lean_name_mk_string;

struct NameGeneratorState {
    tmp_prefix: *mut LeanObject,
    prefixes: Vec<*mut LeanObject>,
}

unsafe impl Send for NameGeneratorState {}
unsafe fn name_contains_registered_prefix(state: &NameGeneratorState, n: *mut LeanObject) -> bool {
    state
        .prefixes
        .iter()
        .copied()
        .any(|p| lean_name_eq(p, n) != 0)
}

static mut CONSTRUCTIONS_FRESH: LeanName = LeanName {
    obj: ptr::null_mut(),
};

static NAME_GENERATOR_STATE: std::sync::Mutex<Option<NameGeneratorState>> =
    std::sync::Mutex::new(None);

pub unsafe fn lean_register_name_generator_prefix(n: *mut LeanObject) {
    let mut guard = NAME_GENERATOR_STATE.lock().unwrap();
    let state = guard
        .as_mut()
        .expect("name generator registry is not initialized");
    assert!(!name_contains_registered_prefix(state, n));
    lean_inc(n);
    state.prefixes.push(n);
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct LeanName {
    obj: *mut LeanObject,
}

pub(crate) unsafe fn mk_name(text: &str) -> LeanName {
    let c_text = std::ffi::CString::new(text).expect("option names never contain NUL");
    let raw_text = lean_mk_string(c_text.as_ptr());
    let raw_name = lean_name_mk_string(lean_box(0), raw_text);
    LeanName { obj: raw_name }
}
pub fn initialize_constructions_util() {
    unsafe {
        CONSTRUCTIONS_FRESH = mk_name("_cnstr_fresh");
        lean_mark_persistent(CONSTRUCTIONS_FRESH.obj);
        lean_register_name_generator_prefix(CONSTRUCTIONS_FRESH.obj);
    }
}

pub fn initialize_constructions_module() {
    initialize_constructions_util();
}

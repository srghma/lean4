use leanh_l1::{
    datatypes::LeanObject,
    emitted::{
        lean_box::lean_box, lean_mark_persistent::lean_mark_persistent,
        lean_mk_string::lean_mk_string,
    },
};

use crate::todo_import_from_lean::lean_name_mk_string::lean_name_mk_string;

pub struct NameGeneratorState {
    pub tmp_prefix: *mut LeanObject,
    pub prefixes: Vec<*mut LeanObject>,
}

unsafe impl Send for NameGeneratorState {}

pub static NAME_GENERATOR_STATE: std::sync::Mutex<Option<NameGeneratorState>> =
    std::sync::Mutex::new(None);

pub fn initialize_name_generator() {
    unsafe {
        let c_str = std::ffi::CString::new("_uniq").expect("static string has no NULs");
        let string = lean_mk_string(c_str.as_ptr());
        let tmp = lean_name_mk_string(lean_box(0), string);
        lean_mark_persistent(tmp);
        let mut guard = NAME_GENERATOR_STATE.lock().unwrap();
        let state = NameGeneratorState {
            tmp_prefix: tmp,
            prefixes: vec![tmp],
        };
        *guard = Some(state);
    }
}

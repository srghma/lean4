use leanh_l1::emitted::lean_mk_string::lean_mk_string;

use crate::{
    r#priv::initialize_constructions_module::{mk_name, LeanName},
    todo_import_from_lean::lean_name_mk_string::lean_name_mk_string,
};

pub(crate) unsafe fn mk_name_path(components: &[&str]) -> LeanName {
    let mut name = mk_name(components[0]);
    for component in &components[1..] {
        let c_text = std::ffi::CString::new(*component).expect("option names never contain NUL");
        let raw_text = lean_mk_string(c_text.as_ptr());
        let raw_name = lean_name_mk_string(name.obj, raw_text);
        name = LeanName { obj: raw_name };
    }
    name
}

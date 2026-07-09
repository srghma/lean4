use leanh_l1::emitted::lean_mark_persistent::lean_mark_persistent;
use std::ptr;

use crate::r#priv::initialize_constructions_module::{LeanName, mk_name};

static mut VERBOSE_OPT: LeanName = LeanName {
    obj: ptr::null_mut(),
};
static mut MAX_MEMORY_OPT: LeanName = LeanName {
    obj: ptr::null_mut(),
};
static mut TIMEOUT_OPT: LeanName = LeanName {
    obj: ptr::null_mut(),
};

pub fn initialize_options() {
    unsafe {
        VERBOSE_OPT = mk_name("verbose");
        MAX_MEMORY_OPT = mk_name("max_memory");
        TIMEOUT_OPT = mk_name("timeout");
        lean_mark_persistent(VERBOSE_OPT.obj);
        lean_mark_persistent(MAX_MEMORY_OPT.obj);
        lean_mark_persistent(TIMEOUT_OPT.obj);
    }
}

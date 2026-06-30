// Lean compiler output
// Module: Lean.Server.Test.Refs
// Imports: Init.Prelude
use crate::r#gen::Init::Prelude::{initialize_Init_Prelude, runtime_initialize_Init_Prelude};
pub static mut l_Lean_Server_Test_Refs_test7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Server_Test_Refs_test8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Server_Test_Refs_test9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Server_Test_Refs_test10: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Server_Test_Refs_test7() -> *mut leanh::LeanObject {
    let mut v___x_5_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5_ = leanh::lean_box(0);
    return v___x_5_;
}
pub unsafe fn _init_l_Lean_Server_Test_Refs_test8() -> *mut leanh::LeanObject {
    let mut v___x_6_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6_ = leanh::lean_box(0);
    return v___x_6_;
}
pub unsafe fn _init_l_Lean_Server_Test_Refs_test9() -> *mut leanh::LeanObject {
    let mut v___x_7_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7_ = leanh::lean_box(0);
    return v___x_7_;
}
pub unsafe fn _init_l_Lean_Server_Test_Refs_test10() -> *mut leanh::LeanObject {
    let mut v___x_8_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8_ = leanh::lean_box(0);
    return v___x_8_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Server_Test_Refs(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Prelude(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Server_Test_Refs_test7 = _init_l_Lean_Server_Test_Refs_test7();
    leanh::lean_mark_persistent(l_Lean_Server_Test_Refs_test7);
    l_Lean_Server_Test_Refs_test8 = _init_l_Lean_Server_Test_Refs_test8();
    leanh::lean_mark_persistent(l_Lean_Server_Test_Refs_test8);
    l_Lean_Server_Test_Refs_test9 = _init_l_Lean_Server_Test_Refs_test9();
    leanh::lean_mark_persistent(l_Lean_Server_Test_Refs_test9);
    l_Lean_Server_Test_Refs_test10 = _init_l_Lean_Server_Test_Refs_test10();
    leanh::lean_mark_persistent(l_Lean_Server_Test_Refs_test10);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Server_Test_Refs(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Server_Test_Refs(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Prelude(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Server_Test_Refs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Server_Test_Refs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Server_Test_Refs(builtin);
}
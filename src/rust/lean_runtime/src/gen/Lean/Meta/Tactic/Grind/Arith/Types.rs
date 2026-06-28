// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Types
// Imports: Init.Core
use crate::r#gen::Init::Core::{initialize_Init_Core, runtime_initialize_Init_Core};
pub static mut l_Lean_Meta_Grind_Arith_instInhabitedState_default: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_instInhabitedState: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Grind_Arith_State_toCtorIdx(
    mut v_x_5_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_6_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_instInhabitedState_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7_ = crate::leanh::lean_box(0);
    return v___x_7_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_instInhabitedState() -> *mut crate::leanh::LeanObject {
    let mut v___x_8_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8_ = crate::leanh::lean_box(0);
    return v___x_8_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Types(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Core(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_Grind_Arith_instInhabitedState_default =
        _init_l_Lean_Meta_Grind_Arith_instInhabitedState_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_instInhabitedState_default);
    l_Lean_Meta_Grind_Arith_instInhabitedState = _init_l_Lean_Meta_Grind_Arith_instInhabitedState();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_instInhabitedState);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Types(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Types(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Core(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Types(builtin);
}

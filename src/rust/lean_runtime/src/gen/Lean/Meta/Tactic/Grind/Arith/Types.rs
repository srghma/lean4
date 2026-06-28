// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Types
// Imports: Init.Core
use crate::r#gen::Init::Core::{initialize_Init_Core, runtime_initialize_Init_Core};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_box, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_mark_persistent, lean_unsigned_to_nat,
};
pub static mut l_Lean_Meta_Grind_Arith_instInhabitedState_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_instInhabitedState: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Grind_Arith_State_toCtorIdx(
    mut v_x_5_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6_: *mut LeanObject = core::ptr::null_mut();
    v___x_6_ = lean_unsigned_to_nat(0);
    return v___x_6_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_instInhabitedState_default() -> *mut LeanObject {
    let mut v___x_7_: *mut LeanObject = core::ptr::null_mut();
    v___x_7_ = lean_box(0);
    return v___x_7_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_instInhabitedState() -> *mut LeanObject {
    let mut v___x_8_: *mut LeanObject = core::ptr::null_mut();
    v___x_8_ = lean_box(0);
    return v___x_8_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Types(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Core(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_Grind_Arith_instInhabitedState_default =
        _init_l_Lean_Meta_Grind_Arith_instInhabitedState_default();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_instInhabitedState_default);
    l_Lean_Meta_Grind_Arith_instInhabitedState = _init_l_Lean_Meta_Grind_Arith_instInhabitedState();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_instInhabitedState);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Types(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Types(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Core(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Types(builtin);
}

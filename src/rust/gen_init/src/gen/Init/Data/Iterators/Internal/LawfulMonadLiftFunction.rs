// Lean compiler output
// Module: Init.Data.Iterators.Internal.LawfulMonadLiftFunction
// Imports: Init.Control.Lawful.MonadLift
use crate::r#gen::Init::Control::Lawful::MonadLift::{
    initialize_Init_Control_Lawful_MonadLift, runtime_initialize_Init_Control_Lawful_MonadLift,
};
pub unsafe fn l_Std_Internal_idToMonad___redArg(
    mut v_inst_13_: *mut leanh::LeanObject,
    mut v_x_14_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_15_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_16_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_17_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_15_ = leanh::lean_ctor_get(v_inst_13_, 0);
    leanh::lean_inc_ref(v_toApplicative_15_);
    leanh::lean_dec_ref(v_inst_13_);
    v_toPure_16_ = leanh::lean_ctor_get(v_toApplicative_15_, 1);
    leanh::lean_inc(v_toPure_16_);
    leanh::lean_dec_ref(v_toApplicative_15_);
    v___x_17_ = leanh::lean_apply_2(v_toPure_16_, leanh::lean_box(0), v_x_14_);
    return v___x_17_;
}
pub unsafe fn l_Std_Internal_idToMonad(
    mut v_m_18_: *mut leanh::LeanObject,
    mut v_inst_19_: *mut leanh::LeanObject,
    mut v_00_u03b1_20_: *mut leanh::LeanObject,
    mut v_x_21_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_22_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_23_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_24_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_22_ = leanh::lean_ctor_get(v_inst_19_, 0);
    leanh::lean_inc_ref(v_toApplicative_22_);
    leanh::lean_dec_ref(v_inst_19_);
    v_toPure_23_ = leanh::lean_ctor_get(v_toApplicative_22_, 1);
    leanh::lean_inc(v_toPure_23_);
    leanh::lean_dec_ref(v_toApplicative_22_);
    v___x_24_ = leanh::lean_apply_2(v_toPure_23_, leanh::lean_box(0), v_x_21_);
    return v___x_24_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Lawful_MonadLift(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Lawful_MonadLift(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(builtin);
}
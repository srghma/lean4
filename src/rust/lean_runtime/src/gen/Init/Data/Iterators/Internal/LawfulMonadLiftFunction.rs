// Lean compiler output
// Module: Init.Data.Iterators.Internal.LawfulMonadLiftFunction
// Imports: Init.Control.Lawful.MonadLift
use crate::r#gen::Init::Control::Lawful::MonadLift::{
    initialize_Init_Control_Lawful_MonadLift, runtime_initialize_Init_Control_Lawful_MonadLift,
};
pub unsafe fn l_Std_Internal_idToMonad___redArg(
    mut v_inst_13_: *mut crate::leanh::LeanObject,
    mut v_x_14_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_15_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_16_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_17_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_15_ = crate::leanh::lean_ctor_get(v_inst_13_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_15_);
    crate::leanh::lean_dec_ref(v_inst_13_);
    v_toPure_16_ = crate::leanh::lean_ctor_get(v_toApplicative_15_, 1);
    crate::leanh::lean_inc(v_toPure_16_);
    crate::leanh::lean_dec_ref(v_toApplicative_15_);
    v___x_17_ = crate::leanh::lean_apply_2(v_toPure_16_, crate::leanh::lean_box(0), v_x_14_);
    return v___x_17_;
}
pub unsafe fn l_Std_Internal_idToMonad(
    mut v_m_18_: *mut crate::leanh::LeanObject,
    mut v_inst_19_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_20_: *mut crate::leanh::LeanObject,
    mut v_x_21_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_22_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_23_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_24_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_22_ = crate::leanh::lean_ctor_get(v_inst_19_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_22_);
    crate::leanh::lean_dec_ref(v_inst_19_);
    v_toPure_23_ = crate::leanh::lean_ctor_get(v_toApplicative_22_, 1);
    crate::leanh::lean_inc(v_toPure_23_);
    crate::leanh::lean_dec_ref(v_toApplicative_22_);
    v___x_24_ = crate::leanh::lean_apply_2(v_toPure_23_, crate::leanh::lean_box(0), v_x_21_);
    return v___x_24_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Lawful_MonadLift(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(
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
pub unsafe fn initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Lawful_MonadLift(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(builtin);
}

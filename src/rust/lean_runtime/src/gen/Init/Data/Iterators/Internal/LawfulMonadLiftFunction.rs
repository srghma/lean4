// Lean compiler output
// Module: Init.Data.Iterators.Internal.LawfulMonadLiftFunction
// Imports: Init.Control.Lawful.MonadLift
use crate::r#gen::Init::Control::Lawful::MonadLift::{
    initialize_Init_Control_Lawful_MonadLift, runtime_initialize_Init_Control_Lawful_MonadLift,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_2, lean_box, lean_ctor_get, lean_dec_ref, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
};
pub unsafe fn l_Std_Internal_idToMonad___redArg(
    mut v_inst_13_: *mut LeanObject,
    mut v_x_14_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_15_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_16_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_17_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_15_ = lean_ctor_get(v_inst_13_, 0);
    lean_inc_ref(v_toApplicative_15_);
    lean_dec_ref(v_inst_13_);
    v_toPure_16_ = lean_ctor_get(v_toApplicative_15_, 1);
    lean_inc(v_toPure_16_);
    lean_dec_ref(v_toApplicative_15_);
    v___x_17_ = lean_apply_2(v_toPure_16_, lean_box(0), v_x_14_);
    return v___x_17_;
}
pub unsafe fn l_Std_Internal_idToMonad(
    mut v_m_18_: *mut LeanObject,
    mut v_inst_19_: *mut LeanObject,
    mut v_00_u03b1_20_: *mut LeanObject,
    mut v_x_21_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_22_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_23_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_24_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_22_ = lean_ctor_get(v_inst_19_, 0);
    lean_inc_ref(v_toApplicative_22_);
    lean_dec_ref(v_inst_19_);
    v_toPure_23_ = lean_ctor_get(v_toApplicative_22_, 1);
    lean_inc(v_toPure_23_);
    lean_dec_ref(v_toApplicative_22_);
    v___x_24_ = lean_apply_2(v_toPure_23_, lean_box(0), v_x_21_);
    return v___x_24_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Lawful_MonadLift(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Lawful_MonadLift(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Internal_LawfulMonadLiftFunction(builtin);
}

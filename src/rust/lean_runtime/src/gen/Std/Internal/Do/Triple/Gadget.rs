// Lean compiler output
// Module: Std.Internal.Do.Triple.Gadget
// Imports: Std.Internal.Do.Triple.Basic Std.Internal.Do.Frame
use crate::r#gen::Std::Internal::Do::Frame::{
    initialize_Std_Internal_Do_Frame, runtime_initialize_Std_Internal_Do_Frame,
};
use crate::r#gen::Std::Internal::Do::Triple::Basic::{
    initialize_Std_Internal_Do_Triple_Basic, runtime_initialize_Std_Internal_Do_Triple_Basic,
};
pub unsafe fn l_Std_Internal_Do_assertGadget___redArg(
    mut v_inst_26_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_27_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_28_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_29_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_30_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_27_ = crate::leanh::lean_ctor_get(v_inst_26_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_27_);
    crate::leanh::lean_dec_ref(v_inst_26_);
    v_toPure_28_ = crate::leanh::lean_ctor_get(v_toApplicative_27_, 1);
    crate::leanh::lean_inc(v_toPure_28_);
    crate::leanh::lean_dec_ref(v_toApplicative_27_);
    v___x_29_ = crate::leanh::lean_box(0);
    v___x_30_ = crate::leanh::lean_apply_2(v_toPure_28_, crate::leanh::lean_box(0), v___x_29_);
    return v___x_30_;
}
pub unsafe fn l_Std_Internal_Do_assertGadget(
    mut v_m_31_: *mut crate::leanh::LeanObject,
    mut v_Pred_32_: *mut crate::leanh::LeanObject,
    mut v_EPred_33_: *mut crate::leanh::LeanObject,
    mut v_inst_34_: *mut crate::leanh::LeanObject,
    mut v_inst_35_: *mut crate::leanh::LeanObject,
    mut v_inst_36_: *mut crate::leanh::LeanObject,
    mut v_inst_37_: *mut crate::leanh::LeanObject,
    mut v_name_38_: *mut crate::leanh::LeanObject,
    mut v_as_39_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_40_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_40_ = l_Std_Internal_Do_assertGadget___redArg(v_inst_34_);
    return v___x_40_;
}
pub unsafe fn l_Std_Internal_Do_assertGadget___boxed(
    mut v_m_41_: *mut crate::leanh::LeanObject,
    mut v_Pred_42_: *mut crate::leanh::LeanObject,
    mut v_EPred_43_: *mut crate::leanh::LeanObject,
    mut v_inst_44_: *mut crate::leanh::LeanObject,
    mut v_inst_45_: *mut crate::leanh::LeanObject,
    mut v_inst_46_: *mut crate::leanh::LeanObject,
    mut v_inst_47_: *mut crate::leanh::LeanObject,
    mut v_name_48_: *mut crate::leanh::LeanObject,
    mut v_as_49_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_50_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_50_ = l_Std_Internal_Do_assertGadget(
        v_m_41_,
        v_Pred_42_,
        v_EPred_43_,
        v_inst_44_,
        v_inst_45_,
        v_inst_46_,
        v_inst_47_,
        v_name_48_,
        v_as_49_,
    );
    crate::leanh::lean_dec(v_as_49_);
    crate::leanh::lean_dec(v_name_48_);
    crate::leanh::lean_dec(v_inst_47_);
    return v_res_50_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Internal_Do_Triple_Gadget(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Internal_Do_Triple_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Do_Frame(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Internal_Do_Triple_Gadget(
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
pub unsafe fn initialize_Std_Internal_Do_Triple_Gadget(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Internal_Do_Triple_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Internal_Do_Frame(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Internal_Do_Triple_Gadget(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Internal_Do_Triple_Gadget(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Internal_Do_Triple_Gadget(builtin);
}

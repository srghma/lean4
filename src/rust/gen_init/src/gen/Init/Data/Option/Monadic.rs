// Lean compiler output
// Module: Init.Data.Option.Monadic
// Imports: Init.Data.Option.Instances Init.Control.Lawful Init.Data.Option.Lemmas
use crate::r#gen::Init::Control::Lawful::{
    initialize_Init_Control_Lawful, runtime_initialize_Init_Control_Lawful,
};
use crate::r#gen::Init::Data::Option::Instances::{
    initialize_Init_Data_Option_Instances, runtime_initialize_Init_Data_Option_Instances,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
pub unsafe fn l___private_Init_Data_Option_Monadic_0__Option_instDecidableEq_match__1_splitter___redArg(
    mut v_b_33_: *mut crate::leanh::LeanObject,
    mut v_h__1_34_: *mut crate::leanh::LeanObject,
    mut v_h__2_35_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_b_33_) == 0 {
        let mut v___x_36_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_37_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_35_);
        v___x_36_ = crate::leanh::lean_box(0);
        v___x_37_ = crate::leanh::lean_apply_1(v_h__1_34_, v___x_36_);
        return v___x_37_;
    } else {
        let mut v_val_38_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_39_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_34_);
        v_val_38_ = crate::leanh::lean_ctor_get(v_b_33_, 0);
        crate::leanh::lean_inc(v_val_38_);
        crate::leanh::lean_dec_ref_known(v_b_33_, 1);
        v___x_39_ = crate::leanh::lean_apply_1(v_h__2_35_, v_val_38_);
        return v___x_39_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Monadic_0__Option_instDecidableEq_match__1_splitter(
    mut v_00_u03b1_40_: *mut crate::leanh::LeanObject,
    mut v_motive_41_: *mut crate::leanh::LeanObject,
    mut v_b_42_: *mut crate::leanh::LeanObject,
    mut v_h__1_43_: *mut crate::leanh::LeanObject,
    mut v_h__2_44_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_b_42_) == 0 {
        let mut v___x_45_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_46_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_44_);
        v___x_45_ = crate::leanh::lean_box(0);
        v___x_46_ = crate::leanh::lean_apply_1(v_h__1_43_, v___x_45_);
        return v___x_46_;
    } else {
        let mut v_val_47_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_48_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_43_);
        v_val_47_ = crate::leanh::lean_ctor_get(v_b_42_, 0);
        crate::leanh::lean_inc(v_val_47_);
        crate::leanh::lean_dec_ref_known(v_b_42_, 1);
        v___x_48_ = crate::leanh::lean_apply_1(v_h__2_44_, v_val_47_);
        return v___x_48_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Monadic_0__Option_instForIn_x27InferInstanceMembershipOfMonad_match__1_splitter___redArg(
    mut v_____do__lift_49_: *mut crate::leanh::LeanObject,
    mut v_h__1_50_: *mut crate::leanh::LeanObject,
    mut v_h__2_51_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_49_) == 0 {
        let mut v_a_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_53_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_51_);
        v_a_52_ = crate::leanh::lean_ctor_get(v_____do__lift_49_, 0);
        crate::leanh::lean_inc(v_a_52_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_49_, 1);
        v___x_53_ = crate::leanh::lean_apply_1(v_h__1_50_, v_a_52_);
        return v___x_53_;
    } else {
        let mut v_a_54_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_55_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_50_);
        v_a_54_ = crate::leanh::lean_ctor_get(v_____do__lift_49_, 0);
        crate::leanh::lean_inc(v_a_54_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_49_, 1);
        v___x_55_ = crate::leanh::lean_apply_1(v_h__2_51_, v_a_54_);
        return v___x_55_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Monadic_0__Option_instForIn_x27InferInstanceMembershipOfMonad_match__1_splitter(
    mut v_00_u03b2_56_: *mut crate::leanh::LeanObject,
    mut v_motive_57_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_58_: *mut crate::leanh::LeanObject,
    mut v_h__1_59_: *mut crate::leanh::LeanObject,
    mut v_h__2_60_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_58_) == 0 {
        let mut v_a_61_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_60_);
        v_a_61_ = crate::leanh::lean_ctor_get(v_____do__lift_58_, 0);
        crate::leanh::lean_inc(v_a_61_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_58_, 1);
        v___x_62_ = crate::leanh::lean_apply_1(v_h__1_59_, v_a_61_);
        return v___x_62_;
    } else {
        let mut v_a_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_64_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_59_);
        v_a_63_ = crate::leanh::lean_ctor_get(v_____do__lift_58_, 0);
        crate::leanh::lean_inc(v_a_63_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_58_, 1);
        v___x_64_ = crate::leanh::lean_apply_1(v_h__2_60_, v_a_63_);
        return v___x_64_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Option_Monadic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Option_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Control_Lawful(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Option_Monadic(
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
pub unsafe fn initialize_Init_Data_Option_Monadic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Option_Instances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Control_Lawful(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Option_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Option_Monadic(builtin);
}

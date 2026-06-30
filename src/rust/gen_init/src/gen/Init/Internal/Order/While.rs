// Lean compiler output
// Module: Init.Internal.Order.While
// Imports: Init.While Init.While Init.Internal.Order.MonadTail
use crate::r#gen::Init::Internal::Order::MonadTail::{
    initialize_Init_Internal_Order_MonadTail, runtime_initialize_Init_Internal_Order_MonadTail,
};
use crate::r#gen::Init::While::{initialize_Init_While, runtime_initialize_Init_While};
pub unsafe fn l___private_Init_Internal_Order_While_0__whileM_body_match__1_splitter___redArg(
    mut v_____do__lift_34_: *mut leanh::LeanObject,
    mut v_h__1_35_: *mut leanh::LeanObject,
    mut v_h__2_36_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_34_) == 0 {
        let mut v_val_37_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_38_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_36_);
        v_val_37_ = leanh::lean_ctor_get(v_____do__lift_34_, 0);
        leanh::lean_inc(v_val_37_);
        leanh::lean_dec_ref_known(v_____do__lift_34_, 1);
        v___x_38_ = leanh::lean_apply_1(v_h__1_35_, v_val_37_);
        return v___x_38_;
    } else {
        let mut v_val_39_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_40_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_35_);
        v_val_39_ = leanh::lean_ctor_get(v_____do__lift_34_, 0);
        leanh::lean_inc(v_val_39_);
        leanh::lean_dec_ref_known(v_____do__lift_34_, 1);
        v___x_40_ = leanh::lean_apply_1(v_h__2_36_, v_val_39_);
        return v___x_40_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_While_0__whileM_body_match__1_splitter(
    mut v_00_u03b1_41_: *mut leanh::LeanObject,
    mut v_00_u03b2_42_: *mut leanh::LeanObject,
    mut v_motive_43_: *mut leanh::LeanObject,
    mut v_____do__lift_44_: *mut leanh::LeanObject,
    mut v_h__1_45_: *mut leanh::LeanObject,
    mut v_h__2_46_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_44_) == 0 {
        let mut v_val_47_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_48_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_46_);
        v_val_47_ = leanh::lean_ctor_get(v_____do__lift_44_, 0);
        leanh::lean_inc(v_val_47_);
        leanh::lean_dec_ref_known(v_____do__lift_44_, 1);
        v___x_48_ = leanh::lean_apply_1(v_h__1_45_, v_val_47_);
        return v___x_48_;
    } else {
        let mut v_val_49_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_50_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_45_);
        v_val_49_ = leanh::lean_ctor_get(v_____do__lift_44_, 0);
        leanh::lean_inc(v_val_49_);
        leanh::lean_dec_ref_known(v_____do__lift_44_, 1);
        v___x_50_ = leanh::lean_apply_1(v_h__2_46_, v_val_49_);
        return v___x_50_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_While_0__Lean_Loop_forIn_match__1_splitter___redArg(
    mut v_____do__lift_51_: *mut leanh::LeanObject,
    mut v_h__1_52_: *mut leanh::LeanObject,
    mut v_h__2_53_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_51_) == 0 {
        let mut v_a_54_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_55_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_53_);
        v_a_54_ = leanh::lean_ctor_get(v_____do__lift_51_, 0);
        leanh::lean_inc(v_a_54_);
        leanh::lean_dec_ref_known(v_____do__lift_51_, 1);
        v___x_55_ = leanh::lean_apply_1(v_h__1_52_, v_a_54_);
        return v___x_55_;
    } else {
        let mut v_a_56_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_57_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_52_);
        v_a_56_ = leanh::lean_ctor_get(v_____do__lift_51_, 0);
        leanh::lean_inc(v_a_56_);
        leanh::lean_dec_ref_known(v_____do__lift_51_, 1);
        v___x_57_ = leanh::lean_apply_1(v_h__2_53_, v_a_56_);
        return v___x_57_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_While_0__Lean_Loop_forIn_match__1_splitter(
    mut v_00_u03b2_58_: *mut leanh::LeanObject,
    mut v_motive_59_: *mut leanh::LeanObject,
    mut v_____do__lift_60_: *mut leanh::LeanObject,
    mut v_h__1_61_: *mut leanh::LeanObject,
    mut v_h__2_62_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_60_) == 0 {
        let mut v_a_63_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_64_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_62_);
        v_a_63_ = leanh::lean_ctor_get(v_____do__lift_60_, 0);
        leanh::lean_inc(v_a_63_);
        leanh::lean_dec_ref_known(v_____do__lift_60_, 1);
        v___x_64_ = leanh::lean_apply_1(v_h__1_61_, v_a_63_);
        return v___x_64_;
    } else {
        let mut v_a_65_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_66_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_61_);
        v_a_65_ = leanh::lean_ctor_get(v_____do__lift_60_, 0);
        leanh::lean_inc(v_a_65_);
        leanh::lean_dec_ref_known(v_____do__lift_60_, 1);
        v___x_66_ = leanh::lean_apply_1(v_h__2_62_, v_a_65_);
        return v___x_66_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Internal_Order_While(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Internal_Order_MonadTail(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Internal_Order_While(
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
pub unsafe fn initialize_Init_Internal_Order_While(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Internal_Order_MonadTail(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Internal_Order_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Internal_Order_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Internal_Order_While(builtin);
}
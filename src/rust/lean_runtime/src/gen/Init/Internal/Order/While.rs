// Lean compiler output
// Module: Init.Internal.Order.While
// Imports: Init.While Init.While Init.Internal.Order.MonadTail
use crate::r#gen::Init::Internal::Order::MonadTail::{
    initialize_Init_Internal_Order_MonadTail, runtime_initialize_Init_Internal_Order_MonadTail,
};
use crate::r#gen::Init::While::{initialize_Init_While, runtime_initialize_Init_While};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_box, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l___private_Init_Internal_Order_While_0__whileM_body_match__1_splitter___redArg(
    mut v_____do__lift_34_: *mut LeanObject,
    mut v_h__1_35_: *mut LeanObject,
    mut v_h__2_36_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_34_) == 0 {
        let mut v_val_37_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_38_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_36_);
        v_val_37_ = lean_ctor_get(v_____do__lift_34_, 0);
        lean_inc(v_val_37_);
        lean_dec_ref_known(v_____do__lift_34_, 1);
        v___x_38_ = lean_apply_1(v_h__1_35_, v_val_37_);
        return v___x_38_;
    } else {
        let mut v_val_39_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_40_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_35_);
        v_val_39_ = lean_ctor_get(v_____do__lift_34_, 0);
        lean_inc(v_val_39_);
        lean_dec_ref_known(v_____do__lift_34_, 1);
        v___x_40_ = lean_apply_1(v_h__2_36_, v_val_39_);
        return v___x_40_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_While_0__whileM_body_match__1_splitter(
    mut v_00_u03b1_41_: *mut LeanObject,
    mut v_00_u03b2_42_: *mut LeanObject,
    mut v_motive_43_: *mut LeanObject,
    mut v_____do__lift_44_: *mut LeanObject,
    mut v_h__1_45_: *mut LeanObject,
    mut v_h__2_46_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_44_) == 0 {
        let mut v_val_47_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_48_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_46_);
        v_val_47_ = lean_ctor_get(v_____do__lift_44_, 0);
        lean_inc(v_val_47_);
        lean_dec_ref_known(v_____do__lift_44_, 1);
        v___x_48_ = lean_apply_1(v_h__1_45_, v_val_47_);
        return v___x_48_;
    } else {
        let mut v_val_49_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_50_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_45_);
        v_val_49_ = lean_ctor_get(v_____do__lift_44_, 0);
        lean_inc(v_val_49_);
        lean_dec_ref_known(v_____do__lift_44_, 1);
        v___x_50_ = lean_apply_1(v_h__2_46_, v_val_49_);
        return v___x_50_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_While_0__Lean_Loop_forIn_match__1_splitter___redArg(
    mut v_____do__lift_51_: *mut LeanObject,
    mut v_h__1_52_: *mut LeanObject,
    mut v_h__2_53_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_51_) == 0 {
        let mut v_a_54_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_55_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_53_);
        v_a_54_ = lean_ctor_get(v_____do__lift_51_, 0);
        lean_inc(v_a_54_);
        lean_dec_ref_known(v_____do__lift_51_, 1);
        v___x_55_ = lean_apply_1(v_h__1_52_, v_a_54_);
        return v___x_55_;
    } else {
        let mut v_a_56_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_57_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_52_);
        v_a_56_ = lean_ctor_get(v_____do__lift_51_, 0);
        lean_inc(v_a_56_);
        lean_dec_ref_known(v_____do__lift_51_, 1);
        v___x_57_ = lean_apply_1(v_h__2_53_, v_a_56_);
        return v___x_57_;
    }
}
pub unsafe fn l___private_Init_Internal_Order_While_0__Lean_Loop_forIn_match__1_splitter(
    mut v_00_u03b2_58_: *mut LeanObject,
    mut v_motive_59_: *mut LeanObject,
    mut v_____do__lift_60_: *mut LeanObject,
    mut v_h__1_61_: *mut LeanObject,
    mut v_h__2_62_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_60_) == 0 {
        let mut v_a_63_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_64_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_62_);
        v_a_63_ = lean_ctor_get(v_____do__lift_60_, 0);
        lean_inc(v_a_63_);
        lean_dec_ref_known(v_____do__lift_60_, 1);
        v___x_64_ = lean_apply_1(v_h__1_61_, v_a_63_);
        return v___x_64_;
    } else {
        let mut v_a_65_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_66_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_61_);
        v_a_65_ = lean_ctor_get(v_____do__lift_60_, 0);
        lean_inc(v_a_65_);
        lean_dec_ref_known(v_____do__lift_60_, 1);
        v___x_66_ = lean_apply_1(v_h__2_62_, v_a_65_);
        return v___x_66_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Internal_Order_While(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Internal_Order_MonadTail(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Internal_Order_While(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Internal_Order_While(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Internal_Order_MonadTail(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Internal_Order_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Internal_Order_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Internal_Order_While(builtin);
}

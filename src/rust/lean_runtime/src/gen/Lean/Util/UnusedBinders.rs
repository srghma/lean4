// Lean compiler output
// Module: Lean.Util.UnusedBinders
// Imports: Lean.Expr
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Expr_cleanupAnnotations, runtime_initialize_Lean_Expr,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_has_loose_bvar;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_2, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_dec_ref, lean_dec_ref_known, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub unsafe fn l_Lean_Expr_hasUnusedForallBindersWhere(
    mut v_p_22_: *mut LeanObject,
    mut v_e_23_: *mut LeanObject,
) -> u8 {
    let mut v___x_24_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_25_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_26_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_27_: u8 = 0;
    let mut v___x_28_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_29_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_30_: u8 = 0;
    let mut v___x_32_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_33_: u8 = 0;
    let mut v___x_34_: u8 = 0;
    let mut v_body_36_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_38_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_24_ = l_Lean_Expr_cleanupAnnotations(v_e_23_);
                match lean_obj_tag(v___x_24_) {
                    7 => {
                        v_binderType_25_ = lean_ctor_get(v___x_24_, 1);
                        lean_inc_ref(v_binderType_25_);
                        v_body_26_ = lean_ctor_get(v___x_24_, 2);
                        lean_inc_ref(v_body_26_);
                        v_binderInfo_27_ = lean_ctor_get_uint8(
                            v___x_24_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                        );
                        lean_dec_ref_known(v___x_24_, 3);
                        v___x_28_ = lean_box((v_binderInfo_27_) as usize);
                        lean_inc_ref(v_p_22_);
                        v___x_29_ = lean_apply_2(v_p_22_, v___x_28_, v_binderType_25_);
                        v___x_30_ = (lean_unbox(v___x_29_) as u8);
                        if v___x_30_ == 0 {
                            v_e_23_ = v_body_26_;
                            state = 0;
                            continue;
                        } else {
                            v___x_32_ = lean_unsigned_to_nat(0);
                            v___x_33_ = lean_expr_has_loose_bvar(v_body_26_, v___x_32_);
                            if v___x_33_ == 0 {
                                lean_dec_ref(v_body_26_);
                                lean_dec_ref(v_p_22_);
                                v___x_34_ = (lean_unbox(v___x_29_) as u8);
                                return v___x_34_;
                            } else {
                                v_e_23_ = v_body_26_;
                                state = 0;
                                continue;
                            }
                        }
                    }
                    8 => {
                        v_body_36_ = lean_ctor_get(v___x_24_, 3);
                        lean_inc_ref(v_body_36_);
                        lean_dec_ref_known(v___x_24_, 4);
                        v_e_23_ = v_body_36_;
                        state = 0;
                        continue;
                    }
                    _ => {
                        lean_dec_ref(v___x_24_);
                        lean_dec_ref(v_p_22_);
                        v___x_38_ = 0;
                        return v___x_38_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Expr_hasUnusedForallBindersWhere___boxed(
    mut v_p_39_: *mut LeanObject,
    mut v_e_40_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_41_: u8 = 0;
    let mut v_r_42_: *mut LeanObject = core::ptr::null_mut();
    v_res_41_ = l_Lean_Expr_hasUnusedForallBindersWhere(v_p_39_, v_e_40_);
    v_r_42_ = lean_box((v_res_41_) as usize);
    return v_r_42_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_UnusedBinders(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_UnusedBinders(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_UnusedBinders(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_UnusedBinders(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Util_UnusedBinders(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Util_UnusedBinders(builtin);
}

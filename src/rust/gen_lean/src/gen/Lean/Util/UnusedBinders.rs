// Lean compiler output
// Module: Lean.Util.UnusedBinders
// Imports: Lean.Expr
use crate::ffi::lean_expr_has_loose_bvar;
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Expr_cleanupAnnotations, runtime_initialize_Lean_Expr,
};
pub unsafe fn l_Lean_Expr_hasUnusedForallBindersWhere(
    mut v_p_22_: *mut crate::leanh::LeanObject,
    mut v_e_23_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_24_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_25_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_26_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_27_: u8 = 0;
    let mut v___x_28_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_29_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_30_: u8 = 0;
    let mut v___x_32_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_33_: u8 = 0;
    let mut v___x_34_: u8 = 0;
    let mut v_body_36_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_38_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_24_ = l_Lean_Expr_cleanupAnnotations(v_e_23_);
                match crate::leanh::lean_obj_tag(v___x_24_) {
                    7 => {
                        v_binderType_25_ = crate::leanh::lean_ctor_get(v___x_24_, 1);
                        crate::leanh::lean_inc_ref(v_binderType_25_);
                        v_body_26_ = crate::leanh::lean_ctor_get(v___x_24_, 2);
                        crate::leanh::lean_inc_ref(v_body_26_);
                        v_binderInfo_27_ = crate::leanh::lean_ctor_get_uint8(
                            v___x_24_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                        );
                        crate::leanh::lean_dec_ref_known(v___x_24_, 3);
                        v___x_28_ = crate::leanh::lean_box((v_binderInfo_27_) as usize);
                        crate::leanh::lean_inc_ref(v_p_22_);
                        v___x_29_ =
                            crate::leanh::lean_apply_2(v_p_22_, v___x_28_, v_binderType_25_);
                        v___x_30_ = (crate::leanh::lean_unbox(v___x_29_) as u8);
                        if v___x_30_ == 0 {
                            v_e_23_ = v_body_26_;
                            state = 0;
                            continue;
                        } else {
                            v___x_32_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_33_ = lean_expr_has_loose_bvar(v_body_26_, v___x_32_);
                            if v___x_33_ == 0 {
                                crate::leanh::lean_dec_ref(v_body_26_);
                                crate::leanh::lean_dec_ref(v_p_22_);
                                v___x_34_ = (crate::leanh::lean_unbox(v___x_29_) as u8);
                                return v___x_34_;
                            } else {
                                v_e_23_ = v_body_26_;
                                state = 0;
                                continue;
                            }
                        }
                    }
                    8 => {
                        v_body_36_ = crate::leanh::lean_ctor_get(v___x_24_, 3);
                        crate::leanh::lean_inc_ref(v_body_36_);
                        crate::leanh::lean_dec_ref_known(v___x_24_, 4);
                        v_e_23_ = v_body_36_;
                        state = 0;
                        continue;
                    }
                    _ => {
                        crate::leanh::lean_dec_ref(v___x_24_);
                        crate::leanh::lean_dec_ref(v_p_22_);
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
    mut v_p_39_: *mut crate::leanh::LeanObject,
    mut v_e_40_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_41_: u8 = 0;
    let mut v_r_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_41_ = l_Lean_Expr_hasUnusedForallBindersWhere(v_p_39_, v_e_40_);
    v_r_42_ = crate::leanh::lean_box((v_res_41_) as usize);
    return v_r_42_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_UnusedBinders(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_UnusedBinders(
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
pub unsafe fn initialize_Lean_Util_UnusedBinders(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_UnusedBinders(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_UnusedBinders(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_UnusedBinders(builtin);
}

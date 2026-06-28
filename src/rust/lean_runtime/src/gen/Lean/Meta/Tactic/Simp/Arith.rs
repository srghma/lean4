// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith
// Imports: Lean.Meta.Tactic.Simp.Arith.Nat Lean.Meta.Tactic.Simp.Arith.Int
use crate::r#gen::Lean::Meta::Tactic::Simp::Arith::Int::{
    initialize_Lean_Meta_Tactic_Simp_Arith_Int, runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Arith::Nat::{
    initialize_Lean_Meta_Tactic_Simp_Arith_Nat, runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Arith::Util::{
    l_Lean_Meta_Simp_Arith_isDvdCnstr, l_Lean_Meta_Simp_Arith_isLinearCnstr,
    l_Lean_Meta_Simp_Arith_isLinearTerm,
};
pub unsafe fn l_Lean_Meta_Simp_Arith_parentIsTarget(
    mut v_parent_x3f_12_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_13_: u8 = 0;
    let mut v_val_14_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_16_: u8 = 0;
    let mut v___x_17_: u8 = 0;
    let mut v___x_18_: u8 = 0;
    let mut v___x_19_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_parent_x3f_12_) == 0 {
                    v___x_13_ = 0;
                    return v___x_13_;
                } else {
                    v_val_14_ = crate::leanh::lean_ctor_get(v_parent_x3f_12_, 0);
                    crate::leanh::lean_inc_n(v_val_14_, 2);
                    crate::leanh::lean_dec_ref_known(v_parent_x3f_12_, 1);
                    v___x_18_ = l_Lean_Meta_Simp_Arith_isLinearTerm(v_val_14_);
                    if v___x_18_ == 0 {
                        crate::leanh::lean_inc(v_val_14_);
                        v___x_19_ = l_Lean_Meta_Simp_Arith_isLinearCnstr(v_val_14_);
                        v___y_16_ = v___x_19_;
                        state = 1;
                        continue;
                    } else {
                        v___y_16_ = v___x_18_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_16_ == 0 {
                    v___x_17_ = l_Lean_Meta_Simp_Arith_isDvdCnstr(v_val_14_);
                    return v___x_17_;
                } else {
                    crate::leanh::lean_dec(v_val_14_);
                    return v___y_16_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Simp_Arith_parentIsTarget___boxed(
    mut v_parent_x3f_20_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_21_: u8 = 0;
    let mut v_r_22_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_21_ = l_Lean_Meta_Simp_Arith_parentIsTarget(v_parent_x3f_20_);
    v_r_22_ = crate::leanh::lean_box((v_res_21_) as usize);
    return v_r_22_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Simp_Arith(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Nat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith_Int(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Simp_Arith(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Simp_Arith(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Arith_Nat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Arith_Int(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Arith(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Simp_Arith(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Simp_Arith(builtin);
}

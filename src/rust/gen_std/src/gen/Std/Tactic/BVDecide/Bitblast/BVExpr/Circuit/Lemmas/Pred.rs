// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Pred
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Lemmas.Expr Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Pred Init.Omega
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Pred::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Lemmas::Expr::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr,
};
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__7_splitter___redArg(
    mut v_pred_45_: *mut crate::leanh::LeanObject,
    mut v_h__1_46_: *mut crate::leanh::LeanObject,
    mut v_h__2_47_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_pred_45_) == 0 {
        let mut v_w_48_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_lhs_49_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_op_50_: u8 = 0;
        let mut v_rhs_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_53_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_47_);
        v_w_48_ = crate::leanh::lean_ctor_get(v_pred_45_, 0);
        crate::leanh::lean_inc(v_w_48_);
        v_lhs_49_ = crate::leanh::lean_ctor_get(v_pred_45_, 1);
        crate::leanh::lean_inc_ref(v_lhs_49_);
        v_op_50_ = crate::leanh::lean_ctor_get_uint8(
            v_pred_45_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        );
        v_rhs_51_ = crate::leanh::lean_ctor_get(v_pred_45_, 2);
        crate::leanh::lean_inc_ref(v_rhs_51_);
        crate::leanh::lean_dec_ref_known(v_pred_45_, 3);
        v___x_52_ = crate::leanh::lean_box((v_op_50_) as usize);
        v___x_53_ =
            crate::leanh::lean_apply_4(v_h__1_46_, v_w_48_, v_lhs_49_, v___x_52_, v_rhs_51_);
        return v___x_53_;
    } else {
        let mut v_w_54_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_expr_55_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_idx_56_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_57_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_46_);
        v_w_54_ = crate::leanh::lean_ctor_get(v_pred_45_, 0);
        crate::leanh::lean_inc(v_w_54_);
        v_expr_55_ = crate::leanh::lean_ctor_get(v_pred_45_, 1);
        crate::leanh::lean_inc_ref(v_expr_55_);
        v_idx_56_ = crate::leanh::lean_ctor_get(v_pred_45_, 2);
        crate::leanh::lean_inc(v_idx_56_);
        crate::leanh::lean_dec_ref_known(v_pred_45_, 3);
        v___x_57_ = crate::leanh::lean_apply_3(v_h__2_47_, v_w_54_, v_expr_55_, v_idx_56_);
        return v___x_57_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__7_splitter(
    mut v_motive_58_: *mut crate::leanh::LeanObject,
    mut v_pred_59_: *mut crate::leanh::LeanObject,
    mut v_h__1_60_: *mut crate::leanh::LeanObject,
    mut v_h__2_61_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_pred_59_) == 0 {
        let mut v_w_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_lhs_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_op_64_: u8 = 0;
        let mut v_rhs_65_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_66_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_67_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_61_);
        v_w_62_ = crate::leanh::lean_ctor_get(v_pred_59_, 0);
        crate::leanh::lean_inc(v_w_62_);
        v_lhs_63_ = crate::leanh::lean_ctor_get(v_pred_59_, 1);
        crate::leanh::lean_inc_ref(v_lhs_63_);
        v_op_64_ = crate::leanh::lean_ctor_get_uint8(
            v_pred_59_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
        );
        v_rhs_65_ = crate::leanh::lean_ctor_get(v_pred_59_, 2);
        crate::leanh::lean_inc_ref(v_rhs_65_);
        crate::leanh::lean_dec_ref_known(v_pred_59_, 3);
        v___x_66_ = crate::leanh::lean_box((v_op_64_) as usize);
        v___x_67_ =
            crate::leanh::lean_apply_4(v_h__1_60_, v_w_62_, v_lhs_63_, v___x_66_, v_rhs_65_);
        return v___x_67_;
    } else {
        let mut v_w_68_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_expr_69_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_idx_70_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_71_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_60_);
        v_w_68_ = crate::leanh::lean_ctor_get(v_pred_59_, 0);
        crate::leanh::lean_inc(v_w_68_);
        v_expr_69_ = crate::leanh::lean_ctor_get(v_pred_59_, 1);
        crate::leanh::lean_inc_ref(v_expr_69_);
        v_idx_70_ = crate::leanh::lean_ctor_get(v_pred_59_, 2);
        crate::leanh::lean_inc(v_idx_70_);
        crate::leanh::lean_dec_ref_known(v_pred_59_, 3);
        v___x_71_ = crate::leanh::lean_apply_3(v_h__2_61_, v_w_68_, v_expr_69_, v_idx_70_);
        return v___x_71_;
    }
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__9_splitter___redArg(
    mut v_input_72_: *mut crate::leanh::LeanObject,
    mut v_h__1_73_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_74_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_74_ = crate::leanh::lean_ctor_get(v_input_72_, 0);
    crate::leanh::lean_inc(v_val_74_);
    v_cache_75_ = crate::leanh::lean_ctor_get(v_input_72_, 1);
    crate::leanh::lean_inc_ref(v_cache_75_);
    crate::leanh::lean_dec_ref(v_input_72_);
    v___x_76_ = crate::leanh::lean_apply_2(v_h__1_73_, v_val_74_, v_cache_75_);
    return v___x_76_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__9_splitter(
    mut v_aig_77_: *mut crate::leanh::LeanObject,
    mut v_motive_78_: *mut crate::leanh::LeanObject,
    mut v_input_79_: *mut crate::leanh::LeanObject,
    mut v_h__1_80_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_val_81_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_82_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_83_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_val_81_ = crate::leanh::lean_ctor_get(v_input_79_, 0);
    crate::leanh::lean_inc(v_val_81_);
    v_cache_82_ = crate::leanh::lean_ctor_get(v_input_79_, 1);
    crate::leanh::lean_inc_ref(v_cache_82_);
    crate::leanh::lean_dec_ref(v_input_79_);
    v___x_83_ = crate::leanh::lean_apply_2(v_h__1_80_, v_val_81_, v_cache_82_);
    return v___x_83_;
}
pub unsafe fn l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__9_splitter___boxed(
    mut v_aig_84_: *mut crate::leanh::LeanObject,
    mut v_motive_85_: *mut crate::leanh::LeanObject,
    mut v_input_86_: *mut crate::leanh::LeanObject,
    mut v_h__1_87_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_88_ = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred_0__Std_Tactic_BVDecide_BVPred_bitblast_match__9_splitter(v_aig_84_, v_motive_85_, v_input_86_, v_h__1_87_);
    crate::leanh::lean_dec_ref(v_aig_84_);
    return v_res_88_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Lemmas_Pred(builtin);
}

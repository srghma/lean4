// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Not
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic Std.Sat.AIG.RefVecOperator
use crate::r#gen::Std::Sat::AIG::CachedGates::l_Std_Sat_AIG_mkNotCached___boxed;
use crate::r#gen::Std::Sat::AIG::RefVecOperator::Map::l_Std_Sat_AIG_RefVec_map___redArg;
use crate::r#gen::Std::Sat::AIG::RefVecOperator::{
    initialize_Std_Sat_AIG_RefVecOperator, runtime_initialize_Std_Sat_AIG_RefVecOperator,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Basic::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
};
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg(
    mut v_inst_29_: *mut crate::leanh::LeanObject,
    mut v_inst_30_: *mut crate::leanh::LeanObject,
    mut v_w_31_: *mut crate::leanh::LeanObject,
    mut v_aig_32_: *mut crate::leanh::LeanObject,
    mut v_s_33_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_34_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_35_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_36_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_34_ = crate::leanh::lean_alloc_closure(
        l_Std_Sat_AIG_mkNotCached___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___x_34_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_34_, 1, v_inst_29_);
    crate::leanh::lean_closure_set(v___x_34_, 2, v_inst_30_);
    v___x_35_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_35_, 0, v_s_33_);
    crate::leanh::lean_ctor_set(v___x_35_, 1, v___x_34_);
    v___x_36_ = l_Std_Sat_AIG_RefVec_map___redArg(v_w_31_, v_aig_32_, v___x_35_);
    return v___x_36_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg___boxed(
    mut v_inst_37_: *mut crate::leanh::LeanObject,
    mut v_inst_38_: *mut crate::leanh::LeanObject,
    mut v_w_39_: *mut crate::leanh::LeanObject,
    mut v_aig_40_: *mut crate::leanh::LeanObject,
    mut v_s_41_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_42_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_42_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg(
        v_inst_37_, v_inst_38_, v_w_39_, v_aig_40_, v_s_41_,
    );
    crate::leanh::lean_dec(v_w_39_);
    return v_res_42_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot(
    mut v_00_u03b1_43_: *mut crate::leanh::LeanObject,
    mut v_inst_44_: *mut crate::leanh::LeanObject,
    mut v_inst_45_: *mut crate::leanh::LeanObject,
    mut v_w_46_: *mut crate::leanh::LeanObject,
    mut v_aig_47_: *mut crate::leanh::LeanObject,
    mut v_s_48_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_49_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_49_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg(
        v_inst_44_, v_inst_45_, v_w_46_, v_aig_47_, v_s_48_,
    );
    return v___x_49_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___boxed(
    mut v_00_u03b1_50_: *mut crate::leanh::LeanObject,
    mut v_inst_51_: *mut crate::leanh::LeanObject,
    mut v_inst_52_: *mut crate::leanh::LeanObject,
    mut v_w_53_: *mut crate::leanh::LeanObject,
    mut v_aig_54_: *mut crate::leanh::LeanObject,
    mut v_s_55_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_56_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_56_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot(
        v_00_u03b1_50_,
        v_inst_51_,
        v_inst_52_,
        v_w_53_,
        v_aig_54_,
        v_s_55_,
    );
    crate::leanh::lean_dec(v_w_53_);
    return v_res_56_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_RefVecOperator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Sat_AIG_RefVecOperator(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(builtin);
}

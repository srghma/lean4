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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_set, lean_dec, lean_dec_ref, lean_io_result_is_error,
    lean_io_result_mk_ok,
};
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg(
    mut v_inst_29_: *mut LeanObject,
    mut v_inst_30_: *mut LeanObject,
    mut v_w_31_: *mut LeanObject,
    mut v_aig_32_: *mut LeanObject,
    mut v_s_33_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_34_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_35_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_36_: *mut LeanObject = core::ptr::null_mut();
    v___x_34_ = lean_alloc_closure(
        l_Std_Sat_AIG_mkNotCached___boxed as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___x_34_, 0, lean_box(0));
    lean_closure_set(v___x_34_, 1, v_inst_29_);
    lean_closure_set(v___x_34_, 2, v_inst_30_);
    v___x_35_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_35_, 0, v_s_33_);
    lean_ctor_set(v___x_35_, 1, v___x_34_);
    v___x_36_ = l_Std_Sat_AIG_RefVec_map___redArg(v_w_31_, v_aig_32_, v___x_35_);
    return v___x_36_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg___boxed(
    mut v_inst_37_: *mut LeanObject,
    mut v_inst_38_: *mut LeanObject,
    mut v_w_39_: *mut LeanObject,
    mut v_aig_40_: *mut LeanObject,
    mut v_s_41_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_42_: *mut LeanObject = core::ptr::null_mut();
    v_res_42_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg(
        v_inst_37_, v_inst_38_, v_w_39_, v_aig_40_, v_s_41_,
    );
    lean_dec(v_w_39_);
    return v_res_42_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot(
    mut v_00_u03b1_43_: *mut LeanObject,
    mut v_inst_44_: *mut LeanObject,
    mut v_inst_45_: *mut LeanObject,
    mut v_w_46_: *mut LeanObject,
    mut v_aig_47_: *mut LeanObject,
    mut v_s_48_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_49_: *mut LeanObject = core::ptr::null_mut();
    v___x_49_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg(
        v_inst_44_, v_inst_45_, v_w_46_, v_aig_47_, v_s_48_,
    );
    return v___x_49_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___boxed(
    mut v_00_u03b1_50_: *mut LeanObject,
    mut v_inst_51_: *mut LeanObject,
    mut v_inst_52_: *mut LeanObject,
    mut v_w_53_: *mut LeanObject,
    mut v_aig_54_: *mut LeanObject,
    mut v_s_55_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_56_: *mut LeanObject = core::ptr::null_mut();
    v_res_56_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot(
        v_00_u03b1_50_,
        v_inst_51_,
        v_inst_52_,
        v_w_53_,
        v_aig_54_,
        v_s_55_,
    );
    lean_dec(v_w_53_);
    return v_res_56_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_RefVecOperator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sat_AIG_RefVecOperator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(builtin);
}

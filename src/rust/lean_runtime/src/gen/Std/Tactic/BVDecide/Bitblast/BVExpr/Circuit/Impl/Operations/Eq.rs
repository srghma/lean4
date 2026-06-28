// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Eq
// Imports: Std.Sat.AIG.RefVecOperator
use crate::r#gen::Std::Sat::AIG::CachedGates::{
    l_Std_Sat_AIG_mkAndCached, l_Std_Sat_AIG_mkBEqCached,
};
use crate::r#gen::Std::Sat::AIG::RefVecOperator::Fold::l_Std_Sat_AIG_RefVec_fold___redArg;
use crate::r#gen::Std::Sat::AIG::RefVecOperator::Zip::l_Std_Sat_AIG_RefVec_zip___redArg;
use crate::r#gen::Std::Sat::AIG::RefVecOperator::{
    initialize_Std_Sat_AIG_RefVecOperator, runtime_initialize_Std_Sat_AIG_RefVecOperator,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_box, lean_closure_set, lean_ctor_get,
    lean_dec, lean_dec_ref, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
};
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(
    mut v_inst_32_: *mut LeanObject,
    mut v_inst_33_: *mut LeanObject,
    mut v_w_34_: *mut LeanObject,
    mut v_aig_35_: *mut LeanObject,
    mut v_pair_36_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_37_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_38_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_39_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vec_40_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_41_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_42_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_inst_33_);
    lean_inc_ref(v_inst_32_);
    v___x_37_ = lean_alloc_closure(l_Std_Sat_AIG_mkBEqCached as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_37_, 0, lean_box(0));
    lean_closure_set(v___x_37_, 1, v_inst_32_);
    lean_closure_set(v___x_37_, 2, v_inst_33_);
    v_res_38_ = l_Std_Sat_AIG_RefVec_zip___redArg(v_w_34_, v_aig_35_, v_pair_36_, v___x_37_);
    v_aig_39_ = lean_ctor_get(v_res_38_, 0);
    lean_inc_ref(v_aig_39_);
    v_vec_40_ = lean_ctor_get(v_res_38_, 1);
    lean_inc_ref(v_vec_40_);
    lean_dec_ref(v_res_38_);
    v___x_41_ = lean_alloc_closure(l_Std_Sat_AIG_mkAndCached as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_41_, 0, lean_box(0));
    lean_closure_set(v___x_41_, 1, v_inst_32_);
    lean_closure_set(v___x_41_, 2, v_inst_33_);
    v___x_42_ = l_Std_Sat_AIG_RefVec_fold___redArg(v_w_34_, v_aig_39_, v_vec_40_, v___x_41_);
    lean_dec_ref(v_vec_40_);
    return v___x_42_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_mkEq___redArg___boxed(
    mut v_inst_43_: *mut LeanObject,
    mut v_inst_44_: *mut LeanObject,
    mut v_w_45_: *mut LeanObject,
    mut v_aig_46_: *mut LeanObject,
    mut v_pair_47_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_48_: *mut LeanObject = core::ptr::null_mut();
    v_res_48_ = l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(
        v_inst_43_, v_inst_44_, v_w_45_, v_aig_46_, v_pair_47_,
    );
    lean_dec_ref(v_pair_47_);
    lean_dec(v_w_45_);
    return v_res_48_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_mkEq(
    mut v_00_u03b1_49_: *mut LeanObject,
    mut v_inst_50_: *mut LeanObject,
    mut v_inst_51_: *mut LeanObject,
    mut v_w_52_: *mut LeanObject,
    mut v_aig_53_: *mut LeanObject,
    mut v_pair_54_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_55_: *mut LeanObject = core::ptr::null_mut();
    v___x_55_ = l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(
        v_inst_50_, v_inst_51_, v_w_52_, v_aig_53_, v_pair_54_,
    );
    return v___x_55_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVPred_mkEq___boxed(
    mut v_00_u03b1_56_: *mut LeanObject,
    mut v_inst_57_: *mut LeanObject,
    mut v_inst_58_: *mut LeanObject,
    mut v_w_59_: *mut LeanObject,
    mut v_aig_60_: *mut LeanObject,
    mut v_pair_61_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_62_: *mut LeanObject = core::ptr::null_mut();
    v_res_62_ = l_Std_Tactic_BVDecide_BVPred_mkEq(
        v_00_u03b1_56_,
        v_inst_57_,
        v_inst_58_,
        v_w_59_,
        v_aig_60_,
        v_pair_61_,
    );
    lean_dec_ref(v_pair_61_);
    lean_dec(v_w_59_);
    return v_res_62_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_AIG_RefVecOperator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_AIG_RefVecOperator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Eq(builtin);
}

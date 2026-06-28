// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Sub
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Neg
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Add::l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg;
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Neg::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Neg,
    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___redArg,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Neg,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive,
};
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___redArg(
    mut v_inst_39_: *mut LeanObject,
    mut v_inst_40_: *mut LeanObject,
    mut v_w_41_: *mut LeanObject,
    mut v_aig_42_: *mut LeanObject,
    mut v_input_43_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lhs_44_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_45_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_47_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_48_: u8 = 0;
    let mut v_res_49_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_50_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vec_51_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_53_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_54_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_55_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_56_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_44_ = lean_ctor_get(v_input_43_, 0);
                v_rhs_45_ = lean_ctor_get(v_input_43_, 1);
                v_isSharedCheck_56_ = (!lean_is_exclusive(v_input_43_)) as u8;
                if v_isSharedCheck_56_ == 0 {
                    v___x_47_ = v_input_43_;
                    v_isShared_48_ = v_isSharedCheck_56_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_rhs_45_);
                    lean_inc(v_lhs_44_);
                    lean_dec(v_input_43_);
                    v___x_47_ = lean_box(0);
                    v_isShared_48_ = v_isSharedCheck_56_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc_ref(v_inst_40_);
                lean_inc_ref(v_inst_39_);
                v_res_49_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___redArg(
                    v_inst_39_, v_inst_40_, v_w_41_, v_aig_42_, v_rhs_45_,
                );
                v_aig_50_ = lean_ctor_get(v_res_49_, 0);
                lean_inc_ref(v_aig_50_);
                v_vec_51_ = lean_ctor_get(v_res_49_, 1);
                lean_inc_ref(v_vec_51_);
                lean_dec_ref(v_res_49_);
                if v_isShared_48_ == 0 {
                    lean_ctor_set(v___x_47_, 1, v_vec_51_);
                    v___x_53_ = v___x_47_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_55_, 0, v_lhs_44_);
                    lean_ctor_set(v_reuseFailAlloc_55_, 1, v_vec_51_);
                    v___x_53_ = v_reuseFailAlloc_55_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_54_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(
                    v_inst_39_, v_inst_40_, v_w_41_, v_aig_50_, v___x_53_,
                );
                return v___x_54_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___redArg___boxed(
    mut v_inst_57_: *mut LeanObject,
    mut v_inst_58_: *mut LeanObject,
    mut v_w_59_: *mut LeanObject,
    mut v_aig_60_: *mut LeanObject,
    mut v_input_61_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_62_: *mut LeanObject = core::ptr::null_mut();
    v_res_62_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___redArg(
        v_inst_57_,
        v_inst_58_,
        v_w_59_,
        v_aig_60_,
        v_input_61_,
    );
    lean_dec(v_w_59_);
    return v_res_62_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub(
    mut v_00_u03b1_63_: *mut LeanObject,
    mut v_inst_64_: *mut LeanObject,
    mut v_inst_65_: *mut LeanObject,
    mut v_w_66_: *mut LeanObject,
    mut v_aig_67_: *mut LeanObject,
    mut v_input_68_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_69_: *mut LeanObject = core::ptr::null_mut();
    v___x_69_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___redArg(
        v_inst_64_,
        v_inst_65_,
        v_w_66_,
        v_aig_67_,
        v_input_68_,
    );
    return v___x_69_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub___boxed(
    mut v_00_u03b1_70_: *mut LeanObject,
    mut v_inst_71_: *mut LeanObject,
    mut v_inst_72_: *mut LeanObject,
    mut v_w_73_: *mut LeanObject,
    mut v_aig_74_: *mut LeanObject,
    mut v_input_75_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_76_: *mut LeanObject = core::ptr::null_mut();
    v_res_76_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastSub(
        v_00_u03b1_70_,
        v_inst_71_,
        v_inst_72_,
        v_w_73_,
        v_aig_74_,
        v_input_75_,
    );
    lean_dec(v_w_73_);
    return v_res_76_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Neg(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Neg(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Sub(builtin);
}

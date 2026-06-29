// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Neg
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Not Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const
use crate::r#gen::Init::Prelude::l_BitVec_ofNat;
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Const::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const,
    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Add::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add,
    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Not::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not,
    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not,
};
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___redArg(
    mut v_inst_40_: *mut crate::leanh::LeanObject,
    mut v_inst_41_: *mut crate::leanh::LeanObject,
    mut v_w_42_: *mut crate::leanh::LeanObject,
    mut v_aig_43_: *mut crate::leanh::LeanObject,
    mut v_input_44_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_45_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_46_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vec_47_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_49_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_50_: u8 = 0;
    let mut v___x_51_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_52_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_53_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_55_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_56_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_57_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_58_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_inst_41_);
                crate::leanh::lean_inc_ref(v_inst_40_);
                v_res_45_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNot___redArg(
                    v_inst_40_,
                    v_inst_41_,
                    v_w_42_,
                    v_aig_43_,
                    v_input_44_,
                );
                v_aig_46_ = crate::leanh::lean_ctor_get(v_res_45_, 0);
                v_vec_47_ = crate::leanh::lean_ctor_get(v_res_45_, 1);
                v_isSharedCheck_58_ = (!crate::leanh::lean_is_exclusive(v_res_45_)) as u8;
                if v_isSharedCheck_58_ == 0 {
                    v___x_49_ = v_res_45_;
                    v_isShared_50_ = v_isSharedCheck_58_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vec_47_);
                    crate::leanh::lean_inc(v_aig_46_);
                    crate::leanh::lean_dec(v_res_45_);
                    v___x_49_ = crate::leanh::lean_box(0);
                    v_isShared_50_ = v_isSharedCheck_58_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_51_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_52_ = l_BitVec_ofNat(v_w_42_, v___x_51_);
                v_one_53_ =
                    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v_w_42_, v___x_52_);
                crate::leanh::lean_dec(v___x_52_);
                if v_isShared_50_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_49_, 1, v_one_53_);
                    crate::leanh::lean_ctor_set(v___x_49_, 0, v_vec_47_);
                    v___x_55_ = v___x_49_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_57_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_57_, 0, v_vec_47_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_57_, 1, v_one_53_);
                    v___x_55_ = v_reuseFailAlloc_57_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_56_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastAdd___redArg(
                    v_inst_40_, v_inst_41_, v_w_42_, v_aig_46_, v___x_55_,
                );
                return v___x_56_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___redArg___boxed(
    mut v_inst_59_: *mut crate::leanh::LeanObject,
    mut v_inst_60_: *mut crate::leanh::LeanObject,
    mut v_w_61_: *mut crate::leanh::LeanObject,
    mut v_aig_62_: *mut crate::leanh::LeanObject,
    mut v_input_63_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_64_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_64_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___redArg(
        v_inst_59_,
        v_inst_60_,
        v_w_61_,
        v_aig_62_,
        v_input_63_,
    );
    crate::leanh::lean_dec(v_w_61_);
    return v_res_64_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg(
    mut v_00_u03b1_65_: *mut crate::leanh::LeanObject,
    mut v_inst_66_: *mut crate::leanh::LeanObject,
    mut v_inst_67_: *mut crate::leanh::LeanObject,
    mut v_w_68_: *mut crate::leanh::LeanObject,
    mut v_aig_69_: *mut crate::leanh::LeanObject,
    mut v_input_70_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_71_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_71_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___redArg(
        v_inst_66_,
        v_inst_67_,
        v_w_68_,
        v_aig_69_,
        v_input_70_,
    );
    return v___x_71_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg___boxed(
    mut v_00_u03b1_72_: *mut crate::leanh::LeanObject,
    mut v_inst_73_: *mut crate::leanh::LeanObject,
    mut v_inst_74_: *mut crate::leanh::LeanObject,
    mut v_w_75_: *mut crate::leanh::LeanObject,
    mut v_aig_76_: *mut crate::leanh::LeanObject,
    mut v_input_77_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_78_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastNeg(
        v_00_u03b1_72_,
        v_inst_73_,
        v_inst_74_,
        v_w_75_,
        v_aig_76_,
        v_input_77_,
    );
    crate::leanh::lean_dec(v_w_75_);
    return v_res_78_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Neg(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
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
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Neg(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Neg(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Not(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Neg(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Neg(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Neg(builtin);
}

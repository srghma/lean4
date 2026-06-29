// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Umod
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Udiv
use crate::r#gen::Init::Prelude::l_BitVec_ofNat;
use crate::r#gen::Std::Sat::AIG::If::l_Std_Sat_AIG_RefVec_ite___redArg;
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Const::l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg;
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Eq::l_Std_Tactic_BVDecide_BVPred_mkEq___redArg;
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Udiv::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv,
    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv,
};
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___redArg(
    mut v_inst_49_: *mut crate::leanh::LeanObject,
    mut v_inst_50_: *mut crate::leanh::LeanObject,
    mut v_w_51_: *mut crate::leanh::LeanObject,
    mut v_aig_52_: *mut crate::leanh::LeanObject,
    mut v_input_53_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lhs_54_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_55_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_57_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_58_: u8 = 0;
    let mut v___x_59_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_61_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_64_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_65_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_66_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_67_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_aig_68_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_69_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_71_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_72_: u8 = 0;
    let mut v_gate_73_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invert_74_: u8 = 0;
    let mut v___x_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_77_: u8 = 0;
    let mut v_discr_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_81_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_82_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_83_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_84_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_85_: u8 = 0;
    let mut v_isSharedCheck_86_: u8 = 0;
    let mut v_unused_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_89_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lhs_54_ = crate::leanh::lean_ctor_get(v_input_53_, 0);
                v_rhs_55_ = crate::leanh::lean_ctor_get(v_input_53_, 1);
                v_isSharedCheck_89_ = (!crate::leanh::lean_is_exclusive(v_input_53_)) as u8;
                if v_isSharedCheck_89_ == 0 {
                    v___x_57_ = v_input_53_;
                    v_isShared_58_ = v_isSharedCheck_89_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_55_);
                    crate::leanh::lean_inc(v_lhs_54_);
                    crate::leanh::lean_dec(v_input_53_);
                    v___x_57_ = crate::leanh::lean_box(0);
                    v_isShared_58_ = v_isSharedCheck_89_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_59_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_60_ = l_BitVec_ofNat(v_w_51_, v___x_59_);
                v_zero_61_ =
                    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v_w_51_, v___x_60_);
                crate::leanh::lean_dec(v___x_60_);
                crate::leanh::lean_inc_ref(v_zero_61_);
                crate::leanh::lean_inc_ref(v_rhs_55_);
                if v_isShared_58_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_57_, 1, v_zero_61_);
                    crate::leanh::lean_ctor_set(v___x_57_, 0, v_rhs_55_);
                    v___x_63_ = v___x_57_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_88_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_88_, 0, v_rhs_55_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_88_, 1, v_zero_61_);
                    v___x_63_ = v_reuseFailAlloc_88_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref_n(v_inst_50_, 2);
                crate::leanh::lean_inc_ref_n(v_inst_49_, 2);
                v_res_64_ = l_Std_Tactic_BVDecide_BVPred_mkEq___redArg(
                    v_inst_49_, v_inst_50_, v_w_51_, v_aig_52_, v___x_63_,
                );
                crate::leanh::lean_dec_ref(v___x_63_);
                v_aig_65_ = crate::leanh::lean_ctor_get(v_res_64_, 0);
                crate::leanh::lean_inc_ref(v_aig_65_);
                v_ref_66_ = crate::leanh::lean_ctor_get(v_res_64_, 1);
                crate::leanh::lean_inc_ref(v_ref_66_);
                crate::leanh::lean_dec_ref(v_res_64_);
                crate::leanh::lean_inc_ref(v_zero_61_);
                crate::leanh::lean_inc(v_w_51_);
                v_res_67_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv_go___redArg(
                    v_inst_49_, v_inst_50_, v_w_51_, v_aig_65_, v_w_51_, v_lhs_54_, v_rhs_55_,
                    v_w_51_, v___x_59_, v_zero_61_, v_zero_61_,
                );
                v_aig_68_ = crate::leanh::lean_ctor_get(v_res_67_, 0);
                v_r_69_ = crate::leanh::lean_ctor_get(v_res_67_, 2);
                v_isSharedCheck_86_ = (!crate::leanh::lean_is_exclusive(v_res_67_)) as u8;
                if v_isSharedCheck_86_ == 0 {
                    v_unused_87_ = crate::leanh::lean_ctor_get(v_res_67_, 1);
                    crate::leanh::lean_dec(v_unused_87_);
                    v___x_71_ = v_res_67_;
                    v_isShared_72_ = v_isSharedCheck_86_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_r_69_);
                    crate::leanh::lean_inc(v_aig_68_);
                    crate::leanh::lean_dec(v_res_67_);
                    v___x_71_ = crate::leanh::lean_box(0);
                    v_isShared_72_ = v_isSharedCheck_86_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_gate_73_ = crate::leanh::lean_ctor_get(v_ref_66_, 0);
                v_invert_74_ = crate::leanh::lean_ctor_get_uint8(
                    v_ref_66_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_85_ = (!crate::leanh::lean_is_exclusive(v_ref_66_)) as u8;
                if v_isSharedCheck_85_ == 0 {
                    v___x_76_ = v_ref_66_;
                    v_isShared_77_ = v_isSharedCheck_85_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_gate_73_);
                    crate::leanh::lean_dec(v_ref_66_);
                    v___x_76_ = crate::leanh::lean_box(0);
                    v_isShared_77_ = v_isSharedCheck_85_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_77_ == 0 {
                    v_discr_79_ = v___x_76_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_84_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_84_, 0, v_gate_73_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_84_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_invert_74_,
                    );
                    v_discr_79_ = v_reuseFailAlloc_84_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_72_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_71_, 1, v_lhs_54_);
                    crate::leanh::lean_ctor_set(v___x_71_, 0, v_discr_79_);
                    v___x_81_ = v___x_71_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_83_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_83_, 0, v_discr_79_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_83_, 1, v_lhs_54_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_83_, 2, v_r_69_);
                    v___x_81_ = v_reuseFailAlloc_83_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_82_ = l_Std_Sat_AIG_RefVec_ite___redArg(
                    v_inst_49_, v_inst_50_, v_w_51_, v_aig_68_, v___x_81_,
                );
                crate::leanh::lean_dec(v_w_51_);
                return v___x_82_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod(
    mut v_00_u03b1_90_: *mut crate::leanh::LeanObject,
    mut v_inst_91_: *mut crate::leanh::LeanObject,
    mut v_inst_92_: *mut crate::leanh::LeanObject,
    mut v_w_93_: *mut crate::leanh::LeanObject,
    mut v_aig_94_: *mut crate::leanh::LeanObject,
    mut v_input_95_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_96_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastUmod___redArg(
        v_inst_91_,
        v_inst_92_,
        v_w_93_,
        v_aig_94_,
        v_input_95_,
    );
    return v___x_96_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Udiv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(
        builtin,
    );
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Umod(builtin);
}

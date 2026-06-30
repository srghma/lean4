// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic Std.Sat.AIG.LawfulVecOperator Init.Omega
use crate::ffi::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt, lean_nat_lor,
};
use crate::r#gen::Init::Data::Bool::l_Bool_toNat;
use crate::r#gen::Init::Data::Nat::Bitwise::Basic::l_Nat_testBit;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Sat::AIG::LawfulVecOperator::{
    initialize_Std_Sat_AIG_LawfulVecOperator, runtime_initialize_Std_Sat_AIG_LawfulVecOperator,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Basic::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic,
};
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___redArg(
    mut v_w_61_: *mut leanh::LeanObject,
    mut v_val_62_: *mut leanh::LeanObject,
    mut v_curr_63_: *mut leanh::LeanObject,
    mut v_s_64_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_65_: u8 = 0;
    let mut v___x_66_: u8 = 0;
    let mut v___x_67_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_68_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_69_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_70_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_71_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_72_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_65_ = lean_nat_dec_lt(v_curr_63_, v_w_61_);
                if v___x_65_ == 0 {
                    leanh::lean_dec(v_curr_63_);
                    return v_s_64_;
                } else {
                    v___x_66_ = l_Nat_testBit(v_val_62_, v_curr_63_);
                    v___x_67_ = leanh::lean_unsigned_to_nat(1);
                    v___x_68_ = lean_nat_add(v_curr_63_, v___x_67_);
                    leanh::lean_dec(v_curr_63_);
                    v___x_69_ = leanh::lean_unsigned_to_nat(0);
                    v___x_70_ = l_Bool_toNat(v___x_66_);
                    v___x_71_ = lean_nat_lor(v___x_69_, v___x_70_);
                    leanh::lean_dec(v___x_70_);
                    v_s_72_ = lean_array_push(v_s_64_, v___x_71_);
                    v_curr_63_ = v___x_68_;
                    v_s_64_ = v_s_72_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___redArg___boxed(
    mut v_w_74_: *mut leanh::LeanObject,
    mut v_val_75_: *mut leanh::LeanObject,
    mut v_curr_76_: *mut leanh::LeanObject,
    mut v_s_77_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_78_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_78_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___redArg(
        v_w_74_, v_val_75_, v_curr_76_, v_s_77_,
    );
    leanh::lean_dec(v_val_75_);
    leanh::lean_dec(v_w_74_);
    return v_res_78_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go(
    mut v_00_u03b1_79_: *mut leanh::LeanObject,
    mut v_inst_80_: *mut leanh::LeanObject,
    mut v_inst_81_: *mut leanh::LeanObject,
    mut v_w_82_: *mut leanh::LeanObject,
    mut v_aig_83_: *mut leanh::LeanObject,
    mut v_val_84_: *mut leanh::LeanObject,
    mut v_curr_85_: *mut leanh::LeanObject,
    mut v_s_86_: *mut leanh::LeanObject,
    mut v_hcurr_87_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_88_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_88_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___redArg(
        v_w_82_, v_val_84_, v_curr_85_, v_s_86_,
    );
    return v___x_88_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___boxed(
    mut v_00_u03b1_89_: *mut leanh::LeanObject,
    mut v_inst_90_: *mut leanh::LeanObject,
    mut v_inst_91_: *mut leanh::LeanObject,
    mut v_w_92_: *mut leanh::LeanObject,
    mut v_aig_93_: *mut leanh::LeanObject,
    mut v_val_94_: *mut leanh::LeanObject,
    mut v_curr_95_: *mut leanh::LeanObject,
    mut v_s_96_: *mut leanh::LeanObject,
    mut v_hcurr_97_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_98_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_98_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go(
        v_00_u03b1_89_,
        v_inst_90_,
        v_inst_91_,
        v_w_92_,
        v_aig_93_,
        v_val_94_,
        v_curr_95_,
        v_s_96_,
        v_hcurr_97_,
    );
    leanh::lean_dec(v_val_94_);
    leanh::lean_dec_ref(v_aig_93_);
    leanh::lean_dec(v_w_92_);
    leanh::lean_dec_ref(v_inst_91_);
    leanh::lean_dec_ref(v_inst_90_);
    return v_res_98_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(
    mut v_w_99_: *mut leanh::LeanObject,
    mut v_val_100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_101_ = leanh::lean_unsigned_to_nat(0);
    v___x_102_ = lean_mk_empty_array_with_capacity(v_w_99_);
    v___x_103_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst_go___redArg(
        v_w_99_, v_val_100_, v___x_101_, v___x_102_,
    );
    return v___x_103_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg___boxed(
    mut v_w_104_: *mut leanh::LeanObject,
    mut v_val_105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_106_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v_w_104_, v_val_105_);
    leanh::lean_dec(v_val_105_);
    leanh::lean_dec(v_w_104_);
    return v_res_106_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst(
    mut v_00_u03b1_107_: *mut leanh::LeanObject,
    mut v_inst_108_: *mut leanh::LeanObject,
    mut v_inst_109_: *mut leanh::LeanObject,
    mut v_w_110_: *mut leanh::LeanObject,
    mut v_aig_111_: *mut leanh::LeanObject,
    mut v_val_112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_113_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v_w_110_, v_val_112_);
    return v___x_113_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___boxed(
    mut v_00_u03b1_114_: *mut leanh::LeanObject,
    mut v_inst_115_: *mut leanh::LeanObject,
    mut v_inst_116_: *mut leanh::LeanObject,
    mut v_w_117_: *mut leanh::LeanObject,
    mut v_aig_118_: *mut leanh::LeanObject,
    mut v_val_119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_120_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst(
        v_00_u03b1_114_,
        v_inst_115_,
        v_inst_116_,
        v_w_117_,
        v_aig_118_,
        v_val_119_,
    );
    leanh::lean_dec(v_val_119_);
    leanh::lean_dec_ref(v_aig_118_);
    leanh::lean_dec(v_w_117_);
    leanh::lean_dec_ref(v_inst_116_);
    leanh::lean_dec_ref(v_inst_115_);
    return v_res_120_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
}
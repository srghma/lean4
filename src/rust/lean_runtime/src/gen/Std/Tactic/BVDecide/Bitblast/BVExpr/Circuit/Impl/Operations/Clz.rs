// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Clz
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Const Std.Sat.AIG.If Init.Omega
use crate::r#gen::Init::Data::BitVec::Basic::l_BitVec_instNatCast___lam__0;
use crate::r#gen::Init::Data::BitVec::BasicAux::l_BitVec_sub;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::l_BitVec_ofNat;
use crate::r#gen::Std::Sat::AIG::If::{
    initialize_Std_Sat_AIG_If, l_Std_Sat_AIG_RefVec_ite___redArg, runtime_initialize_Std_Sat_AIG_If,
};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Const::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const,
    l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::{lean_nat_land, lean_nat_shiftr};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_unsigned_to_nat,
};
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___redArg(
    mut v_inst_88_: *mut LeanObject,
    mut v_inst_89_: *mut LeanObject,
    mut v_w_90_: *mut LeanObject,
    mut v_aig_91_: *mut LeanObject,
    mut v_x_92_: *mut LeanObject,
    mut v_curr_93_: *mut LeanObject,
    mut v_acc_94_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_95_: u8 = 0;
    let mut v___x_96_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_97_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_98_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_99_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vec_109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_116_: u8 = 0;
    let mut v___x_117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_118_: u8 = 0;
    let mut v___x_119_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_95_ = lean_nat_dec_lt(v_curr_93_, v_w_90_);
                if v___x_95_ == 0 {
                    lean_dec(v_curr_93_);
                    lean_dec_ref(v_inst_89_);
                    lean_dec_ref(v_inst_88_);
                    v___x_96_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_96_, 0, v_aig_91_);
                    lean_ctor_set(v___x_96_, 1, v_acc_94_);
                    return v___x_96_;
                } else {
                    v___x_97_ = l_BitVec_instNatCast___lam__0(v_w_90_, v_w_90_);
                    v___x_98_ = lean_unsigned_to_nat(1);
                    v___x_99_ = l_BitVec_ofNat(v_w_90_, v___x_98_);
                    v___x_100_ = l_BitVec_sub(v_w_90_, v___x_97_, v___x_99_);
                    lean_dec(v___x_99_);
                    lean_dec(v___x_97_);
                    v___x_101_ = l_BitVec_instNatCast___lam__0(v_w_90_, v_curr_93_);
                    v___x_102_ = l_BitVec_sub(v_w_90_, v___x_100_, v___x_101_);
                    lean_dec(v___x_101_);
                    lean_dec(v___x_100_);
                    v_lhs_103_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(
                        v_w_90_, v___x_102_,
                    );
                    lean_dec(v___x_102_);
                    v_ref_112_ = lean_array_fget_borrowed(v_x_92_, v_curr_93_);
                    v___x_113_ = lean_nat_shiftr(v_ref_112_, v___x_98_);
                    v___x_114_ = lean_nat_land(v___x_98_, v_ref_112_);
                    v___x_115_ = lean_unsigned_to_nat(0);
                    v___x_116_ = lean_nat_dec_eq(v___x_114_, v___x_115_);
                    lean_dec(v___x_114_);
                    if v___x_116_ == 0 {
                        v___x_117_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_117_, 0, v___x_113_);
                        lean_ctor_set_uint8(
                            v___x_117_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_95_,
                        );
                        v___y_105_ = v___x_117_;
                        state = 1;
                        continue;
                    } else {
                        v___x_118_ = 0;
                        v___x_119_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_119_, 0, v___x_113_);
                        lean_ctor_set_uint8(
                            v___x_119_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_118_,
                        );
                        v___y_105_ = v___x_119_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_106_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_106_, 0, v___y_105_);
                lean_ctor_set(v___x_106_, 1, v_lhs_103_);
                lean_ctor_set(v___x_106_, 2, v_acc_94_);
                lean_inc_ref(v_inst_89_);
                lean_inc_ref(v_inst_88_);
                v_res_107_ = l_Std_Sat_AIG_RefVec_ite___redArg(
                    v_inst_88_, v_inst_89_, v_w_90_, v_aig_91_, v___x_106_,
                );
                v_aig_108_ = lean_ctor_get(v_res_107_, 0);
                lean_inc_ref(v_aig_108_);
                v_vec_109_ = lean_ctor_get(v_res_107_, 1);
                lean_inc_ref(v_vec_109_);
                lean_dec_ref(v_res_107_);
                v___x_110_ = lean_nat_add(v_curr_93_, v___x_98_);
                lean_dec(v_curr_93_);
                v_aig_91_ = v_aig_108_;
                v_curr_93_ = v___x_110_;
                v_acc_94_ = v_vec_109_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___redArg___boxed(
    mut v_inst_120_: *mut LeanObject,
    mut v_inst_121_: *mut LeanObject,
    mut v_w_122_: *mut LeanObject,
    mut v_aig_123_: *mut LeanObject,
    mut v_x_124_: *mut LeanObject,
    mut v_curr_125_: *mut LeanObject,
    mut v_acc_126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_127_: *mut LeanObject = core::ptr::null_mut();
    v_res_127_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___redArg(
        v_inst_120_,
        v_inst_121_,
        v_w_122_,
        v_aig_123_,
        v_x_124_,
        v_curr_125_,
        v_acc_126_,
    );
    lean_dec_ref(v_x_124_);
    lean_dec(v_w_122_);
    return v_res_127_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go(
    mut v_00_u03b1_128_: *mut LeanObject,
    mut v_inst_129_: *mut LeanObject,
    mut v_inst_130_: *mut LeanObject,
    mut v_w_131_: *mut LeanObject,
    mut v_aig_132_: *mut LeanObject,
    mut v_x_133_: *mut LeanObject,
    mut v_curr_134_: *mut LeanObject,
    mut v_acc_135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_136_: *mut LeanObject = core::ptr::null_mut();
    v___x_136_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___redArg(
        v_inst_129_,
        v_inst_130_,
        v_w_131_,
        v_aig_132_,
        v_x_133_,
        v_curr_134_,
        v_acc_135_,
    );
    return v___x_136_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___boxed(
    mut v_00_u03b1_137_: *mut LeanObject,
    mut v_inst_138_: *mut LeanObject,
    mut v_inst_139_: *mut LeanObject,
    mut v_w_140_: *mut LeanObject,
    mut v_aig_141_: *mut LeanObject,
    mut v_x_142_: *mut LeanObject,
    mut v_curr_143_: *mut LeanObject,
    mut v_acc_144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_145_: *mut LeanObject = core::ptr::null_mut();
    v_res_145_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go(
        v_00_u03b1_137_,
        v_inst_138_,
        v_inst_139_,
        v_w_140_,
        v_aig_141_,
        v_x_142_,
        v_curr_143_,
        v_acc_144_,
    );
    lean_dec_ref(v_x_142_);
    lean_dec(v_w_140_);
    return v_res_145_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___redArg(
    mut v_inst_146_: *mut LeanObject,
    mut v_inst_147_: *mut LeanObject,
    mut v_w_148_: *mut LeanObject,
    mut v_aig_149_: *mut LeanObject,
    mut v_x_150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_wconst_152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_154_: *mut LeanObject = core::ptr::null_mut();
    v___x_151_ = l_BitVec_instNatCast___lam__0(v_w_148_, v_w_148_);
    v_wconst_152_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastConst___redArg(v_w_148_, v___x_151_);
    lean_dec(v___x_151_);
    v___x_153_ = lean_unsigned_to_nat(0);
    v___x_154_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz_go___redArg(
        v_inst_146_,
        v_inst_147_,
        v_w_148_,
        v_aig_149_,
        v_x_150_,
        v___x_153_,
        v_wconst_152_,
    );
    return v___x_154_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___redArg___boxed(
    mut v_inst_155_: *mut LeanObject,
    mut v_inst_156_: *mut LeanObject,
    mut v_w_157_: *mut LeanObject,
    mut v_aig_158_: *mut LeanObject,
    mut v_x_159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_160_: *mut LeanObject = core::ptr::null_mut();
    v_res_160_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___redArg(
        v_inst_155_,
        v_inst_156_,
        v_w_157_,
        v_aig_158_,
        v_x_159_,
    );
    lean_dec_ref(v_x_159_);
    lean_dec(v_w_157_);
    return v_res_160_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz(
    mut v_00_u03b1_161_: *mut LeanObject,
    mut v_inst_162_: *mut LeanObject,
    mut v_inst_163_: *mut LeanObject,
    mut v_w_164_: *mut LeanObject,
    mut v_aig_165_: *mut LeanObject,
    mut v_x_166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_167_: *mut LeanObject = core::ptr::null_mut();
    v___x_167_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___redArg(
        v_inst_162_,
        v_inst_163_,
        v_w_164_,
        v_aig_165_,
        v_x_166_,
    );
    return v___x_167_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz___boxed(
    mut v_00_u03b1_168_: *mut LeanObject,
    mut v_inst_169_: *mut LeanObject,
    mut v_inst_170_: *mut LeanObject,
    mut v_w_171_: *mut LeanObject,
    mut v_aig_172_: *mut LeanObject,
    mut v_x_173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_174_: *mut LeanObject = core::ptr::null_mut();
    v_res_174_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_blastClz(
        v_00_u03b1_168_,
        v_inst_169_,
        v_inst_170_,
        v_w_171_,
        v_aig_172_,
        v_x_173_,
    );
    lean_dec_ref(v_x_173_);
    lean_dec(v_w_171_);
    return v_res_174_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Clz(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_If(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Clz(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Clz(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Const(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Sat_AIG_If(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Clz(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Clz(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Clz(builtin);
}

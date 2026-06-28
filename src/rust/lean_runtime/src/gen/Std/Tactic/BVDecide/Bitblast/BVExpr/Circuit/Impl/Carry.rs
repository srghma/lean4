// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Carry
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Operations.Add Init.Omega
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Tactic::BVDecide::Bitblast::BVExpr::Circuit::Impl::Operations::Add::{
    initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add,
    l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg,
    runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::{lean_nat_land, lean_nat_shiftr};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_unsigned_to_nat,
};
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg(
    mut v_inst_87_: *mut LeanObject,
    mut v_inst_88_: *mut LeanObject,
    mut v_w_89_: *mut LeanObject,
    mut v_aig_90_: *mut LeanObject,
    mut v_lhs_91_: *mut LeanObject,
    mut v_rhs_92_: *mut LeanObject,
    mut v_curr_93_: *mut LeanObject,
    mut v_cin_94_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_96_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_97_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_98_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_99_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_105_: u8 = 0;
    let mut v___y_107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_113_: u8 = 0;
    let mut v___x_114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_115_: u8 = 0;
    let mut v___x_116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_123_: u8 = 0;
    let mut v___x_124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_125_: u8 = 0;
    let mut v___x_126_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_105_ = lean_nat_dec_lt(v_curr_93_, v_w_89_);
                if v___x_105_ == 0 {
                    lean_dec(v_curr_93_);
                    lean_dec_ref(v_inst_88_);
                    lean_dec_ref(v_inst_87_);
                    v___x_117_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_117_, 0, v_aig_90_);
                    lean_ctor_set(v___x_117_, 1, v_cin_94_);
                    return v___x_117_;
                } else {
                    v_ref_118_ = lean_array_fget_borrowed(v_lhs_91_, v_curr_93_);
                    v___x_119_ = lean_unsigned_to_nat(1);
                    v___x_120_ = lean_nat_shiftr(v_ref_118_, v___x_119_);
                    v___x_121_ = lean_nat_land(v___x_119_, v_ref_118_);
                    v___x_122_ = lean_unsigned_to_nat(0);
                    v___x_123_ = lean_nat_dec_eq(v___x_121_, v___x_122_);
                    lean_dec(v___x_121_);
                    if v___x_123_ == 0 {
                        v___x_124_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_124_, 0, v___x_120_);
                        lean_ctor_set_uint8(
                            v___x_124_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_105_,
                        );
                        v___y_107_ = v___x_124_;
                        state = 2;
                        continue;
                    } else {
                        v___x_125_ = 0;
                        v___x_126_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_126_, 0, v___x_120_);
                        lean_ctor_set_uint8(
                            v___x_126_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_125_,
                        );
                        v___y_107_ = v___x_126_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_98_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_98_, 0, v___y_96_);
                lean_ctor_set(v___x_98_, 1, v___y_97_);
                lean_ctor_set(v___x_98_, 2, v_cin_94_);
                lean_inc_ref(v_inst_88_);
                lean_inc_ref(v_inst_87_);
                v_res_99_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkFullAdderCarry___redArg(
                    v_inst_87_, v_inst_88_, v_aig_90_, v___x_98_,
                );
                v_aig_100_ = lean_ctor_get(v_res_99_, 0);
                lean_inc_ref(v_aig_100_);
                v_ref_101_ = lean_ctor_get(v_res_99_, 1);
                lean_inc_ref(v_ref_101_);
                lean_dec_ref(v_res_99_);
                v___x_102_ = lean_unsigned_to_nat(1);
                v___x_103_ = lean_nat_add(v_curr_93_, v___x_102_);
                lean_dec(v_curr_93_);
                v_aig_90_ = v_aig_100_;
                v_curr_93_ = v___x_103_;
                v_cin_94_ = v_ref_101_;
                state = 0;
                continue;
            }
            2 => {
                v_ref_108_ = lean_array_fget_borrowed(v_rhs_92_, v_curr_93_);
                v___x_109_ = lean_unsigned_to_nat(1);
                v___x_110_ = lean_nat_shiftr(v_ref_108_, v___x_109_);
                v___x_111_ = lean_nat_land(v___x_109_, v_ref_108_);
                v___x_112_ = lean_unsigned_to_nat(0);
                v___x_113_ = lean_nat_dec_eq(v___x_111_, v___x_112_);
                lean_dec(v___x_111_);
                if v___x_113_ == 0 {
                    v___x_114_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_114_, 0, v___x_110_);
                    lean_ctor_set_uint8(
                        v___x_114_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_105_,
                    );
                    v___y_96_ = v___y_107_;
                    v___y_97_ = v___x_114_;
                    state = 1;
                    continue;
                } else {
                    v___x_115_ = 0;
                    v___x_116_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_116_, 0, v___x_110_);
                    lean_ctor_set_uint8(
                        v___x_116_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_115_,
                    );
                    v___y_96_ = v___y_107_;
                    v___y_97_ = v___x_116_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg___boxed(
    mut v_inst_127_: *mut LeanObject,
    mut v_inst_128_: *mut LeanObject,
    mut v_w_129_: *mut LeanObject,
    mut v_aig_130_: *mut LeanObject,
    mut v_lhs_131_: *mut LeanObject,
    mut v_rhs_132_: *mut LeanObject,
    mut v_curr_133_: *mut LeanObject,
    mut v_cin_134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_135_: *mut LeanObject = core::ptr::null_mut();
    v_res_135_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg(
        v_inst_127_,
        v_inst_128_,
        v_w_129_,
        v_aig_130_,
        v_lhs_131_,
        v_rhs_132_,
        v_curr_133_,
        v_cin_134_,
    );
    lean_dec_ref(v_rhs_132_);
    lean_dec_ref(v_lhs_131_);
    lean_dec(v_w_129_);
    return v_res_135_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go(
    mut v_00_u03b1_136_: *mut LeanObject,
    mut v_inst_137_: *mut LeanObject,
    mut v_inst_138_: *mut LeanObject,
    mut v_w_139_: *mut LeanObject,
    mut v_aig_140_: *mut LeanObject,
    mut v_lhs_141_: *mut LeanObject,
    mut v_rhs_142_: *mut LeanObject,
    mut v_curr_143_: *mut LeanObject,
    mut v_cin_144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_145_: *mut LeanObject = core::ptr::null_mut();
    v___x_145_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg(
        v_inst_137_,
        v_inst_138_,
        v_w_139_,
        v_aig_140_,
        v_lhs_141_,
        v_rhs_142_,
        v_curr_143_,
        v_cin_144_,
    );
    return v___x_145_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___boxed(
    mut v_00_u03b1_146_: *mut LeanObject,
    mut v_inst_147_: *mut LeanObject,
    mut v_inst_148_: *mut LeanObject,
    mut v_w_149_: *mut LeanObject,
    mut v_aig_150_: *mut LeanObject,
    mut v_lhs_151_: *mut LeanObject,
    mut v_rhs_152_: *mut LeanObject,
    mut v_curr_153_: *mut LeanObject,
    mut v_cin_154_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_155_: *mut LeanObject = core::ptr::null_mut();
    v_res_155_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go(
        v_00_u03b1_146_,
        v_inst_147_,
        v_inst_148_,
        v_w_149_,
        v_aig_150_,
        v_lhs_151_,
        v_rhs_152_,
        v_curr_153_,
        v_cin_154_,
    );
    lean_dec_ref(v_rhs_152_);
    lean_dec_ref(v_lhs_151_);
    lean_dec(v_w_149_);
    return v_res_155_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___redArg(
    mut v_inst_156_: *mut LeanObject,
    mut v_inst_157_: *mut LeanObject,
    mut v_aig_158_: *mut LeanObject,
    mut v_input_159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vec_160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_w_161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cin_162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_166_: *mut LeanObject = core::ptr::null_mut();
    v_vec_160_ = lean_ctor_get(v_input_159_, 1);
    lean_inc_ref(v_vec_160_);
    v_w_161_ = lean_ctor_get(v_input_159_, 0);
    lean_inc(v_w_161_);
    v_cin_162_ = lean_ctor_get(v_input_159_, 2);
    lean_inc_ref(v_cin_162_);
    lean_dec_ref(v_input_159_);
    v_lhs_163_ = lean_ctor_get(v_vec_160_, 0);
    lean_inc_ref(v_lhs_163_);
    v_rhs_164_ = lean_ctor_get(v_vec_160_, 1);
    lean_inc_ref(v_rhs_164_);
    lean_dec_ref(v_vec_160_);
    v___x_165_ = lean_unsigned_to_nat(0);
    v___x_166_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit_go___redArg(
        v_inst_156_,
        v_inst_157_,
        v_w_161_,
        v_aig_158_,
        v_lhs_163_,
        v_rhs_164_,
        v___x_165_,
        v_cin_162_,
    );
    lean_dec_ref(v_rhs_164_);
    lean_dec_ref(v_lhs_163_);
    lean_dec(v_w_161_);
    return v___x_166_;
}
pub unsafe fn l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit(
    mut v_00_u03b1_167_: *mut LeanObject,
    mut v_inst_168_: *mut LeanObject,
    mut v_inst_169_: *mut LeanObject,
    mut v_aig_170_: *mut LeanObject,
    mut v_input_171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_172_: *mut LeanObject = core::ptr::null_mut();
    v___x_172_ = l_Std_Tactic_BVDecide_BVExpr_bitblast_mkOverflowBit___redArg(
        v_inst_168_,
        v_inst_169_,
        v_aig_170_,
        v_input_171_,
    );
    return v___x_172_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res =
        runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
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
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(
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
pub unsafe fn initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Operations_Add(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Carry(builtin);
}

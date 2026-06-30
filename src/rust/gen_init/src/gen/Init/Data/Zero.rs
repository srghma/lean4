// Lean compiler output
// Module: Init.Data.Zero
// Imports: Init.Tactics
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
use crate::r#gen::Init::Tactics::{initialize_Init_Tactics, runtime_initialize_Init_Tactics};
pub unsafe fn l_Zero_toOfNat0___redArg(
    mut v_inst_87_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_87_);
    return v_inst_87_;
}
pub unsafe fn l_Zero_toOfNat0___redArg___boxed(
    mut v_inst_88_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_89_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_89_ = l_Zero_toOfNat0___redArg(v_inst_88_);
    leanh::lean_dec(v_inst_88_);
    return v_res_89_;
}
pub unsafe fn l_Zero_toOfNat0(
    mut v_00_u03b1_90_: *mut leanh::LeanObject,
    mut v_inst_91_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_91_);
    return v_inst_91_;
}
pub unsafe fn l_Zero_toOfNat0___boxed(
    mut v_00_u03b1_92_: *mut leanh::LeanObject,
    mut v_inst_93_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_94_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_94_ = l_Zero_toOfNat0(v_00_u03b1_92_, v_inst_93_);
    leanh::lean_dec(v_inst_93_);
    return v_res_94_;
}
pub unsafe fn l_Zero_ofOfNat0___redArg(
    mut v_inst_95_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_95_);
    return v_inst_95_;
}
pub unsafe fn l_Zero_ofOfNat0___redArg___boxed(
    mut v_inst_96_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_97_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_97_ = l_Zero_ofOfNat0___redArg(v_inst_96_);
    leanh::lean_dec(v_inst_96_);
    return v_res_97_;
}
pub unsafe fn l_Zero_ofOfNat0(
    mut v_00_u03b1_98_: *mut leanh::LeanObject,
    mut v_inst_99_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_99_);
    return v_inst_99_;
}
pub unsafe fn l_Zero_ofOfNat0___boxed(
    mut v_00_u03b1_100_: *mut leanh::LeanObject,
    mut v_inst_101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_102_ = l_Zero_ofOfNat0(v_00_u03b1_100_, v_inst_101_);
    leanh::lean_dec(v_inst_101_);
    return v_res_102_;
}
pub unsafe fn l_One_toOfNat1___redArg(
    mut v_inst_103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_103_);
    return v_inst_103_;
}
pub unsafe fn l_One_toOfNat1___redArg___boxed(
    mut v_inst_104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_105_ = l_One_toOfNat1___redArg(v_inst_104_);
    leanh::lean_dec(v_inst_104_);
    return v_res_105_;
}
pub unsafe fn l_One_toOfNat1(
    mut v_00_u03b1_106_: *mut leanh::LeanObject,
    mut v_inst_107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_107_);
    return v_inst_107_;
}
pub unsafe fn l_One_toOfNat1___boxed(
    mut v_00_u03b1_108_: *mut leanh::LeanObject,
    mut v_inst_109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_110_ = l_One_toOfNat1(v_00_u03b1_108_, v_inst_109_);
    leanh::lean_dec(v_inst_109_);
    return v_res_110_;
}
pub unsafe fn l_One_ofOfNat1___redArg(
    mut v_inst_111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_111_);
    return v_inst_111_;
}
pub unsafe fn l_One_ofOfNat1___redArg___boxed(
    mut v_inst_112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_113_ = l_One_ofOfNat1___redArg(v_inst_112_);
    leanh::lean_dec(v_inst_112_);
    return v_res_113_;
}
pub unsafe fn l_One_ofOfNat1(
    mut v_00_u03b1_114_: *mut leanh::LeanObject,
    mut v_inst_115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_inst_115_);
    return v_inst_115_;
}
pub unsafe fn l_One_ofOfNat1___boxed(
    mut v_00_u03b1_116_: *mut leanh::LeanObject,
    mut v_inst_117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_118_ = l_One_ofOfNat1(v_00_u03b1_116_, v_inst_117_);
    leanh::lean_dec(v_inst_117_);
    return v_res_118_;
}
pub unsafe fn l_npowRec___redArg(
    mut v_inst_119_: *mut leanh::LeanObject,
    mut v_inst_120_: *mut leanh::LeanObject,
    mut v_x_121_: *mut leanh::LeanObject,
    mut v_x_122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_124_: u8 = 0;
    v_zero_123_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_124_ = lean_nat_dec_eq(v_x_121_, v_zero_123_);
    if v_isZero_124_ == 1 {
        leanh::lean_dec(v_x_122_);
        leanh::lean_dec(v_inst_120_);
        leanh::lean_inc(v_inst_119_);
        return v_inst_119_;
    } else {
        let mut v_one_125_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_126_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_127_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_128_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_one_125_ = leanh::lean_unsigned_to_nat(1);
        v_n_126_ = lean_nat_sub(v_x_121_, v_one_125_);
        leanh::lean_inc(v_x_122_);
        leanh::lean_inc(v_inst_120_);
        v___x_127_ = l_npowRec___redArg(v_inst_119_, v_inst_120_, v_n_126_, v_x_122_);
        leanh::lean_dec(v_n_126_);
        v___x_128_ = leanh::lean_apply_2(v_inst_120_, v___x_127_, v_x_122_);
        return v___x_128_;
    }
}
pub unsafe fn l_npowRec___redArg___boxed(
    mut v_inst_129_: *mut leanh::LeanObject,
    mut v_inst_130_: *mut leanh::LeanObject,
    mut v_x_131_: *mut leanh::LeanObject,
    mut v_x_132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_133_ = l_npowRec___redArg(v_inst_129_, v_inst_130_, v_x_131_, v_x_132_);
    leanh::lean_dec(v_x_131_);
    leanh::lean_dec(v_inst_129_);
    return v_res_133_;
}
pub unsafe fn l_npowRec(
    mut v_M_134_: *mut leanh::LeanObject,
    mut v_inst_135_: *mut leanh::LeanObject,
    mut v_inst_136_: *mut leanh::LeanObject,
    mut v_x_137_: *mut leanh::LeanObject,
    mut v_x_138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_139_ = l_npowRec___redArg(v_inst_135_, v_inst_136_, v_x_137_, v_x_138_);
    return v___x_139_;
}
pub unsafe fn l_npowRec___boxed(
    mut v_M_140_: *mut leanh::LeanObject,
    mut v_inst_141_: *mut leanh::LeanObject,
    mut v_inst_142_: *mut leanh::LeanObject,
    mut v_x_143_: *mut leanh::LeanObject,
    mut v_x_144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_145_ = l_npowRec(v_M_140_, v_inst_141_, v_inst_142_, v_x_143_, v_x_144_);
    leanh::lean_dec(v_x_143_);
    leanh::lean_dec(v_inst_141_);
    return v_res_145_;
}
pub unsafe fn l_nsmulRec___redArg(
    mut v_inst_146_: *mut leanh::LeanObject,
    mut v_inst_147_: *mut leanh::LeanObject,
    mut v_x_148_: *mut leanh::LeanObject,
    mut v_x_149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_151_: u8 = 0;
    v_zero_150_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_151_ = lean_nat_dec_eq(v_x_148_, v_zero_150_);
    if v_isZero_151_ == 1 {
        leanh::lean_dec(v_x_149_);
        leanh::lean_dec(v_inst_147_);
        leanh::lean_inc(v_inst_146_);
        return v_inst_146_;
    } else {
        let mut v_one_152_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_153_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_154_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_155_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_one_152_ = leanh::lean_unsigned_to_nat(1);
        v_n_153_ = lean_nat_sub(v_x_148_, v_one_152_);
        leanh::lean_inc(v_x_149_);
        leanh::lean_inc(v_inst_147_);
        v___x_154_ = l_nsmulRec___redArg(v_inst_146_, v_inst_147_, v_n_153_, v_x_149_);
        leanh::lean_dec(v_n_153_);
        v___x_155_ = leanh::lean_apply_2(v_inst_147_, v___x_154_, v_x_149_);
        return v___x_155_;
    }
}
pub unsafe fn l_nsmulRec___redArg___boxed(
    mut v_inst_156_: *mut leanh::LeanObject,
    mut v_inst_157_: *mut leanh::LeanObject,
    mut v_x_158_: *mut leanh::LeanObject,
    mut v_x_159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_160_ = l_nsmulRec___redArg(v_inst_156_, v_inst_157_, v_x_158_, v_x_159_);
    leanh::lean_dec(v_x_158_);
    leanh::lean_dec(v_inst_156_);
    return v_res_160_;
}
pub unsafe fn l_nsmulRec(
    mut v_M_161_: *mut leanh::LeanObject,
    mut v_inst_162_: *mut leanh::LeanObject,
    mut v_inst_163_: *mut leanh::LeanObject,
    mut v_x_164_: *mut leanh::LeanObject,
    mut v_x_165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_166_ = l_nsmulRec___redArg(v_inst_162_, v_inst_163_, v_x_164_, v_x_165_);
    return v___x_166_;
}
pub unsafe fn l_nsmulRec___boxed(
    mut v_M_167_: *mut leanh::LeanObject,
    mut v_inst_168_: *mut leanh::LeanObject,
    mut v_inst_169_: *mut leanh::LeanObject,
    mut v_x_170_: *mut leanh::LeanObject,
    mut v_x_171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_172_ = l_nsmulRec(v_M_167_, v_inst_168_, v_inst_169_, v_x_170_, v_x_171_);
    leanh::lean_dec(v_x_170_);
    leanh::lean_dec(v_inst_168_);
    return v_res_172_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Zero(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Zero(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Zero(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Tactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Zero(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Zero(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Zero(builtin);
}
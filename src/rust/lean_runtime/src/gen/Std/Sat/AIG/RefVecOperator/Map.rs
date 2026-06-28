// Lean compiler output
// Module: Std.Sat.AIG.RefVecOperator.Map
// Imports: Std.Sat.AIG.LawfulVecOperator Init.Omega
use crate::r#gen::Init::Data::Bool::l_Bool_toNat;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Std::Sat::AIG::LawfulVecOperator::{
    initialize_Std_Sat_AIG_LawfulVecOperator, runtime_initialize_Std_Sat_AIG_LawfulVecOperator,
};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::{
    lean_nat_land, lean_nat_lor, lean_nat_shiftr,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_mul,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_2, lean_box, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_unsigned_to_nat,
};
pub unsafe fn l_Std_Sat_AIG_RefVec_map_go___redArg(
    mut v_len_92_: *mut LeanObject,
    mut v_aig_93_: *mut LeanObject,
    mut v_idx_94_: *mut LeanObject,
    mut v_s_95_: *mut LeanObject,
    mut v_input_96_: *mut LeanObject,
    mut v_f_97_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_99_: *mut LeanObject = core::ptr::null_mut();
    let mut v_res_100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_aig_102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_gate_103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invert_104_: u8 = 0;
    let mut v___x_105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_113_: u8 = 0;
    let mut v___x_114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_120_: u8 = 0;
    let mut v___x_121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_122_: u8 = 0;
    let mut v___x_123_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_113_ = lean_nat_dec_lt(v_idx_94_, v_len_92_);
                if v___x_113_ == 0 {
                    lean_dec_ref(v_f_97_);
                    lean_dec(v_idx_94_);
                    v___x_114_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_114_, 0, v_aig_93_);
                    lean_ctor_set(v___x_114_, 1, v_s_95_);
                    return v___x_114_;
                } else {
                    v_ref_115_ = lean_array_fget_borrowed(v_input_96_, v_idx_94_);
                    v___x_116_ = lean_unsigned_to_nat(1);
                    v___x_117_ = lean_nat_shiftr(v_ref_115_, v___x_116_);
                    v___x_118_ = lean_nat_land(v___x_116_, v_ref_115_);
                    v___x_119_ = lean_unsigned_to_nat(0);
                    v___x_120_ = lean_nat_dec_eq(v___x_118_, v___x_119_);
                    lean_dec(v___x_118_);
                    if v___x_120_ == 0 {
                        v___x_121_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_121_, 0, v___x_117_);
                        lean_ctor_set_uint8(
                            v___x_121_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_113_,
                        );
                        v___y_99_ = v___x_121_;
                        state = 1;
                        continue;
                    } else {
                        v___x_122_ = 0;
                        v___x_123_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v___x_123_, 0, v___x_117_);
                        lean_ctor_set_uint8(
                            v___x_123_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v___x_122_,
                        );
                        v___y_99_ = v___x_123_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_f_97_);
                v_res_100_ = lean_apply_2(v_f_97_, v_aig_93_, v___y_99_);
                v_ref_101_ = lean_ctor_get(v_res_100_, 1);
                lean_inc_ref(v_ref_101_);
                v_aig_102_ = lean_ctor_get(v_res_100_, 0);
                lean_inc_ref(v_aig_102_);
                lean_dec_ref(v_res_100_);
                v_gate_103_ = lean_ctor_get(v_ref_101_, 0);
                lean_inc(v_gate_103_);
                v_invert_104_ = lean_ctor_get_uint8(
                    v_ref_101_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                lean_dec_ref(v_ref_101_);
                v___x_105_ = lean_unsigned_to_nat(1);
                v___x_106_ = lean_nat_add(v_idx_94_, v___x_105_);
                lean_dec(v_idx_94_);
                v___x_107_ = lean_unsigned_to_nat(2);
                v___x_108_ = lean_nat_mul(v_gate_103_, v___x_107_);
                lean_dec(v_gate_103_);
                v___x_109_ = l_Bool_toNat(v_invert_104_);
                v___x_110_ = lean_nat_lor(v___x_108_, v___x_109_);
                lean_dec(v___x_109_);
                lean_dec(v___x_108_);
                v_s_111_ = lean_array_push(v_s_95_, v___x_110_);
                v_aig_93_ = v_aig_102_;
                v_idx_94_ = v___x_106_;
                v_s_95_ = v_s_111_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map_go___redArg___boxed(
    mut v_len_124_: *mut LeanObject,
    mut v_aig_125_: *mut LeanObject,
    mut v_idx_126_: *mut LeanObject,
    mut v_s_127_: *mut LeanObject,
    mut v_input_128_: *mut LeanObject,
    mut v_f_129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_130_: *mut LeanObject = core::ptr::null_mut();
    v_res_130_ = l_Std_Sat_AIG_RefVec_map_go___redArg(
        v_len_124_,
        v_aig_125_,
        v_idx_126_,
        v_s_127_,
        v_input_128_,
        v_f_129_,
    );
    lean_dec_ref(v_input_128_);
    lean_dec(v_len_124_);
    return v_res_130_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map_go(
    mut v_00_u03b1_131_: *mut LeanObject,
    mut v_inst_132_: *mut LeanObject,
    mut v_inst_133_: *mut LeanObject,
    mut v_len_134_: *mut LeanObject,
    mut v_aig_135_: *mut LeanObject,
    mut v_idx_136_: *mut LeanObject,
    mut v_hidx_137_: *mut LeanObject,
    mut v_s_138_: *mut LeanObject,
    mut v_input_139_: *mut LeanObject,
    mut v_f_140_: *mut LeanObject,
    mut v_inst_141_: *mut LeanObject,
    mut v_inst_142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_143_: *mut LeanObject = core::ptr::null_mut();
    v___x_143_ = l_Std_Sat_AIG_RefVec_map_go___redArg(
        v_len_134_,
        v_aig_135_,
        v_idx_136_,
        v_s_138_,
        v_input_139_,
        v_f_140_,
    );
    return v___x_143_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map_go___boxed(
    mut v_00_u03b1_144_: *mut LeanObject,
    mut v_inst_145_: *mut LeanObject,
    mut v_inst_146_: *mut LeanObject,
    mut v_len_147_: *mut LeanObject,
    mut v_aig_148_: *mut LeanObject,
    mut v_idx_149_: *mut LeanObject,
    mut v_hidx_150_: *mut LeanObject,
    mut v_s_151_: *mut LeanObject,
    mut v_input_152_: *mut LeanObject,
    mut v_f_153_: *mut LeanObject,
    mut v_inst_154_: *mut LeanObject,
    mut v_inst_155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_156_: *mut LeanObject = core::ptr::null_mut();
    v_res_156_ = l_Std_Sat_AIG_RefVec_map_go(
        v_00_u03b1_144_,
        v_inst_145_,
        v_inst_146_,
        v_len_147_,
        v_aig_148_,
        v_idx_149_,
        v_hidx_150_,
        v_s_151_,
        v_input_152_,
        v_f_153_,
        v_inst_154_,
        v_inst_155_,
    );
    lean_dec_ref(v_input_152_);
    lean_dec(v_len_147_);
    lean_dec_ref(v_inst_146_);
    lean_dec_ref(v_inst_145_);
    return v_res_156_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map___redArg(
    mut v_len_157_: *mut LeanObject,
    mut v_aig_158_: *mut LeanObject,
    mut v_target_159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vec_160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_func_161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_164_: *mut LeanObject = core::ptr::null_mut();
    v_vec_160_ = lean_ctor_get(v_target_159_, 0);
    lean_inc_ref(v_vec_160_);
    v_func_161_ = lean_ctor_get(v_target_159_, 1);
    lean_inc_ref(v_func_161_);
    lean_dec_ref(v_target_159_);
    v___x_162_ = lean_unsigned_to_nat(0);
    v___x_163_ = lean_mk_empty_array_with_capacity(v_len_157_);
    v___x_164_ = l_Std_Sat_AIG_RefVec_map_go___redArg(
        v_len_157_,
        v_aig_158_,
        v___x_162_,
        v___x_163_,
        v_vec_160_,
        v_func_161_,
    );
    lean_dec_ref(v_vec_160_);
    return v___x_164_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map___redArg___boxed(
    mut v_len_165_: *mut LeanObject,
    mut v_aig_166_: *mut LeanObject,
    mut v_target_167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_168_: *mut LeanObject = core::ptr::null_mut();
    v_res_168_ = l_Std_Sat_AIG_RefVec_map___redArg(v_len_165_, v_aig_166_, v_target_167_);
    lean_dec(v_len_165_);
    return v_res_168_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map(
    mut v_00_u03b1_169_: *mut LeanObject,
    mut v_inst_170_: *mut LeanObject,
    mut v_inst_171_: *mut LeanObject,
    mut v_len_172_: *mut LeanObject,
    mut v_aig_173_: *mut LeanObject,
    mut v_target_174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_175_: *mut LeanObject = core::ptr::null_mut();
    v___x_175_ = l_Std_Sat_AIG_RefVec_map___redArg(v_len_172_, v_aig_173_, v_target_174_);
    return v___x_175_;
}
pub unsafe fn l_Std_Sat_AIG_RefVec_map___boxed(
    mut v_00_u03b1_176_: *mut LeanObject,
    mut v_inst_177_: *mut LeanObject,
    mut v_inst_178_: *mut LeanObject,
    mut v_len_179_: *mut LeanObject,
    mut v_aig_180_: *mut LeanObject,
    mut v_target_181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_182_: *mut LeanObject = core::ptr::null_mut();
    v_res_182_ = l_Std_Sat_AIG_RefVec_map(
        v_00_u03b1_176_,
        v_inst_177_,
        v_inst_178_,
        v_len_179_,
        v_aig_180_,
        v_target_181_,
    );
    lean_dec(v_len_179_);
    lean_dec_ref(v_inst_178_);
    lean_dec_ref(v_inst_177_);
    return v_res_182_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Sat_AIG_RefVecOperator_Map(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
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
pub unsafe fn meta_initialize_Std_Sat_AIG_RefVecOperator_Map(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Sat_AIG_RefVecOperator_Map(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Sat_AIG_LawfulVecOperator(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Sat_AIG_RefVecOperator_Map(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Sat_AIG_RefVecOperator_Map(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Sat_AIG_RefVecOperator_Map(builtin);
}

// Lean compiler output
// Module: Init.Data.Ord.Array
// Imports: Init.Data.Ord.Basic Init.Omega Init.ByCases Init.Data.Array.Basic Init.WFTactics
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Ord::Basic::{
    initialize_Init_Data_Ord_Basic, runtime_initialize_Init_Data_Ord_Basic,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::WFTactics::{initialize_Init_WFTactics, runtime_initialize_Init_WFTactics};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_nat_add, lean_nat_dec_le,
};
pub unsafe fn l___private_Init_Data_Ord_Array_0__Array_compareLex_go___redArg(
    mut v_cmp_101_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_102_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_103_: *mut crate::leanh::LeanObject,
    mut v_i_104_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_106_: u8 = 0;
    let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_108_: u8 = 0;
    let mut v___x_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_112_: u8 = 0;
    let mut v___x_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_116_: u8 = 0;
    let mut v___x_117_: u8 = 0;
    let mut v___x_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_119_: u8 = 0;
    let mut v___x_120_: u8 = 0;
    let mut v___x_121_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_105_ = lean_array_get_size(v_a_u2081_102_);
                v___x_106_ = lean_nat_dec_le(v___x_105_, v_i_104_);
                if v___x_106_ == 0 {
                    v___x_107_ = lean_array_get_size(v_a_u2082_103_);
                    v___x_108_ = lean_nat_dec_le(v___x_107_, v_i_104_);
                    if v___x_108_ == 0 {
                        v___x_109_ = lean_array_fget_borrowed(v_a_u2081_102_, v_i_104_);
                        v___x_110_ = lean_array_fget_borrowed(v_a_u2082_103_, v_i_104_);
                        crate::leanh::lean_inc_ref(v_cmp_101_);
                        crate::leanh::lean_inc(v___x_110_);
                        crate::leanh::lean_inc(v___x_109_);
                        v___x_111_ = crate::leanh::lean_apply_2(v_cmp_101_, v___x_109_, v___x_110_);
                        v___x_112_ = (crate::leanh::lean_unbox(v___x_111_) as u8);
                        if v___x_112_ == 1 {
                            v___x_113_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_114_ = lean_nat_add(v_i_104_, v___x_113_);
                            crate::leanh::lean_dec(v_i_104_);
                            v_i_104_ = v___x_114_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_i_104_);
                            crate::leanh::lean_dec_ref(v_cmp_101_);
                            v___x_116_ = (crate::leanh::lean_unbox(v___x_111_) as u8);
                            return v___x_116_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_i_104_);
                        crate::leanh::lean_dec_ref(v_cmp_101_);
                        v___x_117_ = 2;
                        return v___x_117_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_cmp_101_);
                    v___x_118_ = lean_array_get_size(v_a_u2082_103_);
                    v___x_119_ = lean_nat_dec_le(v___x_118_, v_i_104_);
                    crate::leanh::lean_dec(v_i_104_);
                    if v___x_119_ == 0 {
                        v___x_120_ = 0;
                        return v___x_120_;
                    } else {
                        v___x_121_ = 1;
                        return v___x_121_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Ord_Array_0__Array_compareLex_go___redArg___boxed(
    mut v_cmp_122_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_123_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_124_: *mut crate::leanh::LeanObject,
    mut v_i_125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_126_: u8 = 0;
    let mut v_r_127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_126_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go___redArg(
        v_cmp_122_,
        v_a_u2081_123_,
        v_a_u2082_124_,
        v_i_125_,
    );
    crate::leanh::lean_dec_ref(v_a_u2082_124_);
    crate::leanh::lean_dec_ref(v_a_u2081_123_);
    v_r_127_ = crate::leanh::lean_box((v_res_126_) as usize);
    return v_r_127_;
}
pub unsafe fn l___private_Init_Data_Ord_Array_0__Array_compareLex_go(
    mut v_00_u03b1_128_: *mut crate::leanh::LeanObject,
    mut v_cmp_129_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_130_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_131_: *mut crate::leanh::LeanObject,
    mut v_i_132_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_133_: u8 = 0;
    v___x_133_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go___redArg(
        v_cmp_129_,
        v_a_u2081_130_,
        v_a_u2082_131_,
        v_i_132_,
    );
    return v___x_133_;
}
pub unsafe fn l___private_Init_Data_Ord_Array_0__Array_compareLex_go___boxed(
    mut v_00_u03b1_134_: *mut crate::leanh::LeanObject,
    mut v_cmp_135_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_136_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_137_: *mut crate::leanh::LeanObject,
    mut v_i_138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_139_: u8 = 0;
    let mut v_r_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_139_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go(
        v_00_u03b1_134_,
        v_cmp_135_,
        v_a_u2081_136_,
        v_a_u2082_137_,
        v_i_138_,
    );
    crate::leanh::lean_dec_ref(v_a_u2082_137_);
    crate::leanh::lean_dec_ref(v_a_u2081_136_);
    v_r_140_ = crate::leanh::lean_box((v_res_139_) as usize);
    return v_r_140_;
}
pub unsafe fn l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter___redArg(
    mut v_x_141_: u8,
    mut v_h__1_142_: *mut crate::leanh::LeanObject,
    mut v_h__2_143_: *mut crate::leanh::LeanObject,
    mut v_h__3_144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_141_ {
        0 => {
            let mut v___x_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_144_);
            crate::leanh::lean_dec(v_h__2_143_);
            v___x_145_ = crate::leanh::lean_box(0);
            v___x_146_ = crate::leanh::lean_apply_1(v_h__1_142_, v___x_145_);
            return v___x_146_;
        }
        1 => {
            let mut v___x_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_144_);
            crate::leanh::lean_dec(v_h__1_142_);
            v___x_147_ = crate::leanh::lean_box(0);
            v___x_148_ = crate::leanh::lean_apply_1(v_h__2_143_, v___x_147_);
            return v___x_148_;
        }
        _ => {
            let mut v___x_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_143_);
            crate::leanh::lean_dec(v_h__1_142_);
            v___x_149_ = crate::leanh::lean_box(0);
            v___x_150_ = crate::leanh::lean_apply_1(v_h__3_144_, v___x_149_);
            return v___x_150_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter___redArg___boxed(
    mut v_x_151_: *mut crate::leanh::LeanObject,
    mut v_h__1_152_: *mut crate::leanh::LeanObject,
    mut v_h__2_153_: *mut crate::leanh::LeanObject,
    mut v_h__3_154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_36__boxed_155_: u8 = 0;
    let mut v_res_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_36__boxed_155_ = (crate::leanh::lean_unbox(v_x_151_) as u8);
    v_res_156_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter___redArg(
        v_x_36__boxed_155_,
        v_h__1_152_,
        v_h__2_153_,
        v_h__3_154_,
    );
    return v_res_156_;
}
pub unsafe fn l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter(
    mut v_motive_157_: *mut crate::leanh::LeanObject,
    mut v_x_158_: u8,
    mut v_h__1_159_: *mut crate::leanh::LeanObject,
    mut v_h__2_160_: *mut crate::leanh::LeanObject,
    mut v_h__3_161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match v_x_158_ {
        0 => {
            let mut v___x_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_161_);
            crate::leanh::lean_dec(v_h__2_160_);
            v___x_162_ = crate::leanh::lean_box(0);
            v___x_163_ = crate::leanh::lean_apply_1(v_h__1_159_, v___x_162_);
            return v___x_163_;
        }
        1 => {
            let mut v___x_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_161_);
            crate::leanh::lean_dec(v_h__1_159_);
            v___x_164_ = crate::leanh::lean_box(0);
            v___x_165_ = crate::leanh::lean_apply_1(v_h__2_160_, v___x_164_);
            return v___x_165_;
        }
        _ => {
            let mut v___x_166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_160_);
            crate::leanh::lean_dec(v_h__1_159_);
            v___x_166_ = crate::leanh::lean_box(0);
            v___x_167_ = crate::leanh::lean_apply_1(v_h__3_161_, v___x_166_);
            return v___x_167_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter___boxed(
    mut v_motive_168_: *mut crate::leanh::LeanObject,
    mut v_x_169_: *mut crate::leanh::LeanObject,
    mut v_h__1_170_: *mut crate::leanh::LeanObject,
    mut v_h__2_171_: *mut crate::leanh::LeanObject,
    mut v_h__3_172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_51__boxed_173_: u8 = 0;
    let mut v_res_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_51__boxed_173_ = (crate::leanh::lean_unbox(v_x_169_) as u8);
    v_res_174_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_match__1_splitter(
        v_motive_168_,
        v_x_51__boxed_173_,
        v_h__1_170_,
        v_h__2_171_,
        v_h__3_172_,
    );
    return v_res_174_;
}
pub unsafe fn l_Array_compareLex___redArg(
    mut v_cmp_175_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_176_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_177_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_179_: u8 = 0;
    v___x_178_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_179_ = l___private_Init_Data_Ord_Array_0__Array_compareLex_go___redArg(
        v_cmp_175_,
        v_a_u2081_176_,
        v_a_u2082_177_,
        v___x_178_,
    );
    return v___x_179_;
}
pub unsafe fn l_Array_compareLex___redArg___boxed(
    mut v_cmp_180_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_181_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_183_: u8 = 0;
    let mut v_r_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_183_ = l_Array_compareLex___redArg(v_cmp_180_, v_a_u2081_181_, v_a_u2082_182_);
    crate::leanh::lean_dec_ref(v_a_u2082_182_);
    crate::leanh::lean_dec_ref(v_a_u2081_181_);
    v_r_184_ = crate::leanh::lean_box((v_res_183_) as usize);
    return v_r_184_;
}
pub unsafe fn l_Array_compareLex(
    mut v_00_u03b1_185_: *mut crate::leanh::LeanObject,
    mut v_cmp_186_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_187_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_188_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_189_: u8 = 0;
    v___x_189_ = l_Array_compareLex___redArg(v_cmp_186_, v_a_u2081_187_, v_a_u2082_188_);
    return v___x_189_;
}
pub unsafe fn l_Array_compareLex___boxed(
    mut v_00_u03b1_190_: *mut crate::leanh::LeanObject,
    mut v_cmp_191_: *mut crate::leanh::LeanObject,
    mut v_a_u2081_192_: *mut crate::leanh::LeanObject,
    mut v_a_u2082_193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_194_: u8 = 0;
    let mut v_r_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_194_ = l_Array_compareLex(v_00_u03b1_190_, v_cmp_191_, v_a_u2081_192_, v_a_u2082_193_);
    crate::leanh::lean_dec_ref(v_a_u2082_193_);
    crate::leanh::lean_dec_ref(v_a_u2081_192_);
    v_r_195_ = crate::leanh::lean_box((v_res_194_) as usize);
    return v_r_195_;
}
pub unsafe fn l_Array_instOrd___redArg(
    mut v_inst_196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_197_ = crate::leanh::lean_alloc_closure(
        l_Array_compareLex___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_197_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_197_, 1, v_inst_196_);
    return v___x_197_;
}
pub unsafe fn l_Array_instOrd(
    mut v_00_u03b1_198_: *mut crate::leanh::LeanObject,
    mut v_inst_199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_200_ = crate::leanh::lean_alloc_closure(
        l_Array_compareLex___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_200_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_200_, 1, v_inst_199_);
    return v___x_200_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Ord_Array(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Ord_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Ord_Array(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Ord_Array(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Ord_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Ord_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Ord_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Ord_Array(builtin);
}

// Lean compiler output
// Module: Lean.Util.ReplaceExpr
// Imports: Lean.Expr Lean.Util.PtrSet
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Expr_app___override, l_Lean_Expr_forallE___override,
    l_Lean_Expr_lam___override, l_Lean_Expr_letE___override, l_Lean_Expr_mdata___override,
    l_Lean_Expr_proj___override, l_Lean_instBEqBinderInfo_beq, runtime_initialize_Lean_Expr,
};
use crate::r#gen::Lean::Util::PtrSet::{
    initialize_Lean_Util_PtrSet, runtime_initialize_Lean_Util_PtrSet,
};
use crate::lean_imports_rs::Init::Prelude::lean_usize_dec_eq;
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub unsafe fn l_Lean_Expr_replaceImpl___boxed(
    mut v_f_x3f_101_: *mut LeanObject,
    mut v_e_102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_103_: *mut LeanObject = core::ptr::null_mut();
    v_res_103_ = lean_replace_expr(v_f_x3f_101_, v_e_102_);
    lean_dec_ref(v_e_102_);
    lean_dec_ref(v_f_x3f_101_);
    return v_res_103_;
}
pub unsafe fn l_Lean_Expr_replace(
    mut v_f_x3f_104_: *mut LeanObject,
    mut v_e_105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_106_: *mut LeanObject = core::ptr::null_mut();
    v___x_106_ = lean_replace_expr(v_f_x3f_104_, v_e_105_);
    return v___x_106_;
}
pub unsafe fn l_Lean_Expr_replace___boxed(
    mut v_f_x3f_107_: *mut LeanObject,
    mut v_e_108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_109_: *mut LeanObject = core::ptr::null_mut();
    v_res_109_ = l_Lean_Expr_replace(v_f_x3f_107_, v_e_108_);
    lean_dec_ref(v_e_108_);
    lean_dec_ref(v_f_x3f_107_);
    return v_res_109_;
}
pub unsafe fn l_Lean_Expr_replaceNoCache(
    mut v_f_x3f_110_: *mut LeanObject,
    mut v_e_111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_116_: u8 = 0;
    let mut v_d_117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_120_: u8 = 0;
    let mut v___x_121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_122_: u8 = 0;
    let mut v___x_123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_124_: usize = 0;
    let mut v___x_125_: usize = 0;
    let mut v___x_126_: u8 = 0;
    let mut v___x_127_: usize = 0;
    let mut v___x_128_: usize = 0;
    let mut v___x_129_: u8 = 0;
    let mut v_binderName_130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_133_: u8 = 0;
    let mut v_d_134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_137_: u8 = 0;
    let mut v___x_138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_139_: u8 = 0;
    let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_141_: usize = 0;
    let mut v___x_142_: usize = 0;
    let mut v___x_143_: u8 = 0;
    let mut v___x_144_: usize = 0;
    let mut v___x_145_: usize = 0;
    let mut v___x_146_: u8 = 0;
    let mut v_data_147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_150_: usize = 0;
    let mut v___x_151_: usize = 0;
    let mut v___x_152_: u8 = 0;
    let mut v___x_153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_158_: u8 = 0;
    let mut v_t_159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_163_: u8 = 0;
    let mut v___x_164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_165_: usize = 0;
    let mut v___x_166_: usize = 0;
    let mut v___x_167_: u8 = 0;
    let mut v___x_168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_169_: usize = 0;
    let mut v___x_170_: usize = 0;
    let mut v___x_171_: u8 = 0;
    let mut v___x_172_: usize = 0;
    let mut v___x_173_: usize = 0;
    let mut v___x_174_: u8 = 0;
    let mut v_fn_175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_f_177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_180_: u8 = 0;
    let mut v___x_181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_182_: usize = 0;
    let mut v___x_183_: usize = 0;
    let mut v___x_184_: u8 = 0;
    let mut v___x_185_: usize = 0;
    let mut v___x_186_: usize = 0;
    let mut v___x_187_: u8 = 0;
    let mut v_typeName_188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_192_: usize = 0;
    let mut v___x_193_: usize = 0;
    let mut v___x_194_: u8 = 0;
    let mut v___x_195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_196_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_f_x3f_110_);
                lean_inc_ref(v_e_111_);
                v___x_112_ = lean_apply_1(v_f_x3f_110_, v_e_111_);
                if lean_obj_tag(v___x_112_) == 0 {
                    match lean_obj_tag(v_e_111_) {
                        7 => {
                            v_binderName_113_ = lean_ctor_get(v_e_111_, 0);
                            v_binderType_114_ = lean_ctor_get(v_e_111_, 1);
                            v_body_115_ = lean_ctor_get(v_e_111_, 2);
                            v_binderInfo_116_ = lean_ctor_get_uint8(
                                v_e_111_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                            );
                            lean_inc_ref(v_binderType_114_);
                            lean_inc_ref(v_f_x3f_110_);
                            v_d_117_ = l_Lean_Expr_replaceNoCache(v_f_x3f_110_, v_binderType_114_);
                            lean_inc_ref(v_body_115_);
                            v_b_118_ = l_Lean_Expr_replaceNoCache(v_f_x3f_110_, v_body_115_);
                            v___x_124_ = lean_ptr_addr(v_binderType_114_);
                            v___x_125_ = lean_ptr_addr(v_d_117_);
                            v___x_126_ = lean_usize_dec_eq(v___x_124_, v___x_125_);
                            if v___x_126_ == 0 {
                                v___y_120_ = v___x_126_;
                                state = 1;
                                continue;
                            } else {
                                v___x_127_ = lean_ptr_addr(v_body_115_);
                                v___x_128_ = lean_ptr_addr(v_b_118_);
                                v___x_129_ = lean_usize_dec_eq(v___x_127_, v___x_128_);
                                v___y_120_ = v___x_129_;
                                state = 1;
                                continue;
                            }
                        }
                        6 => {
                            v_binderName_130_ = lean_ctor_get(v_e_111_, 0);
                            v_binderType_131_ = lean_ctor_get(v_e_111_, 1);
                            v_body_132_ = lean_ctor_get(v_e_111_, 2);
                            v_binderInfo_133_ = lean_ctor_get_uint8(
                                v_e_111_,
                                (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                            );
                            lean_inc_ref(v_binderType_131_);
                            lean_inc_ref(v_f_x3f_110_);
                            v_d_134_ = l_Lean_Expr_replaceNoCache(v_f_x3f_110_, v_binderType_131_);
                            lean_inc_ref(v_body_132_);
                            v_b_135_ = l_Lean_Expr_replaceNoCache(v_f_x3f_110_, v_body_132_);
                            v___x_141_ = lean_ptr_addr(v_binderType_131_);
                            v___x_142_ = lean_ptr_addr(v_d_134_);
                            v___x_143_ = lean_usize_dec_eq(v___x_141_, v___x_142_);
                            if v___x_143_ == 0 {
                                v___y_137_ = v___x_143_;
                                state = 2;
                                continue;
                            } else {
                                v___x_144_ = lean_ptr_addr(v_body_132_);
                                v___x_145_ = lean_ptr_addr(v_b_135_);
                                v___x_146_ = lean_usize_dec_eq(v___x_144_, v___x_145_);
                                v___y_137_ = v___x_146_;
                                state = 2;
                                continue;
                            }
                        }
                        10 => {
                            v_data_147_ = lean_ctor_get(v_e_111_, 0);
                            v_expr_148_ = lean_ctor_get(v_e_111_, 1);
                            lean_inc_ref(v_expr_148_);
                            v_b_149_ = l_Lean_Expr_replaceNoCache(v_f_x3f_110_, v_expr_148_);
                            v___x_150_ = lean_ptr_addr(v_expr_148_);
                            v___x_151_ = lean_ptr_addr(v_b_149_);
                            v___x_152_ = lean_usize_dec_eq(v___x_150_, v___x_151_);
                            if v___x_152_ == 0 {
                                lean_inc(v_data_147_);
                                lean_dec_ref_known(v_e_111_, 2);
                                v___x_153_ = l_Lean_Expr_mdata___override(v_data_147_, v_b_149_);
                                return v___x_153_;
                            } else {
                                lean_dec_ref(v_b_149_);
                                return v_e_111_;
                            }
                        }
                        8 => {
                            v_declName_154_ = lean_ctor_get(v_e_111_, 0);
                            v_type_155_ = lean_ctor_get(v_e_111_, 1);
                            v_value_156_ = lean_ctor_get(v_e_111_, 2);
                            v_body_157_ = lean_ctor_get(v_e_111_, 3);
                            v_nondep_158_ = lean_ctor_get_uint8(
                                v_e_111_,
                                (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
                            );
                            lean_inc_ref(v_type_155_);
                            lean_inc_ref_n(v_f_x3f_110_, 2);
                            v_t_159_ = l_Lean_Expr_replaceNoCache(v_f_x3f_110_, v_type_155_);
                            lean_inc_ref(v_value_156_);
                            v_v_160_ = l_Lean_Expr_replaceNoCache(v_f_x3f_110_, v_value_156_);
                            lean_inc_ref(v_body_157_);
                            v_b_161_ = l_Lean_Expr_replaceNoCache(v_f_x3f_110_, v_body_157_);
                            v___x_169_ = lean_ptr_addr(v_type_155_);
                            v___x_170_ = lean_ptr_addr(v_t_159_);
                            v___x_171_ = lean_usize_dec_eq(v___x_169_, v___x_170_);
                            if v___x_171_ == 0 {
                                v___y_163_ = v___x_171_;
                                state = 3;
                                continue;
                            } else {
                                v___x_172_ = lean_ptr_addr(v_value_156_);
                                v___x_173_ = lean_ptr_addr(v_v_160_);
                                v___x_174_ = lean_usize_dec_eq(v___x_172_, v___x_173_);
                                v___y_163_ = v___x_174_;
                                state = 3;
                                continue;
                            }
                        }
                        5 => {
                            v_fn_175_ = lean_ctor_get(v_e_111_, 0);
                            v_arg_176_ = lean_ctor_get(v_e_111_, 1);
                            lean_inc_ref(v_fn_175_);
                            lean_inc_ref(v_f_x3f_110_);
                            v_f_177_ = l_Lean_Expr_replaceNoCache(v_f_x3f_110_, v_fn_175_);
                            lean_inc_ref(v_arg_176_);
                            v_a_178_ = l_Lean_Expr_replaceNoCache(v_f_x3f_110_, v_arg_176_);
                            v___x_182_ = lean_ptr_addr(v_fn_175_);
                            v___x_183_ = lean_ptr_addr(v_f_177_);
                            v___x_184_ = lean_usize_dec_eq(v___x_182_, v___x_183_);
                            if v___x_184_ == 0 {
                                v___y_180_ = v___x_184_;
                                state = 4;
                                continue;
                            } else {
                                v___x_185_ = lean_ptr_addr(v_arg_176_);
                                v___x_186_ = lean_ptr_addr(v_a_178_);
                                v___x_187_ = lean_usize_dec_eq(v___x_185_, v___x_186_);
                                v___y_180_ = v___x_187_;
                                state = 4;
                                continue;
                            }
                        }
                        11 => {
                            v_typeName_188_ = lean_ctor_get(v_e_111_, 0);
                            v_idx_189_ = lean_ctor_get(v_e_111_, 1);
                            v_struct_190_ = lean_ctor_get(v_e_111_, 2);
                            lean_inc_ref(v_struct_190_);
                            v_b_191_ = l_Lean_Expr_replaceNoCache(v_f_x3f_110_, v_struct_190_);
                            v___x_192_ = lean_ptr_addr(v_struct_190_);
                            v___x_193_ = lean_ptr_addr(v_b_191_);
                            v___x_194_ = lean_usize_dec_eq(v___x_192_, v___x_193_);
                            if v___x_194_ == 0 {
                                lean_inc(v_idx_189_);
                                lean_inc(v_typeName_188_);
                                lean_dec_ref_known(v_e_111_, 3);
                                v___x_195_ = l_Lean_Expr_proj___override(
                                    v_typeName_188_,
                                    v_idx_189_,
                                    v_b_191_,
                                );
                                return v___x_195_;
                            } else {
                                lean_dec_ref(v_b_191_);
                                return v_e_111_;
                            }
                        }
                        _ => {
                            lean_dec_ref(v_f_x3f_110_);
                            return v_e_111_;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_111_);
                    lean_dec_ref(v_f_x3f_110_);
                    v_val_196_ = lean_ctor_get(v___x_112_, 0);
                    lean_inc(v_val_196_);
                    lean_dec_ref_known(v___x_112_, 1);
                    return v_val_196_;
                }
            }
            1 => {
                if v___y_120_ == 0 {
                    lean_inc(v_binderName_113_);
                    lean_dec_ref_known(v_e_111_, 3);
                    v___x_121_ = l_Lean_Expr_forallE___override(
                        v_binderName_113_,
                        v_d_117_,
                        v_b_118_,
                        v_binderInfo_116_,
                    );
                    return v___x_121_;
                } else {
                    v___x_122_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_116_, v_binderInfo_116_);
                    if v___x_122_ == 0 {
                        lean_inc(v_binderName_113_);
                        lean_dec_ref_known(v_e_111_, 3);
                        v___x_123_ = l_Lean_Expr_forallE___override(
                            v_binderName_113_,
                            v_d_117_,
                            v_b_118_,
                            v_binderInfo_116_,
                        );
                        return v___x_123_;
                    } else {
                        lean_dec_ref(v_b_118_);
                        lean_dec_ref(v_d_117_);
                        return v_e_111_;
                    }
                }
            }
            2 => {
                if v___y_137_ == 0 {
                    lean_inc(v_binderName_130_);
                    lean_dec_ref_known(v_e_111_, 3);
                    v___x_138_ = l_Lean_Expr_lam___override(
                        v_binderName_130_,
                        v_d_134_,
                        v_b_135_,
                        v_binderInfo_133_,
                    );
                    return v___x_138_;
                } else {
                    v___x_139_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_133_, v_binderInfo_133_);
                    if v___x_139_ == 0 {
                        lean_inc(v_binderName_130_);
                        lean_dec_ref_known(v_e_111_, 3);
                        v___x_140_ = l_Lean_Expr_lam___override(
                            v_binderName_130_,
                            v_d_134_,
                            v_b_135_,
                            v_binderInfo_133_,
                        );
                        return v___x_140_;
                    } else {
                        lean_dec_ref(v_b_135_);
                        lean_dec_ref(v_d_134_);
                        return v_e_111_;
                    }
                }
            }
            3 => {
                if v___y_163_ == 0 {
                    lean_inc(v_declName_154_);
                    lean_dec_ref_known(v_e_111_, 4);
                    v___x_164_ = l_Lean_Expr_letE___override(
                        v_declName_154_,
                        v_t_159_,
                        v_v_160_,
                        v_b_161_,
                        v_nondep_158_,
                    );
                    return v___x_164_;
                } else {
                    v___x_165_ = lean_ptr_addr(v_body_157_);
                    v___x_166_ = lean_ptr_addr(v_b_161_);
                    v___x_167_ = lean_usize_dec_eq(v___x_165_, v___x_166_);
                    if v___x_167_ == 0 {
                        lean_inc(v_declName_154_);
                        lean_dec_ref_known(v_e_111_, 4);
                        v___x_168_ = l_Lean_Expr_letE___override(
                            v_declName_154_,
                            v_t_159_,
                            v_v_160_,
                            v_b_161_,
                            v_nondep_158_,
                        );
                        return v___x_168_;
                    } else {
                        lean_dec_ref(v_b_161_);
                        lean_dec_ref(v_v_160_);
                        lean_dec_ref(v_t_159_);
                        return v_e_111_;
                    }
                }
            }
            4 => {
                if v___y_180_ == 0 {
                    lean_dec_ref_known(v_e_111_, 2);
                    v___x_181_ = l_Lean_Expr_app___override(v_f_177_, v_a_178_);
                    return v___x_181_;
                } else {
                    lean_dec_ref(v_a_178_);
                    lean_dec_ref(v_f_177_);
                    return v_e_111_;
                }
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_ReplaceExpr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_PtrSet(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_ReplaceExpr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_ReplaceExpr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Util_PtrSet(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ReplaceExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Util_ReplaceExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Util_ReplaceExpr(builtin);
}

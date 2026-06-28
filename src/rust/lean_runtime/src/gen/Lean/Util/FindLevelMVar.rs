// Lean compiler output
// Module: Lean.Util.FindLevelMVar
// Imports: Lean.Expr
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Expr_hasLevelMVar, runtime_initialize_Lean_Expr,
};
use crate::r#gen::Lean::Level::l_Lean_Level_hasMVar;
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_of_nat, lean_usize_sub};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_mk, lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_FindLevelMVar_main___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_FindLevelMVar_main___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_FindLevelMVar_main___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_FindLevelMVar_main___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lean_FindLevelMVar_mainLevel(
    mut v_p_118_: *mut LeanObject,
    mut v_x_119_: *mut LeanObject,
    mut v_a_120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_l_u2081_122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_u2082_123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_135_: u8 = 0;
    let mut v___x_136_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_119_) {
                1 => {
                    v_a_127_ = lean_ctor_get(v_x_119_, 0);
                    lean_inc(v_a_127_);
                    lean_dec_ref_known(v_x_119_, 1);
                    v___x_128_ = l_Lean_FindLevelMVar_visitLevel(v_p_118_, v_a_127_, v_a_120_);
                    return v___x_128_;
                }
                2 => {
                    v_a_129_ = lean_ctor_get(v_x_119_, 0);
                    lean_inc(v_a_129_);
                    v_a_130_ = lean_ctor_get(v_x_119_, 1);
                    lean_inc(v_a_130_);
                    lean_dec_ref_known(v_x_119_, 2);
                    v_l_u2081_122_ = v_a_129_;
                    v_l_u2082_123_ = v_a_130_;
                    v___y_124_ = v_a_120_;
                    state = 1;
                    continue;
                }
                3 => {
                    v_a_131_ = lean_ctor_get(v_x_119_, 0);
                    lean_inc(v_a_131_);
                    v_a_132_ = lean_ctor_get(v_x_119_, 1);
                    lean_inc(v_a_132_);
                    lean_dec_ref_known(v_x_119_, 2);
                    v_l_u2081_122_ = v_a_131_;
                    v_l_u2082_123_ = v_a_132_;
                    v___y_124_ = v_a_120_;
                    state = 1;
                    continue;
                }
                5 => {
                    v_a_133_ = lean_ctor_get(v_x_119_, 0);
                    lean_inc_n(v_a_133_, 2);
                    lean_dec_ref_known(v_x_119_, 1);
                    v___x_134_ = lean_apply_1(v_p_118_, v_a_133_);
                    v___x_135_ = (lean_unbox(v___x_134_) as u8);
                    if v___x_135_ == 0 {
                        lean_dec(v_a_133_);
                        lean_inc(v_a_120_);
                        return v_a_120_;
                    } else {
                        v___x_136_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_136_, 0, v_a_133_);
                        return v___x_136_;
                    }
                }
                _ => {
                    lean_dec(v_x_119_);
                    lean_dec_ref(v_p_118_);
                    lean_inc(v_a_120_);
                    return v_a_120_;
                }
            },
            1 => {
                lean_inc_ref(v_p_118_);
                v___x_125_ = l_Lean_FindLevelMVar_visitLevel(v_p_118_, v_l_u2082_123_, v___y_124_);
                v___x_126_ = l_Lean_FindLevelMVar_visitLevel(v_p_118_, v_l_u2081_122_, v___x_125_);
                lean_dec(v___x_125_);
                return v___x_126_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_FindLevelMVar_visitLevel(
    mut v_p_137_: *mut LeanObject,
    mut v_l_138_: *mut LeanObject,
    mut v_s_139_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_s_139_) == 0 {
        let mut v___x_140_: u8 = 0;
        v___x_140_ = l_Lean_Level_hasMVar(v_l_138_);
        if v___x_140_ == 0 {
            lean_dec(v_l_138_);
            lean_dec_ref(v_p_137_);
            return v_s_139_;
        } else {
            let mut v___x_141_: *mut LeanObject = core::ptr::null_mut();
            v___x_141_ = l_Lean_FindLevelMVar_mainLevel(v_p_137_, v_l_138_, v_s_139_);
            return v___x_141_;
        }
    } else {
        lean_dec(v_l_138_);
        lean_dec_ref(v_p_137_);
        lean_inc_ref(v_s_139_);
        return v_s_139_;
    }
}
pub unsafe fn l_Lean_FindLevelMVar_visitLevel___boxed(
    mut v_p_142_: *mut LeanObject,
    mut v_l_143_: *mut LeanObject,
    mut v_s_144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_145_: *mut LeanObject = core::ptr::null_mut();
    v_res_145_ = l_Lean_FindLevelMVar_visitLevel(v_p_142_, v_l_143_, v_s_144_);
    lean_dec(v_s_144_);
    return v_res_145_;
}
pub unsafe fn l_Lean_FindLevelMVar_mainLevel___boxed(
    mut v_p_146_: *mut LeanObject,
    mut v_x_147_: *mut LeanObject,
    mut v_a_148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_149_: *mut LeanObject = core::ptr::null_mut();
    v_res_149_ = l_Lean_FindLevelMVar_mainLevel(v_p_146_, v_x_147_, v_a_148_);
    lean_dec(v_a_148_);
    return v_res_149_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1___lam__0(
    mut v_b_150_: *mut LeanObject,
    mut v_p_151_: *mut LeanObject,
    mut v___x_152_: *mut LeanObject,
    mut v___y_153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_155_: *mut LeanObject = core::ptr::null_mut();
    v___x_154_ = lean_apply_1(v_b_150_, v___y_153_);
    v___x_155_ = l_Lean_FindLevelMVar_visitLevel(v_p_151_, v___x_152_, v___x_154_);
    lean_dec(v___x_154_);
    return v___x_155_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1(
    mut v_p_156_: *mut LeanObject,
    mut v_as_157_: *mut LeanObject,
    mut v_i_158_: usize,
    mut v_stop_159_: usize,
    mut v_b_160_: *mut LeanObject,
    mut v___y_161_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_162_: u8 = 0;
    let mut v___x_163_: usize = 0;
    let mut v___x_164_: usize = 0;
    let mut v___x_165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_168_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_162_ = lean_usize_dec_eq(v_i_158_, v_stop_159_);
                if v___x_162_ == 0 {
                    v___x_163_ = 1usize;
                    v___x_164_ = lean_usize_sub(v_i_158_, v___x_163_);
                    v___x_165_ = lean_array_uget_borrowed(v_as_157_, v___x_164_);
                    lean_inc(v___x_165_);
                    lean_inc_ref(v_p_156_);
                    v___f_166_ = lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1___lam__0 as *mut core::ffi::c_void, 4, 3);
                    lean_closure_set(v___f_166_, 0, v_b_160_);
                    lean_closure_set(v___f_166_, 1, v_p_156_);
                    lean_closure_set(v___f_166_, 2, v___x_165_);
                    v_i_158_ = v___x_164_;
                    v_b_160_ = v___f_166_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_p_156_);
                    v___x_168_ = lean_apply_1(v_b_160_, v___y_161_);
                    return v___x_168_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1___boxed(
    mut v_p_169_: *mut LeanObject,
    mut v_as_170_: *mut LeanObject,
    mut v_i_171_: *mut LeanObject,
    mut v_stop_172_: *mut LeanObject,
    mut v_b_173_: *mut LeanObject,
    mut v___y_174_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_175_: usize = 0;
    let mut v_stop_boxed_176_: usize = 0;
    let mut v_res_177_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_175_ = lean_unbox_usize(v_i_171_);
    lean_dec(v_i_171_);
    v_stop_boxed_176_ = lean_unbox_usize(v_stop_172_);
    lean_dec(v_stop_172_);
    v_res_177_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1(v_p_169_, v_as_170_, v_i_boxed_175_, v_stop_boxed_176_, v_b_173_, v___y_174_);
    lean_dec_ref(v_as_170_);
    return v_res_177_;
}
pub unsafe fn l_List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1(
    mut v_p_178_: *mut LeanObject,
    mut v_init_179_: *mut LeanObject,
    mut v_l_180_: *mut LeanObject,
    mut v___y_181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_185_: u8 = 0;
    v___x_182_ = lean_array_mk(v_l_180_);
    v___x_183_ = lean_array_get_size(v___x_182_);
    v___x_184_ = lean_unsigned_to_nat(0);
    v___x_185_ = lean_nat_dec_lt(v___x_184_, v___x_183_);
    if v___x_185_ == 0 {
        let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v___x_182_);
        lean_dec_ref(v_p_178_);
        v___x_186_ = lean_apply_1(v_init_179_, v___y_181_);
        return v___x_186_;
    } else {
        let mut v___x_187_: usize = 0;
        let mut v___x_188_: usize = 0;
        let mut v___x_189_: *mut LeanObject = core::ptr::null_mut();
        v___x_187_ = lean_usize_of_nat(v___x_183_);
        v___x_188_ = 0usize;
        v___x_189_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1(v_p_178_, v___x_182_, v___x_187_, v___x_188_, v_init_179_, v___y_181_);
        lean_dec_ref(v___x_182_);
        return v___x_189_;
    }
}
pub unsafe fn l_Lean_FindLevelMVar_main___lam__0(
    mut v___y_190_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v___y_190_);
    return v___y_190_;
}
pub unsafe fn l_Lean_FindLevelMVar_main___lam__0___boxed(
    mut v___y_191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_192_: *mut LeanObject = core::ptr::null_mut();
    v_res_192_ = l_Lean_FindLevelMVar_main___lam__0(v___y_191_);
    lean_dec(v___y_191_);
    return v_res_192_;
}
pub unsafe fn l_Lean_FindLevelMVar_main(
    mut v_p_194_: *mut LeanObject,
    mut v_x_195_: *mut LeanObject,
    mut v_a_196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_d_198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_x_195_) {
                3 => {
                    v_u_203_ = lean_ctor_get(v_x_195_, 0);
                    lean_inc(v_u_203_);
                    lean_dec_ref_known(v_x_195_, 1);
                    v___x_204_ = l_Lean_FindLevelMVar_visitLevel(v_p_194_, v_u_203_, v_a_196_);
                    lean_dec(v_a_196_);
                    return v___x_204_;
                }
                4 => {
                    v_us_205_ = lean_ctor_get(v_x_195_, 1);
                    lean_inc(v_us_205_);
                    lean_dec_ref_known(v_x_195_, 2);
                    v___f_206_ = l_Lean_FindLevelMVar_main___closed__0;
                    v___x_207_ = l_List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1(
                        v_p_194_, v___f_206_, v_us_205_, v_a_196_,
                    );
                    return v___x_207_;
                }
                7 => {
                    v_binderType_208_ = lean_ctor_get(v_x_195_, 1);
                    lean_inc_ref(v_binderType_208_);
                    v_body_209_ = lean_ctor_get(v_x_195_, 2);
                    lean_inc_ref(v_body_209_);
                    lean_dec_ref_known(v_x_195_, 3);
                    v_d_198_ = v_binderType_208_;
                    v_b_199_ = v_body_209_;
                    v___y_200_ = v_a_196_;
                    state = 1;
                    continue;
                }
                6 => {
                    v_binderType_210_ = lean_ctor_get(v_x_195_, 1);
                    lean_inc_ref(v_binderType_210_);
                    v_body_211_ = lean_ctor_get(v_x_195_, 2);
                    lean_inc_ref(v_body_211_);
                    lean_dec_ref_known(v_x_195_, 3);
                    v_d_198_ = v_binderType_210_;
                    v_b_199_ = v_body_211_;
                    v___y_200_ = v_a_196_;
                    state = 1;
                    continue;
                }
                8 => {
                    v_type_212_ = lean_ctor_get(v_x_195_, 1);
                    lean_inc_ref(v_type_212_);
                    v_value_213_ = lean_ctor_get(v_x_195_, 2);
                    lean_inc_ref(v_value_213_);
                    v_body_214_ = lean_ctor_get(v_x_195_, 3);
                    lean_inc_ref(v_body_214_);
                    lean_dec_ref_known(v_x_195_, 4);
                    lean_inc_ref_n(v_p_194_, 2);
                    v___x_215_ = l_Lean_FindLevelMVar_visit(v_p_194_, v_type_212_, v_a_196_);
                    v___x_216_ = l_Lean_FindLevelMVar_visit(v_p_194_, v_value_213_, v___x_215_);
                    v___x_217_ = l_Lean_FindLevelMVar_visit(v_p_194_, v_body_214_, v___x_216_);
                    return v___x_217_;
                }
                5 => {
                    v_fn_218_ = lean_ctor_get(v_x_195_, 0);
                    lean_inc_ref(v_fn_218_);
                    v_arg_219_ = lean_ctor_get(v_x_195_, 1);
                    lean_inc_ref(v_arg_219_);
                    lean_dec_ref_known(v_x_195_, 2);
                    lean_inc_ref(v_p_194_);
                    v___x_220_ = l_Lean_FindLevelMVar_visit(v_p_194_, v_fn_218_, v_a_196_);
                    v___x_221_ = l_Lean_FindLevelMVar_visit(v_p_194_, v_arg_219_, v___x_220_);
                    return v___x_221_;
                }
                10 => {
                    v_expr_222_ = lean_ctor_get(v_x_195_, 1);
                    lean_inc_ref(v_expr_222_);
                    lean_dec_ref_known(v_x_195_, 2);
                    v___x_223_ = l_Lean_FindLevelMVar_visit(v_p_194_, v_expr_222_, v_a_196_);
                    return v___x_223_;
                }
                11 => {
                    v_struct_224_ = lean_ctor_get(v_x_195_, 2);
                    lean_inc_ref(v_struct_224_);
                    lean_dec_ref_known(v_x_195_, 3);
                    v___x_225_ = l_Lean_FindLevelMVar_visit(v_p_194_, v_struct_224_, v_a_196_);
                    return v___x_225_;
                }
                _ => {
                    lean_dec_ref(v_x_195_);
                    lean_dec_ref(v_p_194_);
                    return v_a_196_;
                }
            },
            1 => {
                lean_inc_ref(v_p_194_);
                v___x_201_ = l_Lean_FindLevelMVar_visit(v_p_194_, v_d_198_, v___y_200_);
                v___x_202_ = l_Lean_FindLevelMVar_visit(v_p_194_, v_b_199_, v___x_201_);
                return v___x_202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_FindLevelMVar_visit(
    mut v_p_226_: *mut LeanObject,
    mut v_e_227_: *mut LeanObject,
    mut v_s_228_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_s_228_) == 0 {
        let mut v___x_229_: u8 = 0;
        v___x_229_ = l_Lean_Expr_hasLevelMVar(v_e_227_);
        if v___x_229_ == 0 {
            lean_dec_ref(v_e_227_);
            lean_dec_ref(v_p_226_);
            return v_s_228_;
        } else {
            let mut v___x_230_: *mut LeanObject = core::ptr::null_mut();
            v___x_230_ = l_Lean_FindLevelMVar_main(v_p_226_, v_e_227_, v_s_228_);
            return v___x_230_;
        }
    } else {
        lean_dec_ref(v_e_227_);
        lean_dec_ref(v_p_226_);
        return v_s_228_;
    }
}
pub unsafe fn l_Lean_Expr_findLevelMVar_x3f(
    mut v_e_231_: *mut LeanObject,
    mut v_p_232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut LeanObject = core::ptr::null_mut();
    v___x_233_ = lean_box(0);
    v___x_234_ = l_Lean_FindLevelMVar_main(v_p_232_, v_e_231_, v___x_233_);
    return v___x_234_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_FindLevelMVar(builtin: u8) -> *mut LeanObject {
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
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_FindLevelMVar(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_FindLevelMVar(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lean_Util_FindLevelMVar(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Util_FindLevelMVar(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Util_FindLevelMVar(builtin);
}

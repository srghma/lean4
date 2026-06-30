// Lean compiler output
// Module: Lean.Util.FindLevelMVar
// Imports: Lean.Expr
use crate::ffi::{
    lean_array_get_size, lean_array_mk, lean_array_uget_borrowed, lean_nat_dec_lt,
    lean_usize_dec_eq, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Lean::Expr::{
    initialize_Lean_Expr, l_Lean_Expr_hasLevelMVar, runtime_initialize_Lean_Expr,
};
use crate::r#gen::Lean::Level::l_Lean_Level_hasMVar;
pub static l_Lean_FindLevelMVar_main___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_FindLevelMVar_main___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_FindLevelMVar_main___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_FindLevelMVar_main___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_FindLevelMVar_mainLevel(
    mut v_p_118_: *mut leanh::LeanObject,
    mut v_x_119_: *mut leanh::LeanObject,
    mut v_a_120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_l_u2081_122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_u2082_123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_135_: u8 = 0;
    let mut v___x_136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_119_) {
                1 => {
                    v_a_127_ = leanh::lean_ctor_get(v_x_119_, 0);
                    leanh::lean_inc(v_a_127_);
                    leanh::lean_dec_ref_known(v_x_119_, 1);
                    v___x_128_ = l_Lean_FindLevelMVar_visitLevel(v_p_118_, v_a_127_, v_a_120_);
                    return v___x_128_;
                }
                2 => {
                    v_a_129_ = leanh::lean_ctor_get(v_x_119_, 0);
                    leanh::lean_inc(v_a_129_);
                    v_a_130_ = leanh::lean_ctor_get(v_x_119_, 1);
                    leanh::lean_inc(v_a_130_);
                    leanh::lean_dec_ref_known(v_x_119_, 2);
                    v_l_u2081_122_ = v_a_129_;
                    v_l_u2082_123_ = v_a_130_;
                    v___y_124_ = v_a_120_;
                    state = 1;
                    continue;
                }
                3 => {
                    v_a_131_ = leanh::lean_ctor_get(v_x_119_, 0);
                    leanh::lean_inc(v_a_131_);
                    v_a_132_ = leanh::lean_ctor_get(v_x_119_, 1);
                    leanh::lean_inc(v_a_132_);
                    leanh::lean_dec_ref_known(v_x_119_, 2);
                    v_l_u2081_122_ = v_a_131_;
                    v_l_u2082_123_ = v_a_132_;
                    v___y_124_ = v_a_120_;
                    state = 1;
                    continue;
                }
                5 => {
                    v_a_133_ = leanh::lean_ctor_get(v_x_119_, 0);
                    leanh::lean_inc_n(v_a_133_, 2);
                    leanh::lean_dec_ref_known(v_x_119_, 1);
                    v___x_134_ = leanh::lean_apply_1(v_p_118_, v_a_133_);
                    v___x_135_ = (leanh::lean_unbox(v___x_134_) as u8);
                    if v___x_135_ == 0 {
                        leanh::lean_dec(v_a_133_);
                        leanh::lean_inc(v_a_120_);
                        return v_a_120_;
                    } else {
                        v___x_136_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_136_, 0, v_a_133_);
                        return v___x_136_;
                    }
                }
                _ => {
                    leanh::lean_dec(v_x_119_);
                    leanh::lean_dec_ref(v_p_118_);
                    leanh::lean_inc(v_a_120_);
                    return v_a_120_;
                }
            },
            1 => {
                leanh::lean_inc_ref(v_p_118_);
                v___x_125_ = l_Lean_FindLevelMVar_visitLevel(v_p_118_, v_l_u2082_123_, v___y_124_);
                v___x_126_ = l_Lean_FindLevelMVar_visitLevel(v_p_118_, v_l_u2081_122_, v___x_125_);
                leanh::lean_dec(v___x_125_);
                return v___x_126_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_FindLevelMVar_visitLevel(
    mut v_p_137_: *mut leanh::LeanObject,
    mut v_l_138_: *mut leanh::LeanObject,
    mut v_s_139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_s_139_) == 0 {
        let mut v___x_140_: u8 = 0;
        v___x_140_ = l_Lean_Level_hasMVar(v_l_138_);
        if v___x_140_ == 0 {
            leanh::lean_dec(v_l_138_);
            leanh::lean_dec_ref(v_p_137_);
            return v_s_139_;
        } else {
            let mut v___x_141_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_141_ = l_Lean_FindLevelMVar_mainLevel(v_p_137_, v_l_138_, v_s_139_);
            return v___x_141_;
        }
    } else {
        leanh::lean_dec(v_l_138_);
        leanh::lean_dec_ref(v_p_137_);
        leanh::lean_inc_ref(v_s_139_);
        return v_s_139_;
    }
}
pub unsafe fn l_Lean_FindLevelMVar_visitLevel___boxed(
    mut v_p_142_: *mut leanh::LeanObject,
    mut v_l_143_: *mut leanh::LeanObject,
    mut v_s_144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_145_ = l_Lean_FindLevelMVar_visitLevel(v_p_142_, v_l_143_, v_s_144_);
    leanh::lean_dec(v_s_144_);
    return v_res_145_;
}
pub unsafe fn l_Lean_FindLevelMVar_mainLevel___boxed(
    mut v_p_146_: *mut leanh::LeanObject,
    mut v_x_147_: *mut leanh::LeanObject,
    mut v_a_148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_149_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_149_ = l_Lean_FindLevelMVar_mainLevel(v_p_146_, v_x_147_, v_a_148_);
    leanh::lean_dec(v_a_148_);
    return v_res_149_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1___lam__0(
    mut v_b_150_: *mut leanh::LeanObject,
    mut v_p_151_: *mut leanh::LeanObject,
    mut v___x_152_: *mut leanh::LeanObject,
    mut v___y_153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_154_ = leanh::lean_apply_1(v_b_150_, v___y_153_);
    v___x_155_ = l_Lean_FindLevelMVar_visitLevel(v_p_151_, v___x_152_, v___x_154_);
    leanh::lean_dec(v___x_154_);
    return v___x_155_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1(
    mut v_p_156_: *mut leanh::LeanObject,
    mut v_as_157_: *mut leanh::LeanObject,
    mut v_i_158_: usize,
    mut v_stop_159_: usize,
    mut v_b_160_: *mut leanh::LeanObject,
    mut v___y_161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_162_: u8 = 0;
    let mut v___x_163_: usize = 0;
    let mut v___x_164_: usize = 0;
    let mut v___x_165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_162_ = lean_usize_dec_eq(v_i_158_, v_stop_159_);
                if v___x_162_ == 0 {
                    v___x_163_ = 1usize;
                    v___x_164_ = lean_usize_sub(v_i_158_, v___x_163_);
                    v___x_165_ = lean_array_uget_borrowed(v_as_157_, v___x_164_);
                    leanh::lean_inc(v___x_165_);
                    leanh::lean_inc_ref(v_p_156_);
                    v___f_166_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1___lam__0 as *mut core::ffi::c_void, 4, 3);
                    leanh::lean_closure_set(v___f_166_, 0, v_b_160_);
                    leanh::lean_closure_set(v___f_166_, 1, v_p_156_);
                    leanh::lean_closure_set(v___f_166_, 2, v___x_165_);
                    v_i_158_ = v___x_164_;
                    v_b_160_ = v___f_166_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_p_156_);
                    v___x_168_ = leanh::lean_apply_1(v_b_160_, v___y_161_);
                    return v___x_168_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1___boxed(
    mut v_p_169_: *mut leanh::LeanObject,
    mut v_as_170_: *mut leanh::LeanObject,
    mut v_i_171_: *mut leanh::LeanObject,
    mut v_stop_172_: *mut leanh::LeanObject,
    mut v_b_173_: *mut leanh::LeanObject,
    mut v___y_174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_175_: usize = 0;
    let mut v_stop_boxed_176_: usize = 0;
    let mut v_res_177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_175_ = leanh::lean_unbox_usize(v_i_171_);
    leanh::lean_dec(v_i_171_);
    v_stop_boxed_176_ = leanh::lean_unbox_usize(v_stop_172_);
    leanh::lean_dec(v_stop_172_);
    v_res_177_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1(v_p_169_, v_as_170_, v_i_boxed_175_, v_stop_boxed_176_, v_b_173_, v___y_174_);
    leanh::lean_dec_ref(v_as_170_);
    return v_res_177_;
}
pub unsafe fn l_List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1(
    mut v_p_178_: *mut leanh::LeanObject,
    mut v_init_179_: *mut leanh::LeanObject,
    mut v_l_180_: *mut leanh::LeanObject,
    mut v___y_181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_185_: u8 = 0;
    v___x_182_ = lean_array_mk(v_l_180_);
    v___x_183_ = lean_array_get_size(v___x_182_);
    v___x_184_ = leanh::lean_unsigned_to_nat(0);
    v___x_185_ = lean_nat_dec_lt(v___x_184_, v___x_183_);
    if v___x_185_ == 0 {
        let mut v___x_186_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___x_182_);
        leanh::lean_dec_ref(v_p_178_);
        v___x_186_ = leanh::lean_apply_1(v_init_179_, v___y_181_);
        return v___x_186_;
    } else {
        let mut v___x_187_: usize = 0;
        let mut v___x_188_: usize = 0;
        let mut v___x_189_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_187_ = lean_usize_of_nat(v___x_183_);
        v___x_188_ = 0usize;
        v___x_189_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1_spec__1(v_p_178_, v___x_182_, v___x_187_, v___x_188_, v_init_179_, v___y_181_);
        leanh::lean_dec_ref(v___x_182_);
        return v___x_189_;
    }
}
pub unsafe fn l_Lean_FindLevelMVar_main___lam__0(
    mut v___y_190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v___y_190_);
    return v___y_190_;
}
pub unsafe fn l_Lean_FindLevelMVar_main___lam__0___boxed(
    mut v___y_191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_192_ = l_Lean_FindLevelMVar_main___lam__0(v___y_191_);
    leanh::lean_dec(v___y_191_);
    return v_res_192_;
}
pub unsafe fn l_Lean_FindLevelMVar_main(
    mut v_p_194_: *mut leanh::LeanObject,
    mut v_x_195_: *mut leanh::LeanObject,
    mut v_a_196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_d_198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_195_) {
                3 => {
                    v_u_203_ = leanh::lean_ctor_get(v_x_195_, 0);
                    leanh::lean_inc(v_u_203_);
                    leanh::lean_dec_ref_known(v_x_195_, 1);
                    v___x_204_ = l_Lean_FindLevelMVar_visitLevel(v_p_194_, v_u_203_, v_a_196_);
                    leanh::lean_dec(v_a_196_);
                    return v___x_204_;
                }
                4 => {
                    v_us_205_ = leanh::lean_ctor_get(v_x_195_, 1);
                    leanh::lean_inc(v_us_205_);
                    leanh::lean_dec_ref_known(v_x_195_, 2);
                    v___f_206_ = l_Lean_FindLevelMVar_main___closed__0;
                    v___x_207_ = l_List_foldrTR___at___00Lean_FindLevelMVar_main_spec__1(
                        v_p_194_, v___f_206_, v_us_205_, v_a_196_,
                    );
                    return v___x_207_;
                }
                7 => {
                    v_binderType_208_ = leanh::lean_ctor_get(v_x_195_, 1);
                    leanh::lean_inc_ref(v_binderType_208_);
                    v_body_209_ = leanh::lean_ctor_get(v_x_195_, 2);
                    leanh::lean_inc_ref(v_body_209_);
                    leanh::lean_dec_ref_known(v_x_195_, 3);
                    v_d_198_ = v_binderType_208_;
                    v_b_199_ = v_body_209_;
                    v___y_200_ = v_a_196_;
                    state = 1;
                    continue;
                }
                6 => {
                    v_binderType_210_ = leanh::lean_ctor_get(v_x_195_, 1);
                    leanh::lean_inc_ref(v_binderType_210_);
                    v_body_211_ = leanh::lean_ctor_get(v_x_195_, 2);
                    leanh::lean_inc_ref(v_body_211_);
                    leanh::lean_dec_ref_known(v_x_195_, 3);
                    v_d_198_ = v_binderType_210_;
                    v_b_199_ = v_body_211_;
                    v___y_200_ = v_a_196_;
                    state = 1;
                    continue;
                }
                8 => {
                    v_type_212_ = leanh::lean_ctor_get(v_x_195_, 1);
                    leanh::lean_inc_ref(v_type_212_);
                    v_value_213_ = leanh::lean_ctor_get(v_x_195_, 2);
                    leanh::lean_inc_ref(v_value_213_);
                    v_body_214_ = leanh::lean_ctor_get(v_x_195_, 3);
                    leanh::lean_inc_ref(v_body_214_);
                    leanh::lean_dec_ref_known(v_x_195_, 4);
                    leanh::lean_inc_ref_n(v_p_194_, 2);
                    v___x_215_ = l_Lean_FindLevelMVar_visit(v_p_194_, v_type_212_, v_a_196_);
                    v___x_216_ = l_Lean_FindLevelMVar_visit(v_p_194_, v_value_213_, v___x_215_);
                    v___x_217_ = l_Lean_FindLevelMVar_visit(v_p_194_, v_body_214_, v___x_216_);
                    return v___x_217_;
                }
                5 => {
                    v_fn_218_ = leanh::lean_ctor_get(v_x_195_, 0);
                    leanh::lean_inc_ref(v_fn_218_);
                    v_arg_219_ = leanh::lean_ctor_get(v_x_195_, 1);
                    leanh::lean_inc_ref(v_arg_219_);
                    leanh::lean_dec_ref_known(v_x_195_, 2);
                    leanh::lean_inc_ref(v_p_194_);
                    v___x_220_ = l_Lean_FindLevelMVar_visit(v_p_194_, v_fn_218_, v_a_196_);
                    v___x_221_ = l_Lean_FindLevelMVar_visit(v_p_194_, v_arg_219_, v___x_220_);
                    return v___x_221_;
                }
                10 => {
                    v_expr_222_ = leanh::lean_ctor_get(v_x_195_, 1);
                    leanh::lean_inc_ref(v_expr_222_);
                    leanh::lean_dec_ref_known(v_x_195_, 2);
                    v___x_223_ = l_Lean_FindLevelMVar_visit(v_p_194_, v_expr_222_, v_a_196_);
                    return v___x_223_;
                }
                11 => {
                    v_struct_224_ = leanh::lean_ctor_get(v_x_195_, 2);
                    leanh::lean_inc_ref(v_struct_224_);
                    leanh::lean_dec_ref_known(v_x_195_, 3);
                    v___x_225_ = l_Lean_FindLevelMVar_visit(v_p_194_, v_struct_224_, v_a_196_);
                    return v___x_225_;
                }
                _ => {
                    leanh::lean_dec_ref(v_x_195_);
                    leanh::lean_dec_ref(v_p_194_);
                    return v_a_196_;
                }
            },
            1 => {
                leanh::lean_inc_ref(v_p_194_);
                v___x_201_ = l_Lean_FindLevelMVar_visit(v_p_194_, v_d_198_, v___y_200_);
                v___x_202_ = l_Lean_FindLevelMVar_visit(v_p_194_, v_b_199_, v___x_201_);
                return v___x_202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_FindLevelMVar_visit(
    mut v_p_226_: *mut leanh::LeanObject,
    mut v_e_227_: *mut leanh::LeanObject,
    mut v_s_228_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_s_228_) == 0 {
        let mut v___x_229_: u8 = 0;
        v___x_229_ = l_Lean_Expr_hasLevelMVar(v_e_227_);
        if v___x_229_ == 0 {
            leanh::lean_dec_ref(v_e_227_);
            leanh::lean_dec_ref(v_p_226_);
            return v_s_228_;
        } else {
            let mut v___x_230_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_230_ = l_Lean_FindLevelMVar_main(v_p_226_, v_e_227_, v_s_228_);
            return v___x_230_;
        }
    } else {
        leanh::lean_dec_ref(v_e_227_);
        leanh::lean_dec_ref(v_p_226_);
        return v_s_228_;
    }
}
pub unsafe fn l_Lean_Expr_findLevelMVar_x3f(
    mut v_e_231_: *mut leanh::LeanObject,
    mut v_p_232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_233_ = leanh::lean_box(0);
    v___x_234_ = l_Lean_FindLevelMVar_main(v_p_232_, v_e_231_, v___x_233_);
    return v___x_234_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_FindLevelMVar(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_FindLevelMVar(
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
pub unsafe fn initialize_Lean_Util_FindLevelMVar(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_FindLevelMVar(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_FindLevelMVar(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Util_FindLevelMVar(builtin);
}
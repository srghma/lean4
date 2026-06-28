// Lean compiler output
// Module: Init.Data.RArray
// Imports: Init.GetElem Init.PropLemmas
use crate::r#gen::Init::GetElem::{initialize_Init_GetElem, runtime_initialize_Init_GetElem};
use crate::r#gen::Init::PropLemmas::{
    initialize_Init_PropLemmas, runtime_initialize_Init_PropLemmas,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_add, lean_nat_dec_lt};
pub static l_Lean_instGetElemRArrayNatTrue___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_instGetElemRArrayNatTrue___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instGetElemRArrayNatTrue___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instGetElemRArrayNatTrue___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_RArray_ctorIdx___redArg(
    mut v_x_138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_138_) == 0 {
        let mut v___x_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_139_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_139_;
    } else {
        let mut v___x_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_140_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_140_;
    }
}
pub unsafe fn l_Lean_RArray_ctorIdx___redArg___boxed(
    mut v_x_141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_142_ = l_Lean_RArray_ctorIdx___redArg(v_x_141_);
    crate::leanh::lean_dec_ref(v_x_141_);
    return v_res_142_;
}
pub unsafe fn l_Lean_RArray_ctorIdx(
    mut v_00_u03b1_143_: *mut crate::leanh::LeanObject,
    mut v_x_144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_145_ = l_Lean_RArray_ctorIdx___redArg(v_x_144_);
    return v___x_145_;
}
pub unsafe fn l_Lean_RArray_ctorIdx___boxed(
    mut v_00_u03b1_146_: *mut crate::leanh::LeanObject,
    mut v_x_147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_148_ = l_Lean_RArray_ctorIdx(v_00_u03b1_146_, v_x_147_);
    crate::leanh::lean_dec_ref(v_x_147_);
    return v_res_148_;
}
pub unsafe fn l_Lean_RArray_ctorElim___redArg(
    mut v_t_149_: *mut crate::leanh::LeanObject,
    mut v_k_150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_149_) == 0 {
        let mut v_a_151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_151_ = crate::leanh::lean_ctor_get(v_t_149_, 0);
        crate::leanh::lean_inc(v_a_151_);
        crate::leanh::lean_dec_ref_known(v_t_149_, 1);
        v___x_152_ = crate::leanh::lean_apply_1(v_k_150_, v_a_151_);
        return v___x_152_;
    } else {
        let mut v_a_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_153_ = crate::leanh::lean_ctor_get(v_t_149_, 0);
        crate::leanh::lean_inc(v_a_153_);
        v_a_154_ = crate::leanh::lean_ctor_get(v_t_149_, 1);
        crate::leanh::lean_inc_ref(v_a_154_);
        v_a_155_ = crate::leanh::lean_ctor_get(v_t_149_, 2);
        crate::leanh::lean_inc_ref(v_a_155_);
        crate::leanh::lean_dec_ref_known(v_t_149_, 3);
        v___x_156_ = crate::leanh::lean_apply_3(v_k_150_, v_a_153_, v_a_154_, v_a_155_);
        return v___x_156_;
    }
}
pub unsafe fn l_Lean_RArray_ctorElim(
    mut v_00_u03b1_157_: *mut crate::leanh::LeanObject,
    mut v_motive_158_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_159_: *mut crate::leanh::LeanObject,
    mut v_t_160_: *mut crate::leanh::LeanObject,
    mut v_h_161_: *mut crate::leanh::LeanObject,
    mut v_k_162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_163_ = l_Lean_RArray_ctorElim___redArg(v_t_160_, v_k_162_);
    return v___x_163_;
}
pub unsafe fn l_Lean_RArray_ctorElim___boxed(
    mut v_00_u03b1_164_: *mut crate::leanh::LeanObject,
    mut v_motive_165_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_166_: *mut crate::leanh::LeanObject,
    mut v_t_167_: *mut crate::leanh::LeanObject,
    mut v_h_168_: *mut crate::leanh::LeanObject,
    mut v_k_169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_170_ = l_Lean_RArray_ctorElim(
        v_00_u03b1_164_,
        v_motive_165_,
        v_ctorIdx_166_,
        v_t_167_,
        v_h_168_,
        v_k_169_,
    );
    crate::leanh::lean_dec(v_ctorIdx_166_);
    return v_res_170_;
}
pub unsafe fn l_Lean_RArray_leaf_elim___redArg(
    mut v_t_171_: *mut crate::leanh::LeanObject,
    mut v_leaf_172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_173_ = l_Lean_RArray_ctorElim___redArg(v_t_171_, v_leaf_172_);
    return v___x_173_;
}
pub unsafe fn l_Lean_RArray_leaf_elim(
    mut v_00_u03b1_174_: *mut crate::leanh::LeanObject,
    mut v_motive_175_: *mut crate::leanh::LeanObject,
    mut v_t_176_: *mut crate::leanh::LeanObject,
    mut v_h_177_: *mut crate::leanh::LeanObject,
    mut v_leaf_178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_179_ = l_Lean_RArray_ctorElim___redArg(v_t_176_, v_leaf_178_);
    return v___x_179_;
}
pub unsafe fn l_Lean_RArray_branch_elim___redArg(
    mut v_t_180_: *mut crate::leanh::LeanObject,
    mut v_branch_181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_182_ = l_Lean_RArray_ctorElim___redArg(v_t_180_, v_branch_181_);
    return v___x_182_;
}
pub unsafe fn l_Lean_RArray_branch_elim(
    mut v_00_u03b1_183_: *mut crate::leanh::LeanObject,
    mut v_motive_184_: *mut crate::leanh::LeanObject,
    mut v_t_185_: *mut crate::leanh::LeanObject,
    mut v_h_186_: *mut crate::leanh::LeanObject,
    mut v_branch_187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_188_ = l_Lean_RArray_ctorElim___redArg(v_t_185_, v_branch_187_);
    return v___x_188_;
}
pub unsafe fn l___private_Init_Data_RArray_0__Lean_RArray_get__eq__def_match__1_splitter___redArg(
    mut v_a_189_: *mut crate::leanh::LeanObject,
    mut v_h__1_190_: *mut crate::leanh::LeanObject,
    mut v_h__2_191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_189_) == 0 {
        let mut v_a_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_191_);
        v_a_192_ = crate::leanh::lean_ctor_get(v_a_189_, 0);
        crate::leanh::lean_inc(v_a_192_);
        crate::leanh::lean_dec_ref_known(v_a_189_, 1);
        v___x_193_ = crate::leanh::lean_apply_1(v_h__1_190_, v_a_192_);
        return v___x_193_;
    } else {
        let mut v_a_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_190_);
        v_a_194_ = crate::leanh::lean_ctor_get(v_a_189_, 0);
        crate::leanh::lean_inc(v_a_194_);
        v_a_195_ = crate::leanh::lean_ctor_get(v_a_189_, 1);
        crate::leanh::lean_inc_ref(v_a_195_);
        v_a_196_ = crate::leanh::lean_ctor_get(v_a_189_, 2);
        crate::leanh::lean_inc_ref(v_a_196_);
        crate::leanh::lean_dec_ref_known(v_a_189_, 3);
        v___x_197_ = crate::leanh::lean_apply_3(v_h__2_191_, v_a_194_, v_a_195_, v_a_196_);
        return v___x_197_;
    }
}
pub unsafe fn l___private_Init_Data_RArray_0__Lean_RArray_get__eq__def_match__1_splitter(
    mut v_00_u03b1_198_: *mut crate::leanh::LeanObject,
    mut v_motive_199_: *mut crate::leanh::LeanObject,
    mut v_a_200_: *mut crate::leanh::LeanObject,
    mut v_h__1_201_: *mut crate::leanh::LeanObject,
    mut v_h__2_202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_200_) == 0 {
        let mut v_a_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_202_);
        v_a_203_ = crate::leanh::lean_ctor_get(v_a_200_, 0);
        crate::leanh::lean_inc(v_a_203_);
        crate::leanh::lean_dec_ref_known(v_a_200_, 1);
        v___x_204_ = crate::leanh::lean_apply_1(v_h__1_201_, v_a_203_);
        return v___x_204_;
    } else {
        let mut v_a_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_201_);
        v_a_205_ = crate::leanh::lean_ctor_get(v_a_200_, 0);
        crate::leanh::lean_inc(v_a_205_);
        v_a_206_ = crate::leanh::lean_ctor_get(v_a_200_, 1);
        crate::leanh::lean_inc_ref(v_a_206_);
        v_a_207_ = crate::leanh::lean_ctor_get(v_a_200_, 2);
        crate::leanh::lean_inc_ref(v_a_207_);
        crate::leanh::lean_dec_ref_known(v_a_200_, 3);
        v___x_208_ = crate::leanh::lean_apply_3(v_h__2_202_, v_a_205_, v_a_206_, v_a_207_);
        return v___x_208_;
    }
}
pub unsafe fn l_Lean_RArray_getImpl___redArg(
    mut v_a_209_: *mut crate::leanh::LeanObject,
    mut v_n_210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_215_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_209_) == 0 {
                    v_a_211_ = crate::leanh::lean_ctor_get(v_a_209_, 0);
                    crate::leanh::lean_inc(v_a_211_);
                    return v_a_211_;
                } else {
                    v_a_212_ = crate::leanh::lean_ctor_get(v_a_209_, 0);
                    v_a_213_ = crate::leanh::lean_ctor_get(v_a_209_, 1);
                    v_a_214_ = crate::leanh::lean_ctor_get(v_a_209_, 2);
                    v___x_215_ = lean_nat_dec_lt(v_n_210_, v_a_212_);
                    if v___x_215_ == 0 {
                        v_a_209_ = v_a_214_;
                        state = 0;
                        continue;
                    } else {
                        v_a_209_ = v_a_213_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_RArray_getImpl___redArg___boxed(
    mut v_a_218_: *mut crate::leanh::LeanObject,
    mut v_n_219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_220_ = l_Lean_RArray_getImpl___redArg(v_a_218_, v_n_219_);
    crate::leanh::lean_dec(v_n_219_);
    crate::leanh::lean_dec_ref(v_a_218_);
    return v_res_220_;
}
pub unsafe fn l_Lean_RArray_getImpl(
    mut v_00_u03b1_221_: *mut crate::leanh::LeanObject,
    mut v_a_222_: *mut crate::leanh::LeanObject,
    mut v_n_223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_224_ = l_Lean_RArray_getImpl___redArg(v_a_222_, v_n_223_);
    return v___x_224_;
}
pub unsafe fn l_Lean_RArray_getImpl___boxed(
    mut v_00_u03b1_225_: *mut crate::leanh::LeanObject,
    mut v_a_226_: *mut crate::leanh::LeanObject,
    mut v_n_227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_228_ = l_Lean_RArray_getImpl(v_00_u03b1_225_, v_a_226_, v_n_227_);
    crate::leanh::lean_dec(v_n_227_);
    crate::leanh::lean_dec_ref(v_a_226_);
    return v_res_228_;
}
pub unsafe fn l___private_Init_Data_RArray_0__Lean_RArray_getImpl_match__1_splitter___redArg(
    mut v_a_229_: *mut crate::leanh::LeanObject,
    mut v_h__1_230_: *mut crate::leanh::LeanObject,
    mut v_h__2_231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_229_) == 0 {
        let mut v_a_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_231_);
        v_a_232_ = crate::leanh::lean_ctor_get(v_a_229_, 0);
        crate::leanh::lean_inc(v_a_232_);
        crate::leanh::lean_dec_ref_known(v_a_229_, 1);
        v___x_233_ = crate::leanh::lean_apply_1(v_h__1_230_, v_a_232_);
        return v___x_233_;
    } else {
        let mut v_a_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_230_);
        v_a_234_ = crate::leanh::lean_ctor_get(v_a_229_, 0);
        crate::leanh::lean_inc(v_a_234_);
        v_a_235_ = crate::leanh::lean_ctor_get(v_a_229_, 1);
        crate::leanh::lean_inc_ref(v_a_235_);
        v_a_236_ = crate::leanh::lean_ctor_get(v_a_229_, 2);
        crate::leanh::lean_inc_ref(v_a_236_);
        crate::leanh::lean_dec_ref_known(v_a_229_, 3);
        v___x_237_ = crate::leanh::lean_apply_3(v_h__2_231_, v_a_234_, v_a_235_, v_a_236_);
        return v___x_237_;
    }
}
pub unsafe fn l___private_Init_Data_RArray_0__Lean_RArray_getImpl_match__1_splitter(
    mut v_00_u03b1_238_: *mut crate::leanh::LeanObject,
    mut v_motive_239_: *mut crate::leanh::LeanObject,
    mut v_a_240_: *mut crate::leanh::LeanObject,
    mut v_h__1_241_: *mut crate::leanh::LeanObject,
    mut v_h__2_242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_a_240_) == 0 {
        let mut v_a_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_242_);
        v_a_243_ = crate::leanh::lean_ctor_get(v_a_240_, 0);
        crate::leanh::lean_inc(v_a_243_);
        crate::leanh::lean_dec_ref_known(v_a_240_, 1);
        v___x_244_ = crate::leanh::lean_apply_1(v_h__1_241_, v_a_243_);
        return v___x_244_;
    } else {
        let mut v_a_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_241_);
        v_a_245_ = crate::leanh::lean_ctor_get(v_a_240_, 0);
        crate::leanh::lean_inc(v_a_245_);
        v_a_246_ = crate::leanh::lean_ctor_get(v_a_240_, 1);
        crate::leanh::lean_inc_ref(v_a_246_);
        v_a_247_ = crate::leanh::lean_ctor_get(v_a_240_, 2);
        crate::leanh::lean_inc_ref(v_a_247_);
        crate::leanh::lean_dec_ref_known(v_a_240_, 3);
        v___x_248_ = crate::leanh::lean_apply_3(v_h__2_242_, v_a_245_, v_a_246_, v_a_247_);
        return v___x_248_;
    }
}
pub unsafe fn l_Lean_instGetElemRArrayNatTrue___lam__0(
    mut v_a_249_: *mut crate::leanh::LeanObject,
    mut v_n_250_: *mut crate::leanh::LeanObject,
    mut v_x_251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_252_ = l_Lean_RArray_getImpl___redArg(v_a_249_, v_n_250_);
    return v___x_252_;
}
pub unsafe fn l_Lean_instGetElemRArrayNatTrue___lam__0___boxed(
    mut v_a_253_: *mut crate::leanh::LeanObject,
    mut v_n_254_: *mut crate::leanh::LeanObject,
    mut v_x_255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_256_ = l_Lean_instGetElemRArrayNatTrue___lam__0(v_a_253_, v_n_254_, v_x_255_);
    crate::leanh::lean_dec(v_n_254_);
    crate::leanh::lean_dec_ref(v_a_253_);
    return v_res_256_;
}
pub unsafe fn l_Lean_instGetElemRArrayNatTrue(
    mut v_00_u03b1_258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_259_ = l_Lean_instGetElemRArrayNatTrue___closed__0;
    return v___f_259_;
}
pub unsafe fn l_Lean_RArray_size___redArg(
    mut v_x_260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_260_) == 0 {
        let mut v___x_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_261_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_261_;
    } else {
        let mut v_a_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_262_ = crate::leanh::lean_ctor_get(v_x_260_, 1);
        v_a_263_ = crate::leanh::lean_ctor_get(v_x_260_, 2);
        v___x_264_ = l_Lean_RArray_size___redArg(v_a_262_);
        v___x_265_ = l_Lean_RArray_size___redArg(v_a_263_);
        v___x_266_ = lean_nat_add(v___x_264_, v___x_265_);
        crate::leanh::lean_dec(v___x_265_);
        crate::leanh::lean_dec(v___x_264_);
        return v___x_266_;
    }
}
pub unsafe fn l_Lean_RArray_size___redArg___boxed(
    mut v_x_267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_268_ = l_Lean_RArray_size___redArg(v_x_267_);
    crate::leanh::lean_dec_ref(v_x_267_);
    return v_res_268_;
}
pub unsafe fn l_Lean_RArray_size(
    mut v_00_u03b1_269_: *mut crate::leanh::LeanObject,
    mut v_x_270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_271_ = l_Lean_RArray_size___redArg(v_x_270_);
    return v___x_271_;
}
pub unsafe fn l_Lean_RArray_size___boxed(
    mut v_00_u03b1_272_: *mut crate::leanh::LeanObject,
    mut v_x_273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_274_ = l_Lean_RArray_size(v_00_u03b1_272_, v_x_273_);
    crate::leanh::lean_dec_ref(v_x_273_);
    return v_res_274_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_RArray(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_GetElem(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_PropLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_RArray(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_RArray(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_GetElem(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_PropLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_RArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_RArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_RArray(builtin);
}

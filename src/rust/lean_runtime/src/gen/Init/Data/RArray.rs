// Lean compiler output
// Module: Init.Data.RArray
// Imports: Init.GetElem Init.PropLemmas
use crate::r#gen::Init::GetElem::{initialize_Init_GetElem, runtime_initialize_Init_GetElem};
use crate::r#gen::Init::PropLemmas::{
    initialize_Init_PropLemmas, runtime_initialize_Init_PropLemmas,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_add, lean_nat_dec_lt};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_3, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lean_instGetElemRArrayNatTrue___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_instGetElemRArrayNatTrue___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instGetElemRArrayNatTrue___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_instGetElemRArrayNatTrue___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lean_RArray_ctorIdx___redArg(mut v_x_138_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_138_) == 0 {
        let mut v___x_139_: *mut LeanObject = core::ptr::null_mut();
        v___x_139_ = lean_unsigned_to_nat(0);
        return v___x_139_;
    } else {
        let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
        v___x_140_ = lean_unsigned_to_nat(1);
        return v___x_140_;
    }
}
pub unsafe fn l_Lean_RArray_ctorIdx___redArg___boxed(
    mut v_x_141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_142_: *mut LeanObject = core::ptr::null_mut();
    v_res_142_ = l_Lean_RArray_ctorIdx___redArg(v_x_141_);
    lean_dec_ref(v_x_141_);
    return v_res_142_;
}
pub unsafe fn l_Lean_RArray_ctorIdx(
    mut v_00_u03b1_143_: *mut LeanObject,
    mut v_x_144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_145_: *mut LeanObject = core::ptr::null_mut();
    v___x_145_ = l_Lean_RArray_ctorIdx___redArg(v_x_144_);
    return v___x_145_;
}
pub unsafe fn l_Lean_RArray_ctorIdx___boxed(
    mut v_00_u03b1_146_: *mut LeanObject,
    mut v_x_147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_148_: *mut LeanObject = core::ptr::null_mut();
    v_res_148_ = l_Lean_RArray_ctorIdx(v_00_u03b1_146_, v_x_147_);
    lean_dec_ref(v_x_147_);
    return v_res_148_;
}
pub unsafe fn l_Lean_RArray_ctorElim___redArg(
    mut v_t_149_: *mut LeanObject,
    mut v_k_150_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_149_) == 0 {
        let mut v_a_151_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_152_: *mut LeanObject = core::ptr::null_mut();
        v_a_151_ = lean_ctor_get(v_t_149_, 0);
        lean_inc(v_a_151_);
        lean_dec_ref_known(v_t_149_, 1);
        v___x_152_ = lean_apply_1(v_k_150_, v_a_151_);
        return v___x_152_;
    } else {
        let mut v_a_153_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_154_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_155_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_156_: *mut LeanObject = core::ptr::null_mut();
        v_a_153_ = lean_ctor_get(v_t_149_, 0);
        lean_inc(v_a_153_);
        v_a_154_ = lean_ctor_get(v_t_149_, 1);
        lean_inc_ref(v_a_154_);
        v_a_155_ = lean_ctor_get(v_t_149_, 2);
        lean_inc_ref(v_a_155_);
        lean_dec_ref_known(v_t_149_, 3);
        v___x_156_ = lean_apply_3(v_k_150_, v_a_153_, v_a_154_, v_a_155_);
        return v___x_156_;
    }
}
pub unsafe fn l_Lean_RArray_ctorElim(
    mut v_00_u03b1_157_: *mut LeanObject,
    mut v_motive_158_: *mut LeanObject,
    mut v_ctorIdx_159_: *mut LeanObject,
    mut v_t_160_: *mut LeanObject,
    mut v_h_161_: *mut LeanObject,
    mut v_k_162_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_163_: *mut LeanObject = core::ptr::null_mut();
    v___x_163_ = l_Lean_RArray_ctorElim___redArg(v_t_160_, v_k_162_);
    return v___x_163_;
}
pub unsafe fn l_Lean_RArray_ctorElim___boxed(
    mut v_00_u03b1_164_: *mut LeanObject,
    mut v_motive_165_: *mut LeanObject,
    mut v_ctorIdx_166_: *mut LeanObject,
    mut v_t_167_: *mut LeanObject,
    mut v_h_168_: *mut LeanObject,
    mut v_k_169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_170_: *mut LeanObject = core::ptr::null_mut();
    v_res_170_ = l_Lean_RArray_ctorElim(
        v_00_u03b1_164_,
        v_motive_165_,
        v_ctorIdx_166_,
        v_t_167_,
        v_h_168_,
        v_k_169_,
    );
    lean_dec(v_ctorIdx_166_);
    return v_res_170_;
}
pub unsafe fn l_Lean_RArray_leaf_elim___redArg(
    mut v_t_171_: *mut LeanObject,
    mut v_leaf_172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
    v___x_173_ = l_Lean_RArray_ctorElim___redArg(v_t_171_, v_leaf_172_);
    return v___x_173_;
}
pub unsafe fn l_Lean_RArray_leaf_elim(
    mut v_00_u03b1_174_: *mut LeanObject,
    mut v_motive_175_: *mut LeanObject,
    mut v_t_176_: *mut LeanObject,
    mut v_h_177_: *mut LeanObject,
    mut v_leaf_178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_179_: *mut LeanObject = core::ptr::null_mut();
    v___x_179_ = l_Lean_RArray_ctorElim___redArg(v_t_176_, v_leaf_178_);
    return v___x_179_;
}
pub unsafe fn l_Lean_RArray_branch_elim___redArg(
    mut v_t_180_: *mut LeanObject,
    mut v_branch_181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_182_: *mut LeanObject = core::ptr::null_mut();
    v___x_182_ = l_Lean_RArray_ctorElim___redArg(v_t_180_, v_branch_181_);
    return v___x_182_;
}
pub unsafe fn l_Lean_RArray_branch_elim(
    mut v_00_u03b1_183_: *mut LeanObject,
    mut v_motive_184_: *mut LeanObject,
    mut v_t_185_: *mut LeanObject,
    mut v_h_186_: *mut LeanObject,
    mut v_branch_187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_188_: *mut LeanObject = core::ptr::null_mut();
    v___x_188_ = l_Lean_RArray_ctorElim___redArg(v_t_185_, v_branch_187_);
    return v___x_188_;
}
pub unsafe fn l___private_Init_Data_RArray_0__Lean_RArray_get__eq__def_match__1_splitter___redArg(
    mut v_a_189_: *mut LeanObject,
    mut v_h__1_190_: *mut LeanObject,
    mut v_h__2_191_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_189_) == 0 {
        let mut v_a_192_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_193_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_191_);
        v_a_192_ = lean_ctor_get(v_a_189_, 0);
        lean_inc(v_a_192_);
        lean_dec_ref_known(v_a_189_, 1);
        v___x_193_ = lean_apply_1(v_h__1_190_, v_a_192_);
        return v___x_193_;
    } else {
        let mut v_a_194_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_195_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_196_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_197_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_190_);
        v_a_194_ = lean_ctor_get(v_a_189_, 0);
        lean_inc(v_a_194_);
        v_a_195_ = lean_ctor_get(v_a_189_, 1);
        lean_inc_ref(v_a_195_);
        v_a_196_ = lean_ctor_get(v_a_189_, 2);
        lean_inc_ref(v_a_196_);
        lean_dec_ref_known(v_a_189_, 3);
        v___x_197_ = lean_apply_3(v_h__2_191_, v_a_194_, v_a_195_, v_a_196_);
        return v___x_197_;
    }
}
pub unsafe fn l___private_Init_Data_RArray_0__Lean_RArray_get__eq__def_match__1_splitter(
    mut v_00_u03b1_198_: *mut LeanObject,
    mut v_motive_199_: *mut LeanObject,
    mut v_a_200_: *mut LeanObject,
    mut v_h__1_201_: *mut LeanObject,
    mut v_h__2_202_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_200_) == 0 {
        let mut v_a_203_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_204_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_202_);
        v_a_203_ = lean_ctor_get(v_a_200_, 0);
        lean_inc(v_a_203_);
        lean_dec_ref_known(v_a_200_, 1);
        v___x_204_ = lean_apply_1(v_h__1_201_, v_a_203_);
        return v___x_204_;
    } else {
        let mut v_a_205_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_206_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_207_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_208_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_201_);
        v_a_205_ = lean_ctor_get(v_a_200_, 0);
        lean_inc(v_a_205_);
        v_a_206_ = lean_ctor_get(v_a_200_, 1);
        lean_inc_ref(v_a_206_);
        v_a_207_ = lean_ctor_get(v_a_200_, 2);
        lean_inc_ref(v_a_207_);
        lean_dec_ref_known(v_a_200_, 3);
        v___x_208_ = lean_apply_3(v_h__2_202_, v_a_205_, v_a_206_, v_a_207_);
        return v___x_208_;
    }
}
pub unsafe fn l_Lean_RArray_getImpl___redArg(
    mut v_a_209_: *mut LeanObject,
    mut v_n_210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_215_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_209_) == 0 {
                    v_a_211_ = lean_ctor_get(v_a_209_, 0);
                    lean_inc(v_a_211_);
                    return v_a_211_;
                } else {
                    v_a_212_ = lean_ctor_get(v_a_209_, 0);
                    v_a_213_ = lean_ctor_get(v_a_209_, 1);
                    v_a_214_ = lean_ctor_get(v_a_209_, 2);
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
    mut v_a_218_: *mut LeanObject,
    mut v_n_219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_220_: *mut LeanObject = core::ptr::null_mut();
    v_res_220_ = l_Lean_RArray_getImpl___redArg(v_a_218_, v_n_219_);
    lean_dec(v_n_219_);
    lean_dec_ref(v_a_218_);
    return v_res_220_;
}
pub unsafe fn l_Lean_RArray_getImpl(
    mut v_00_u03b1_221_: *mut LeanObject,
    mut v_a_222_: *mut LeanObject,
    mut v_n_223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_224_: *mut LeanObject = core::ptr::null_mut();
    v___x_224_ = l_Lean_RArray_getImpl___redArg(v_a_222_, v_n_223_);
    return v___x_224_;
}
pub unsafe fn l_Lean_RArray_getImpl___boxed(
    mut v_00_u03b1_225_: *mut LeanObject,
    mut v_a_226_: *mut LeanObject,
    mut v_n_227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_228_: *mut LeanObject = core::ptr::null_mut();
    v_res_228_ = l_Lean_RArray_getImpl(v_00_u03b1_225_, v_a_226_, v_n_227_);
    lean_dec(v_n_227_);
    lean_dec_ref(v_a_226_);
    return v_res_228_;
}
pub unsafe fn l___private_Init_Data_RArray_0__Lean_RArray_getImpl_match__1_splitter___redArg(
    mut v_a_229_: *mut LeanObject,
    mut v_h__1_230_: *mut LeanObject,
    mut v_h__2_231_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_229_) == 0 {
        let mut v_a_232_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_233_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_231_);
        v_a_232_ = lean_ctor_get(v_a_229_, 0);
        lean_inc(v_a_232_);
        lean_dec_ref_known(v_a_229_, 1);
        v___x_233_ = lean_apply_1(v_h__1_230_, v_a_232_);
        return v___x_233_;
    } else {
        let mut v_a_234_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_235_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_236_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_237_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_230_);
        v_a_234_ = lean_ctor_get(v_a_229_, 0);
        lean_inc(v_a_234_);
        v_a_235_ = lean_ctor_get(v_a_229_, 1);
        lean_inc_ref(v_a_235_);
        v_a_236_ = lean_ctor_get(v_a_229_, 2);
        lean_inc_ref(v_a_236_);
        lean_dec_ref_known(v_a_229_, 3);
        v___x_237_ = lean_apply_3(v_h__2_231_, v_a_234_, v_a_235_, v_a_236_);
        return v___x_237_;
    }
}
pub unsafe fn l___private_Init_Data_RArray_0__Lean_RArray_getImpl_match__1_splitter(
    mut v_00_u03b1_238_: *mut LeanObject,
    mut v_motive_239_: *mut LeanObject,
    mut v_a_240_: *mut LeanObject,
    mut v_h__1_241_: *mut LeanObject,
    mut v_h__2_242_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_a_240_) == 0 {
        let mut v_a_243_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_244_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_242_);
        v_a_243_ = lean_ctor_get(v_a_240_, 0);
        lean_inc(v_a_243_);
        lean_dec_ref_known(v_a_240_, 1);
        v___x_244_ = lean_apply_1(v_h__1_241_, v_a_243_);
        return v___x_244_;
    } else {
        let mut v_a_245_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_246_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_247_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_241_);
        v_a_245_ = lean_ctor_get(v_a_240_, 0);
        lean_inc(v_a_245_);
        v_a_246_ = lean_ctor_get(v_a_240_, 1);
        lean_inc_ref(v_a_246_);
        v_a_247_ = lean_ctor_get(v_a_240_, 2);
        lean_inc_ref(v_a_247_);
        lean_dec_ref_known(v_a_240_, 3);
        v___x_248_ = lean_apply_3(v_h__2_242_, v_a_245_, v_a_246_, v_a_247_);
        return v___x_248_;
    }
}
pub unsafe fn l_Lean_instGetElemRArrayNatTrue___lam__0(
    mut v_a_249_: *mut LeanObject,
    mut v_n_250_: *mut LeanObject,
    mut v_x_251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_252_: *mut LeanObject = core::ptr::null_mut();
    v___x_252_ = l_Lean_RArray_getImpl___redArg(v_a_249_, v_n_250_);
    return v___x_252_;
}
pub unsafe fn l_Lean_instGetElemRArrayNatTrue___lam__0___boxed(
    mut v_a_253_: *mut LeanObject,
    mut v_n_254_: *mut LeanObject,
    mut v_x_255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_256_: *mut LeanObject = core::ptr::null_mut();
    v_res_256_ = l_Lean_instGetElemRArrayNatTrue___lam__0(v_a_253_, v_n_254_, v_x_255_);
    lean_dec(v_n_254_);
    lean_dec_ref(v_a_253_);
    return v_res_256_;
}
pub unsafe fn l_Lean_instGetElemRArrayNatTrue(
    mut v_00_u03b1_258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_259_: *mut LeanObject = core::ptr::null_mut();
    v___f_259_ = l_Lean_instGetElemRArrayNatTrue___closed__0;
    return v___f_259_;
}
pub unsafe fn l_Lean_RArray_size___redArg(mut v_x_260_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_260_) == 0 {
        let mut v___x_261_: *mut LeanObject = core::ptr::null_mut();
        v___x_261_ = lean_unsigned_to_nat(1);
        return v___x_261_;
    } else {
        let mut v_a_262_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_263_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
        v_a_262_ = lean_ctor_get(v_x_260_, 1);
        v_a_263_ = lean_ctor_get(v_x_260_, 2);
        v___x_264_ = l_Lean_RArray_size___redArg(v_a_262_);
        v___x_265_ = l_Lean_RArray_size___redArg(v_a_263_);
        v___x_266_ = lean_nat_add(v___x_264_, v___x_265_);
        lean_dec(v___x_265_);
        lean_dec(v___x_264_);
        return v___x_266_;
    }
}
pub unsafe fn l_Lean_RArray_size___redArg___boxed(
    mut v_x_267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_268_: *mut LeanObject = core::ptr::null_mut();
    v_res_268_ = l_Lean_RArray_size___redArg(v_x_267_);
    lean_dec_ref(v_x_267_);
    return v_res_268_;
}
pub unsafe fn l_Lean_RArray_size(
    mut v_00_u03b1_269_: *mut LeanObject,
    mut v_x_270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
    v___x_271_ = l_Lean_RArray_size___redArg(v_x_270_);
    return v___x_271_;
}
pub unsafe fn l_Lean_RArray_size___boxed(
    mut v_00_u03b1_272_: *mut LeanObject,
    mut v_x_273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_274_: *mut LeanObject = core::ptr::null_mut();
    v_res_274_ = l_Lean_RArray_size(v_00_u03b1_272_, v_x_273_);
    lean_dec_ref(v_x_273_);
    return v_res_274_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_RArray(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_GetElem(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_PropLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_RArray(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_RArray(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_GetElem(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_PropLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_RArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_RArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_RArray(builtin);
}

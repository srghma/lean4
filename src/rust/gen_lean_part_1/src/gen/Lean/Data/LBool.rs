// Lean compiler output
// Module: Lean.Data.LBool
// Imports: Init.Data.ToString.Basic
use crate::ffi::lean_nat_dec_eq;
use crate::r#gen::Init::Data::ToString::Basic::{
    initialize_Init_Data_ToString_Basic, runtime_initialize_Init_Data_ToString_Basic,
};
pub static mut l_Lean_instInhabitedLBool_default: u8 = 0;
pub static mut l_Lean_instInhabitedLBool: u8 = 0;
pub static l_Lean_instBEqLBool___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqLBool_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqLBool___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqLBool___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Lean_instBEqLBool: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqLBool___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_LBool_toString___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_LBool_toString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LBool_toString___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_LBool_toString___closed__1_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lean_LBool_toString___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LBool_toString___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_LBool_toString___closed__2_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [117, 110, 100, 101, 102, 0],
    };
static mut l_Lean_LBool_toString___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LBool_toString___closed__2_value) as *mut leanh::LeanObject;
pub static l_Lean_LBool_instToString___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_LBool_toString___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_LBool_instToString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LBool_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_LBool_instToString: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_LBool_instToString___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_LBool_ctorIdx(mut v_x_140_: u8) -> *mut leanh::LeanObject {
    match v_x_140_ {
        0 => {
            let mut v___x_141_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_141_ = leanh::lean_unsigned_to_nat(0);
            return v___x_141_;
        }
        1 => {
            let mut v___x_142_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_142_ = leanh::lean_unsigned_to_nat(1);
            return v___x_142_;
        }
        _ => {
            let mut v___x_143_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_143_ = leanh::lean_unsigned_to_nat(2);
            return v___x_143_;
        }
    }
}
pub unsafe fn l_Lean_LBool_ctorIdx___boxed(
    mut v_x_144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_145_: u8 = 0;
    let mut v_res_146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_145_ = (leanh::lean_unbox(v_x_144_) as u8);
    v_res_146_ = l_Lean_LBool_ctorIdx(v_x_boxed_145_);
    return v_res_146_;
}
pub unsafe fn l_Lean_LBool_toCtorIdx(mut v_x_147_: u8) -> *mut leanh::LeanObject {
    let mut v___x_148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_148_ = l_Lean_LBool_ctorIdx(v_x_147_);
    return v___x_148_;
}
pub unsafe fn l_Lean_LBool_toCtorIdx___boxed(
    mut v_x_149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_150_: u8 = 0;
    let mut v_res_151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_150_ = (leanh::lean_unbox(v_x_149_) as u8);
    v_res_151_ = l_Lean_LBool_toCtorIdx(v_x_4__boxed_150_);
    return v_res_151_;
}
pub unsafe fn l_Lean_LBool_ctorElim___redArg(
    mut v_k_152_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_152_);
    return v_k_152_;
}
pub unsafe fn l_Lean_LBool_ctorElim___redArg___boxed(
    mut v_k_153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_154_ = l_Lean_LBool_ctorElim___redArg(v_k_153_);
    leanh::lean_dec(v_k_153_);
    return v_res_154_;
}
pub unsafe fn l_Lean_LBool_ctorElim(
    mut v_motive_155_: *mut leanh::LeanObject,
    mut v_ctorIdx_156_: *mut leanh::LeanObject,
    mut v_t_157_: u8,
    mut v_h_158_: *mut leanh::LeanObject,
    mut v_k_159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_159_);
    return v_k_159_;
}
pub unsafe fn l_Lean_LBool_ctorElim___boxed(
    mut v_motive_160_: *mut leanh::LeanObject,
    mut v_ctorIdx_161_: *mut leanh::LeanObject,
    mut v_t_162_: *mut leanh::LeanObject,
    mut v_h_163_: *mut leanh::LeanObject,
    mut v_k_164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_165_: u8 = 0;
    let mut v_res_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_165_ = (leanh::lean_unbox(v_t_162_) as u8);
    v_res_166_ = l_Lean_LBool_ctorElim(
        v_motive_160_,
        v_ctorIdx_161_,
        v_t_boxed_165_,
        v_h_163_,
        v_k_164_,
    );
    leanh::lean_dec(v_k_164_);
    leanh::lean_dec(v_ctorIdx_161_);
    return v_res_166_;
}
pub unsafe fn l_Lean_LBool_false_elim___redArg(
    mut v_false_167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_false_167_);
    return v_false_167_;
}
pub unsafe fn l_Lean_LBool_false_elim___redArg___boxed(
    mut v_false_168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_169_ = l_Lean_LBool_false_elim___redArg(v_false_168_);
    leanh::lean_dec(v_false_168_);
    return v_res_169_;
}
pub unsafe fn l_Lean_LBool_false_elim(
    mut v_motive_170_: *mut leanh::LeanObject,
    mut v_t_171_: u8,
    mut v_h_172_: *mut leanh::LeanObject,
    mut v_false_173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_false_173_);
    return v_false_173_;
}
pub unsafe fn l_Lean_LBool_false_elim___boxed(
    mut v_motive_174_: *mut leanh::LeanObject,
    mut v_t_175_: *mut leanh::LeanObject,
    mut v_h_176_: *mut leanh::LeanObject,
    mut v_false_177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_178_: u8 = 0;
    let mut v_res_179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_178_ = (leanh::lean_unbox(v_t_175_) as u8);
    v_res_179_ = l_Lean_LBool_false_elim(v_motive_174_, v_t_boxed_178_, v_h_176_, v_false_177_);
    leanh::lean_dec(v_false_177_);
    return v_res_179_;
}
pub unsafe fn l_Lean_LBool_true_elim___redArg(
    mut v_true_180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_true_180_);
    return v_true_180_;
}
pub unsafe fn l_Lean_LBool_true_elim___redArg___boxed(
    mut v_true_181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_182_ = l_Lean_LBool_true_elim___redArg(v_true_181_);
    leanh::lean_dec(v_true_181_);
    return v_res_182_;
}
pub unsafe fn l_Lean_LBool_true_elim(
    mut v_motive_183_: *mut leanh::LeanObject,
    mut v_t_184_: u8,
    mut v_h_185_: *mut leanh::LeanObject,
    mut v_true_186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_true_186_);
    return v_true_186_;
}
pub unsafe fn l_Lean_LBool_true_elim___boxed(
    mut v_motive_187_: *mut leanh::LeanObject,
    mut v_t_188_: *mut leanh::LeanObject,
    mut v_h_189_: *mut leanh::LeanObject,
    mut v_true_190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_191_: u8 = 0;
    let mut v_res_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_191_ = (leanh::lean_unbox(v_t_188_) as u8);
    v_res_192_ = l_Lean_LBool_true_elim(v_motive_187_, v_t_boxed_191_, v_h_189_, v_true_190_);
    leanh::lean_dec(v_true_190_);
    return v_res_192_;
}
pub unsafe fn l_Lean_LBool_undef_elim___redArg(
    mut v_undef_193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_undef_193_);
    return v_undef_193_;
}
pub unsafe fn l_Lean_LBool_undef_elim___redArg___boxed(
    mut v_undef_194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_195_ = l_Lean_LBool_undef_elim___redArg(v_undef_194_);
    leanh::lean_dec(v_undef_194_);
    return v_res_195_;
}
pub unsafe fn l_Lean_LBool_undef_elim(
    mut v_motive_196_: *mut leanh::LeanObject,
    mut v_t_197_: u8,
    mut v_h_198_: *mut leanh::LeanObject,
    mut v_undef_199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_undef_199_);
    return v_undef_199_;
}
pub unsafe fn l_Lean_LBool_undef_elim___boxed(
    mut v_motive_200_: *mut leanh::LeanObject,
    mut v_t_201_: *mut leanh::LeanObject,
    mut v_h_202_: *mut leanh::LeanObject,
    mut v_undef_203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_204_: u8 = 0;
    let mut v_res_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_204_ = (leanh::lean_unbox(v_t_201_) as u8);
    v_res_205_ = l_Lean_LBool_undef_elim(v_motive_200_, v_t_boxed_204_, v_h_202_, v_undef_203_);
    leanh::lean_dec(v_undef_203_);
    return v_res_205_;
}
pub unsafe fn _init_l_Lean_instInhabitedLBool_default() -> u8 {
    let mut v___x_206_: u8 = 0;
    v___x_206_ = 0;
    return v___x_206_;
}
pub unsafe fn _init_l_Lean_instInhabitedLBool() -> u8 {
    let mut v___x_207_: u8 = 0;
    v___x_207_ = 0;
    return v___x_207_;
}
pub unsafe fn l_Lean_instBEqLBool_beq(mut v_x_208_: u8, mut v_y_209_: u8) -> u8 {
    let mut v___x_210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_212_: u8 = 0;
    v___x_210_ = l_Lean_LBool_ctorIdx(v_x_208_);
    v___x_211_ = l_Lean_LBool_ctorIdx(v_y_209_);
    v___x_212_ = lean_nat_dec_eq(v___x_210_, v___x_211_);
    leanh::lean_dec(v___x_211_);
    leanh::lean_dec(v___x_210_);
    return v___x_212_;
}
pub unsafe fn l_Lean_instBEqLBool_beq___boxed(
    mut v_x_213_: *mut leanh::LeanObject,
    mut v_y_214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_17__boxed_215_: u8 = 0;
    let mut v_y_18__boxed_216_: u8 = 0;
    let mut v_res_217_: u8 = 0;
    let mut v_r_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_215_ = (leanh::lean_unbox(v_x_213_) as u8);
    v_y_18__boxed_216_ = (leanh::lean_unbox(v_y_214_) as u8);
    v_res_217_ = l_Lean_instBEqLBool_beq(v_x_17__boxed_215_, v_y_18__boxed_216_);
    v_r_218_ = leanh::lean_box((v_res_217_) as usize);
    return v_r_218_;
}
pub unsafe fn l_Lean_LBool_neg(mut v_x_221_: u8) -> u8 {
    match v_x_221_ {
        0 => {
            let mut v___x_222_: u8 = 0;
            v___x_222_ = 1;
            return v___x_222_;
        }
        1 => {
            let mut v___x_223_: u8 = 0;
            v___x_223_ = 0;
            return v___x_223_;
        }
        _ => {
            return v_x_221_;
        }
    }
}
pub unsafe fn l_Lean_LBool_neg___boxed(
    mut v_x_224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_25__boxed_225_: u8 = 0;
    let mut v_res_226_: u8 = 0;
    let mut v_r_227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_25__boxed_225_ = (leanh::lean_unbox(v_x_224_) as u8);
    v_res_226_ = l_Lean_LBool_neg(v_x_25__boxed_225_);
    v_r_227_ = leanh::lean_box((v_res_226_) as usize);
    return v_r_227_;
}
pub unsafe fn l_Lean_LBool_and(mut v_x_228_: u8, mut v_x_229_: u8) -> u8 {
    if v_x_228_ == 1 {
        return v_x_229_;
    } else {
        return v_x_228_;
    }
}
pub unsafe fn l_Lean_LBool_and___boxed(
    mut v_x_230_: *mut leanh::LeanObject,
    mut v_x_231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_16__boxed_232_: u8 = 0;
    let mut v_x_17__boxed_233_: u8 = 0;
    let mut v_res_234_: u8 = 0;
    let mut v_r_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_16__boxed_232_ = (leanh::lean_unbox(v_x_230_) as u8);
    v_x_17__boxed_233_ = (leanh::lean_unbox(v_x_231_) as u8);
    v_res_234_ = l_Lean_LBool_and(v_x_16__boxed_232_, v_x_17__boxed_233_);
    v_r_235_ = leanh::lean_box((v_res_234_) as usize);
    return v_r_235_;
}
pub unsafe fn l_Lean_LBool_toString(mut v_x_239_: u8) -> *mut leanh::LeanObject {
    match v_x_239_ {
        0 => {
            let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_240_ = l_Lean_LBool_toString___closed__0;
            return v___x_240_;
        }
        1 => {
            let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_241_ = l_Lean_LBool_toString___closed__1;
            return v___x_241_;
        }
        _ => {
            let mut v___x_242_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_242_ = l_Lean_LBool_toString___closed__2;
            return v___x_242_;
        }
    }
}
pub unsafe fn l_Lean_LBool_toString___boxed(
    mut v_x_243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_31__boxed_244_: u8 = 0;
    let mut v_res_245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_31__boxed_244_ = (leanh::lean_unbox(v_x_243_) as u8);
    v_res_245_ = l_Lean_LBool_toString(v_x_31__boxed_244_);
    return v_res_245_;
}
pub unsafe fn l_Bool_toLBool(mut v_x_248_: u8) -> u8 {
    if v_x_248_ == 0 {
        let mut v___x_249_: u8 = 0;
        v___x_249_ = 0;
        return v___x_249_;
    } else {
        let mut v___x_250_: u8 = 0;
        v___x_250_ = 1;
        return v___x_250_;
    }
}
pub unsafe fn l_Bool_toLBool___boxed(
    mut v_x_251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_18__boxed_252_: u8 = 0;
    let mut v_res_253_: u8 = 0;
    let mut v_r_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_18__boxed_252_ = (leanh::lean_unbox(v_x_251_) as u8);
    v_res_253_ = l_Bool_toLBool(v_x_18__boxed_252_);
    v_r_254_ = leanh::lean_box((v_res_253_) as usize);
    return v_r_254_;
}
pub unsafe fn l_toLBoolM___redArg___lam__0(
    mut v_toPure_255_: *mut leanh::LeanObject,
    mut v_b_256_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_257_: u8 = 0;
    let mut v___x_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_257_ = l_Bool_toLBool(v_b_256_);
    v___x_258_ = leanh::lean_box((v___x_257_) as usize);
    v___x_259_ = leanh::lean_apply_2(v_toPure_255_, leanh::lean_box(0), v___x_258_);
    return v___x_259_;
}
pub unsafe fn l_toLBoolM___redArg___lam__0___boxed(
    mut v_toPure_260_: *mut leanh::LeanObject,
    mut v_b_261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_262_: u8 = 0;
    let mut v_res_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_262_ = (leanh::lean_unbox(v_b_261_) as u8);
    v_res_263_ = l_toLBoolM___redArg___lam__0(v_toPure_260_, v_b_boxed_262_);
    return v_res_263_;
}
pub unsafe fn l_toLBoolM___redArg(
    mut v_inst_264_: *mut leanh::LeanObject,
    mut v_x_265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_266_ = leanh::lean_ctor_get(v_inst_264_, 0);
    leanh::lean_inc_ref(v_toApplicative_266_);
    v_toBind_267_ = leanh::lean_ctor_get(v_inst_264_, 1);
    leanh::lean_inc(v_toBind_267_);
    leanh::lean_dec_ref(v_inst_264_);
    v_toPure_268_ = leanh::lean_ctor_get(v_toApplicative_266_, 1);
    leanh::lean_inc(v_toPure_268_);
    leanh::lean_dec_ref(v_toApplicative_266_);
    v___f_269_ = leanh::lean_alloc_closure(
        l_toLBoolM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_269_, 0, v_toPure_268_);
    v___x_270_ = leanh::lean_apply_4(
        v_toBind_267_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_265_,
        v___f_269_,
    );
    return v___x_270_;
}
pub unsafe fn l_toLBoolM(
    mut v_m_271_: *mut leanh::LeanObject,
    mut v_inst_272_: *mut leanh::LeanObject,
    mut v_x_273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_274_ = leanh::lean_ctor_get(v_inst_272_, 0);
    leanh::lean_inc_ref(v_toApplicative_274_);
    v_toBind_275_ = leanh::lean_ctor_get(v_inst_272_, 1);
    leanh::lean_inc(v_toBind_275_);
    leanh::lean_dec_ref(v_inst_272_);
    v_toPure_276_ = leanh::lean_ctor_get(v_toApplicative_274_, 1);
    leanh::lean_inc(v_toPure_276_);
    leanh::lean_dec_ref(v_toApplicative_274_);
    v___f_277_ = leanh::lean_alloc_closure(
        l_toLBoolM___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_277_, 0, v_toPure_276_);
    v___x_278_ = leanh::lean_apply_4(
        v_toBind_275_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_273_,
        v___f_277_,
    );
    return v___x_278_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_LBool(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_instInhabitedLBool_default = _init_l_Lean_instInhabitedLBool_default();
    l_Lean_instInhabitedLBool = _init_l_Lean_instInhabitedLBool();
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_LBool(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_LBool(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_LBool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_LBool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_LBool(builtin);
}
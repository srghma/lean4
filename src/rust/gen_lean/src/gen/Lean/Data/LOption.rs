// Lean compiler output
// Module: Lean.Data.LOption
// Imports: Init.Data.String.Basic
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::ffi::lean_string_append;
pub static l_Lean_instToStringLOption___redArg___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [110, 111, 110, 101, 0],
};
static mut l_Lean_instToStringLOption___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringLOption___redArg___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instToStringLOption___redArg___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [40, 115, 111, 109, 101, 32, 0],
};
static mut l_Lean_instToStringLOption___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringLOption___redArg___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instToStringLOption___redArg___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [41, 0],
};
static mut l_Lean_instToStringLOption___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringLOption___redArg___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_instToStringLOption___redArg___lam__0___closed__3_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_instToStringLOption___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instToStringLOption___redArg___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_LOption_ctorIdx___redArg(
    mut v_x_160_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_160_) {
        0 => {
            let mut v___x_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_161_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_161_;
        }
        1 => {
            let mut v___x_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_162_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_162_;
        }
        _ => {
            let mut v___x_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_163_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_163_;
        }
    }
}
pub unsafe fn l_Lean_LOption_ctorIdx___redArg___boxed(
    mut v_x_164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_165_ = l_Lean_LOption_ctorIdx___redArg(v_x_164_);
    crate::leanh::lean_dec(v_x_164_);
    return v_res_165_;
}
pub unsafe fn l_Lean_LOption_ctorIdx(
    mut v_00_u03b1_166_: *mut crate::leanh::LeanObject,
    mut v_x_167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_168_ = l_Lean_LOption_ctorIdx___redArg(v_x_167_);
    return v___x_168_;
}
pub unsafe fn l_Lean_LOption_ctorIdx___boxed(
    mut v_00_u03b1_169_: *mut crate::leanh::LeanObject,
    mut v_x_170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_171_ = l_Lean_LOption_ctorIdx(v_00_u03b1_169_, v_x_170_);
    crate::leanh::lean_dec(v_x_170_);
    return v_res_171_;
}
pub unsafe fn l_Lean_LOption_ctorElim___redArg(
    mut v_t_172_: *mut crate::leanh::LeanObject,
    mut v_k_173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_172_) == 1 {
        let mut v_a_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_174_ = crate::leanh::lean_ctor_get(v_t_172_, 0);
        crate::leanh::lean_inc(v_a_174_);
        crate::leanh::lean_dec_ref_known(v_t_172_, 1);
        v___x_175_ = crate::leanh::lean_apply_1(v_k_173_, v_a_174_);
        return v___x_175_;
    } else {
        crate::leanh::lean_dec(v_t_172_);
        return v_k_173_;
    }
}
pub unsafe fn l_Lean_LOption_ctorElim(
    mut v_00_u03b1_176_: *mut crate::leanh::LeanObject,
    mut v_motive_177_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_178_: *mut crate::leanh::LeanObject,
    mut v_t_179_: *mut crate::leanh::LeanObject,
    mut v_h_180_: *mut crate::leanh::LeanObject,
    mut v_k_181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_182_ = l_Lean_LOption_ctorElim___redArg(v_t_179_, v_k_181_);
    return v___x_182_;
}
pub unsafe fn l_Lean_LOption_ctorElim___boxed(
    mut v_00_u03b1_183_: *mut crate::leanh::LeanObject,
    mut v_motive_184_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_185_: *mut crate::leanh::LeanObject,
    mut v_t_186_: *mut crate::leanh::LeanObject,
    mut v_h_187_: *mut crate::leanh::LeanObject,
    mut v_k_188_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_189_ = l_Lean_LOption_ctorElim(
        v_00_u03b1_183_,
        v_motive_184_,
        v_ctorIdx_185_,
        v_t_186_,
        v_h_187_,
        v_k_188_,
    );
    crate::leanh::lean_dec(v_ctorIdx_185_);
    return v_res_189_;
}
pub unsafe fn l_Lean_LOption_none_elim___redArg(
    mut v_t_190_: *mut crate::leanh::LeanObject,
    mut v_none_191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_192_ = l_Lean_LOption_ctorElim___redArg(v_t_190_, v_none_191_);
    return v___x_192_;
}
pub unsafe fn l_Lean_LOption_none_elim(
    mut v_00_u03b1_193_: *mut crate::leanh::LeanObject,
    mut v_motive_194_: *mut crate::leanh::LeanObject,
    mut v_t_195_: *mut crate::leanh::LeanObject,
    mut v_h_196_: *mut crate::leanh::LeanObject,
    mut v_none_197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_198_ = l_Lean_LOption_ctorElim___redArg(v_t_195_, v_none_197_);
    return v___x_198_;
}
pub unsafe fn l_Lean_LOption_some_elim___redArg(
    mut v_t_199_: *mut crate::leanh::LeanObject,
    mut v_some_200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_201_ = l_Lean_LOption_ctorElim___redArg(v_t_199_, v_some_200_);
    return v___x_201_;
}
pub unsafe fn l_Lean_LOption_some_elim(
    mut v_00_u03b1_202_: *mut crate::leanh::LeanObject,
    mut v_motive_203_: *mut crate::leanh::LeanObject,
    mut v_t_204_: *mut crate::leanh::LeanObject,
    mut v_h_205_: *mut crate::leanh::LeanObject,
    mut v_some_206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_207_ = l_Lean_LOption_ctorElim___redArg(v_t_204_, v_some_206_);
    return v___x_207_;
}
pub unsafe fn l_Lean_LOption_undef_elim___redArg(
    mut v_t_208_: *mut crate::leanh::LeanObject,
    mut v_undef_209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_210_ = l_Lean_LOption_ctorElim___redArg(v_t_208_, v_undef_209_);
    return v___x_210_;
}
pub unsafe fn l_Lean_LOption_undef_elim(
    mut v_00_u03b1_211_: *mut crate::leanh::LeanObject,
    mut v_motive_212_: *mut crate::leanh::LeanObject,
    mut v_t_213_: *mut crate::leanh::LeanObject,
    mut v_h_214_: *mut crate::leanh::LeanObject,
    mut v_undef_215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_216_ = l_Lean_LOption_ctorElim___redArg(v_t_213_, v_undef_215_);
    return v___x_216_;
}
pub unsafe fn l_Lean_instInhabitedLOption_default(
    mut v_00_u03b1_217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_218_ = crate::leanh::lean_box(0);
    return v___x_218_;
}
pub unsafe fn l_Lean_instInhabitedLOption(
    mut v_a_219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_220_ = crate::leanh::lean_box(0);
    return v___x_220_;
}
pub unsafe fn l_Lean_instBEqLOption_beq___redArg(
    mut v_inst_221_: *mut crate::leanh::LeanObject,
    mut v_x_222_: *mut crate::leanh::LeanObject,
    mut v_x_223_: *mut crate::leanh::LeanObject,
) -> u8 {
    match crate::leanh::lean_obj_tag(v_x_222_) {
        0 => {
            crate::leanh::lean_dec_ref(v_inst_221_);
            if crate::leanh::lean_obj_tag(v_x_223_) == 0 {
                let mut v___x_224_: u8 = 0;
                v___x_224_ = 1;
                return v___x_224_;
            } else {
                let mut v___x_225_: u8 = 0;
                crate::leanh::lean_dec(v_x_223_);
                v___x_225_ = 0;
                return v___x_225_;
            }
        }
        1 => {
            if crate::leanh::lean_obj_tag(v_x_223_) == 1 {
                let mut v_a_226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_a_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_229_: u8 = 0;
                v_a_226_ = crate::leanh::lean_ctor_get(v_x_222_, 0);
                crate::leanh::lean_inc(v_a_226_);
                crate::leanh::lean_dec_ref_known(v_x_222_, 1);
                v_a_227_ = crate::leanh::lean_ctor_get(v_x_223_, 0);
                crate::leanh::lean_inc(v_a_227_);
                crate::leanh::lean_dec_ref_known(v_x_223_, 1);
                v___x_228_ = crate::leanh::lean_apply_2(v_inst_221_, v_a_226_, v_a_227_);
                v___x_229_ = (crate::leanh::lean_unbox(v___x_228_) as u8);
                return v___x_229_;
            } else {
                let mut v___x_230_: u8 = 0;
                crate::leanh::lean_dec_ref_known(v_x_222_, 1);
                crate::leanh::lean_dec(v_x_223_);
                crate::leanh::lean_dec_ref(v_inst_221_);
                v___x_230_ = 0;
                return v___x_230_;
            }
        }
        _ => {
            crate::leanh::lean_dec_ref(v_inst_221_);
            if crate::leanh::lean_obj_tag(v_x_223_) == 2 {
                let mut v___x_231_: u8 = 0;
                v___x_231_ = 1;
                return v___x_231_;
            } else {
                let mut v___x_232_: u8 = 0;
                crate::leanh::lean_dec(v_x_223_);
                v___x_232_ = 0;
                return v___x_232_;
            }
        }
    }
}
pub unsafe fn l_Lean_instBEqLOption_beq___redArg___boxed(
    mut v_inst_233_: *mut crate::leanh::LeanObject,
    mut v_x_234_: *mut crate::leanh::LeanObject,
    mut v_x_235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_236_: u8 = 0;
    let mut v_r_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_236_ = l_Lean_instBEqLOption_beq___redArg(v_inst_233_, v_x_234_, v_x_235_);
    v_r_237_ = crate::leanh::lean_box((v_res_236_) as usize);
    return v_r_237_;
}
pub unsafe fn l_Lean_instBEqLOption_beq(
    mut v_00_u03b1_238_: *mut crate::leanh::LeanObject,
    mut v_inst_239_: *mut crate::leanh::LeanObject,
    mut v_x_240_: *mut crate::leanh::LeanObject,
    mut v_x_241_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_242_: u8 = 0;
    v___x_242_ = l_Lean_instBEqLOption_beq___redArg(v_inst_239_, v_x_240_, v_x_241_);
    return v___x_242_;
}
pub unsafe fn l_Lean_instBEqLOption_beq___boxed(
    mut v_00_u03b1_243_: *mut crate::leanh::LeanObject,
    mut v_inst_244_: *mut crate::leanh::LeanObject,
    mut v_x_245_: *mut crate::leanh::LeanObject,
    mut v_x_246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_247_: u8 = 0;
    let mut v_r_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_247_ = l_Lean_instBEqLOption_beq(v_00_u03b1_243_, v_inst_244_, v_x_245_, v_x_246_);
    v_r_248_ = crate::leanh::lean_box((v_res_247_) as usize);
    return v_r_248_;
}
pub unsafe fn l_Lean_instBEqLOption___redArg(
    mut v_inst_249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_250_ = crate::leanh::lean_alloc_closure(
        l_Lean_instBEqLOption_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_250_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_250_, 1, v_inst_249_);
    return v___x_250_;
}
pub unsafe fn l_Lean_instBEqLOption(
    mut v_00_u03b1_251_: *mut crate::leanh::LeanObject,
    mut v_inst_252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_253_ = crate::leanh::lean_alloc_closure(
        l_Lean_instBEqLOption_beq___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___x_253_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_253_, 1, v_inst_252_);
    return v___x_253_;
}
pub unsafe fn l_Lean_instToStringLOption___redArg___lam__0(
    mut v_inst_258_: *mut crate::leanh::LeanObject,
    mut v_x_259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_259_) {
        0 => {
            let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_inst_258_);
            v___x_260_ = l_Lean_instToStringLOption___redArg___lam__0___closed__0;
            return v___x_260_;
        }
        1 => {
            let mut v_a_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_261_ = crate::leanh::lean_ctor_get(v_x_259_, 0);
            crate::leanh::lean_inc(v_a_261_);
            crate::leanh::lean_dec_ref_known(v_x_259_, 1);
            v___x_262_ = l_Lean_instToStringLOption___redArg___lam__0___closed__1;
            v___x_263_ = crate::leanh::lean_apply_1(v_inst_258_, v_a_261_);
            v___x_264_ = lean_string_append(v___x_262_, v___x_263_);
            crate::leanh::lean_dec_ref(v___x_263_);
            v___x_265_ = l_Lean_instToStringLOption___redArg___lam__0___closed__2;
            v___x_266_ = lean_string_append(v___x_264_, v___x_265_);
            return v___x_266_;
        }
        _ => {
            let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_inst_258_);
            v___x_267_ = l_Lean_instToStringLOption___redArg___lam__0___closed__3;
            return v___x_267_;
        }
    }
}
pub unsafe fn l_Lean_instToStringLOption___redArg(
    mut v_inst_268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_269_ = crate::leanh::lean_alloc_closure(
        l_Lean_instToStringLOption___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_269_, 0, v_inst_268_);
    return v___f_269_;
}
pub unsafe fn l_Lean_instToStringLOption(
    mut v_00_u03b1_270_: *mut crate::leanh::LeanObject,
    mut v_inst_271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_272_ = crate::leanh::lean_alloc_closure(
        l_Lean_instToStringLOption___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_272_, 0, v_inst_271_);
    return v___f_272_;
}
pub unsafe fn l_Lean_LOption_toOption___redArg(
    mut v_x_273_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_277_: u8 = 0;
    let mut v___x_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_281_: u8 = 0;
    let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_273_) == 1 {
                    v_a_274_ = crate::leanh::lean_ctor_get(v_x_273_, 0);
                    v_isSharedCheck_281_ = (!crate::leanh::lean_is_exclusive(v_x_273_)) as u8;
                    if v_isSharedCheck_281_ == 0 {
                        v___x_276_ = v_x_273_;
                        v_isShared_277_ = v_isSharedCheck_281_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_274_);
                        crate::leanh::lean_dec(v_x_273_);
                        v___x_276_ = crate::leanh::lean_box(0);
                        v_isShared_277_ = v_isSharedCheck_281_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_x_273_);
                    v___x_282_ = crate::leanh::lean_box(0);
                    return v___x_282_;
                }
            }
            1 => {
                if v_isShared_277_ == 0 {
                    v___x_279_ = v___x_276_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_280_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_280_, 0, v_a_274_);
                    v___x_279_ = v_reuseFailAlloc_280_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_279_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_LOption_toOption(
    mut v_00_u03b1_283_: *mut crate::leanh::LeanObject,
    mut v_x_284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_285_ = l_Lean_LOption_toOption___redArg(v_x_284_);
    return v___x_285_;
}
pub unsafe fn l_Option_toLOption___redArg(
    mut v_x_286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_291_: u8 = 0;
    let mut v___x_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_295_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_286_) == 0 {
                    v___x_287_ = crate::leanh::lean_box(0);
                    return v___x_287_;
                } else {
                    v_val_288_ = crate::leanh::lean_ctor_get(v_x_286_, 0);
                    v_isSharedCheck_295_ = (!crate::leanh::lean_is_exclusive(v_x_286_)) as u8;
                    if v_isSharedCheck_295_ == 0 {
                        v___x_290_ = v_x_286_;
                        v_isShared_291_ = v_isSharedCheck_295_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_288_);
                        crate::leanh::lean_dec(v_x_286_);
                        v___x_290_ = crate::leanh::lean_box(0);
                        v_isShared_291_ = v_isSharedCheck_295_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_291_ == 0 {
                    v___x_293_ = v___x_290_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_294_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_294_, 0, v_val_288_);
                    v___x_293_ = v_reuseFailAlloc_294_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_293_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_toLOption(
    mut v_00_u03b1_296_: *mut crate::leanh::LeanObject,
    mut v_x_297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_298_ = l_Option_toLOption___redArg(v_x_297_);
    return v___x_298_;
}
pub unsafe fn l_toLOptionM___redArg___lam__0(
    mut v_toPure_299_: *mut crate::leanh::LeanObject,
    mut v_b_300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_301_ = l_Option_toLOption___redArg(v_b_300_);
    v___x_302_ = crate::leanh::lean_apply_2(v_toPure_299_, crate::leanh::lean_box(0), v___x_301_);
    return v___x_302_;
}
pub unsafe fn l_toLOptionM___redArg(
    mut v_inst_303_: *mut crate::leanh::LeanObject,
    mut v_x_304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_305_ = crate::leanh::lean_ctor_get(v_inst_303_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_305_);
    v_toBind_306_ = crate::leanh::lean_ctor_get(v_inst_303_, 1);
    crate::leanh::lean_inc(v_toBind_306_);
    crate::leanh::lean_dec_ref(v_inst_303_);
    v_toPure_307_ = crate::leanh::lean_ctor_get(v_toApplicative_305_, 1);
    crate::leanh::lean_inc(v_toPure_307_);
    crate::leanh::lean_dec_ref(v_toApplicative_305_);
    v___f_308_ = crate::leanh::lean_alloc_closure(
        l_toLOptionM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_308_, 0, v_toPure_307_);
    v___x_309_ = crate::leanh::lean_apply_4(
        v_toBind_306_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_304_,
        v___f_308_,
    );
    return v___x_309_;
}
pub unsafe fn l_toLOptionM(
    mut v_00_u03b1_310_: *mut crate::leanh::LeanObject,
    mut v_m_311_: *mut crate::leanh::LeanObject,
    mut v_inst_312_: *mut crate::leanh::LeanObject,
    mut v_x_313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_314_ = crate::leanh::lean_ctor_get(v_inst_312_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_314_);
    v_toBind_315_ = crate::leanh::lean_ctor_get(v_inst_312_, 1);
    crate::leanh::lean_inc(v_toBind_315_);
    crate::leanh::lean_dec_ref(v_inst_312_);
    v_toPure_316_ = crate::leanh::lean_ctor_get(v_toApplicative_314_, 1);
    crate::leanh::lean_inc(v_toPure_316_);
    crate::leanh::lean_dec_ref(v_toApplicative_314_);
    v___f_317_ = crate::leanh::lean_alloc_closure(
        l_toLOptionM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_317_, 0, v_toPure_316_);
    v___x_318_ = crate::leanh::lean_apply_4(
        v_toBind_315_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_313_,
        v___f_317_,
    );
    return v___x_318_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_LOption(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_LOption(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_LOption(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_LOption(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_LOption(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_LOption(builtin);
}

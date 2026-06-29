// Lean compiler output
// Module: Init.Data.Char.Basic
// Imports: Init.Data.UInt.BasicAux Init.Data.Nat.Div.Basic
use crate::r#gen::Init::Data::Nat::Div::Basic::{
    initialize_Init_Data_Nat_Div_Basic, runtime_initialize_Init_Data_Nat_Div_Basic,
};
use crate::r#gen::Init::Data::UInt::BasicAux::{
    initialize_Init_Data_UInt_BasicAux, runtime_initialize_Init_Data_UInt_BasicAux,
};
use crate::ffi::{
    lean_uint8_to_uint32, lean_uint32_add, lean_uint32_to_uint8,
};
use crate::ffi::{
    lean_uint32_dec_eq, lean_uint32_dec_le, lean_uint32_dec_lt, lean_uint32_to_nat,
};
pub static mut l_Char_instLT: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_instLE: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_instInhabited: u32 = 0;
pub unsafe fn _init_l_Char_instLT() -> *mut crate::leanh::LeanObject {
    let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_158_ = crate::leanh::lean_box(0);
    return v___x_158_;
}
pub unsafe fn _init_l_Char_instLE() -> *mut crate::leanh::LeanObject {
    let mut v___x_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_159_ = crate::leanh::lean_box(0);
    return v___x_159_;
}
pub unsafe fn l_Char_instDecidableLt(mut v_a_160_: u32, mut v_b_161_: u32) -> u8 {
    let mut v___x_162_: u8 = 0;
    v___x_162_ = lean_uint32_dec_lt(v_a_160_, v_b_161_);
    return v___x_162_;
}
pub unsafe fn l_Char_instDecidableLt___boxed(
    mut v_a_163_: *mut crate::leanh::LeanObject,
    mut v_b_164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_165_: u32 = 0;
    let mut v_b_boxed_166_: u32 = 0;
    let mut v_res_167_: u8 = 0;
    let mut v_r_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_165_ = crate::leanh::lean_unbox_uint32(v_a_163_);
    crate::leanh::lean_dec(v_a_163_);
    v_b_boxed_166_ = crate::leanh::lean_unbox_uint32(v_b_164_);
    crate::leanh::lean_dec(v_b_164_);
    v_res_167_ = l_Char_instDecidableLt(v_a_boxed_165_, v_b_boxed_166_);
    v_r_168_ = crate::leanh::lean_box((v_res_167_) as usize);
    return v_r_168_;
}
pub unsafe fn l_Char_instDecidableLe(mut v_a_169_: u32, mut v_b_170_: u32) -> u8 {
    let mut v___x_171_: u8 = 0;
    v___x_171_ = lean_uint32_dec_le(v_a_169_, v_b_170_);
    return v___x_171_;
}
pub unsafe fn l_Char_instDecidableLe___boxed(
    mut v_a_172_: *mut crate::leanh::LeanObject,
    mut v_b_173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_boxed_174_: u32 = 0;
    let mut v_b_boxed_175_: u32 = 0;
    let mut v_res_176_: u8 = 0;
    let mut v_r_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_174_ = crate::leanh::lean_unbox_uint32(v_a_172_);
    crate::leanh::lean_dec(v_a_172_);
    v_b_boxed_175_ = crate::leanh::lean_unbox_uint32(v_b_173_);
    crate::leanh::lean_dec(v_b_173_);
    v_res_176_ = l_Char_instDecidableLe(v_a_boxed_174_, v_b_boxed_175_);
    v_r_177_ = crate::leanh::lean_box((v_res_176_) as usize);
    return v_r_177_;
}
pub unsafe fn l_Char_toNat(mut v_c_178_: u32) -> *mut crate::leanh::LeanObject {
    let mut v___x_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_179_ = lean_uint32_to_nat(v_c_178_);
    return v___x_179_;
}
pub unsafe fn l_Char_toNat___boxed(
    mut v_c_180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_181_: u32 = 0;
    let mut v_res_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_181_ = crate::leanh::lean_unbox_uint32(v_c_180_);
    crate::leanh::lean_dec(v_c_180_);
    v_res_182_ = l_Char_toNat(v_c_boxed_181_);
    return v_res_182_;
}
pub unsafe fn l_Char_toUInt8(mut v_c_183_: u32) -> u8 {
    let mut v___x_184_: u8 = 0;
    v___x_184_ = lean_uint32_to_uint8(v_c_183_);
    return v___x_184_;
}
pub unsafe fn l_Char_toUInt8___boxed(
    mut v_c_185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_186_: u32 = 0;
    let mut v_res_187_: u8 = 0;
    let mut v_r_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_186_ = crate::leanh::lean_unbox_uint32(v_c_185_);
    crate::leanh::lean_dec(v_c_185_);
    v_res_187_ = l_Char_toUInt8(v_c_boxed_186_);
    v_r_188_ = crate::leanh::lean_box((v_res_187_) as usize);
    return v_r_188_;
}
pub unsafe fn l_Char_ofUInt8(mut v_n_189_: u8) -> u32 {
    let mut v___x_190_: u32 = 0;
    v___x_190_ = lean_uint8_to_uint32(v_n_189_);
    return v___x_190_;
}
pub unsafe fn l_Char_ofUInt8___boxed(
    mut v_n_191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_192_: u8 = 0;
    let mut v_res_193_: u32 = 0;
    let mut v_r_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_192_ = (crate::leanh::lean_unbox(v_n_191_) as u8);
    v_res_193_ = l_Char_ofUInt8(v_n_boxed_192_);
    v_r_194_ = crate::leanh::lean_box_uint32(v_res_193_);
    return v_r_194_;
}
pub unsafe fn _init_l_Char_instInhabited() -> u32 {
    let mut v___x_195_: u32 = 0;
    v___x_195_ = 65;
    return v___x_195_;
}
pub unsafe fn l_Char_isWhitespace(mut v_c_196_: u32) -> u8 {
    let mut v___y_198_: u8 = 0;
    let mut v___x_199_: u32 = 0;
    let mut v___x_200_: u8 = 0;
    let mut v___x_201_: u32 = 0;
    let mut v___x_202_: u8 = 0;
    let mut v___x_203_: u32 = 0;
    let mut v___x_204_: u8 = 0;
    let mut v___x_205_: u32 = 0;
    let mut v___x_206_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_203_ = 32;
                v___x_204_ = lean_uint32_dec_eq(v_c_196_, v___x_203_);
                if v___x_204_ == 0 {
                    v___x_205_ = 9;
                    v___x_206_ = lean_uint32_dec_eq(v_c_196_, v___x_205_);
                    v___y_198_ = v___x_206_;
                    state = 1;
                    continue;
                } else {
                    v___y_198_ = v___x_204_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_198_ == 0 {
                    v___x_199_ = 13;
                    v___x_200_ = lean_uint32_dec_eq(v_c_196_, v___x_199_);
                    if v___x_200_ == 0 {
                        v___x_201_ = 10;
                        v___x_202_ = lean_uint32_dec_eq(v_c_196_, v___x_201_);
                        return v___x_202_;
                    } else {
                        return v___x_200_;
                    }
                } else {
                    return v___y_198_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_isWhitespace___boxed(
    mut v_c_207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_208_: u32 = 0;
    let mut v_res_209_: u8 = 0;
    let mut v_r_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_208_ = crate::leanh::lean_unbox_uint32(v_c_207_);
    crate::leanh::lean_dec(v_c_207_);
    v_res_209_ = l_Char_isWhitespace(v_c_boxed_208_);
    v_r_210_ = crate::leanh::lean_box((v_res_209_) as usize);
    return v_r_210_;
}
pub unsafe fn l_Char_isUpper(mut v_c_211_: u32) -> u8 {
    let mut v___x_212_: u32 = 0;
    let mut v___x_213_: u8 = 0;
    v___x_212_ = 65;
    v___x_213_ = lean_uint32_dec_le(v___x_212_, v_c_211_);
    if v___x_213_ == 0 {
        return v___x_213_;
    } else {
        let mut v___x_214_: u32 = 0;
        let mut v___x_215_: u8 = 0;
        v___x_214_ = 90;
        v___x_215_ = lean_uint32_dec_le(v_c_211_, v___x_214_);
        return v___x_215_;
    }
}
pub unsafe fn l_Char_isUpper___boxed(
    mut v_c_216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_217_: u32 = 0;
    let mut v_res_218_: u8 = 0;
    let mut v_r_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_217_ = crate::leanh::lean_unbox_uint32(v_c_216_);
    crate::leanh::lean_dec(v_c_216_);
    v_res_218_ = l_Char_isUpper(v_c_boxed_217_);
    v_r_219_ = crate::leanh::lean_box((v_res_218_) as usize);
    return v_r_219_;
}
pub unsafe fn l_Char_isLower(mut v_c_220_: u32) -> u8 {
    let mut v___x_221_: u32 = 0;
    let mut v___x_222_: u8 = 0;
    v___x_221_ = 97;
    v___x_222_ = lean_uint32_dec_le(v___x_221_, v_c_220_);
    if v___x_222_ == 0 {
        return v___x_222_;
    } else {
        let mut v___x_223_: u32 = 0;
        let mut v___x_224_: u8 = 0;
        v___x_223_ = 122;
        v___x_224_ = lean_uint32_dec_le(v_c_220_, v___x_223_);
        return v___x_224_;
    }
}
pub unsafe fn l_Char_isLower___boxed(
    mut v_c_225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_226_: u32 = 0;
    let mut v_res_227_: u8 = 0;
    let mut v_r_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_226_ = crate::leanh::lean_unbox_uint32(v_c_225_);
    crate::leanh::lean_dec(v_c_225_);
    v_res_227_ = l_Char_isLower(v_c_boxed_226_);
    v_r_228_ = crate::leanh::lean_box((v_res_227_) as usize);
    return v_r_228_;
}
pub unsafe fn l_Char_isAlpha(mut v_c_229_: u32) -> u8 {
    let mut v___x_231_: u32 = 0;
    let mut v___x_232_: u8 = 0;
    let mut v___x_233_: u32 = 0;
    let mut v___x_234_: u8 = 0;
    let mut v___x_235_: u32 = 0;
    let mut v___x_236_: u8 = 0;
    let mut v___x_237_: u32 = 0;
    let mut v___x_238_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_235_ = 65;
                v___x_236_ = lean_uint32_dec_le(v___x_235_, v_c_229_);
                if v___x_236_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_237_ = 90;
                    v___x_238_ = lean_uint32_dec_le(v_c_229_, v___x_237_);
                    if v___x_238_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        return v___x_238_;
                    }
                }
            }
            1 => {
                v___x_231_ = 97;
                v___x_232_ = lean_uint32_dec_le(v___x_231_, v_c_229_);
                if v___x_232_ == 0 {
                    return v___x_232_;
                } else {
                    v___x_233_ = 122;
                    v___x_234_ = lean_uint32_dec_le(v_c_229_, v___x_233_);
                    return v___x_234_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_isAlpha___boxed(
    mut v_c_239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_240_: u32 = 0;
    let mut v_res_241_: u8 = 0;
    let mut v_r_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_240_ = crate::leanh::lean_unbox_uint32(v_c_239_);
    crate::leanh::lean_dec(v_c_239_);
    v_res_241_ = l_Char_isAlpha(v_c_boxed_240_);
    v_r_242_ = crate::leanh::lean_box((v_res_241_) as usize);
    return v_r_242_;
}
pub unsafe fn l_Char_isDigit(mut v_c_243_: u32) -> u8 {
    let mut v___x_244_: u32 = 0;
    let mut v___x_245_: u8 = 0;
    v___x_244_ = 48;
    v___x_245_ = lean_uint32_dec_le(v___x_244_, v_c_243_);
    if v___x_245_ == 0 {
        return v___x_245_;
    } else {
        let mut v___x_246_: u32 = 0;
        let mut v___x_247_: u8 = 0;
        v___x_246_ = 57;
        v___x_247_ = lean_uint32_dec_le(v_c_243_, v___x_246_);
        return v___x_247_;
    }
}
pub unsafe fn l_Char_isDigit___boxed(
    mut v_c_248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_249_: u32 = 0;
    let mut v_res_250_: u8 = 0;
    let mut v_r_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_249_ = crate::leanh::lean_unbox_uint32(v_c_248_);
    crate::leanh::lean_dec(v_c_248_);
    v_res_250_ = l_Char_isDigit(v_c_boxed_249_);
    v_r_251_ = crate::leanh::lean_box((v_res_250_) as usize);
    return v_r_251_;
}
pub unsafe fn l_Char_isHexDigit(mut v_c_252_: u32) -> u8 {
    let mut v___y_254_: u8 = 0;
    let mut v___x_255_: u32 = 0;
    let mut v___x_256_: u8 = 0;
    let mut v___x_257_: u32 = 0;
    let mut v___x_258_: u8 = 0;
    let mut v___y_260_: u8 = 0;
    let mut v___x_261_: u32 = 0;
    let mut v___x_262_: u8 = 0;
    let mut v___x_263_: u32 = 0;
    let mut v___x_264_: u8 = 0;
    let mut v___x_265_: u32 = 0;
    let mut v___x_266_: u8 = 0;
    let mut v___x_267_: u32 = 0;
    let mut v___x_268_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_265_ = 48;
                v___x_266_ = lean_uint32_dec_le(v___x_265_, v_c_252_);
                if v___x_266_ == 0 {
                    v___y_260_ = v___x_266_;
                    state = 2;
                    continue;
                } else {
                    v___x_267_ = 57;
                    v___x_268_ = lean_uint32_dec_le(v_c_252_, v___x_267_);
                    v___y_260_ = v___x_268_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v___y_254_ == 0 {
                    v___x_255_ = 65;
                    v___x_256_ = lean_uint32_dec_le(v___x_255_, v_c_252_);
                    if v___x_256_ == 0 {
                        return v___x_256_;
                    } else {
                        v___x_257_ = 70;
                        v___x_258_ = lean_uint32_dec_le(v_c_252_, v___x_257_);
                        return v___x_258_;
                    }
                } else {
                    return v___y_254_;
                }
            }
            2 => {
                if v___y_260_ == 0 {
                    v___x_261_ = 97;
                    v___x_262_ = lean_uint32_dec_le(v___x_261_, v_c_252_);
                    if v___x_262_ == 0 {
                        v___y_254_ = v___x_262_;
                        state = 1;
                        continue;
                    } else {
                        v___x_263_ = 102;
                        v___x_264_ = lean_uint32_dec_le(v_c_252_, v___x_263_);
                        v___y_254_ = v___x_264_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___y_260_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_isHexDigit___boxed(
    mut v_c_269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_270_: u32 = 0;
    let mut v_res_271_: u8 = 0;
    let mut v_r_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_270_ = crate::leanh::lean_unbox_uint32(v_c_269_);
    crate::leanh::lean_dec(v_c_269_);
    v_res_271_ = l_Char_isHexDigit(v_c_boxed_270_);
    v_r_272_ = crate::leanh::lean_box((v_res_271_) as usize);
    return v_r_272_;
}
pub unsafe fn l_Char_isAlphanum(mut v_c_273_: u32) -> u8 {
    let mut v___y_275_: u8 = 0;
    let mut v___x_276_: u32 = 0;
    let mut v___x_277_: u8 = 0;
    let mut v___x_278_: u32 = 0;
    let mut v___x_279_: u8 = 0;
    let mut v___x_281_: u32 = 0;
    let mut v___x_282_: u8 = 0;
    let mut v___x_283_: u32 = 0;
    let mut v___x_284_: u8 = 0;
    let mut v___x_285_: u32 = 0;
    let mut v___x_286_: u8 = 0;
    let mut v___x_287_: u32 = 0;
    let mut v___x_288_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_285_ = 65;
                v___x_286_ = lean_uint32_dec_le(v___x_285_, v_c_273_);
                if v___x_286_ == 0 {
                    state = 2;
                    continue;
                } else {
                    v___x_287_ = 90;
                    v___x_288_ = lean_uint32_dec_le(v_c_273_, v___x_287_);
                    if v___x_288_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        return v___x_288_;
                    }
                }
            }
            1 => {
                if v___y_275_ == 0 {
                    v___x_276_ = 48;
                    v___x_277_ = lean_uint32_dec_le(v___x_276_, v_c_273_);
                    if v___x_277_ == 0 {
                        return v___x_277_;
                    } else {
                        v___x_278_ = 57;
                        v___x_279_ = lean_uint32_dec_le(v_c_273_, v___x_278_);
                        return v___x_279_;
                    }
                } else {
                    return v___y_275_;
                }
            }
            2 => {
                v___x_281_ = 97;
                v___x_282_ = lean_uint32_dec_le(v___x_281_, v_c_273_);
                if v___x_282_ == 0 {
                    v___y_275_ = v___x_282_;
                    state = 1;
                    continue;
                } else {
                    v___x_283_ = 122;
                    v___x_284_ = lean_uint32_dec_le(v_c_273_, v___x_283_);
                    v___y_275_ = v___x_284_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Char_isAlphanum___boxed(
    mut v_c_289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_290_: u32 = 0;
    let mut v_res_291_: u8 = 0;
    let mut v_r_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_290_ = crate::leanh::lean_unbox_uint32(v_c_289_);
    crate::leanh::lean_dec(v_c_289_);
    v_res_291_ = l_Char_isAlphanum(v_c_boxed_290_);
    v_r_292_ = crate::leanh::lean_box((v_res_291_) as usize);
    return v_r_292_;
}
pub unsafe fn l_Char_toLower(mut v_c_293_: u32) -> u32 {
    let mut v___x_294_: u32 = 0;
    let mut v___x_295_: u8 = 0;
    v___x_294_ = 65;
    v___x_295_ = lean_uint32_dec_le(v___x_294_, v_c_293_);
    if v___x_295_ == 0 {
        return v_c_293_;
    } else {
        let mut v___x_296_: u32 = 0;
        let mut v___x_297_: u8 = 0;
        v___x_296_ = 90;
        v___x_297_ = lean_uint32_dec_le(v_c_293_, v___x_296_);
        if v___x_297_ == 0 {
            return v_c_293_;
        } else {
            let mut v___x_298_: u32 = 0;
            let mut v___x_299_: u32 = 0;
            v___x_298_ = 32;
            v___x_299_ = lean_uint32_add(v_c_293_, v___x_298_);
            return v___x_299_;
        }
    }
}
pub unsafe fn l_Char_toLower___boxed(
    mut v_c_300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_301_: u32 = 0;
    let mut v_res_302_: u32 = 0;
    let mut v_r_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_301_ = crate::leanh::lean_unbox_uint32(v_c_300_);
    crate::leanh::lean_dec(v_c_300_);
    v_res_302_ = l_Char_toLower(v_c_boxed_301_);
    v_r_303_ = crate::leanh::lean_box_uint32(v_res_302_);
    return v_r_303_;
}
pub unsafe fn l_Char_toUpper(mut v_c_304_: u32) -> u32 {
    let mut v___x_305_: u32 = 0;
    let mut v___x_306_: u8 = 0;
    v___x_305_ = 97;
    v___x_306_ = lean_uint32_dec_le(v___x_305_, v_c_304_);
    if v___x_306_ == 0 {
        return v_c_304_;
    } else {
        let mut v___x_307_: u32 = 0;
        let mut v___x_308_: u8 = 0;
        v___x_307_ = 122;
        v___x_308_ = lean_uint32_dec_le(v_c_304_, v___x_307_);
        if v___x_308_ == 0 {
            return v_c_304_;
        } else {
            let mut v___x_309_: u32 = 0;
            let mut v___x_310_: u32 = 0;
            v___x_309_ = 4294967264;
            v___x_310_ = lean_uint32_add(v_c_304_, v___x_309_);
            return v___x_310_;
        }
    }
}
pub unsafe fn l_Char_toUpper___boxed(
    mut v_c_311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_312_: u32 = 0;
    let mut v_res_313_: u32 = 0;
    let mut v_r_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_312_ = crate::leanh::lean_unbox_uint32(v_c_311_);
    crate::leanh::lean_dec(v_c_311_);
    v_res_313_ = l_Char_toUpper(v_c_boxed_312_);
    v_r_314_ = crate::leanh::lean_box_uint32(v_res_313_);
    return v_r_314_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Char_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_UInt_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Char_instLT = _init_l_Char_instLT();
    crate::leanh::lean_mark_persistent(l_Char_instLT);
    l_Char_instLE = _init_l_Char_instLE();
    crate::leanh::lean_mark_persistent(l_Char_instLE);
    l_Char_instInhabited = _init_l_Char_instInhabited();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Char_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Char_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_UInt_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Div_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Char_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Char_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Char_Basic(builtin);
}

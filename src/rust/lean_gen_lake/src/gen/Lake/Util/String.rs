// Lean compiler output
// Module: Lake.Util.String
// Imports: Init.Data.ToString.Basic Init.Data.UInt.Lemmas Init.Data.String.Basic Init.Data.Nat.Fold Init.Data.String.Length
use crate::r#gen::Init::Data::Nat::Fold::{
    initialize_Init_Data_Nat_Fold, runtime_initialize_Init_Data_Nat_Fold,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Data::String::Length::{
    initialize_Init_Data_String_Length, runtime_initialize_Init_Data_String_Length,
};
use crate::r#gen::Init::Data::ToString::Basic::{
    initialize_Init_Data_ToString_Basic, runtime_initialize_Init_Data_ToString_Basic,
};
use crate::r#gen::Init::Data::UInt::Lemmas::{
    initialize_Init_Data_UInt_Lemmas, runtime_initialize_Init_Data_UInt_Lemmas,
};
use crate::lean_imports_rs::Init::Data::String::Bootstrap::lean_string_push;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::String::PosRaw::lean_string_get_byte_fast;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint8_add, lean_uint64_land, lean_uint64_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint8_to_uint32, lean_uint64_to_uint8,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_mk_empty_byte_array, lean_nat_dec_eq, lean_nat_sub, lean_string_from_utf8_unchecked,
    lean_string_utf8_byte_size, lean_uint8_dec_le,
};
pub static l_Lake_lpadAscii___closed__0_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 1,
        m_capacity: 1,
        m_length: 0,
        m_data: [0],
    };
static mut l_Lake_lpadAscii___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_lpadAscii___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lake_lowerHexUInt64___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_lowerHexUInt64___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lake_lowerHexUInt64___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lake_lowerHexUInt64___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lake_lpadAscii_spec__0(
    mut v_c_216_: u32,
    mut v_x_217_: *mut crate::leanh::LeanObject,
    mut v_x_218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_220_: u8 = 0;
    let mut v_one_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_219_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_220_ = lean_nat_dec_eq(v_x_217_, v_zero_219_);
                if v_isZero_220_ == 1 {
                    crate::leanh::lean_dec(v_x_217_);
                    return v_x_218_;
                } else {
                    v_one_221_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_222_ = lean_nat_sub(v_x_217_, v_one_221_);
                    crate::leanh::lean_dec(v_x_217_);
                    v___x_223_ = lean_string_push(v_x_218_, v_c_216_);
                    v_x_217_ = v_n_222_;
                    v_x_218_ = v___x_223_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lake_lpadAscii_spec__0___boxed(
    mut v_c_225_: *mut crate::leanh::LeanObject,
    mut v_x_226_: *mut crate::leanh::LeanObject,
    mut v_x_227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_228_: u32 = 0;
    let mut v_res_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_228_ = crate::leanh::lean_unbox_uint32(v_c_225_);
    crate::leanh::lean_dec(v_c_225_);
    v_res_229_ =
        l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lake_lpadAscii_spec__0(
            v_c_boxed_228_,
            v_x_226_,
            v_x_227_,
        );
    return v_res_229_;
}
pub unsafe fn l_Lake_lpadAscii(
    mut v_s_231_: *mut crate::leanh::LeanObject,
    mut v_c_232_: u32,
    mut v_len_233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_234_ = l_Lake_lpadAscii___closed__0;
    v___x_235_ = lean_string_utf8_byte_size(v_s_231_);
    v___x_236_ = lean_nat_sub(v_len_233_, v___x_235_);
    v___x_237_ =
        l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lake_lpadAscii_spec__0(
            v_c_232_, v___x_236_, v___x_234_,
        );
    v___x_238_ = lean_string_append(v___x_237_, v_s_231_);
    return v___x_238_;
}
pub unsafe fn l_Lake_lpadAscii___boxed(
    mut v_s_239_: *mut crate::leanh::LeanObject,
    mut v_c_240_: *mut crate::leanh::LeanObject,
    mut v_len_241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_242_: u32 = 0;
    let mut v_res_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_242_ = crate::leanh::lean_unbox_uint32(v_c_240_);
    crate::leanh::lean_dec(v_c_240_);
    v_res_243_ = l_Lake_lpadAscii(v_s_239_, v_c_boxed_242_, v_len_241_);
    crate::leanh::lean_dec(v_len_241_);
    crate::leanh::lean_dec_ref(v_s_239_);
    return v_res_243_;
}
pub unsafe fn l_Lake_rpadAscii(
    mut v_s_244_: *mut crate::leanh::LeanObject,
    mut v_c_245_: u32,
    mut v_len_246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_247_ = lean_string_utf8_byte_size(v_s_244_);
    v___x_248_ = lean_nat_sub(v_len_246_, v___x_247_);
    v___x_249_ =
        l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00Lake_lpadAscii_spec__0(
            v_c_245_, v___x_248_, v_s_244_,
        );
    return v___x_249_;
}
pub unsafe fn l_Lake_rpadAscii___boxed(
    mut v_s_250_: *mut crate::leanh::LeanObject,
    mut v_c_251_: *mut crate::leanh::LeanObject,
    mut v_len_252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_253_: u32 = 0;
    let mut v_res_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_253_ = crate::leanh::lean_unbox_uint32(v_c_251_);
    crate::leanh::lean_dec(v_c_251_);
    v_res_254_ = l_Lake_rpadAscii(v_s_250_, v_c_boxed_253_, v_len_252_);
    crate::leanh::lean_dec(v_len_252_);
    return v_res_254_;
}
pub unsafe fn l_Lake_zpad(
    mut v_n_255_: *mut crate::leanh::LeanObject,
    mut v_len_256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_258_: u32 = 0;
    let mut v___x_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_257_ = l_Nat_reprFast(v_n_255_);
    v___x_258_ = 48;
    v___x_259_ = l_Lake_lpadAscii(v___x_257_, v___x_258_, v_len_256_);
    crate::leanh::lean_dec_ref(v___x_257_);
    return v___x_259_;
}
pub unsafe fn l_Lake_zpad___boxed(
    mut v_n_260_: *mut crate::leanh::LeanObject,
    mut v_len_261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_262_ = l_Lake_zpad(v_n_260_, v_len_261_);
    crate::leanh::lean_dec(v_len_261_);
    return v_res_262_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___redArg(
    mut v_s_263_: *mut crate::leanh::LeanObject,
    mut v_n_264_: *mut crate::leanh::LeanObject,
    mut v_i_265_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_267_: u8 = 0;
    let mut v_one_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_271_: u8 = 0;
    let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_274_: u8 = 0;
    let mut v___x_275_: u8 = 0;
    let mut v___x_276_: u8 = 0;
    let mut v___x_277_: u8 = 0;
    let mut v___x_278_: u8 = 0;
    let mut v___x_279_: u8 = 0;
    let mut v___x_280_: u8 = 0;
    let mut v___x_281_: u8 = 0;
    let mut v___x_282_: u8 = 0;
    let mut v___x_283_: u8 = 0;
    let mut v___x_284_: u8 = 0;
    let mut v___x_285_: u8 = 0;
    let mut v___x_286_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_266_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_267_ = lean_nat_dec_eq(v_i_265_, v_zero_266_);
                if v_isZero_267_ == 1 {
                    crate::leanh::lean_dec(v_i_265_);
                    return v_isZero_267_;
                } else {
                    v_one_268_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_269_ = lean_nat_sub(v_i_265_, v_one_268_);
                    v___x_273_ = lean_nat_sub(v_n_264_, v_i_265_);
                    crate::leanh::lean_dec(v_i_265_);
                    v_c_274_ = lean_string_get_byte_fast(v_s_263_, v___x_273_);
                    v___x_275_ = 57;
                    v___x_276_ = lean_uint8_dec_le(v_c_274_, v___x_275_);
                    if v___x_276_ == 0 {
                        v___x_277_ = 102;
                        v___x_278_ = lean_uint8_dec_le(v_c_274_, v___x_277_);
                        if v___x_278_ == 0 {
                            v___x_279_ = 70;
                            v___x_280_ = lean_uint8_dec_le(v_c_274_, v___x_279_);
                            if v___x_280_ == 0 {
                                crate::leanh::lean_dec(v_n_269_);
                                return v___x_280_;
                            } else {
                                v___x_281_ = 65;
                                v___x_282_ = lean_uint8_dec_le(v___x_281_, v_c_274_);
                                v___y_271_ = v___x_282_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_283_ = 97;
                            v___x_284_ = lean_uint8_dec_le(v___x_283_, v_c_274_);
                            v___y_271_ = v___x_284_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_285_ = 48;
                        v___x_286_ = lean_uint8_dec_le(v___x_285_, v_c_274_);
                        v___y_271_ = v___x_286_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_271_ == 0 {
                    crate::leanh::lean_dec(v_n_269_);
                    return v___y_271_;
                } else {
                    v_i_265_ = v_n_269_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___redArg___boxed(
    mut v_s_287_: *mut crate::leanh::LeanObject,
    mut v_n_288_: *mut crate::leanh::LeanObject,
    mut v_i_289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_290_: u8 = 0;
    let mut v_r_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_290_ =
        l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___redArg(
            v_s_287_, v_n_288_, v_i_289_,
        );
    crate::leanh::lean_dec(v_n_288_);
    crate::leanh::lean_dec_ref(v_s_287_);
    v_r_291_ = crate::leanh::lean_box((v_res_290_) as usize);
    return v_r_291_;
}
pub unsafe fn l_Lake_isHex(mut v_s_292_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: u8 = 0;
    v___x_293_ = lean_string_utf8_byte_size(v_s_292_);
    v___x_294_ =
        l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___redArg(
            v_s_292_, v___x_293_, v___x_293_,
        );
    return v___x_294_;
}
pub unsafe fn l_Lake_isHex___boxed(
    mut v_s_295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_296_: u8 = 0;
    let mut v_r_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_296_ = l_Lake_isHex(v_s_295_);
    crate::leanh::lean_dec_ref(v_s_295_);
    v_r_297_ = crate::leanh::lean_box((v_res_296_) as usize);
    return v_r_297_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0(
    mut v_s_298_: *mut crate::leanh::LeanObject,
    mut v_n_299_: *mut crate::leanh::LeanObject,
    mut v_i_300_: *mut crate::leanh::LeanObject,
    mut v_a_301_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_302_: u8 = 0;
    v___x_302_ =
        l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___redArg(
            v_s_298_, v_n_299_, v_i_300_,
        );
    return v___x_302_;
}
pub unsafe fn l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0___boxed(
    mut v_s_303_: *mut crate::leanh::LeanObject,
    mut v_n_304_: *mut crate::leanh::LeanObject,
    mut v_i_305_: *mut crate::leanh::LeanObject,
    mut v_a_306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_307_: u8 = 0;
    let mut v_r_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_307_ = l___private_Init_Data_Nat_Fold_0__Nat_allTR_loop___at___00Lake_isHex_spec__0(
        v_s_303_, v_n_304_, v_i_305_, v_a_306_,
    );
    crate::leanh::lean_dec(v_n_304_);
    crate::leanh::lean_dec_ref(v_s_303_);
    v_r_308_ = crate::leanh::lean_box((v_res_307_) as usize);
    return v_r_308_;
}
pub unsafe fn l___private_Lake_Util_String_0__Lake_lowerHexByte(mut v_n_309_: u8) -> u8 {
    let mut v___x_310_: u8 = 0;
    let mut v___x_311_: u8 = 0;
    v___x_310_ = 9;
    v___x_311_ = lean_uint8_dec_le(v_n_309_, v___x_310_);
    if v___x_311_ == 0 {
        let mut v___x_312_: u8 = 0;
        let mut v___x_313_: u8 = 0;
        v___x_312_ = 87;
        v___x_313_ = lean_uint8_add(v_n_309_, v___x_312_);
        return v___x_313_;
    } else {
        let mut v___x_314_: u8 = 0;
        let mut v___x_315_: u8 = 0;
        v___x_314_ = 48;
        v___x_315_ = lean_uint8_add(v_n_309_, v___x_314_);
        return v___x_315_;
    }
}
pub unsafe fn l___private_Lake_Util_String_0__Lake_lowerHexByte___boxed(
    mut v_n_316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_317_: u8 = 0;
    let mut v_res_318_: u8 = 0;
    let mut v_r_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_317_ = (crate::leanh::lean_unbox(v_n_316_) as u8);
    v_res_318_ = l___private_Lake_Util_String_0__Lake_lowerHexByte(v_n_boxed_317_);
    v_r_319_ = crate::leanh::lean_box((v_res_318_) as usize);
    return v_r_319_;
}
pub unsafe fn l___private_Lake_Util_String_0__Lake_lowerHexChar(mut v_n_320_: u8) -> u32 {
    let mut v___x_321_: u8 = 0;
    let mut v___x_322_: u32 = 0;
    v___x_321_ = l___private_Lake_Util_String_0__Lake_lowerHexByte(v_n_320_);
    v___x_322_ = lean_uint8_to_uint32(v___x_321_);
    return v___x_322_;
}
pub unsafe fn l___private_Lake_Util_String_0__Lake_lowerHexChar___boxed(
    mut v_n_323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_324_: u8 = 0;
    let mut v_res_325_: u32 = 0;
    let mut v_r_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_324_ = (crate::leanh::lean_unbox(v_n_323_) as u8);
    v_res_325_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v_n_boxed_324_);
    v_r_326_ = crate::leanh::lean_box_uint32(v_res_325_);
    return v_r_326_;
}
pub unsafe fn _init_l_Lake_lowerHexUInt64___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_327_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_328_ = lean_mk_empty_byte_array(v___x_327_);
    return v___x_328_;
}
pub unsafe fn _init_l_Lake_lowerHexUInt64___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_329_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_lowerHexUInt64___closed__0),
        core::ptr::addr_of_mut!(l_Lake_lowerHexUInt64___closed__0_once),
        _init_l_Lake_lowerHexUInt64___closed__0,
    );
    v___x_330_ = lean_string_from_utf8_unchecked(v___x_329_);
    return v___x_330_;
}
pub unsafe fn l_Lake_lowerHexUInt64(mut v_n_331_: u64) -> *mut crate::leanh::LeanObject {
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: u64 = 0;
    let mut v___x_334_: u64 = 0;
    let mut v___x_335_: u64 = 0;
    let mut v___x_336_: u64 = 0;
    let mut v___x_337_: u8 = 0;
    let mut v___x_338_: u32 = 0;
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_340_: u64 = 0;
    let mut v___x_341_: u64 = 0;
    let mut v___x_342_: u64 = 0;
    let mut v___x_343_: u8 = 0;
    let mut v___x_344_: u32 = 0;
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: u64 = 0;
    let mut v___x_347_: u64 = 0;
    let mut v___x_348_: u64 = 0;
    let mut v___x_349_: u8 = 0;
    let mut v___x_350_: u32 = 0;
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: u64 = 0;
    let mut v___x_353_: u64 = 0;
    let mut v___x_354_: u64 = 0;
    let mut v___x_355_: u8 = 0;
    let mut v___x_356_: u32 = 0;
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: u64 = 0;
    let mut v___x_359_: u64 = 0;
    let mut v___x_360_: u64 = 0;
    let mut v___x_361_: u8 = 0;
    let mut v___x_362_: u32 = 0;
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: u64 = 0;
    let mut v___x_365_: u64 = 0;
    let mut v___x_366_: u64 = 0;
    let mut v___x_367_: u8 = 0;
    let mut v___x_368_: u32 = 0;
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: u64 = 0;
    let mut v___x_371_: u64 = 0;
    let mut v___x_372_: u64 = 0;
    let mut v___x_373_: u8 = 0;
    let mut v___x_374_: u32 = 0;
    let mut v___x_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: u64 = 0;
    let mut v___x_377_: u64 = 0;
    let mut v___x_378_: u64 = 0;
    let mut v___x_379_: u8 = 0;
    let mut v___x_380_: u32 = 0;
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: u64 = 0;
    let mut v___x_383_: u64 = 0;
    let mut v___x_384_: u64 = 0;
    let mut v___x_385_: u8 = 0;
    let mut v___x_386_: u32 = 0;
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: u64 = 0;
    let mut v___x_389_: u64 = 0;
    let mut v___x_390_: u64 = 0;
    let mut v___x_391_: u8 = 0;
    let mut v___x_392_: u32 = 0;
    let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: u64 = 0;
    let mut v___x_395_: u64 = 0;
    let mut v___x_396_: u64 = 0;
    let mut v___x_397_: u8 = 0;
    let mut v___x_398_: u32 = 0;
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: u64 = 0;
    let mut v___x_401_: u64 = 0;
    let mut v___x_402_: u64 = 0;
    let mut v___x_403_: u8 = 0;
    let mut v___x_404_: u32 = 0;
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: u64 = 0;
    let mut v___x_407_: u64 = 0;
    let mut v___x_408_: u64 = 0;
    let mut v___x_409_: u8 = 0;
    let mut v___x_410_: u32 = 0;
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: u64 = 0;
    let mut v___x_413_: u64 = 0;
    let mut v___x_414_: u64 = 0;
    let mut v___x_415_: u8 = 0;
    let mut v___x_416_: u32 = 0;
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: u64 = 0;
    let mut v___x_419_: u64 = 0;
    let mut v___x_420_: u64 = 0;
    let mut v___x_421_: u8 = 0;
    let mut v___x_422_: u32 = 0;
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: u64 = 0;
    let mut v___x_425_: u8 = 0;
    let mut v___x_426_: u32 = 0;
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_332_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lake_lowerHexUInt64___closed__1),
        core::ptr::addr_of_mut!(l_Lake_lowerHexUInt64___closed__1_once),
        _init_l_Lake_lowerHexUInt64___closed__1,
    );
    v___x_333_ = 60u64;
    v___x_334_ = lean_uint64_shift_right(v_n_331_, v___x_333_);
    v___x_335_ = 15u64;
    v___x_336_ = lean_uint64_land(v___x_334_, v___x_335_);
    v___x_337_ = lean_uint64_to_uint8(v___x_336_);
    v___x_338_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_337_);
    v___x_339_ = lean_string_push(v___x_332_, v___x_338_);
    v___x_340_ = 56u64;
    v___x_341_ = lean_uint64_shift_right(v_n_331_, v___x_340_);
    v___x_342_ = lean_uint64_land(v___x_341_, v___x_335_);
    v___x_343_ = lean_uint64_to_uint8(v___x_342_);
    v___x_344_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_343_);
    v___x_345_ = lean_string_push(v___x_339_, v___x_344_);
    v___x_346_ = 52u64;
    v___x_347_ = lean_uint64_shift_right(v_n_331_, v___x_346_);
    v___x_348_ = lean_uint64_land(v___x_347_, v___x_335_);
    v___x_349_ = lean_uint64_to_uint8(v___x_348_);
    v___x_350_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_349_);
    v___x_351_ = lean_string_push(v___x_345_, v___x_350_);
    v___x_352_ = 48u64;
    v___x_353_ = lean_uint64_shift_right(v_n_331_, v___x_352_);
    v___x_354_ = lean_uint64_land(v___x_353_, v___x_335_);
    v___x_355_ = lean_uint64_to_uint8(v___x_354_);
    v___x_356_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_355_);
    v___x_357_ = lean_string_push(v___x_351_, v___x_356_);
    v___x_358_ = 44u64;
    v___x_359_ = lean_uint64_shift_right(v_n_331_, v___x_358_);
    v___x_360_ = lean_uint64_land(v___x_359_, v___x_335_);
    v___x_361_ = lean_uint64_to_uint8(v___x_360_);
    v___x_362_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_361_);
    v___x_363_ = lean_string_push(v___x_357_, v___x_362_);
    v___x_364_ = 40u64;
    v___x_365_ = lean_uint64_shift_right(v_n_331_, v___x_364_);
    v___x_366_ = lean_uint64_land(v___x_365_, v___x_335_);
    v___x_367_ = lean_uint64_to_uint8(v___x_366_);
    v___x_368_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_367_);
    v___x_369_ = lean_string_push(v___x_363_, v___x_368_);
    v___x_370_ = 36u64;
    v___x_371_ = lean_uint64_shift_right(v_n_331_, v___x_370_);
    v___x_372_ = lean_uint64_land(v___x_371_, v___x_335_);
    v___x_373_ = lean_uint64_to_uint8(v___x_372_);
    v___x_374_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_373_);
    v___x_375_ = lean_string_push(v___x_369_, v___x_374_);
    v___x_376_ = 32u64;
    v___x_377_ = lean_uint64_shift_right(v_n_331_, v___x_376_);
    v___x_378_ = lean_uint64_land(v___x_377_, v___x_335_);
    v___x_379_ = lean_uint64_to_uint8(v___x_378_);
    v___x_380_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_379_);
    v___x_381_ = lean_string_push(v___x_375_, v___x_380_);
    v___x_382_ = 28u64;
    v___x_383_ = lean_uint64_shift_right(v_n_331_, v___x_382_);
    v___x_384_ = lean_uint64_land(v___x_383_, v___x_335_);
    v___x_385_ = lean_uint64_to_uint8(v___x_384_);
    v___x_386_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_385_);
    v___x_387_ = lean_string_push(v___x_381_, v___x_386_);
    v___x_388_ = 24u64;
    v___x_389_ = lean_uint64_shift_right(v_n_331_, v___x_388_);
    v___x_390_ = lean_uint64_land(v___x_389_, v___x_335_);
    v___x_391_ = lean_uint64_to_uint8(v___x_390_);
    v___x_392_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_391_);
    v___x_393_ = lean_string_push(v___x_387_, v___x_392_);
    v___x_394_ = 20u64;
    v___x_395_ = lean_uint64_shift_right(v_n_331_, v___x_394_);
    v___x_396_ = lean_uint64_land(v___x_395_, v___x_335_);
    v___x_397_ = lean_uint64_to_uint8(v___x_396_);
    v___x_398_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_397_);
    v___x_399_ = lean_string_push(v___x_393_, v___x_398_);
    v___x_400_ = 16u64;
    v___x_401_ = lean_uint64_shift_right(v_n_331_, v___x_400_);
    v___x_402_ = lean_uint64_land(v___x_401_, v___x_335_);
    v___x_403_ = lean_uint64_to_uint8(v___x_402_);
    v___x_404_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_403_);
    v___x_405_ = lean_string_push(v___x_399_, v___x_404_);
    v___x_406_ = 12u64;
    v___x_407_ = lean_uint64_shift_right(v_n_331_, v___x_406_);
    v___x_408_ = lean_uint64_land(v___x_407_, v___x_335_);
    v___x_409_ = lean_uint64_to_uint8(v___x_408_);
    v___x_410_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_409_);
    v___x_411_ = lean_string_push(v___x_405_, v___x_410_);
    v___x_412_ = 8u64;
    v___x_413_ = lean_uint64_shift_right(v_n_331_, v___x_412_);
    v___x_414_ = lean_uint64_land(v___x_413_, v___x_335_);
    v___x_415_ = lean_uint64_to_uint8(v___x_414_);
    v___x_416_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_415_);
    v___x_417_ = lean_string_push(v___x_411_, v___x_416_);
    v___x_418_ = 4u64;
    v___x_419_ = lean_uint64_shift_right(v_n_331_, v___x_418_);
    v___x_420_ = lean_uint64_land(v___x_419_, v___x_335_);
    v___x_421_ = lean_uint64_to_uint8(v___x_420_);
    v___x_422_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_421_);
    v___x_423_ = lean_string_push(v___x_417_, v___x_422_);
    v___x_424_ = lean_uint64_land(v_n_331_, v___x_335_);
    v___x_425_ = lean_uint64_to_uint8(v___x_424_);
    v___x_426_ = l___private_Lake_Util_String_0__Lake_lowerHexChar(v___x_425_);
    v___x_427_ = lean_string_push(v___x_423_, v___x_426_);
    return v___x_427_;
}
pub unsafe fn l_Lake_lowerHexUInt64___boxed(
    mut v_n_428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_boxed_429_: u64 = 0;
    let mut v_res_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_n_boxed_429_ = crate::leanh::lean_unbox_uint64(v_n_428_);
    crate::leanh::lean_dec_ref(v_n_428_);
    v_res_430_ = l_Lake_lowerHexUInt64(v_n_boxed_429_);
    return v_res_430_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_String(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ToString_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Fold(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Length(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_String(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_String(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ToString_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Fold(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Length(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_String(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_String(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Util_String(builtin);
}

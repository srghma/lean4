// Lean compiler output
// Module: Init.Data.String.Bootstrap
// Imports: Init.Data.ByteArray.Bootstrap Init.Data.Char.Basic
use crate::ffi::{
    lean_string_any, lean_string_append, lean_string_capitalize, lean_string_contains,
    lean_string_drop, lean_string_dropright, lean_string_foldl, lean_string_front,
    lean_string_get_byte_fast, lean_string_intercalate, lean_string_isempty,
    lean_string_isprefixof, lean_string_length, lean_string_mk, lean_string_nextwhile,
    lean_string_offsetofpos, lean_string_pos_min, lean_string_pos_sub, lean_string_posof,
    lean_string_push, lean_string_pushn, lean_string_trim, lean_string_utf8_at_end,
    lean_string_utf8_extract, lean_string_utf8_get, lean_string_utf8_next, lean_substring_all,
    lean_substring_beq, lean_substring_drop, lean_substring_extract, lean_substring_front,
    lean_substring_get, lean_substring_isempty, lean_substring_prev, lean_substring_takewhile,
    lean_substring_tostring,
};
use crate::r#gen::Init::Data::ByteArray::Bootstrap::{
    initialize_Init_Data_ByteArray_Bootstrap, runtime_initialize_Init_Data_ByteArray_Bootstrap,
};
use crate::r#gen::Init::Data::Char::Basic::{
    initialize_Init_Data_Char_Basic, runtime_initialize_Init_Data_Char_Basic,
};
pub static mut l_String_instOfNatRaw: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_String_instInhabited___closed__0_value: leanh::LeanStringObject<1> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_String_instInhabited___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_instInhabited___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_String_instInhabited: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_instInhabited___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn _init_l_String_instOfNatRaw() -> *mut leanh::LeanObject {
    let mut v___x_209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_209_ = leanh::lean_unsigned_to_nat(0);
    return v___x_209_;
}
pub unsafe fn l_String_push___boxed(
    mut v_a_00___x40___internal___hyg_214_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_215_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_2__boxed_216_: u32 = 0;
    let mut v_res_217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_2__boxed_216_ =
        leanh::lean_unbox_uint32(v_a_00___x40___internal___hyg_215_);
    leanh::lean_dec(v_a_00___x40___internal___hyg_215_);
    v_res_217_ = lean_string_push(
        v_a_00___x40___internal___hyg_214_,
        v_a_00___x40___internal___hyg_2__boxed_216_,
    );
    return v_res_217_;
}
pub unsafe fn l_String_singleton(mut v_c_218_: u32) -> *mut leanh::LeanObject {
    let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_219_ = l_String_instInhabited___closed__0;
    v___x_220_ = lean_string_push(v___x_219_, v_c_218_);
    return v___x_220_;
}
pub unsafe fn l_String_singleton___boxed(
    mut v_c_221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_222_: u32 = 0;
    let mut v_res_223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_222_ = leanh::lean_unbox_uint32(v_c_221_);
    leanh::lean_dec(v_c_221_);
    v_res_223_ = l_String_singleton(v_c_boxed_222_);
    return v_res_223_;
}
pub unsafe fn l_String_Internal_posOf___boxed(
    mut v_s_226_: *mut leanh::LeanObject,
    mut v_c_227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_228_: u32 = 0;
    let mut v_res_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_228_ = leanh::lean_unbox_uint32(v_c_227_);
    leanh::lean_dec(v_c_227_);
    v_res_229_ = lean_string_posof(v_s_226_, v_c_boxed_228_);
    return v_res_229_;
}
pub unsafe fn l_String_Internal_offsetOfPos___boxed(
    mut v_s_232_: *mut leanh::LeanObject,
    mut v_pos_233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_234_ = lean_string_offsetofpos(v_s_232_, v_pos_233_);
    return v_res_234_;
}
pub unsafe fn l_String_Internal_extract___boxed(
    mut v_a_00___x40___internal___hyg_238_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_239_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_241_ = lean_string_utf8_extract(
        v_a_00___x40___internal___hyg_238_,
        v_a_00___x40___internal___hyg_239_,
        v_a_00___x40___internal___hyg_240_,
    );
    leanh::lean_dec(v_a_00___x40___internal___hyg_240_);
    leanh::lean_dec(v_a_00___x40___internal___hyg_239_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_238_);
    return v_res_241_;
}
pub unsafe fn l_String_Internal_length___boxed(
    mut v_a_00___x40___internal___hyg_243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_244_ = lean_string_length(v_a_00___x40___internal___hyg_243_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_243_);
    return v_res_244_;
}
pub unsafe fn l_String_Internal_pushn___boxed(
    mut v_s_248_: *mut leanh::LeanObject,
    mut v_c_249_: *mut leanh::LeanObject,
    mut v_n_250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_251_: u32 = 0;
    let mut v_res_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_251_ = leanh::lean_unbox_uint32(v_c_249_);
    leanh::lean_dec(v_c_249_);
    v_res_252_ = lean_string_pushn(v_s_248_, v_c_boxed_251_, v_n_250_);
    return v_res_252_;
}
pub unsafe fn l_String_Internal_append___boxed(
    mut v_a_00___x40___internal___hyg_255_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_257_ = lean_string_append(
        v_a_00___x40___internal___hyg_255_,
        v_a_00___x40___internal___hyg_256_,
    );
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_256_);
    return v_res_257_;
}
pub unsafe fn l_String_Internal_next___boxed(
    mut v_s_260_: *mut leanh::LeanObject,
    mut v_p_261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_262_ = lean_string_utf8_next(v_s_260_, v_p_261_);
    leanh::lean_dec(v_p_261_);
    leanh::lean_dec_ref(v_s_260_);
    return v_res_262_;
}
pub unsafe fn l_String_Internal_isEmpty___boxed(
    mut v_s_264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_265_: u8 = 0;
    let mut v_r_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_265_ = lean_string_isempty(v_s_264_);
    v_r_266_ = leanh::lean_box((v_res_265_) as usize);
    return v_r_266_;
}
pub unsafe fn l_String_Internal_foldl___boxed(
    mut v_f_270_: *mut leanh::LeanObject,
    mut v_init_271_: *mut leanh::LeanObject,
    mut v_s_272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_273_ = lean_string_foldl(v_f_270_, v_init_271_, v_s_272_);
    return v_res_273_;
}
pub unsafe fn l_String_Internal_isPrefixOf___boxed(
    mut v_p_276_: *mut leanh::LeanObject,
    mut v_s_277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_278_: u8 = 0;
    let mut v_r_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_278_ = lean_string_isprefixof(v_p_276_, v_s_277_);
    v_r_279_ = leanh::lean_box((v_res_278_) as usize);
    return v_r_279_;
}
pub unsafe fn l_String_Internal_any___boxed(
    mut v_s_282_: *mut leanh::LeanObject,
    mut v_p_283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_284_: u8 = 0;
    let mut v_r_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_284_ = lean_string_any(v_s_282_, v_p_283_);
    v_r_285_ = leanh::lean_box((v_res_284_) as usize);
    return v_r_285_;
}
pub unsafe fn l_String_Internal_contains___boxed(
    mut v_s_288_: *mut leanh::LeanObject,
    mut v_c_289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_290_: u32 = 0;
    let mut v_res_291_: u8 = 0;
    let mut v_r_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_290_ = leanh::lean_unbox_uint32(v_c_289_);
    leanh::lean_dec(v_c_289_);
    v_res_291_ = lean_string_contains(v_s_288_, v_c_boxed_290_);
    v_r_292_ = leanh::lean_box((v_res_291_) as usize);
    return v_r_292_;
}
pub unsafe fn l_String_Internal_get___boxed(
    mut v_s_295_: *mut leanh::LeanObject,
    mut v_p_296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_297_: u32 = 0;
    let mut v_r_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_297_ = lean_string_utf8_get(v_s_295_, v_p_296_);
    leanh::lean_dec(v_p_296_);
    leanh::lean_dec_ref(v_s_295_);
    v_r_298_ = leanh::lean_box_uint32(v_res_297_);
    return v_r_298_;
}
pub unsafe fn l_String_Internal_capitalize___boxed(
    mut v_s_300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_301_ = lean_string_capitalize(v_s_300_);
    return v_res_301_;
}
pub unsafe fn l_String_Internal_atEnd___boxed(
    mut v_a_00___x40___internal___hyg_304_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_306_: u8 = 0;
    let mut v_r_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_306_ = lean_string_utf8_at_end(
        v_a_00___x40___internal___hyg_304_,
        v_a_00___x40___internal___hyg_305_,
    );
    leanh::lean_dec(v_a_00___x40___internal___hyg_305_);
    leanh::lean_dec_ref(v_a_00___x40___internal___hyg_304_);
    v_r_307_ = leanh::lean_box((v_res_306_) as usize);
    return v_r_307_;
}
pub unsafe fn l_String_Internal_nextWhile___boxed(
    mut v_s_311_: *mut leanh::LeanObject,
    mut v_p_312_: *mut leanh::LeanObject,
    mut v_i_313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_314_ = lean_string_nextwhile(v_s_311_, v_p_312_, v_i_313_);
    return v_res_314_;
}
pub unsafe fn l_String_Internal_trim___boxed(
    mut v_s_316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_317_ = lean_string_trim(v_s_316_);
    return v_res_317_;
}
pub unsafe fn l_String_Internal_intercalate___boxed(
    mut v_s_320_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_322_ = lean_string_intercalate(v_s_320_, v_a_00___x40___internal___hyg_321_);
    return v_res_322_;
}
pub unsafe fn l_String_Internal_front___boxed(
    mut v_s_324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_325_: u32 = 0;
    let mut v_r_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_325_ = lean_string_front(v_s_324_);
    v_r_326_ = leanh::lean_box_uint32(v_res_325_);
    return v_r_326_;
}
pub unsafe fn l_String_Internal_drop___boxed(
    mut v_s_329_: *mut leanh::LeanObject,
    mut v_n_330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_331_ = lean_string_drop(v_s_329_, v_n_330_);
    return v_res_331_;
}
pub unsafe fn l_String_Internal_dropRight___boxed(
    mut v_s_334_: *mut leanh::LeanObject,
    mut v_n_335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_336_ = lean_string_dropright(v_s_334_, v_n_335_);
    return v_res_336_;
}
pub unsafe fn l_String_Internal_getUTF8Byte___boxed(
    mut v_s_340_: *mut leanh::LeanObject,
    mut v_n_341_: *mut leanh::LeanObject,
    mut v_h_342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_343_: u8 = 0;
    let mut v_r_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_343_ = lean_string_get_byte_fast(v_s_340_, v_n_341_);
    leanh::lean_dec_ref(v_s_340_);
    v_r_344_ = leanh::lean_box((v_res_343_) as usize);
    return v_r_344_;
}
pub unsafe fn l_String_mk___boxed(
    mut v_data_346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_347_ = lean_string_mk(v_data_346_);
    return v_res_347_;
}
pub unsafe fn l_List_asString(
    mut v_s_348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_349_ = lean_string_mk(v_s_348_);
    return v___x_349_;
}
pub unsafe fn l_Substring_Raw_Internal_toString___boxed(
    mut v_a_00___x40___internal___hyg_351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_352_ = lean_substring_tostring(v_a_00___x40___internal___hyg_351_);
    return v_res_352_;
}
pub unsafe fn l_Substring_Raw_Internal_drop___boxed(
    mut v_a_00___x40___internal___hyg_355_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_357_ = lean_substring_drop(
        v_a_00___x40___internal___hyg_355_,
        v_a_00___x40___internal___hyg_356_,
    );
    return v_res_357_;
}
pub unsafe fn l_Substring_Raw_Internal_front___boxed(
    mut v_s_359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_360_: u32 = 0;
    let mut v_r_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_360_ = lean_substring_front(v_s_359_);
    v_r_361_ = leanh::lean_box_uint32(v_res_360_);
    return v_r_361_;
}
pub unsafe fn l_Substring_Raw_Internal_takeWhile___boxed(
    mut v_a_00___x40___internal___hyg_364_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_366_ = lean_substring_takewhile(
        v_a_00___x40___internal___hyg_364_,
        v_a_00___x40___internal___hyg_365_,
    );
    return v_res_366_;
}
pub unsafe fn l_Substring_Raw_Internal_extract___boxed(
    mut v_a_00___x40___internal___hyg_370_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_371_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_373_ = lean_substring_extract(
        v_a_00___x40___internal___hyg_370_,
        v_a_00___x40___internal___hyg_371_,
        v_a_00___x40___internal___hyg_372_,
    );
    return v_res_373_;
}
pub unsafe fn l_Substring_Raw_Internal_all___boxed(
    mut v_s_376_: *mut leanh::LeanObject,
    mut v_p_377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_378_: u8 = 0;
    let mut v_r_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_378_ = lean_substring_all(v_s_376_, v_p_377_);
    v_r_379_ = leanh::lean_box((v_res_378_) as usize);
    return v_r_379_;
}
pub unsafe fn l_Substring_Raw_Internal_beq___boxed(
    mut v_ss1_382_: *mut leanh::LeanObject,
    mut v_ss2_383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_384_: u8 = 0;
    let mut v_r_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_384_ = lean_substring_beq(v_ss1_382_, v_ss2_383_);
    v_r_385_ = leanh::lean_box((v_res_384_) as usize);
    return v_r_385_;
}
pub unsafe fn l_Substring_Raw_Internal_isEmpty___boxed(
    mut v_ss_387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_388_: u8 = 0;
    let mut v_r_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_388_ = lean_substring_isempty(v_ss_387_);
    v_r_389_ = leanh::lean_box((v_res_388_) as usize);
    return v_r_389_;
}
pub unsafe fn l_Substring_Raw_Internal_get___boxed(
    mut v_a_00___x40___internal___hyg_392_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_394_: u32 = 0;
    let mut v_r_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_394_ = lean_substring_get(
        v_a_00___x40___internal___hyg_392_,
        v_a_00___x40___internal___hyg_393_,
    );
    v_r_395_ = leanh::lean_box_uint32(v_res_394_);
    return v_r_395_;
}
pub unsafe fn l_Substring_Raw_Internal_prev___boxed(
    mut v_a_00___x40___internal___hyg_398_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_400_ = lean_substring_prev(
        v_a_00___x40___internal___hyg_398_,
        v_a_00___x40___internal___hyg_399_,
    );
    return v_res_400_;
}
pub unsafe fn l_String_Pos_Raw_Internal_sub___boxed(
    mut v_a_00___x40___internal___hyg_403_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_405_ = lean_string_pos_sub(
        v_a_00___x40___internal___hyg_403_,
        v_a_00___x40___internal___hyg_404_,
    );
    return v_res_405_;
}
pub unsafe fn l_String_Pos_Raw_Internal_min___boxed(
    mut v_p_u2081_408_: *mut leanh::LeanObject,
    mut v_p_u2082_409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_410_ = lean_string_pos_min(v_p_u2081_408_, v_p_u2082_409_);
    return v_res_410_;
}
pub unsafe fn l_Char_toString(mut v_c_411_: u32) -> *mut leanh::LeanObject {
    let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_412_ = l_String_instInhabited___closed__0;
    v___x_413_ = lean_string_push(v___x_412_, v_c_411_);
    return v___x_413_;
}
pub unsafe fn l_Char_toString___boxed(
    mut v_c_414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_415_: u32 = 0;
    let mut v_res_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_415_ = leanh::lean_unbox_uint32(v_c_414_);
    leanh::lean_dec(v_c_414_);
    v_res_416_ = l_Char_toString(v_c_boxed_415_);
    return v_res_416_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Bootstrap(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_ByteArray_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Char_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_String_instOfNatRaw = _init_l_String_instOfNatRaw();
    leanh::lean_mark_persistent(l_String_instOfNatRaw);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Bootstrap(
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
pub unsafe fn initialize_Init_Data_String_Bootstrap(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_ByteArray_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Char_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Bootstrap(builtin);
}
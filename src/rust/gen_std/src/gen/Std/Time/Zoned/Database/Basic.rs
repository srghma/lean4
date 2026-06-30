// Lean compiler output
// Module: Std.Time.Zoned.Database.Basic
// Imports: Std.Time.Zoned.ZoneRules Std.Time.Zoned.Database.TzIf
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_nat_add, lean_nat_dec_lt, lean_nat_to_int, lean_string_append,
    lean_uint8_to_nat, lean_uint32_to_nat,
};
use crate::r#gen::Init::Data::Int::Basic::l_Int_instInhabited;
use crate::r#gen::Init::Data::Rat::Basic::l_Rat_ofInt;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::l_instInhabitedUInt8;
use crate::r#gen::Std::Time::Zoned::Database::TzIf::{
    initialize_Std_Time_Zoned_Database_TzIf, runtime_initialize_Std_Time_Zoned_Database_TzIf,
};
use crate::r#gen::Std::Time::Zoned::Offset::l_Std_Time_TimeZone_Offset_toIsoString;
use crate::r#gen::Std::Time::Zoned::ZoneRules::{
    initialize_Std_Time_Zoned_ZoneRules, l_Std_Time_TimeZone_instInhabitedLocalTimeType_default,
    runtime_initialize_Std_Time_Zoned_ZoneRules,
};
pub static l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__0_value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [99, 97, 110, 110, 111, 116, 32, 99, 111, 110, 118, 101, 114, 116, 32, 116, 114, 97, 110, 115, 105, 116, 105, 111, 110, 32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__1_value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [32, 111, 102, 32, 116, 104, 101, 32, 102, 105, 108, 101, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg___closed__0_value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [99, 97, 110, 110, 111, 116, 32, 99, 111, 110, 118, 101, 114, 116, 32, 108, 111, 99, 97, 108, 32, 116, 105, 109, 101, 32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_convertTZifV1___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Std_Time_TimeZone_convertTZifV1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_convertTZifV1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_TimeZone_convertTZifV1___closed__1_value: leanh::LeanStringObject<23> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            101, 109, 112, 116, 121, 32, 116, 114, 97, 110, 115, 105, 116, 105, 111, 110, 115, 32,
            102, 111, 114, 32, 0,
        ],
    };
static mut l_Std_Time_TimeZone_convertTZifV1___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_TimeZone_convertTZifV1___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_Time_TimeZone_convertWall(mut v_x_238_: u8) -> u8 {
    if v_x_238_ == 0 {
        let mut v___x_239_: u8 = 0;
        v___x_239_ = 0;
        return v___x_239_;
    } else {
        let mut v___x_240_: u8 = 0;
        v___x_240_ = 1;
        return v___x_240_;
    }
}
pub unsafe fn l_Std_Time_TimeZone_convertWall___boxed(
    mut v_x_241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_18__boxed_242_: u8 = 0;
    let mut v_res_243_: u8 = 0;
    let mut v_r_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_18__boxed_242_ = (leanh::lean_unbox(v_x_241_) as u8);
    v_res_243_ = l_Std_Time_TimeZone_convertWall(v_x_18__boxed_242_);
    v_r_244_ = leanh::lean_box((v_res_243_) as usize);
    return v_r_244_;
}
pub unsafe fn l_Std_Time_TimeZone_convertUt(mut v_x_245_: u8) -> u8 {
    if v_x_245_ == 0 {
        let mut v___x_246_: u8 = 0;
        v___x_246_ = 1;
        return v___x_246_;
    } else {
        let mut v___x_247_: u8 = 0;
        v___x_247_ = 0;
        return v___x_247_;
    }
}
pub unsafe fn l_Std_Time_TimeZone_convertUt___boxed(
    mut v_x_248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_18__boxed_249_: u8 = 0;
    let mut v_res_250_: u8 = 0;
    let mut v_r_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_18__boxed_249_ = (leanh::lean_unbox(v_x_248_) as u8);
    v_res_250_ = l_Std_Time_TimeZone_convertUt(v_x_18__boxed_249_);
    v_r_251_ = leanh::lean_box((v_res_250_) as usize);
    return v_r_251_;
}
pub unsafe fn l_Std_Time_TimeZone_convertLocalTimeType(
    mut v_index_252_: *mut leanh::LeanObject,
    mut v_tz_253_: *mut leanh::LeanObject,
    mut v_identifier_254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_localTimeTypes_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abbreviations_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stdWallIndicators_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_utLocalIndicators_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_260_: u8 = 0;
    let mut v___x_261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_gmtOffset_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isDst_264_: u8 = 0;
    let mut v___y_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_267_: u8 = 0;
    let mut v___y_268_: u8 = 0;
    let mut v___x_269_: u8 = 0;
    let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_274_: u8 = 0;
    let mut v___x_275_: u8 = 0;
    let mut v___x_276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_277_: u8 = 0;
    let mut v___x_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: u8 = 0;
    let mut v___y_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: u8 = 0;
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: u8 = 0;
    let mut v___x_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: u8 = 0;
    let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_localTimeTypes_255_ = leanh::lean_ctor_get(v_tz_253_, 3);
                v_abbreviations_256_ = leanh::lean_ctor_get(v_tz_253_, 4);
                v_stdWallIndicators_257_ = leanh::lean_ctor_get(v_tz_253_, 6);
                v_utLocalIndicators_258_ = leanh::lean_ctor_get(v_tz_253_, 7);
                v___x_259_ = lean_array_get_size(v_localTimeTypes_255_);
                v___x_260_ = lean_nat_dec_lt(v_index_252_, v___x_259_);
                if v___x_260_ == 0 {
                    leanh::lean_dec_ref(v_identifier_254_);
                    v___x_261_ = leanh::lean_box(0);
                    return v___x_261_;
                } else {
                    v___x_262_ = lean_array_fget_borrowed(v_localTimeTypes_255_, v_index_252_);
                    v_gmtOffset_263_ = leanh::lean_ctor_get(v___x_262_, 0);
                    v_isDst_264_ = leanh::lean_ctor_get_uint8(
                        v___x_262_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v___x_286_ = lean_array_get_size(v_abbreviations_256_);
                    v___x_287_ = lean_nat_dec_lt(v_index_252_, v___x_286_);
                    if v___x_287_ == 0 {
                        leanh::lean_inc(v_gmtOffset_263_);
                        v___x_288_ =
                            l_Std_Time_TimeZone_Offset_toIsoString(v_gmtOffset_263_, v___x_260_);
                        v___y_281_ = v___x_288_;
                        state = 3;
                        continue;
                    } else {
                        v___x_289_ = lean_array_fget_borrowed(v_abbreviations_256_, v_index_252_);
                        leanh::lean_inc(v___x_289_);
                        v___y_281_ = v___x_289_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_269_ = l_Std_Time_TimeZone_convertUt(v___y_268_);
                leanh::lean_inc(v_gmtOffset_263_);
                v___x_270_ = leanh::lean_alloc_ctor(0, 3, (3) as u32);
                leanh::lean_ctor_set(v___x_270_, 0, v_gmtOffset_263_);
                leanh::lean_ctor_set(v___x_270_, 1, v___y_266_);
                leanh::lean_ctor_set(v___x_270_, 2, v_identifier_254_);
                leanh::lean_ctor_set_uint8(
                    v___x_270_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v_isDst_264_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_270_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
                    v___y_267_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_270_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
                    v___x_269_,
                );
                v___x_271_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_271_, 0, v___x_270_);
                return v___x_271_;
            }
            2 => {
                v___x_275_ = l_Std_Time_TimeZone_convertWall(v___y_274_);
                v___x_276_ = lean_array_get_size(v_utLocalIndicators_258_);
                v___x_277_ = lean_nat_dec_lt(v_index_252_, v___x_276_);
                if v___x_277_ == 0 {
                    v___y_266_ = v___y_273_;
                    v___y_267_ = v___x_275_;
                    v___y_268_ = v___x_260_;
                    state = 1;
                    continue;
                } else {
                    v___x_278_ = lean_array_fget_borrowed(v_utLocalIndicators_258_, v_index_252_);
                    v___x_279_ = (leanh::lean_unbox(v___x_278_) as u8);
                    v___y_266_ = v___y_273_;
                    v___y_267_ = v___x_275_;
                    v___y_268_ = v___x_279_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_282_ = lean_array_get_size(v_stdWallIndicators_257_);
                v___x_283_ = lean_nat_dec_lt(v_index_252_, v___x_282_);
                if v___x_283_ == 0 {
                    v___y_273_ = v___y_281_;
                    v___y_274_ = v___x_260_;
                    state = 2;
                    continue;
                } else {
                    v___x_284_ = lean_array_fget_borrowed(v_stdWallIndicators_257_, v_index_252_);
                    v___x_285_ = (leanh::lean_unbox(v___x_284_) as u8);
                    v___y_273_ = v___y_281_;
                    v___y_274_ = v___x_285_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_TimeZone_convertLocalTimeType___boxed(
    mut v_index_290_: *mut leanh::LeanObject,
    mut v_tz_291_: *mut leanh::LeanObject,
    mut v_identifier_292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_293_ =
        l_Std_Time_TimeZone_convertLocalTimeType(v_index_290_, v_tz_291_, v_identifier_292_);
    leanh::lean_dec_ref(v_tz_291_);
    leanh::lean_dec(v_index_290_);
    return v_res_293_;
}
pub unsafe fn l_Nat_cast___at___00Nat_cast___at___00Std_Time_TimeZone_convertLocalTimeType_spec__0_spec__0(
    mut v_a_294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_295_ = lean_nat_to_int(v_a_294_);
    return v___x_295_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_TimeZone_convertLocalTimeType_spec__0(
    mut v_a_296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_297_ = lean_nat_to_int(v_a_296_);
    v___x_298_ = l_Rat_ofInt(v___x_297_);
    return v___x_298_;
}
pub unsafe fn l_Std_Time_TimeZone_convertTransition(
    mut v_times_299_: *mut leanh::LeanObject,
    mut v_index_300_: *mut leanh::LeanObject,
    mut v_tz_301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_transitionTimes_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitionIndices_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: u8 = 0;
    let mut v___x_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_time_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indice_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: u8 = 0;
    let mut v___x_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_transitionTimes_302_ = leanh::lean_ctor_get(v_tz_301_, 1);
    v_transitionIndices_303_ = leanh::lean_ctor_get(v_tz_301_, 2);
    v___x_304_ = l_Int_instInhabited;
    v___x_305_ = l_instInhabitedUInt8;
    v___x_306_ = l_Std_Time_TimeZone_instInhabitedLocalTimeType_default;
    v_time_307_ = lean_array_get_borrowed(v___x_304_, v_transitionTimes_302_, v_index_300_);
    v___x_308_ = leanh::lean_box((v___x_305_) as usize);
    v_indice_309_ = lean_array_get(v___x_308_, v_transitionIndices_303_, v_index_300_);
    leanh::lean_dec(v___x_308_);
    v___x_310_ = (leanh::lean_unbox(v_indice_309_) as u8);
    leanh::lean_dec(v_indice_309_);
    v___x_311_ = lean_uint8_to_nat(v___x_310_);
    v___x_312_ = lean_array_get_borrowed(v___x_306_, v_times_299_, v___x_311_);
    leanh::lean_inc(v___x_312_);
    leanh::lean_inc(v_time_307_);
    v___x_313_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_313_, 0, v_time_307_);
    leanh::lean_ctor_set(v___x_313_, 1, v___x_312_);
    v___x_314_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_314_, 0, v___x_313_);
    return v___x_314_;
}
pub unsafe fn l_Std_Time_TimeZone_convertTransition___boxed(
    mut v_times_315_: *mut leanh::LeanObject,
    mut v_index_316_: *mut leanh::LeanObject,
    mut v_tz_317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_318_ = l_Std_Time_TimeZone_convertTransition(v_times_315_, v_index_316_, v_tz_317_);
    leanh::lean_dec_ref(v_tz_317_);
    leanh::lean_dec(v_index_316_);
    leanh::lean_dec_ref(v_times_315_);
    return v_res_318_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg(
    mut v_upperBound_321_: *mut leanh::LeanObject,
    mut v_a_322_: *mut leanh::LeanObject,
    mut v_tz_323_: *mut leanh::LeanObject,
    mut v_a_324_: *mut leanh::LeanObject,
    mut v_b_325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_326_: u8 = 0;
    let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_326_ = lean_nat_dec_lt(v_a_324_, v_upperBound_321_);
                if v___x_326_ == 0 {
                    leanh::lean_dec(v_a_324_);
                    v___x_327_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_327_, 0, v_b_325_);
                    return v___x_327_;
                } else {
                    v___x_328_ =
                        l_Std_Time_TimeZone_convertTransition(v_a_322_, v_a_324_, v_tz_323_);
                    if leanh::lean_obj_tag(v___x_328_) == 1 {
                        v_val_329_ = leanh::lean_ctor_get(v___x_328_, 0);
                        leanh::lean_inc(v_val_329_);
                        leanh::lean_dec_ref_known(v___x_328_, 1);
                        v___x_330_ = lean_array_push(v_b_325_, v_val_329_);
                        v___x_331_ = leanh::lean_unsigned_to_nat(1);
                        v___x_332_ = lean_nat_add(v_a_324_, v___x_331_);
                        leanh::lean_dec(v_a_324_);
                        v_a_324_ = v___x_332_;
                        v_b_325_ = v___x_330_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_328_);
                        leanh::lean_dec_ref(v_b_325_);
                        v___x_334_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__0;
                        v___x_335_ = l_Nat_reprFast(v_a_324_);
                        v___x_336_ = lean_string_append(v___x_334_, v___x_335_);
                        leanh::lean_dec_ref(v___x_335_);
                        v___x_337_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__1;
                        v___x_338_ = lean_string_append(v___x_336_, v___x_337_);
                        v___x_339_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_339_, 0, v___x_338_);
                        return v___x_339_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___boxed(
    mut v_upperBound_340_: *mut leanh::LeanObject,
    mut v_a_341_: *mut leanh::LeanObject,
    mut v_tz_342_: *mut leanh::LeanObject,
    mut v_a_343_: *mut leanh::LeanObject,
    mut v_b_344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_345_ =
        l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg(
            v_upperBound_340_,
            v_a_341_,
            v_tz_342_,
            v_a_343_,
            v_b_344_,
        );
    leanh::lean_dec_ref(v_tz_342_);
    leanh::lean_dec_ref(v_a_341_);
    leanh::lean_dec(v_upperBound_340_);
    return v_res_345_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg(
    mut v_upperBound_347_: *mut leanh::LeanObject,
    mut v_tz_348_: *mut leanh::LeanObject,
    mut v_id_349_: *mut leanh::LeanObject,
    mut v_a_350_: *mut leanh::LeanObject,
    mut v_b_351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_352_: u8 = 0;
    let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_352_ = lean_nat_dec_lt(v_a_350_, v_upperBound_347_);
                if v___x_352_ == 0 {
                    leanh::lean_dec(v_a_350_);
                    leanh::lean_dec_ref(v_id_349_);
                    v___x_353_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_353_, 0, v_b_351_);
                    return v___x_353_;
                } else {
                    leanh::lean_inc_ref(v_id_349_);
                    v___x_354_ =
                        l_Std_Time_TimeZone_convertLocalTimeType(v_a_350_, v_tz_348_, v_id_349_);
                    if leanh::lean_obj_tag(v___x_354_) == 1 {
                        v_val_355_ = leanh::lean_ctor_get(v___x_354_, 0);
                        leanh::lean_inc(v_val_355_);
                        leanh::lean_dec_ref_known(v___x_354_, 1);
                        v___x_356_ = lean_array_push(v_b_351_, v_val_355_);
                        v___x_357_ = leanh::lean_unsigned_to_nat(1);
                        v___x_358_ = lean_nat_add(v_a_350_, v___x_357_);
                        leanh::lean_dec(v_a_350_);
                        v_a_350_ = v___x_358_;
                        v_b_351_ = v___x_356_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_354_);
                        leanh::lean_dec_ref(v_b_351_);
                        leanh::lean_dec_ref(v_id_349_);
                        v___x_360_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg___closed__0;
                        v___x_361_ = l_Nat_reprFast(v_a_350_);
                        v___x_362_ = lean_string_append(v___x_360_, v___x_361_);
                        leanh::lean_dec_ref(v___x_361_);
                        v___x_363_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg___closed__1;
                        v___x_364_ = lean_string_append(v___x_362_, v___x_363_);
                        v___x_365_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_365_, 0, v___x_364_);
                        return v___x_365_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg___boxed(
    mut v_upperBound_366_: *mut leanh::LeanObject,
    mut v_tz_367_: *mut leanh::LeanObject,
    mut v_id_368_: *mut leanh::LeanObject,
    mut v_a_369_: *mut leanh::LeanObject,
    mut v_b_370_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_371_ =
        l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg(
            v_upperBound_366_,
            v_tz_367_,
            v_id_368_,
            v_a_369_,
            v_b_370_,
        );
    leanh::lean_dec_ref(v_tz_367_);
    leanh::lean_dec(v_upperBound_366_);
    return v_res_371_;
}
pub unsafe fn l_Std_Time_TimeZone_convertTZifV1(
    mut v_tz_375_: *mut leanh::LeanObject,
    mut v_id_376_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_header_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_transitionTimes_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_typecnt_379_: u32 = 0;
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_times_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_387_: u8 = 0;
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_391_: u8 = 0;
    let mut v_a_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_398_: u8 = 0;
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_402_: u8 = 0;
    let mut v_a_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_406_: u8 = 0;
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_418_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_header_377_ = leanh::lean_ctor_get(v_tz_375_, 0);
                v_transitionTimes_378_ = leanh::lean_ctor_get(v_tz_375_, 1);
                v_typecnt_379_ = leanh::lean_ctor_get_uint32(v_header_377_, 16 as u32);
                v___x_380_ = lean_uint32_to_nat(v_typecnt_379_);
                v___x_381_ = leanh::lean_unsigned_to_nat(0);
                v_times_382_ = l_Std_Time_TimeZone_convertTZifV1___closed__0;
                leanh::lean_inc_ref(v_id_376_);
                v___x_383_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg(v___x_380_, v_tz_375_, v_id_376_, v___x_381_, v_times_382_);
                leanh::lean_dec(v___x_380_);
                if leanh::lean_obj_tag(v___x_383_) == 0 {
                    leanh::lean_dec_ref(v_id_376_);
                    v_a_384_ = leanh::lean_ctor_get(v___x_383_, 0);
                    v_isSharedCheck_391_ = (!leanh::lean_is_exclusive(v___x_383_)) as u8;
                    if v_isSharedCheck_391_ == 0 {
                        v___x_386_ = v___x_383_;
                        v_isShared_387_ = v_isSharedCheck_391_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_384_);
                        leanh::lean_dec(v___x_383_);
                        v___x_386_ = leanh::lean_box(0);
                        v_isShared_387_ = v_isSharedCheck_391_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_392_ = leanh::lean_ctor_get(v___x_383_, 0);
                    leanh::lean_inc(v_a_392_);
                    leanh::lean_dec_ref_known(v___x_383_, 1);
                    v___x_393_ = lean_array_get_size(v_transitionTimes_378_);
                    v___x_394_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg(v___x_393_, v_a_392_, v_tz_375_, v___x_381_, v_times_382_);
                    leanh::lean_dec(v_a_392_);
                    if leanh::lean_obj_tag(v___x_394_) == 0 {
                        leanh::lean_dec_ref(v_id_376_);
                        v_a_395_ = leanh::lean_ctor_get(v___x_394_, 0);
                        v_isSharedCheck_402_ = (!leanh::lean_is_exclusive(v___x_394_)) as u8;
                        if v_isSharedCheck_402_ == 0 {
                            v___x_397_ = v___x_394_;
                            v_isShared_398_ = v_isSharedCheck_402_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_395_);
                            leanh::lean_dec(v___x_394_);
                            v___x_397_ = leanh::lean_box(0);
                            v_isShared_398_ = v_isSharedCheck_402_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_403_ = leanh::lean_ctor_get(v___x_394_, 0);
                        v_isSharedCheck_418_ = (!leanh::lean_is_exclusive(v___x_394_)) as u8;
                        if v_isSharedCheck_418_ == 0 {
                            v___x_405_ = v___x_394_;
                            v_isShared_406_ = v_isSharedCheck_418_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_403_);
                            leanh::lean_dec(v___x_394_);
                            v___x_405_ = leanh::lean_box(0);
                            v_isShared_406_ = v_isSharedCheck_418_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_387_ == 0 {
                    v___x_389_ = v___x_386_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_390_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
                    v___x_389_ = v_reuseFailAlloc_390_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_389_;
            }
            3 => {
                if v_isShared_398_ == 0 {
                    v___x_400_ = v___x_397_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_401_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
                    v___x_400_ = v_reuseFailAlloc_401_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_400_;
            }
            5 => {
                leanh::lean_inc_ref(v_id_376_);
                v___x_407_ =
                    l_Std_Time_TimeZone_convertLocalTimeType(v___x_381_, v_tz_375_, v_id_376_);
                if leanh::lean_obj_tag(v___x_407_) == 1 {
                    leanh::lean_dec_ref(v_id_376_);
                    v_val_408_ = leanh::lean_ctor_get(v___x_407_, 0);
                    leanh::lean_inc(v_val_408_);
                    leanh::lean_dec_ref_known(v___x_407_, 1);
                    v___x_409_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_409_, 0, v_val_408_);
                    leanh::lean_ctor_set(v___x_409_, 1, v_a_403_);
                    if v_isShared_406_ == 0 {
                        leanh::lean_ctor_set(v___x_405_, 0, v___x_409_);
                        v___x_411_ = v___x_405_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_412_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_412_, 0, v___x_409_);
                        v___x_411_ = v_reuseFailAlloc_412_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_407_);
                    leanh::lean_dec(v_a_403_);
                    v___x_413_ = l_Std_Time_TimeZone_convertTZifV1___closed__1;
                    v___x_414_ = lean_string_append(v___x_413_, v_id_376_);
                    leanh::lean_dec_ref(v_id_376_);
                    if v_isShared_406_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_405_, 0);
                        leanh::lean_ctor_set(v___x_405_, 0, v___x_414_);
                        v___x_416_ = v___x_405_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_417_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_417_, 0, v___x_414_);
                        v___x_416_ = v_reuseFailAlloc_417_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_411_;
            }
            7 => {
                return v___x_416_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_TimeZone_convertTZifV1___boxed(
    mut v_tz_419_: *mut leanh::LeanObject,
    mut v_id_420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_421_ = l_Std_Time_TimeZone_convertTZifV1(v_tz_419_, v_id_420_);
    leanh::lean_dec_ref(v_tz_419_);
    return v_res_421_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0(
    mut v_upperBound_422_: *mut leanh::LeanObject,
    mut v_a_423_: *mut leanh::LeanObject,
    mut v_tz_424_: *mut leanh::LeanObject,
    mut v_inst_425_: *mut leanh::LeanObject,
    mut v_R_426_: *mut leanh::LeanObject,
    mut v_a_427_: *mut leanh::LeanObject,
    mut v_b_428_: *mut leanh::LeanObject,
    mut v_c_429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_430_ =
        l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___redArg(
            v_upperBound_422_,
            v_a_423_,
            v_tz_424_,
            v_a_427_,
            v_b_428_,
        );
    return v___x_430_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0___boxed(
    mut v_upperBound_431_: *mut leanh::LeanObject,
    mut v_a_432_: *mut leanh::LeanObject,
    mut v_tz_433_: *mut leanh::LeanObject,
    mut v_inst_434_: *mut leanh::LeanObject,
    mut v_R_435_: *mut leanh::LeanObject,
    mut v_a_436_: *mut leanh::LeanObject,
    mut v_b_437_: *mut leanh::LeanObject,
    mut v_c_438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_439_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__0(
        v_upperBound_431_,
        v_a_432_,
        v_tz_433_,
        v_inst_434_,
        v_R_435_,
        v_a_436_,
        v_b_437_,
        v_c_438_,
    );
    leanh::lean_dec_ref(v_tz_433_);
    leanh::lean_dec_ref(v_a_432_);
    leanh::lean_dec(v_upperBound_431_);
    return v_res_439_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1(
    mut v_upperBound_440_: *mut leanh::LeanObject,
    mut v_tz_441_: *mut leanh::LeanObject,
    mut v_id_442_: *mut leanh::LeanObject,
    mut v_inst_443_: *mut leanh::LeanObject,
    mut v_R_444_: *mut leanh::LeanObject,
    mut v_a_445_: *mut leanh::LeanObject,
    mut v_b_446_: *mut leanh::LeanObject,
    mut v_c_447_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_448_ =
        l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___redArg(
            v_upperBound_440_,
            v_tz_441_,
            v_id_442_,
            v_a_445_,
            v_b_446_,
        );
    return v___x_448_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1___boxed(
    mut v_upperBound_449_: *mut leanh::LeanObject,
    mut v_tz_450_: *mut leanh::LeanObject,
    mut v_id_451_: *mut leanh::LeanObject,
    mut v_inst_452_: *mut leanh::LeanObject,
    mut v_R_453_: *mut leanh::LeanObject,
    mut v_a_454_: *mut leanh::LeanObject,
    mut v_b_455_: *mut leanh::LeanObject,
    mut v_c_456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_457_ = l_WellFounded_opaqueFix_u2083___at___00Std_Time_TimeZone_convertTZifV1_spec__1(
        v_upperBound_449_,
        v_tz_450_,
        v_id_451_,
        v_inst_452_,
        v_R_453_,
        v_a_454_,
        v_b_455_,
        v_c_456_,
    );
    leanh::lean_dec_ref(v_tz_450_);
    leanh::lean_dec(v_upperBound_449_);
    return v_res_457_;
}
pub unsafe fn l_Std_Time_TimeZone_convertTZifV2(
    mut v_tz_458_: *mut leanh::LeanObject,
    mut v_id_459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toTZifV1_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toTZifV1_460_ = leanh::lean_ctor_get(v_tz_458_, 0);
    v___x_461_ = l_Std_Time_TimeZone_convertTZifV1(v_toTZifV1_460_, v_id_459_);
    return v___x_461_;
}
pub unsafe fn l_Std_Time_TimeZone_convertTZifV2___boxed(
    mut v_tz_462_: *mut leanh::LeanObject,
    mut v_id_463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_464_ = l_Std_Time_TimeZone_convertTZifV2(v_tz_462_, v_id_463_);
    leanh::lean_dec_ref(v_tz_462_);
    return v_res_464_;
}
pub unsafe fn l_Std_Time_TimeZone_convertTZif(
    mut v_tz_465_: *mut leanh::LeanObject,
    mut v_id_466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v2_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_v2_467_ = leanh::lean_ctor_get(v_tz_465_, 1);
    if leanh::lean_obj_tag(v_v2_467_) == 1 {
        let mut v_val_468_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_469_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_468_ = leanh::lean_ctor_get(v_v2_467_, 0);
        v___x_469_ = l_Std_Time_TimeZone_convertTZifV2(v_val_468_, v_id_466_);
        return v___x_469_;
    } else {
        let mut v_v1_470_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_v1_470_ = leanh::lean_ctor_get(v_tz_465_, 0);
        v___x_471_ = l_Std_Time_TimeZone_convertTZifV1(v_v1_470_, v_id_466_);
        return v___x_471_;
    }
}
pub unsafe fn l_Std_Time_TimeZone_convertTZif___boxed(
    mut v_tz_472_: *mut leanh::LeanObject,
    mut v_id_473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_474_ = l_Std_Time_TimeZone_convertTZif(v_tz_472_, v_id_473_);
    leanh::lean_dec_ref(v_tz_472_);
    return v_res_474_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Zoned_Database_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Time_Zoned_ZoneRules(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_Database_TzIf(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Zoned_Database_Basic(
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
pub unsafe fn initialize_Std_Time_Zoned_Database_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Time_Zoned_ZoneRules(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Std_Time_Zoned_Database_TzIf(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_Database_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Zoned_Database_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Time_Zoned_Database_Basic(builtin);
}
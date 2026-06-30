// Lean compiler output
// Module: Init.Data.String.FindPos
// Imports: Init.Data.String.Basic Init.Omega Init.Data.String.OrderInstances Init.Data.String.Lemmas.Basic
use crate::ffi::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_sub, lean_panic_fn_borrowed, lean_string_utf8_byte_size,
};
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, l_String_Pos_Raw_isValidForSlice,
    runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Data::String::Lemmas::Basic::{
    initialize_Init_Data_String_Lemmas_Basic, runtime_initialize_Init_Data_String_Lemmas_Basic,
};
use crate::r#gen::Init::Data::String::OrderInstances::{
    initialize_Init_Data_String_OrderInstances, runtime_initialize_Init_Data_String_OrderInstances,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
pub static l_String_Slice_Pos_prev_x21___closed__0_value: leanh::LeanStringObject<25> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            73, 110, 105, 116, 46, 68, 97, 116, 97, 46, 83, 116, 114, 105, 110, 103, 46, 70, 105,
            110, 100, 80, 111, 115, 0,
        ],
    };
static mut l_String_Slice_Pos_prev_x21___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pos_prev_x21___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_String_Slice_Pos_prev_x21___closed__1_value: leanh::LeanStringObject<23> =
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
            83, 116, 114, 105, 110, 103, 46, 83, 108, 105, 99, 101, 46, 80, 111, 115, 46, 112, 114,
            101, 118, 33, 0,
        ],
    };
static mut l_String_Slice_Pos_prev_x21___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pos_prev_x21___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_String_Slice_Pos_prev_x21___closed__2_value: leanh::LeanStringObject<44> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 44,
        m_capacity: 44,
        m_length: 43,
        m_data: [
            84, 104, 101, 32, 115, 116, 97, 114, 116, 32, 112, 111, 115, 105, 116, 105, 111, 110,
            32, 104, 97, 115, 32, 110, 111, 32, 112, 114, 101, 118, 105, 111, 117, 115, 32, 112,
            111, 115, 105, 116, 105, 111, 110, 0,
        ],
    };
static mut l_String_Slice_Pos_prev_x21___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pos_prev_x21___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_String_Slice_Pos_prev_x21___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_String_Slice_Pos_prev_x21___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_String_Slice_posGE___redArg(
    mut v_s_280_: *mut leanh::LeanObject,
    mut v_offset_281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_282_: u8 = 0;
    let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_282_ = l_String_Pos_Raw_isValidForSlice(v_s_280_, v_offset_281_);
                if v___x_282_ == 0 {
                    v___x_283_ = leanh::lean_unsigned_to_nat(1);
                    v___x_284_ = lean_nat_add(v_offset_281_, v___x_283_);
                    leanh::lean_dec(v_offset_281_);
                    v_offset_281_ = v___x_284_;
                    state = 0;
                    continue;
                } else {
                    return v_offset_281_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_posGE___redArg___boxed(
    mut v_s_286_: *mut leanh::LeanObject,
    mut v_offset_287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_288_ = l_String_Slice_posGE___redArg(v_s_286_, v_offset_287_);
    leanh::lean_dec_ref(v_s_286_);
    return v_res_288_;
}
pub unsafe fn l_String_Slice_posGE(
    mut v_s_289_: *mut leanh::LeanObject,
    mut v_offset_290_: *mut leanh::LeanObject,
    mut v_h_291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_292_ = l_String_Slice_posGE___redArg(v_s_289_, v_offset_290_);
    return v___x_292_;
}
pub unsafe fn l_String_Slice_posGE___boxed(
    mut v_s_293_: *mut leanh::LeanObject,
    mut v_offset_294_: *mut leanh::LeanObject,
    mut v_h_295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_296_ = l_String_Slice_posGE(v_s_293_, v_offset_294_, v_h_295_);
    leanh::lean_dec_ref(v_s_293_);
    return v_res_296_;
}
pub unsafe fn l_String_Slice_posGT___redArg(
    mut v_s_297_: *mut leanh::LeanObject,
    mut v_offset_298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_299_ = leanh::lean_unsigned_to_nat(1);
    v___x_300_ = lean_nat_add(v_offset_298_, v___x_299_);
    v___x_301_ = l_String_Slice_posGE___redArg(v_s_297_, v___x_300_);
    return v___x_301_;
}
pub unsafe fn l_String_Slice_posGT___redArg___boxed(
    mut v_s_302_: *mut leanh::LeanObject,
    mut v_offset_303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_304_ = l_String_Slice_posGT___redArg(v_s_302_, v_offset_303_);
    leanh::lean_dec(v_offset_303_);
    leanh::lean_dec_ref(v_s_302_);
    return v_res_304_;
}
pub unsafe fn l_String_Slice_posGT(
    mut v_s_305_: *mut leanh::LeanObject,
    mut v_offset_306_: *mut leanh::LeanObject,
    mut v_h_307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_308_ = leanh::lean_unsigned_to_nat(1);
    v___x_309_ = lean_nat_add(v_offset_306_, v___x_308_);
    v___x_310_ = l_String_Slice_posGE___redArg(v_s_305_, v___x_309_);
    return v___x_310_;
}
pub unsafe fn l_String_Slice_posGT___boxed(
    mut v_s_311_: *mut leanh::LeanObject,
    mut v_offset_312_: *mut leanh::LeanObject,
    mut v_h_313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_314_ = l_String_Slice_posGT(v_s_311_, v_offset_312_, v_h_313_);
    leanh::lean_dec(v_offset_312_);
    leanh::lean_dec_ref(v_s_311_);
    return v_res_314_;
}
pub unsafe fn l_String_Slice_findNextPos___redArg(
    mut v_offset_315_: *mut leanh::LeanObject,
    mut v_s_316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_317_ = leanh::lean_unsigned_to_nat(1);
    v___x_318_ = lean_nat_add(v_offset_315_, v___x_317_);
    v___x_319_ = l_String_Slice_posGE___redArg(v_s_316_, v___x_318_);
    return v___x_319_;
}
pub unsafe fn l_String_Slice_findNextPos___redArg___boxed(
    mut v_offset_320_: *mut leanh::LeanObject,
    mut v_s_321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_322_ = l_String_Slice_findNextPos___redArg(v_offset_320_, v_s_321_);
    leanh::lean_dec_ref(v_s_321_);
    leanh::lean_dec(v_offset_320_);
    return v_res_322_;
}
pub unsafe fn l_String_Slice_findNextPos(
    mut v_offset_323_: *mut leanh::LeanObject,
    mut v_s_324_: *mut leanh::LeanObject,
    mut v_h_325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_326_ = l_String_Slice_findNextPos___redArg(v_offset_323_, v_s_324_);
    return v___x_326_;
}
pub unsafe fn l_String_Slice_findNextPos___boxed(
    mut v_offset_327_: *mut leanh::LeanObject,
    mut v_s_328_: *mut leanh::LeanObject,
    mut v_h_329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_330_ = l_String_Slice_findNextPos(v_offset_327_, v_s_328_, v_h_329_);
    leanh::lean_dec_ref(v_s_328_);
    leanh::lean_dec(v_offset_327_);
    return v_res_330_;
}
pub unsafe fn l_String_posGE___redArg(
    mut v_s_331_: *mut leanh::LeanObject,
    mut v_offset_332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_333_ = leanh::lean_unsigned_to_nat(0);
    v___x_334_ = lean_string_utf8_byte_size(v_s_331_);
    v___x_335_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_335_, 0, v_s_331_);
    leanh::lean_ctor_set(v___x_335_, 1, v___x_333_);
    leanh::lean_ctor_set(v___x_335_, 2, v___x_334_);
    v___x_336_ = l_String_Slice_posGE___redArg(v___x_335_, v_offset_332_);
    leanh::lean_dec_ref_known(v___x_335_, 3);
    return v___x_336_;
}
pub unsafe fn l_String_posGE(
    mut v_s_337_: *mut leanh::LeanObject,
    mut v_offset_338_: *mut leanh::LeanObject,
    mut v_h_339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_340_ = leanh::lean_unsigned_to_nat(0);
    v___x_341_ = lean_string_utf8_byte_size(v_s_337_);
    v___x_342_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_342_, 0, v_s_337_);
    leanh::lean_ctor_set(v___x_342_, 1, v___x_340_);
    leanh::lean_ctor_set(v___x_342_, 2, v___x_341_);
    v___x_343_ = l_String_Slice_posGE___redArg(v___x_342_, v_offset_338_);
    leanh::lean_dec_ref_known(v___x_342_, 3);
    return v___x_343_;
}
pub unsafe fn l_String_posGT___redArg(
    mut v_s_344_: *mut leanh::LeanObject,
    mut v_offset_345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_346_ = leanh::lean_unsigned_to_nat(0);
    v___x_347_ = lean_string_utf8_byte_size(v_s_344_);
    v___x_348_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_348_, 0, v_s_344_);
    leanh::lean_ctor_set(v___x_348_, 1, v___x_346_);
    leanh::lean_ctor_set(v___x_348_, 2, v___x_347_);
    v___x_349_ = leanh::lean_unsigned_to_nat(1);
    v___x_350_ = lean_nat_add(v_offset_345_, v___x_349_);
    v___x_351_ = l_String_Slice_posGE___redArg(v___x_348_, v___x_350_);
    leanh::lean_dec_ref_known(v___x_348_, 3);
    return v___x_351_;
}
pub unsafe fn l_String_posGT___redArg___boxed(
    mut v_s_352_: *mut leanh::LeanObject,
    mut v_offset_353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_354_ = l_String_posGT___redArg(v_s_352_, v_offset_353_);
    leanh::lean_dec(v_offset_353_);
    return v_res_354_;
}
pub unsafe fn l_String_posGT(
    mut v_s_355_: *mut leanh::LeanObject,
    mut v_offset_356_: *mut leanh::LeanObject,
    mut v_h_357_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_358_ = leanh::lean_unsigned_to_nat(0);
    v___x_359_ = lean_string_utf8_byte_size(v_s_355_);
    v___x_360_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_360_, 0, v_s_355_);
    leanh::lean_ctor_set(v___x_360_, 1, v___x_358_);
    leanh::lean_ctor_set(v___x_360_, 2, v___x_359_);
    v___x_361_ = leanh::lean_unsigned_to_nat(1);
    v___x_362_ = lean_nat_add(v_offset_356_, v___x_361_);
    v___x_363_ = l_String_Slice_posGE___redArg(v___x_360_, v___x_362_);
    leanh::lean_dec_ref_known(v___x_360_, 3);
    return v___x_363_;
}
pub unsafe fn l_String_posGT___boxed(
    mut v_s_364_: *mut leanh::LeanObject,
    mut v_offset_365_: *mut leanh::LeanObject,
    mut v_h_366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_367_ = l_String_posGT(v_s_364_, v_offset_365_, v_h_366_);
    leanh::lean_dec(v_offset_365_);
    return v_res_367_;
}
pub unsafe fn l_String_Slice_posLE(
    mut v_s_368_: *mut leanh::LeanObject,
    mut v_offset_369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_370_: u8 = 0;
    let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_370_ = l_String_Pos_Raw_isValidForSlice(v_s_368_, v_offset_369_);
                if v___x_370_ == 0 {
                    v___x_371_ = leanh::lean_unsigned_to_nat(1);
                    v___x_372_ = lean_nat_sub(v_offset_369_, v___x_371_);
                    leanh::lean_dec(v_offset_369_);
                    v_offset_369_ = v___x_372_;
                    state = 0;
                    continue;
                } else {
                    return v_offset_369_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_posLE___boxed(
    mut v_s_374_: *mut leanh::LeanObject,
    mut v_offset_375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_376_ = l_String_Slice_posLE(v_s_374_, v_offset_375_);
    leanh::lean_dec_ref(v_s_374_);
    return v_res_376_;
}
pub unsafe fn l_String_Slice_posLT___redArg(
    mut v_s_377_: *mut leanh::LeanObject,
    mut v_offset_378_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_379_ = leanh::lean_unsigned_to_nat(1);
    v___x_380_ = lean_nat_sub(v_offset_378_, v___x_379_);
    v___x_381_ = l_String_Slice_posLE(v_s_377_, v___x_380_);
    return v___x_381_;
}
pub unsafe fn l_String_Slice_posLT___redArg___boxed(
    mut v_s_382_: *mut leanh::LeanObject,
    mut v_offset_383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_384_ = l_String_Slice_posLT___redArg(v_s_382_, v_offset_383_);
    leanh::lean_dec(v_offset_383_);
    leanh::lean_dec_ref(v_s_382_);
    return v_res_384_;
}
pub unsafe fn l_String_Slice_posLT(
    mut v_s_385_: *mut leanh::LeanObject,
    mut v_offset_386_: *mut leanh::LeanObject,
    mut v___h_387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_388_ = leanh::lean_unsigned_to_nat(1);
    v___x_389_ = lean_nat_sub(v_offset_386_, v___x_388_);
    v___x_390_ = l_String_Slice_posLE(v_s_385_, v___x_389_);
    return v___x_390_;
}
pub unsafe fn l_String_Slice_posLT___boxed(
    mut v_s_391_: *mut leanh::LeanObject,
    mut v_offset_392_: *mut leanh::LeanObject,
    mut v___h_393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_394_ = l_String_Slice_posLT(v_s_391_, v_offset_392_, v___h_393_);
    leanh::lean_dec(v_offset_392_);
    leanh::lean_dec_ref(v_s_391_);
    return v_res_394_;
}
pub unsafe fn l_String_posLE(
    mut v_s_395_: *mut leanh::LeanObject,
    mut v_offset_396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_397_ = leanh::lean_unsigned_to_nat(0);
    v___x_398_ = lean_string_utf8_byte_size(v_s_395_);
    v___x_399_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_399_, 0, v_s_395_);
    leanh::lean_ctor_set(v___x_399_, 1, v___x_397_);
    leanh::lean_ctor_set(v___x_399_, 2, v___x_398_);
    v___x_400_ = l_String_Slice_posLE(v___x_399_, v_offset_396_);
    leanh::lean_dec_ref_known(v___x_399_, 3);
    return v___x_400_;
}
pub unsafe fn l_String_posLT___redArg(
    mut v_s_401_: *mut leanh::LeanObject,
    mut v_offset_402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_403_ = leanh::lean_unsigned_to_nat(0);
    v___x_404_ = lean_string_utf8_byte_size(v_s_401_);
    v___x_405_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_405_, 0, v_s_401_);
    leanh::lean_ctor_set(v___x_405_, 1, v___x_403_);
    leanh::lean_ctor_set(v___x_405_, 2, v___x_404_);
    v___x_406_ = leanh::lean_unsigned_to_nat(1);
    v___x_407_ = lean_nat_sub(v_offset_402_, v___x_406_);
    v___x_408_ = l_String_Slice_posLE(v___x_405_, v___x_407_);
    leanh::lean_dec_ref_known(v___x_405_, 3);
    return v___x_408_;
}
pub unsafe fn l_String_posLT___redArg___boxed(
    mut v_s_409_: *mut leanh::LeanObject,
    mut v_offset_410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_411_ = l_String_posLT___redArg(v_s_409_, v_offset_410_);
    leanh::lean_dec(v_offset_410_);
    return v_res_411_;
}
pub unsafe fn l_String_posLT(
    mut v_s_412_: *mut leanh::LeanObject,
    mut v_offset_413_: *mut leanh::LeanObject,
    mut v_h_414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_415_ = leanh::lean_unsigned_to_nat(0);
    v___x_416_ = lean_string_utf8_byte_size(v_s_412_);
    v___x_417_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_417_, 0, v_s_412_);
    leanh::lean_ctor_set(v___x_417_, 1, v___x_415_);
    leanh::lean_ctor_set(v___x_417_, 2, v___x_416_);
    v___x_418_ = leanh::lean_unsigned_to_nat(1);
    v___x_419_ = lean_nat_sub(v_offset_413_, v___x_418_);
    v___x_420_ = l_String_Slice_posLE(v___x_417_, v___x_419_);
    leanh::lean_dec_ref_known(v___x_417_, 3);
    return v___x_420_;
}
pub unsafe fn l_String_posLT___boxed(
    mut v_s_421_: *mut leanh::LeanObject,
    mut v_offset_422_: *mut leanh::LeanObject,
    mut v_h_423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_424_ = l_String_posLT(v_s_421_, v_offset_422_, v_h_423_);
    leanh::lean_dec(v_offset_422_);
    return v_res_424_;
}
pub unsafe fn l_String_Slice_Pos_prev___redArg(
    mut v_s_425_: *mut leanh::LeanObject,
    mut v_pos_426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_427_ = leanh::lean_unsigned_to_nat(1);
    v___x_428_ = lean_nat_sub(v_pos_426_, v___x_427_);
    v___x_429_ = l_String_Slice_posLE(v_s_425_, v___x_428_);
    return v___x_429_;
}
pub unsafe fn l_String_Slice_Pos_prev___redArg___boxed(
    mut v_s_430_: *mut leanh::LeanObject,
    mut v_pos_431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_432_ = l_String_Slice_Pos_prev___redArg(v_s_430_, v_pos_431_);
    leanh::lean_dec(v_pos_431_);
    leanh::lean_dec_ref(v_s_430_);
    return v_res_432_;
}
pub unsafe fn l_String_Slice_Pos_prev(
    mut v_s_433_: *mut leanh::LeanObject,
    mut v_pos_434_: *mut leanh::LeanObject,
    mut v_h_435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_436_ = leanh::lean_unsigned_to_nat(1);
    v___x_437_ = lean_nat_sub(v_pos_434_, v___x_436_);
    v___x_438_ = l_String_Slice_posLE(v_s_433_, v___x_437_);
    return v___x_438_;
}
pub unsafe fn l_String_Slice_Pos_prev___boxed(
    mut v_s_439_: *mut leanh::LeanObject,
    mut v_pos_440_: *mut leanh::LeanObject,
    mut v_h_441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_442_ = l_String_Slice_Pos_prev(v_s_439_, v_pos_440_, v_h_441_);
    leanh::lean_dec(v_pos_440_);
    leanh::lean_dec_ref(v_s_439_);
    return v_res_442_;
}
pub unsafe fn l_String_Slice_Pos_prev_x3f(
    mut v_s_443_: *mut leanh::LeanObject,
    mut v_pos_444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: u8 = 0;
    v___x_445_ = leanh::lean_unsigned_to_nat(0);
    v___x_446_ = lean_nat_dec_eq(v_pos_444_, v___x_445_);
    if v___x_446_ == 0 {
        let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_447_ = leanh::lean_unsigned_to_nat(1);
        v___x_448_ = lean_nat_sub(v_pos_444_, v___x_447_);
        v___x_449_ = l_String_Slice_posLE(v_s_443_, v___x_448_);
        v___x_450_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_450_, 0, v___x_449_);
        return v___x_450_;
    } else {
        let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_451_ = leanh::lean_box(0);
        return v___x_451_;
    }
}
pub unsafe fn l_String_Slice_Pos_prev_x3f___boxed(
    mut v_s_452_: *mut leanh::LeanObject,
    mut v_pos_453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_454_ = l_String_Slice_Pos_prev_x3f(v_s_452_, v_pos_453_);
    leanh::lean_dec(v_pos_453_);
    leanh::lean_dec_ref(v_s_452_);
    return v_res_454_;
}
pub unsafe fn l_panic___at___00String_Slice_Pos_prev_x21_spec__0___redArg(
    mut v_msg_455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_456_ = leanh::lean_unsigned_to_nat(0);
    v___x_457_ = lean_panic_fn_borrowed(v___x_456_, v_msg_455_);
    return v___x_457_;
}
pub unsafe fn l_panic___at___00String_Slice_Pos_prev_x21_spec__0(
    mut v_s_458_: *mut leanh::LeanObject,
    mut v_msg_459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_460_ = l_panic___at___00String_Slice_Pos_prev_x21_spec__0___redArg(v_msg_459_);
    return v___x_460_;
}
pub unsafe fn l_panic___at___00String_Slice_Pos_prev_x21_spec__0___boxed(
    mut v_s_461_: *mut leanh::LeanObject,
    mut v_msg_462_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_463_ = l_panic___at___00String_Slice_Pos_prev_x21_spec__0(v_s_461_, v_msg_462_);
    leanh::lean_dec_ref(v_s_461_);
    return v_res_463_;
}
pub unsafe fn _init_l_String_Slice_Pos_prev_x21___closed__3() -> *mut leanh::LeanObject {
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_467_ = l_String_Slice_Pos_prev_x21___closed__2;
    v___x_468_ = leanh::lean_unsigned_to_nat(31);
    v___x_469_ = leanh::lean_unsigned_to_nat(115);
    v___x_470_ = l_String_Slice_Pos_prev_x21___closed__1;
    v___x_471_ = l_String_Slice_Pos_prev_x21___closed__0;
    v___x_472_ =
        l_mkPanicMessageWithDecl(v___x_471_, v___x_470_, v___x_469_, v___x_468_, v___x_467_);
    return v___x_472_;
}
pub unsafe fn l_String_Slice_Pos_prev_x21(
    mut v_s_473_: *mut leanh::LeanObject,
    mut v_pos_474_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: u8 = 0;
    v___x_475_ = leanh::lean_unsigned_to_nat(0);
    v___x_476_ = lean_nat_dec_eq(v_pos_474_, v___x_475_);
    if v___x_476_ == 0 {
        let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_477_ = leanh::lean_unsigned_to_nat(1);
        v___x_478_ = lean_nat_sub(v_pos_474_, v___x_477_);
        v___x_479_ = l_String_Slice_posLE(v_s_473_, v___x_478_);
        return v___x_479_;
    } else {
        let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_480_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_String_Slice_Pos_prev_x21___closed__3),
            core::ptr::addr_of_mut!(l_String_Slice_Pos_prev_x21___closed__3_once),
            _init_l_String_Slice_Pos_prev_x21___closed__3,
        );
        v___x_481_ = l_panic___at___00String_Slice_Pos_prev_x21_spec__0___redArg(v___x_480_);
        return v___x_481_;
    }
}
pub unsafe fn l_String_Slice_Pos_prev_x21___boxed(
    mut v_s_482_: *mut leanh::LeanObject,
    mut v_pos_483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_484_ = l_String_Slice_Pos_prev_x21(v_s_482_, v_pos_483_);
    leanh::lean_dec(v_pos_483_);
    leanh::lean_dec_ref(v_s_482_);
    return v_res_484_;
}
pub unsafe fn l_String_Pos_prev___redArg(
    mut v_s_485_: *mut leanh::LeanObject,
    mut v_pos_486_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_487_ = leanh::lean_unsigned_to_nat(0);
    v___x_488_ = lean_string_utf8_byte_size(v_s_485_);
    v___x_489_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_489_, 0, v_s_485_);
    leanh::lean_ctor_set(v___x_489_, 1, v___x_487_);
    leanh::lean_ctor_set(v___x_489_, 2, v___x_488_);
    v___x_490_ = leanh::lean_unsigned_to_nat(1);
    v___x_491_ = lean_nat_sub(v_pos_486_, v___x_490_);
    v___x_492_ = l_String_Slice_posLE(v___x_489_, v___x_491_);
    leanh::lean_dec_ref_known(v___x_489_, 3);
    return v___x_492_;
}
pub unsafe fn l_String_Pos_prev___redArg___boxed(
    mut v_s_493_: *mut leanh::LeanObject,
    mut v_pos_494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_495_ = l_String_Pos_prev___redArg(v_s_493_, v_pos_494_);
    leanh::lean_dec(v_pos_494_);
    return v_res_495_;
}
pub unsafe fn l_String_Pos_prev(
    mut v_s_496_: *mut leanh::LeanObject,
    mut v_pos_497_: *mut leanh::LeanObject,
    mut v_h_498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_499_ = leanh::lean_unsigned_to_nat(0);
    v___x_500_ = lean_string_utf8_byte_size(v_s_496_);
    v___x_501_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_501_, 0, v_s_496_);
    leanh::lean_ctor_set(v___x_501_, 1, v___x_499_);
    leanh::lean_ctor_set(v___x_501_, 2, v___x_500_);
    v___x_502_ = leanh::lean_unsigned_to_nat(1);
    v___x_503_ = lean_nat_sub(v_pos_497_, v___x_502_);
    v___x_504_ = l_String_Slice_posLE(v___x_501_, v___x_503_);
    leanh::lean_dec_ref_known(v___x_501_, 3);
    return v___x_504_;
}
pub unsafe fn l_String_Pos_prev___boxed(
    mut v_s_505_: *mut leanh::LeanObject,
    mut v_pos_506_: *mut leanh::LeanObject,
    mut v_h_507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_508_ = l_String_Pos_prev(v_s_505_, v_pos_506_, v_h_507_);
    leanh::lean_dec(v_pos_506_);
    return v_res_508_;
}
pub unsafe fn l_String_Pos_prev_x3f(
    mut v_s_509_: *mut leanh::LeanObject,
    mut v_pos_510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_519_: u8 = 0;
    let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_523_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_511_ = leanh::lean_unsigned_to_nat(0);
                v___x_512_ = lean_string_utf8_byte_size(v_s_509_);
                v___x_513_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_513_, 0, v_s_509_);
                leanh::lean_ctor_set(v___x_513_, 1, v___x_511_);
                leanh::lean_ctor_set(v___x_513_, 2, v___x_512_);
                v___x_514_ = l_String_Slice_Pos_prev_x3f(v___x_513_, v_pos_510_);
                leanh::lean_dec_ref_known(v___x_513_, 3);
                if leanh::lean_obj_tag(v___x_514_) == 0 {
                    v___x_515_ = leanh::lean_box(0);
                    return v___x_515_;
                } else {
                    v_val_516_ = leanh::lean_ctor_get(v___x_514_, 0);
                    v_isSharedCheck_523_ = (!leanh::lean_is_exclusive(v___x_514_)) as u8;
                    if v_isSharedCheck_523_ == 0 {
                        v___x_518_ = v___x_514_;
                        v_isShared_519_ = v_isSharedCheck_523_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_516_);
                        leanh::lean_dec(v___x_514_);
                        v___x_518_ = leanh::lean_box(0);
                        v_isShared_519_ = v_isSharedCheck_523_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_519_ == 0 {
                    v___x_521_ = v___x_518_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_522_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_522_, 0, v_val_516_);
                    v___x_521_ = v_reuseFailAlloc_522_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_521_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Pos_prev_x3f___boxed(
    mut v_s_524_: *mut leanh::LeanObject,
    mut v_pos_525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_526_ = l_String_Pos_prev_x3f(v_s_524_, v_pos_525_);
    leanh::lean_dec(v_pos_525_);
    return v_res_526_;
}
pub unsafe fn l_String_Pos_prev_x21(
    mut v_s_527_: *mut leanh::LeanObject,
    mut v_pos_528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_529_ = leanh::lean_unsigned_to_nat(0);
    v___x_530_ = lean_string_utf8_byte_size(v_s_527_);
    v___x_531_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_531_, 0, v_s_527_);
    leanh::lean_ctor_set(v___x_531_, 1, v___x_529_);
    leanh::lean_ctor_set(v___x_531_, 2, v___x_530_);
    v___x_532_ = l_String_Slice_Pos_prev_x21(v___x_531_, v_pos_528_);
    leanh::lean_dec_ref_known(v___x_531_, 3);
    return v___x_532_;
}
pub unsafe fn l_String_Pos_prev_x21___boxed(
    mut v_s_533_: *mut leanh::LeanObject,
    mut v_pos_534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_535_ = l_String_Pos_prev_x21(v_s_533_, v_pos_534_);
    leanh::lean_dec(v_pos_534_);
    return v_res_535_;
}
pub unsafe fn l_String_Slice_Pos_prevn(
    mut v_s_536_: *mut leanh::LeanObject,
    mut v_p_537_: *mut leanh::LeanObject,
    mut v_n_538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_540_: u8 = 0;
    let mut v_one_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_539_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_540_ = lean_nat_dec_eq(v_n_538_, v_zero_539_);
                if v_isZero_540_ == 1 {
                    leanh::lean_dec(v_n_538_);
                    return v_p_537_;
                } else {
                    v_one_541_ = leanh::lean_unsigned_to_nat(1);
                    v_n_542_ = lean_nat_sub(v_n_538_, v_one_541_);
                    leanh::lean_dec(v_n_538_);
                    v___x_547_ = lean_nat_dec_eq(v_p_537_, v_zero_539_);
                    if v___x_547_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        if v_isZero_540_ == 0 {
                            leanh::lean_dec(v_n_542_);
                            return v_p_537_;
                        } else {
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_544_ = lean_nat_sub(v_p_537_, v_one_541_);
                leanh::lean_dec(v_p_537_);
                v___x_545_ = l_String_Slice_posLE(v_s_536_, v___x_544_);
                v_p_537_ = v___x_545_;
                v_n_538_ = v_n_542_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pos_prevn___boxed(
    mut v_s_548_: *mut leanh::LeanObject,
    mut v_p_549_: *mut leanh::LeanObject,
    mut v_n_550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_551_ = l_String_Slice_Pos_prevn(v_s_548_, v_p_549_, v_n_550_);
    leanh::lean_dec_ref(v_s_548_);
    return v_res_551_;
}
pub unsafe fn l_String_Pos_prevn(
    mut v_s_552_: *mut leanh::LeanObject,
    mut v_p_553_: *mut leanh::LeanObject,
    mut v_n_554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_555_ = leanh::lean_unsigned_to_nat(0);
    v___x_556_ = lean_string_utf8_byte_size(v_s_552_);
    v___x_557_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_557_, 0, v_s_552_);
    leanh::lean_ctor_set(v___x_557_, 1, v___x_555_);
    leanh::lean_ctor_set(v___x_557_, 2, v___x_556_);
    v___x_558_ = l_String_Slice_Pos_prevn(v___x_557_, v_p_553_, v_n_554_);
    leanh::lean_dec_ref_known(v___x_557_, 3);
    return v___x_558_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_FindPos(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_FindPos(
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
pub unsafe fn initialize_Init_Data_String_FindPos(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_OrderInstances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_FindPos(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_FindPos(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_FindPos(builtin);
}
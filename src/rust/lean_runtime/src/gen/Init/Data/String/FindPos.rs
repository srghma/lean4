// Lean compiler output
// Module: Init.Data.String.FindPos
// Imports: Init.Data.String.Basic Init.Omega Init.Data.String.OrderInstances Init.Data.String.Lemmas.Basic
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
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_sub, lean_panic_fn_borrowed, lean_string_utf8_byte_size,
};
pub static l_String_Slice_Pos_prev_x21___closed__0_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_String_Slice_Pos_prev_x21___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pos_prev_x21___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_Pos_prev_x21___closed__1_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_String_Slice_Pos_prev_x21___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pos_prev_x21___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_Pos_prev_x21___closed__2_value: crate::leanh::LeanStringObject<44> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
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
static mut l_String_Slice_Pos_prev_x21___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pos_prev_x21___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_String_Slice_Pos_prev_x21___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_String_Slice_Pos_prev_x21___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_String_Slice_posGE___redArg(
    mut v_s_280_: *mut crate::leanh::LeanObject,
    mut v_offset_281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_282_: u8 = 0;
    let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_282_ = l_String_Pos_Raw_isValidForSlice(v_s_280_, v_offset_281_);
                if v___x_282_ == 0 {
                    v___x_283_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_284_ = lean_nat_add(v_offset_281_, v___x_283_);
                    crate::leanh::lean_dec(v_offset_281_);
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
    mut v_s_286_: *mut crate::leanh::LeanObject,
    mut v_offset_287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_288_ = l_String_Slice_posGE___redArg(v_s_286_, v_offset_287_);
    crate::leanh::lean_dec_ref(v_s_286_);
    return v_res_288_;
}
pub unsafe fn l_String_Slice_posGE(
    mut v_s_289_: *mut crate::leanh::LeanObject,
    mut v_offset_290_: *mut crate::leanh::LeanObject,
    mut v_h_291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_292_ = l_String_Slice_posGE___redArg(v_s_289_, v_offset_290_);
    return v___x_292_;
}
pub unsafe fn l_String_Slice_posGE___boxed(
    mut v_s_293_: *mut crate::leanh::LeanObject,
    mut v_offset_294_: *mut crate::leanh::LeanObject,
    mut v_h_295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_296_ = l_String_Slice_posGE(v_s_293_, v_offset_294_, v_h_295_);
    crate::leanh::lean_dec_ref(v_s_293_);
    return v_res_296_;
}
pub unsafe fn l_String_Slice_posGT___redArg(
    mut v_s_297_: *mut crate::leanh::LeanObject,
    mut v_offset_298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_299_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_300_ = lean_nat_add(v_offset_298_, v___x_299_);
    v___x_301_ = l_String_Slice_posGE___redArg(v_s_297_, v___x_300_);
    return v___x_301_;
}
pub unsafe fn l_String_Slice_posGT___redArg___boxed(
    mut v_s_302_: *mut crate::leanh::LeanObject,
    mut v_offset_303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_304_ = l_String_Slice_posGT___redArg(v_s_302_, v_offset_303_);
    crate::leanh::lean_dec(v_offset_303_);
    crate::leanh::lean_dec_ref(v_s_302_);
    return v_res_304_;
}
pub unsafe fn l_String_Slice_posGT(
    mut v_s_305_: *mut crate::leanh::LeanObject,
    mut v_offset_306_: *mut crate::leanh::LeanObject,
    mut v_h_307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_308_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_309_ = lean_nat_add(v_offset_306_, v___x_308_);
    v___x_310_ = l_String_Slice_posGE___redArg(v_s_305_, v___x_309_);
    return v___x_310_;
}
pub unsafe fn l_String_Slice_posGT___boxed(
    mut v_s_311_: *mut crate::leanh::LeanObject,
    mut v_offset_312_: *mut crate::leanh::LeanObject,
    mut v_h_313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_314_ = l_String_Slice_posGT(v_s_311_, v_offset_312_, v_h_313_);
    crate::leanh::lean_dec(v_offset_312_);
    crate::leanh::lean_dec_ref(v_s_311_);
    return v_res_314_;
}
pub unsafe fn l_String_Slice_findNextPos___redArg(
    mut v_offset_315_: *mut crate::leanh::LeanObject,
    mut v_s_316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_317_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_318_ = lean_nat_add(v_offset_315_, v___x_317_);
    v___x_319_ = l_String_Slice_posGE___redArg(v_s_316_, v___x_318_);
    return v___x_319_;
}
pub unsafe fn l_String_Slice_findNextPos___redArg___boxed(
    mut v_offset_320_: *mut crate::leanh::LeanObject,
    mut v_s_321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_322_ = l_String_Slice_findNextPos___redArg(v_offset_320_, v_s_321_);
    crate::leanh::lean_dec_ref(v_s_321_);
    crate::leanh::lean_dec(v_offset_320_);
    return v_res_322_;
}
pub unsafe fn l_String_Slice_findNextPos(
    mut v_offset_323_: *mut crate::leanh::LeanObject,
    mut v_s_324_: *mut crate::leanh::LeanObject,
    mut v_h_325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_326_ = l_String_Slice_findNextPos___redArg(v_offset_323_, v_s_324_);
    return v___x_326_;
}
pub unsafe fn l_String_Slice_findNextPos___boxed(
    mut v_offset_327_: *mut crate::leanh::LeanObject,
    mut v_s_328_: *mut crate::leanh::LeanObject,
    mut v_h_329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_330_ = l_String_Slice_findNextPos(v_offset_327_, v_s_328_, v_h_329_);
    crate::leanh::lean_dec_ref(v_s_328_);
    crate::leanh::lean_dec(v_offset_327_);
    return v_res_330_;
}
pub unsafe fn l_String_posGE___redArg(
    mut v_s_331_: *mut crate::leanh::LeanObject,
    mut v_offset_332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_333_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_334_ = lean_string_utf8_byte_size(v_s_331_);
    v___x_335_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_335_, 0, v_s_331_);
    crate::leanh::lean_ctor_set(v___x_335_, 1, v___x_333_);
    crate::leanh::lean_ctor_set(v___x_335_, 2, v___x_334_);
    v___x_336_ = l_String_Slice_posGE___redArg(v___x_335_, v_offset_332_);
    crate::leanh::lean_dec_ref_known(v___x_335_, 3);
    return v___x_336_;
}
pub unsafe fn l_String_posGE(
    mut v_s_337_: *mut crate::leanh::LeanObject,
    mut v_offset_338_: *mut crate::leanh::LeanObject,
    mut v_h_339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_340_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_341_ = lean_string_utf8_byte_size(v_s_337_);
    v___x_342_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_342_, 0, v_s_337_);
    crate::leanh::lean_ctor_set(v___x_342_, 1, v___x_340_);
    crate::leanh::lean_ctor_set(v___x_342_, 2, v___x_341_);
    v___x_343_ = l_String_Slice_posGE___redArg(v___x_342_, v_offset_338_);
    crate::leanh::lean_dec_ref_known(v___x_342_, 3);
    return v___x_343_;
}
pub unsafe fn l_String_posGT___redArg(
    mut v_s_344_: *mut crate::leanh::LeanObject,
    mut v_offset_345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_346_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_347_ = lean_string_utf8_byte_size(v_s_344_);
    v___x_348_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_348_, 0, v_s_344_);
    crate::leanh::lean_ctor_set(v___x_348_, 1, v___x_346_);
    crate::leanh::lean_ctor_set(v___x_348_, 2, v___x_347_);
    v___x_349_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_350_ = lean_nat_add(v_offset_345_, v___x_349_);
    v___x_351_ = l_String_Slice_posGE___redArg(v___x_348_, v___x_350_);
    crate::leanh::lean_dec_ref_known(v___x_348_, 3);
    return v___x_351_;
}
pub unsafe fn l_String_posGT___redArg___boxed(
    mut v_s_352_: *mut crate::leanh::LeanObject,
    mut v_offset_353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_354_ = l_String_posGT___redArg(v_s_352_, v_offset_353_);
    crate::leanh::lean_dec(v_offset_353_);
    return v_res_354_;
}
pub unsafe fn l_String_posGT(
    mut v_s_355_: *mut crate::leanh::LeanObject,
    mut v_offset_356_: *mut crate::leanh::LeanObject,
    mut v_h_357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_358_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_359_ = lean_string_utf8_byte_size(v_s_355_);
    v___x_360_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_360_, 0, v_s_355_);
    crate::leanh::lean_ctor_set(v___x_360_, 1, v___x_358_);
    crate::leanh::lean_ctor_set(v___x_360_, 2, v___x_359_);
    v___x_361_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_362_ = lean_nat_add(v_offset_356_, v___x_361_);
    v___x_363_ = l_String_Slice_posGE___redArg(v___x_360_, v___x_362_);
    crate::leanh::lean_dec_ref_known(v___x_360_, 3);
    return v___x_363_;
}
pub unsafe fn l_String_posGT___boxed(
    mut v_s_364_: *mut crate::leanh::LeanObject,
    mut v_offset_365_: *mut crate::leanh::LeanObject,
    mut v_h_366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_367_ = l_String_posGT(v_s_364_, v_offset_365_, v_h_366_);
    crate::leanh::lean_dec(v_offset_365_);
    return v_res_367_;
}
pub unsafe fn l_String_Slice_posLE(
    mut v_s_368_: *mut crate::leanh::LeanObject,
    mut v_offset_369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_370_: u8 = 0;
    let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_370_ = l_String_Pos_Raw_isValidForSlice(v_s_368_, v_offset_369_);
                if v___x_370_ == 0 {
                    v___x_371_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_372_ = lean_nat_sub(v_offset_369_, v___x_371_);
                    crate::leanh::lean_dec(v_offset_369_);
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
    mut v_s_374_: *mut crate::leanh::LeanObject,
    mut v_offset_375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_376_ = l_String_Slice_posLE(v_s_374_, v_offset_375_);
    crate::leanh::lean_dec_ref(v_s_374_);
    return v_res_376_;
}
pub unsafe fn l_String_Slice_posLT___redArg(
    mut v_s_377_: *mut crate::leanh::LeanObject,
    mut v_offset_378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_379_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_380_ = lean_nat_sub(v_offset_378_, v___x_379_);
    v___x_381_ = l_String_Slice_posLE(v_s_377_, v___x_380_);
    return v___x_381_;
}
pub unsafe fn l_String_Slice_posLT___redArg___boxed(
    mut v_s_382_: *mut crate::leanh::LeanObject,
    mut v_offset_383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_384_ = l_String_Slice_posLT___redArg(v_s_382_, v_offset_383_);
    crate::leanh::lean_dec(v_offset_383_);
    crate::leanh::lean_dec_ref(v_s_382_);
    return v_res_384_;
}
pub unsafe fn l_String_Slice_posLT(
    mut v_s_385_: *mut crate::leanh::LeanObject,
    mut v_offset_386_: *mut crate::leanh::LeanObject,
    mut v___h_387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_388_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_389_ = lean_nat_sub(v_offset_386_, v___x_388_);
    v___x_390_ = l_String_Slice_posLE(v_s_385_, v___x_389_);
    return v___x_390_;
}
pub unsafe fn l_String_Slice_posLT___boxed(
    mut v_s_391_: *mut crate::leanh::LeanObject,
    mut v_offset_392_: *mut crate::leanh::LeanObject,
    mut v___h_393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_394_ = l_String_Slice_posLT(v_s_391_, v_offset_392_, v___h_393_);
    crate::leanh::lean_dec(v_offset_392_);
    crate::leanh::lean_dec_ref(v_s_391_);
    return v_res_394_;
}
pub unsafe fn l_String_posLE(
    mut v_s_395_: *mut crate::leanh::LeanObject,
    mut v_offset_396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_397_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_398_ = lean_string_utf8_byte_size(v_s_395_);
    v___x_399_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_399_, 0, v_s_395_);
    crate::leanh::lean_ctor_set(v___x_399_, 1, v___x_397_);
    crate::leanh::lean_ctor_set(v___x_399_, 2, v___x_398_);
    v___x_400_ = l_String_Slice_posLE(v___x_399_, v_offset_396_);
    crate::leanh::lean_dec_ref_known(v___x_399_, 3);
    return v___x_400_;
}
pub unsafe fn l_String_posLT___redArg(
    mut v_s_401_: *mut crate::leanh::LeanObject,
    mut v_offset_402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_403_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_404_ = lean_string_utf8_byte_size(v_s_401_);
    v___x_405_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_405_, 0, v_s_401_);
    crate::leanh::lean_ctor_set(v___x_405_, 1, v___x_403_);
    crate::leanh::lean_ctor_set(v___x_405_, 2, v___x_404_);
    v___x_406_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_407_ = lean_nat_sub(v_offset_402_, v___x_406_);
    v___x_408_ = l_String_Slice_posLE(v___x_405_, v___x_407_);
    crate::leanh::lean_dec_ref_known(v___x_405_, 3);
    return v___x_408_;
}
pub unsafe fn l_String_posLT___redArg___boxed(
    mut v_s_409_: *mut crate::leanh::LeanObject,
    mut v_offset_410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_411_ = l_String_posLT___redArg(v_s_409_, v_offset_410_);
    crate::leanh::lean_dec(v_offset_410_);
    return v_res_411_;
}
pub unsafe fn l_String_posLT(
    mut v_s_412_: *mut crate::leanh::LeanObject,
    mut v_offset_413_: *mut crate::leanh::LeanObject,
    mut v_h_414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_415_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_416_ = lean_string_utf8_byte_size(v_s_412_);
    v___x_417_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_417_, 0, v_s_412_);
    crate::leanh::lean_ctor_set(v___x_417_, 1, v___x_415_);
    crate::leanh::lean_ctor_set(v___x_417_, 2, v___x_416_);
    v___x_418_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_419_ = lean_nat_sub(v_offset_413_, v___x_418_);
    v___x_420_ = l_String_Slice_posLE(v___x_417_, v___x_419_);
    crate::leanh::lean_dec_ref_known(v___x_417_, 3);
    return v___x_420_;
}
pub unsafe fn l_String_posLT___boxed(
    mut v_s_421_: *mut crate::leanh::LeanObject,
    mut v_offset_422_: *mut crate::leanh::LeanObject,
    mut v_h_423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_424_ = l_String_posLT(v_s_421_, v_offset_422_, v_h_423_);
    crate::leanh::lean_dec(v_offset_422_);
    return v_res_424_;
}
pub unsafe fn l_String_Slice_Pos_prev___redArg(
    mut v_s_425_: *mut crate::leanh::LeanObject,
    mut v_pos_426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_427_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_428_ = lean_nat_sub(v_pos_426_, v___x_427_);
    v___x_429_ = l_String_Slice_posLE(v_s_425_, v___x_428_);
    return v___x_429_;
}
pub unsafe fn l_String_Slice_Pos_prev___redArg___boxed(
    mut v_s_430_: *mut crate::leanh::LeanObject,
    mut v_pos_431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_432_ = l_String_Slice_Pos_prev___redArg(v_s_430_, v_pos_431_);
    crate::leanh::lean_dec(v_pos_431_);
    crate::leanh::lean_dec_ref(v_s_430_);
    return v_res_432_;
}
pub unsafe fn l_String_Slice_Pos_prev(
    mut v_s_433_: *mut crate::leanh::LeanObject,
    mut v_pos_434_: *mut crate::leanh::LeanObject,
    mut v_h_435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_436_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_437_ = lean_nat_sub(v_pos_434_, v___x_436_);
    v___x_438_ = l_String_Slice_posLE(v_s_433_, v___x_437_);
    return v___x_438_;
}
pub unsafe fn l_String_Slice_Pos_prev___boxed(
    mut v_s_439_: *mut crate::leanh::LeanObject,
    mut v_pos_440_: *mut crate::leanh::LeanObject,
    mut v_h_441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_442_ = l_String_Slice_Pos_prev(v_s_439_, v_pos_440_, v_h_441_);
    crate::leanh::lean_dec(v_pos_440_);
    crate::leanh::lean_dec_ref(v_s_439_);
    return v_res_442_;
}
pub unsafe fn l_String_Slice_Pos_prev_x3f(
    mut v_s_443_: *mut crate::leanh::LeanObject,
    mut v_pos_444_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: u8 = 0;
    v___x_445_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_446_ = lean_nat_dec_eq(v_pos_444_, v___x_445_);
    if v___x_446_ == 0 {
        let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_447_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_448_ = lean_nat_sub(v_pos_444_, v___x_447_);
        v___x_449_ = l_String_Slice_posLE(v_s_443_, v___x_448_);
        v___x_450_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_450_, 0, v___x_449_);
        return v___x_450_;
    } else {
        let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_451_ = crate::leanh::lean_box(0);
        return v___x_451_;
    }
}
pub unsafe fn l_String_Slice_Pos_prev_x3f___boxed(
    mut v_s_452_: *mut crate::leanh::LeanObject,
    mut v_pos_453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_454_ = l_String_Slice_Pos_prev_x3f(v_s_452_, v_pos_453_);
    crate::leanh::lean_dec(v_pos_453_);
    crate::leanh::lean_dec_ref(v_s_452_);
    return v_res_454_;
}
pub unsafe fn l_panic___at___00String_Slice_Pos_prev_x21_spec__0___redArg(
    mut v_msg_455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_456_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_457_ = lean_panic_fn_borrowed(v___x_456_, v_msg_455_);
    return v___x_457_;
}
pub unsafe fn l_panic___at___00String_Slice_Pos_prev_x21_spec__0(
    mut v_s_458_: *mut crate::leanh::LeanObject,
    mut v_msg_459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_460_ = l_panic___at___00String_Slice_Pos_prev_x21_spec__0___redArg(v_msg_459_);
    return v___x_460_;
}
pub unsafe fn l_panic___at___00String_Slice_Pos_prev_x21_spec__0___boxed(
    mut v_s_461_: *mut crate::leanh::LeanObject,
    mut v_msg_462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_463_ = l_panic___at___00String_Slice_Pos_prev_x21_spec__0(v_s_461_, v_msg_462_);
    crate::leanh::lean_dec_ref(v_s_461_);
    return v_res_463_;
}
pub unsafe fn _init_l_String_Slice_Pos_prev_x21___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_467_ = l_String_Slice_Pos_prev_x21___closed__2;
    v___x_468_ = crate::leanh::lean_unsigned_to_nat(31);
    v___x_469_ = crate::leanh::lean_unsigned_to_nat(115);
    v___x_470_ = l_String_Slice_Pos_prev_x21___closed__1;
    v___x_471_ = l_String_Slice_Pos_prev_x21___closed__0;
    v___x_472_ =
        l_mkPanicMessageWithDecl(v___x_471_, v___x_470_, v___x_469_, v___x_468_, v___x_467_);
    return v___x_472_;
}
pub unsafe fn l_String_Slice_Pos_prev_x21(
    mut v_s_473_: *mut crate::leanh::LeanObject,
    mut v_pos_474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: u8 = 0;
    v___x_475_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_476_ = lean_nat_dec_eq(v_pos_474_, v___x_475_);
    if v___x_476_ == 0 {
        let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_477_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_478_ = lean_nat_sub(v_pos_474_, v___x_477_);
        v___x_479_ = l_String_Slice_posLE(v_s_473_, v___x_478_);
        return v___x_479_;
    } else {
        let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_480_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_String_Slice_Pos_prev_x21___closed__3),
            core::ptr::addr_of_mut!(l_String_Slice_Pos_prev_x21___closed__3_once),
            _init_l_String_Slice_Pos_prev_x21___closed__3,
        );
        v___x_481_ = l_panic___at___00String_Slice_Pos_prev_x21_spec__0___redArg(v___x_480_);
        return v___x_481_;
    }
}
pub unsafe fn l_String_Slice_Pos_prev_x21___boxed(
    mut v_s_482_: *mut crate::leanh::LeanObject,
    mut v_pos_483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_484_ = l_String_Slice_Pos_prev_x21(v_s_482_, v_pos_483_);
    crate::leanh::lean_dec(v_pos_483_);
    crate::leanh::lean_dec_ref(v_s_482_);
    return v_res_484_;
}
pub unsafe fn l_String_Pos_prev___redArg(
    mut v_s_485_: *mut crate::leanh::LeanObject,
    mut v_pos_486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_487_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_488_ = lean_string_utf8_byte_size(v_s_485_);
    v___x_489_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_489_, 0, v_s_485_);
    crate::leanh::lean_ctor_set(v___x_489_, 1, v___x_487_);
    crate::leanh::lean_ctor_set(v___x_489_, 2, v___x_488_);
    v___x_490_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_491_ = lean_nat_sub(v_pos_486_, v___x_490_);
    v___x_492_ = l_String_Slice_posLE(v___x_489_, v___x_491_);
    crate::leanh::lean_dec_ref_known(v___x_489_, 3);
    return v___x_492_;
}
pub unsafe fn l_String_Pos_prev___redArg___boxed(
    mut v_s_493_: *mut crate::leanh::LeanObject,
    mut v_pos_494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_495_ = l_String_Pos_prev___redArg(v_s_493_, v_pos_494_);
    crate::leanh::lean_dec(v_pos_494_);
    return v_res_495_;
}
pub unsafe fn l_String_Pos_prev(
    mut v_s_496_: *mut crate::leanh::LeanObject,
    mut v_pos_497_: *mut crate::leanh::LeanObject,
    mut v_h_498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_499_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_500_ = lean_string_utf8_byte_size(v_s_496_);
    v___x_501_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_501_, 0, v_s_496_);
    crate::leanh::lean_ctor_set(v___x_501_, 1, v___x_499_);
    crate::leanh::lean_ctor_set(v___x_501_, 2, v___x_500_);
    v___x_502_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_503_ = lean_nat_sub(v_pos_497_, v___x_502_);
    v___x_504_ = l_String_Slice_posLE(v___x_501_, v___x_503_);
    crate::leanh::lean_dec_ref_known(v___x_501_, 3);
    return v___x_504_;
}
pub unsafe fn l_String_Pos_prev___boxed(
    mut v_s_505_: *mut crate::leanh::LeanObject,
    mut v_pos_506_: *mut crate::leanh::LeanObject,
    mut v_h_507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_508_ = l_String_Pos_prev(v_s_505_, v_pos_506_, v_h_507_);
    crate::leanh::lean_dec(v_pos_506_);
    return v_res_508_;
}
pub unsafe fn l_String_Pos_prev_x3f(
    mut v_s_509_: *mut crate::leanh::LeanObject,
    mut v_pos_510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_519_: u8 = 0;
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_523_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_511_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_512_ = lean_string_utf8_byte_size(v_s_509_);
                v___x_513_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_513_, 0, v_s_509_);
                crate::leanh::lean_ctor_set(v___x_513_, 1, v___x_511_);
                crate::leanh::lean_ctor_set(v___x_513_, 2, v___x_512_);
                v___x_514_ = l_String_Slice_Pos_prev_x3f(v___x_513_, v_pos_510_);
                crate::leanh::lean_dec_ref_known(v___x_513_, 3);
                if crate::leanh::lean_obj_tag(v___x_514_) == 0 {
                    v___x_515_ = crate::leanh::lean_box(0);
                    return v___x_515_;
                } else {
                    v_val_516_ = crate::leanh::lean_ctor_get(v___x_514_, 0);
                    v_isSharedCheck_523_ = (!crate::leanh::lean_is_exclusive(v___x_514_)) as u8;
                    if v_isSharedCheck_523_ == 0 {
                        v___x_518_ = v___x_514_;
                        v_isShared_519_ = v_isSharedCheck_523_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_516_);
                        crate::leanh::lean_dec(v___x_514_);
                        v___x_518_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_522_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_522_, 0, v_val_516_);
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
    mut v_s_524_: *mut crate::leanh::LeanObject,
    mut v_pos_525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_526_ = l_String_Pos_prev_x3f(v_s_524_, v_pos_525_);
    crate::leanh::lean_dec(v_pos_525_);
    return v_res_526_;
}
pub unsafe fn l_String_Pos_prev_x21(
    mut v_s_527_: *mut crate::leanh::LeanObject,
    mut v_pos_528_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_529_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_530_ = lean_string_utf8_byte_size(v_s_527_);
    v___x_531_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_531_, 0, v_s_527_);
    crate::leanh::lean_ctor_set(v___x_531_, 1, v___x_529_);
    crate::leanh::lean_ctor_set(v___x_531_, 2, v___x_530_);
    v___x_532_ = l_String_Slice_Pos_prev_x21(v___x_531_, v_pos_528_);
    crate::leanh::lean_dec_ref_known(v___x_531_, 3);
    return v___x_532_;
}
pub unsafe fn l_String_Pos_prev_x21___boxed(
    mut v_s_533_: *mut crate::leanh::LeanObject,
    mut v_pos_534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_535_ = l_String_Pos_prev_x21(v_s_533_, v_pos_534_);
    crate::leanh::lean_dec(v_pos_534_);
    return v_res_535_;
}
pub unsafe fn l_String_Slice_Pos_prevn(
    mut v_s_536_: *mut crate::leanh::LeanObject,
    mut v_p_537_: *mut crate::leanh::LeanObject,
    mut v_n_538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_540_: u8 = 0;
    let mut v_one_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_547_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_539_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_540_ = lean_nat_dec_eq(v_n_538_, v_zero_539_);
                if v_isZero_540_ == 1 {
                    crate::leanh::lean_dec(v_n_538_);
                    return v_p_537_;
                } else {
                    v_one_541_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_542_ = lean_nat_sub(v_n_538_, v_one_541_);
                    crate::leanh::lean_dec(v_n_538_);
                    v___x_547_ = lean_nat_dec_eq(v_p_537_, v_zero_539_);
                    if v___x_547_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        if v_isZero_540_ == 0 {
                            crate::leanh::lean_dec(v_n_542_);
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
                crate::leanh::lean_dec(v_p_537_);
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
    mut v_s_548_: *mut crate::leanh::LeanObject,
    mut v_p_549_: *mut crate::leanh::LeanObject,
    mut v_n_550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_551_ = l_String_Slice_Pos_prevn(v_s_548_, v_p_549_, v_n_550_);
    crate::leanh::lean_dec_ref(v_s_548_);
    return v_res_551_;
}
pub unsafe fn l_String_Pos_prevn(
    mut v_s_552_: *mut crate::leanh::LeanObject,
    mut v_p_553_: *mut crate::leanh::LeanObject,
    mut v_n_554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_555_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_556_ = lean_string_utf8_byte_size(v_s_552_);
    v___x_557_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_557_, 0, v_s_552_);
    crate::leanh::lean_ctor_set(v___x_557_, 1, v___x_555_);
    crate::leanh::lean_ctor_set(v___x_557_, 2, v___x_556_);
    v___x_558_ = l_String_Slice_Pos_prevn(v___x_557_, v_p_553_, v_n_554_);
    crate::leanh::lean_dec_ref_known(v___x_557_, 3);
    return v___x_558_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_FindPos(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_FindPos(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_FindPos(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_OrderInstances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_FindPos(builtin);
}

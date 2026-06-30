// Lean compiler output
// Module: Lean.Data.Lsp.Utf16
// Imports: Lean.Data.Lsp.BasicAux Lean.DeclarationRange Init.Data.String.Search
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_string_utf8_byte_size,
    lean_string_utf8_get, lean_string_utf8_get_fast, lean_string_utf8_next, lean_uint32_dec_le,
    lean_uint32_to_nat,
};
use crate::r#gen::Init::Data::String::FindPos::l_String_Slice_posLE;
use crate::r#gen::Init::Data::String::Iterate::l_String_Slice_revPositions;
use crate::r#gen::Init::Data::String::Search::{
    initialize_Init_Data_String_Search, runtime_initialize_Init_Data_String_Search,
};
use crate::r#gen::Lean::Data::Lsp::BasicAux::{
    initialize_Lean_Data_Lsp_BasicAux, runtime_initialize_Lean_Data_Lsp_BasicAux,
};
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::DeclarationRange::{
    initialize_Lean_DeclarationRange, runtime_initialize_Lean_DeclarationRange,
};
use crate::r#gen::Lean::Syntax::l_Lean_Syntax_getRange_x3f;
pub unsafe fn l_Char_utf16Size(mut v_c_280_: u32) -> u32 {
    let mut v___x_281_: u32 = 0;
    let mut v___x_282_: u8 = 0;
    v___x_281_ = 65535;
    v___x_282_ = lean_uint32_dec_le(v_c_280_, v___x_281_);
    if v___x_282_ == 0 {
        let mut v___x_283_: u32 = 0;
        v___x_283_ = 2;
        return v___x_283_;
    } else {
        let mut v___x_284_: u32 = 0;
        v___x_284_ = 1;
        return v___x_284_;
    }
}
pub unsafe fn l_Char_utf16Size___boxed(
    mut v_c_285_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_286_: u32 = 0;
    let mut v_res_287_: u32 = 0;
    let mut v_r_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_286_ = leanh::lean_unbox_uint32(v_c_285_);
    leanh::lean_dec(v_c_285_);
    v_res_287_ = l_Char_utf16Size(v_c_boxed_286_);
    v_r_288_ = leanh::lean_box_uint32(v_res_287_);
    return v_r_288_;
}
pub unsafe fn l___private_Lean_Data_Lsp_Utf16_0__String_csize16(
    mut v_c_289_: u32,
) -> *mut leanh::LeanObject {
    let mut v___x_290_: u32 = 0;
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_290_ = l_Char_utf16Size(v_c_289_);
    v___x_291_ = lean_uint32_to_nat(v___x_290_);
    return v___x_291_;
}
pub unsafe fn l___private_Lean_Data_Lsp_Utf16_0__String_csize16___boxed(
    mut v_c_292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_293_: u32 = 0;
    let mut v_res_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_293_ = leanh::lean_unbox_uint32(v_c_292_);
    leanh::lean_dec(v_c_292_);
    v_res_294_ = l___private_Lean_Data_Lsp_Utf16_0__String_csize16(v_c_boxed_293_);
    return v_res_294_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0___redArg(
    mut v___x_295_: *mut leanh::LeanObject,
    mut v_s_296_: *mut leanh::LeanObject,
    mut v_a_297_: *mut leanh::LeanObject,
    mut v_b_298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: u8 = 0;
    let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_prevPos_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_304_: u32 = 0;
    let mut v___x_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_299_ = leanh::lean_unsigned_to_nat(0);
                v___x_300_ = lean_nat_dec_eq(v_a_297_, v___x_299_);
                if v___x_300_ == 0 {
                    v___x_301_ = leanh::lean_unsigned_to_nat(1);
                    v___x_302_ = lean_nat_sub(v_a_297_, v___x_301_);
                    leanh::lean_dec(v_a_297_);
                    v_prevPos_303_ = l_String_Slice_posLE(v___x_295_, v___x_302_);
                    v___x_304_ = lean_string_utf8_get_fast(v_s_296_, v_prevPos_303_);
                    v___x_305_ = l___private_Lean_Data_Lsp_Utf16_0__String_csize16(v___x_304_);
                    v___x_306_ = lean_nat_add(v___x_305_, v_b_298_);
                    leanh::lean_dec(v_b_298_);
                    leanh::lean_dec(v___x_305_);
                    v_a_297_ = v_prevPos_303_;
                    v_b_298_ = v___x_306_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_a_297_);
                    return v_b_298_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0___redArg___boxed(
    mut v___x_308_: *mut leanh::LeanObject,
    mut v_s_309_: *mut leanh::LeanObject,
    mut v_a_310_: *mut leanh::LeanObject,
    mut v_b_311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_312_ = l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0___redArg(
        v___x_308_, v_s_309_, v_a_310_, v_b_311_,
    );
    leanh::lean_dec_ref(v_s_309_);
    leanh::lean_dec_ref(v___x_308_);
    return v_res_312_;
}
pub unsafe fn l_String_utf16Length(
    mut v_s_313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_314_ = leanh::lean_unsigned_to_nat(0);
    v___x_315_ = lean_string_utf8_byte_size(v_s_313_);
    leanh::lean_inc_ref(v_s_313_);
    v___x_316_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_316_, 0, v_s_313_);
    leanh::lean_ctor_set(v___x_316_, 1, v___x_314_);
    leanh::lean_ctor_set(v___x_316_, 2, v___x_315_);
    v___x_317_ = l_String_Slice_revPositions(v___x_316_);
    v___x_318_ = l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0___redArg(
        v___x_316_, v_s_313_, v___x_317_, v___x_314_,
    );
    leanh::lean_dec_ref(v_s_313_);
    leanh::lean_dec_ref_known(v___x_316_, 3);
    return v___x_318_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0(
    mut v___x_319_: *mut leanh::LeanObject,
    mut v_s_320_: *mut leanh::LeanObject,
    mut v_inst_321_: *mut leanh::LeanObject,
    mut v_R_322_: *mut leanh::LeanObject,
    mut v_a_323_: *mut leanh::LeanObject,
    mut v_b_324_: *mut leanh::LeanObject,
    mut v_c_325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_326_ = l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0___redArg(
        v___x_319_, v_s_320_, v_a_323_, v_b_324_,
    );
    return v___x_326_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0___boxed(
    mut v___x_327_: *mut leanh::LeanObject,
    mut v_s_328_: *mut leanh::LeanObject,
    mut v_inst_329_: *mut leanh::LeanObject,
    mut v_R_330_: *mut leanh::LeanObject,
    mut v_a_331_: *mut leanh::LeanObject,
    mut v_b_332_: *mut leanh::LeanObject,
    mut v_c_333_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_334_ = l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0(
        v___x_327_,
        v_s_328_,
        v_inst_329_,
        v_R_330_,
        v_a_331_,
        v_b_332_,
        v_c_333_,
    );
    leanh::lean_dec_ref(v_s_328_);
    leanh::lean_dec_ref(v___x_327_);
    return v_res_334_;
}
pub unsafe fn l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux(
    mut v_s_335_: *mut leanh::LeanObject,
    mut v_x_336_: *mut leanh::LeanObject,
    mut v_x_337_: *mut leanh::LeanObject,
    mut v_x_338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_340_: u8 = 0;
    let mut v_one_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: u32 = 0;
    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_339_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_340_ = lean_nat_dec_eq(v_x_336_, v_zero_339_);
                if v_isZero_340_ == 1 {
                    leanh::lean_dec(v_x_337_);
                    leanh::lean_dec(v_x_336_);
                    return v_x_338_;
                } else {
                    v_one_341_ = leanh::lean_unsigned_to_nat(1);
                    v_n_342_ = lean_nat_sub(v_x_336_, v_one_341_);
                    leanh::lean_dec(v_x_336_);
                    v___x_343_ = lean_string_utf8_next(v_s_335_, v_x_337_);
                    v___x_344_ = lean_string_utf8_get(v_s_335_, v_x_337_);
                    leanh::lean_dec(v_x_337_);
                    v___x_345_ = l___private_Lean_Data_Lsp_Utf16_0__String_csize16(v___x_344_);
                    v___x_346_ = lean_nat_add(v_x_338_, v___x_345_);
                    leanh::lean_dec(v___x_345_);
                    leanh::lean_dec(v_x_338_);
                    v_x_336_ = v_n_342_;
                    v_x_337_ = v___x_343_;
                    v_x_338_ = v___x_346_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux___boxed(
    mut v_s_348_: *mut leanh::LeanObject,
    mut v_x_349_: *mut leanh::LeanObject,
    mut v_x_350_: *mut leanh::LeanObject,
    mut v_x_351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_352_ = l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux(
        v_s_348_, v_x_349_, v_x_350_, v_x_351_,
    );
    leanh::lean_dec_ref(v_s_348_);
    return v_res_352_;
}
pub unsafe fn l_String_codepointPosToUtf16PosFrom(
    mut v_s_353_: *mut leanh::LeanObject,
    mut v_n_354_: *mut leanh::LeanObject,
    mut v_off_355_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_356_ = leanh::lean_unsigned_to_nat(0);
    v___x_357_ = l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux(
        v_s_353_, v_n_354_, v_off_355_, v___x_356_,
    );
    return v___x_357_;
}
pub unsafe fn l_String_codepointPosToUtf16PosFrom___boxed(
    mut v_s_358_: *mut leanh::LeanObject,
    mut v_n_359_: *mut leanh::LeanObject,
    mut v_off_360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_361_ = l_String_codepointPosToUtf16PosFrom(v_s_358_, v_n_359_, v_off_360_);
    leanh::lean_dec_ref(v_s_358_);
    return v_res_361_;
}
pub unsafe fn l_String_codepointPosToUtf16Pos(
    mut v_s_362_: *mut leanh::LeanObject,
    mut v_pos_363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_364_ = leanh::lean_unsigned_to_nat(0);
    v___x_365_ = l_String_codepointPosToUtf16PosFrom(v_s_362_, v_pos_363_, v___x_364_);
    return v___x_365_;
}
pub unsafe fn l_String_codepointPosToUtf16Pos___boxed(
    mut v_s_366_: *mut leanh::LeanObject,
    mut v_pos_367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_368_ = l_String_codepointPosToUtf16Pos(v_s_366_, v_pos_367_);
    leanh::lean_dec_ref(v_s_366_);
    return v_res_368_;
}
pub unsafe fn l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux(
    mut v_s_369_: *mut leanh::LeanObject,
    mut v_x_370_: *mut leanh::LeanObject,
    mut v_x_371_: *mut leanh::LeanObject,
    mut v_x_372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: u8 = 0;
    let mut v___x_375_: u32 = 0;
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_373_ = leanh::lean_unsigned_to_nat(0);
                v___x_374_ = lean_nat_dec_eq(v_x_370_, v___x_373_);
                if v___x_374_ == 0 {
                    v___x_375_ = lean_string_utf8_get(v_s_369_, v_x_371_);
                    v___x_376_ = l___private_Lean_Data_Lsp_Utf16_0__String_csize16(v___x_375_);
                    v___x_377_ = lean_nat_sub(v_x_370_, v___x_376_);
                    leanh::lean_dec(v___x_376_);
                    leanh::lean_dec(v_x_370_);
                    v___x_378_ = lean_string_utf8_next(v_s_369_, v_x_371_);
                    leanh::lean_dec(v_x_371_);
                    v___x_379_ = leanh::lean_unsigned_to_nat(1);
                    v___x_380_ = lean_nat_add(v_x_372_, v___x_379_);
                    leanh::lean_dec(v_x_372_);
                    v_x_370_ = v___x_377_;
                    v_x_371_ = v___x_378_;
                    v_x_372_ = v___x_380_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_x_371_);
                    leanh::lean_dec(v_x_370_);
                    return v_x_372_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux___boxed(
    mut v_s_382_: *mut leanh::LeanObject,
    mut v_x_383_: *mut leanh::LeanObject,
    mut v_x_384_: *mut leanh::LeanObject,
    mut v_x_385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_386_ = l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux(
        v_s_382_, v_x_383_, v_x_384_, v_x_385_,
    );
    leanh::lean_dec_ref(v_s_382_);
    return v_res_386_;
}
pub unsafe fn l_String_utf16PosToCodepointPosFrom(
    mut v_s_387_: *mut leanh::LeanObject,
    mut v_utf16pos_388_: *mut leanh::LeanObject,
    mut v_off_389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_390_ = leanh::lean_unsigned_to_nat(0);
    v___x_391_ = l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux(
        v_s_387_,
        v_utf16pos_388_,
        v_off_389_,
        v___x_390_,
    );
    return v___x_391_;
}
pub unsafe fn l_String_utf16PosToCodepointPosFrom___boxed(
    mut v_s_392_: *mut leanh::LeanObject,
    mut v_utf16pos_393_: *mut leanh::LeanObject,
    mut v_off_394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_395_ = l_String_utf16PosToCodepointPosFrom(v_s_392_, v_utf16pos_393_, v_off_394_);
    leanh::lean_dec_ref(v_s_392_);
    return v_res_395_;
}
pub unsafe fn l_String_utf16PosToCodepointPos(
    mut v_s_396_: *mut leanh::LeanObject,
    mut v_pos_397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_398_ = leanh::lean_unsigned_to_nat(0);
    v___x_399_ = l_String_utf16PosToCodepointPosFrom(v_s_396_, v_pos_397_, v___x_398_);
    return v___x_399_;
}
pub unsafe fn l_String_utf16PosToCodepointPos___boxed(
    mut v_s_400_: *mut leanh::LeanObject,
    mut v_pos_401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_402_ = l_String_utf16PosToCodepointPos(v_s_400_, v_pos_401_);
    leanh::lean_dec_ref(v_s_400_);
    return v_res_402_;
}
pub unsafe fn l_String_codepointPosToUtf8PosFrom(
    mut v_s_403_: *mut leanh::LeanObject,
    mut v_x_404_: *mut leanh::LeanObject,
    mut v_x_405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_407_: u8 = 0;
    let mut v_one_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_406_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_407_ = lean_nat_dec_eq(v_x_405_, v_zero_406_);
                if v_isZero_407_ == 1 {
                    leanh::lean_dec(v_x_405_);
                    return v_x_404_;
                } else {
                    v_one_408_ = leanh::lean_unsigned_to_nat(1);
                    v_n_409_ = lean_nat_sub(v_x_405_, v_one_408_);
                    leanh::lean_dec(v_x_405_);
                    v___x_410_ = lean_string_utf8_next(v_s_403_, v_x_404_);
                    leanh::lean_dec(v_x_404_);
                    v_x_404_ = v___x_410_;
                    v_x_405_ = v_n_409_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_codepointPosToUtf8PosFrom___boxed(
    mut v_s_412_: *mut leanh::LeanObject,
    mut v_x_413_: *mut leanh::LeanObject,
    mut v_x_414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_415_ = l_String_codepointPosToUtf8PosFrom(v_s_412_, v_x_413_, v_x_414_);
    leanh::lean_dec_ref(v_s_412_);
    return v_res_415_;
}
pub unsafe fn l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos(
    mut v_text_416_: *mut leanh::LeanObject,
    mut v_line_417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_positions_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: u8 = 0;
    v_positions_418_ = leanh::lean_ctor_get(v_text_416_, 1);
    v___x_419_ = lean_array_get_size(v_positions_418_);
    v___x_420_ = lean_nat_dec_lt(v_line_417_, v___x_419_);
    if v___x_420_ == 0 {
        let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_422_: u8 = 0;
        v___x_421_ = leanh::lean_unsigned_to_nat(0);
        v___x_422_ = lean_nat_dec_eq(v___x_419_, v___x_421_);
        if v___x_422_ == 0 {
            let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_425_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_423_ = leanh::lean_unsigned_to_nat(1);
            v___x_424_ = lean_nat_sub(v___x_419_, v___x_423_);
            v___x_425_ = lean_array_get_borrowed(v___x_421_, v_positions_418_, v___x_424_);
            leanh::lean_dec(v___x_424_);
            leanh::lean_inc(v___x_425_);
            return v___x_425_;
        } else {
            return v___x_421_;
        }
    } else {
        let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_426_ = lean_array_fget_borrowed(v_positions_418_, v_line_417_);
        leanh::lean_inc(v___x_426_);
        return v___x_426_;
    }
}
pub unsafe fn l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos___boxed(
    mut v_text_427_: *mut leanh::LeanObject,
    mut v_line_428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_429_ =
        l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos(v_text_427_, v_line_428_);
    leanh::lean_dec(v_line_428_);
    leanh::lean_dec_ref(v_text_427_);
    return v_res_429_;
}
pub unsafe fn l_Lean_FileMap_lspPosToUtf8Pos(
    mut v_text_430_: *mut leanh::LeanObject,
    mut v_pos_431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_line_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lineStartPos_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_chr_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_line_432_ = leanh::lean_ctor_get(v_pos_431_, 0);
    leanh::lean_inc(v_line_432_);
    v_character_433_ = leanh::lean_ctor_get(v_pos_431_, 1);
    leanh::lean_inc(v_character_433_);
    leanh::lean_dec_ref(v_pos_431_);
    v_source_434_ = leanh::lean_ctor_get(v_text_430_, 0);
    v_lineStartPos_435_ =
        l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos(v_text_430_, v_line_432_);
    leanh::lean_dec(v_line_432_);
    leanh::lean_inc(v_lineStartPos_435_);
    v_chr_436_ =
        l_String_utf16PosToCodepointPosFrom(v_source_434_, v_character_433_, v_lineStartPos_435_);
    v___x_437_ = l_String_codepointPosToUtf8PosFrom(v_source_434_, v_lineStartPos_435_, v_chr_436_);
    return v___x_437_;
}
pub unsafe fn l_Lean_FileMap_lspPosToUtf8Pos___boxed(
    mut v_text_438_: *mut leanh::LeanObject,
    mut v_pos_439_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_440_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_438_, v_pos_439_);
    leanh::lean_dec_ref(v_text_438_);
    return v_res_440_;
}
pub unsafe fn l_Lean_FileMap_leanPosToLspPos(
    mut v_text_441_: *mut leanh::LeanObject,
    mut v_x_442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_line_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_451_: u8 = 0;
    let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_456_: u8 = 0;
    let mut v_unused_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_443_ = leanh::lean_ctor_get(v_x_442_, 0);
                leanh::lean_inc(v_line_443_);
                v_column_444_ = leanh::lean_ctor_get(v_x_442_, 1);
                leanh::lean_inc(v_column_444_);
                leanh::lean_dec_ref(v_x_442_);
                v_source_445_ = leanh::lean_ctor_get(v_text_441_, 0);
                leanh::lean_inc_ref(v_source_445_);
                v___x_446_ = leanh::lean_unsigned_to_nat(1);
                v___x_447_ = lean_nat_sub(v_line_443_, v___x_446_);
                leanh::lean_dec(v_line_443_);
                v___x_448_ = l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos(
                    v_text_441_,
                    v___x_447_,
                );
                v_isSharedCheck_456_ = (!leanh::lean_is_exclusive(v_text_441_)) as u8;
                if v_isSharedCheck_456_ == 0 {
                    v_unused_457_ = leanh::lean_ctor_get(v_text_441_, 1);
                    leanh::lean_dec(v_unused_457_);
                    v_unused_458_ = leanh::lean_ctor_get(v_text_441_, 0);
                    leanh::lean_dec(v_unused_458_);
                    v___x_450_ = v_text_441_;
                    v_isShared_451_ = v_isSharedCheck_456_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_text_441_);
                    v___x_450_ = leanh::lean_box(0);
                    v_isShared_451_ = v_isSharedCheck_456_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_452_ =
                    l_String_codepointPosToUtf16PosFrom(v_source_445_, v_column_444_, v___x_448_);
                leanh::lean_dec_ref(v_source_445_);
                if v_isShared_451_ == 0 {
                    leanh::lean_ctor_set(v___x_450_, 1, v___x_452_);
                    leanh::lean_ctor_set(v___x_450_, 0, v___x_447_);
                    v___x_454_ = v___x_450_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_455_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_447_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_455_, 1, v___x_452_);
                    v___x_454_ = v_reuseFailAlloc_455_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_454_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_FileMap_utf8PosToLspPos(
    mut v_text_459_: *mut leanh::LeanObject,
    mut v_pos_460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_text_459_);
    v___x_461_ = l_Lean_FileMap_toPosition(v_text_459_, v_pos_460_);
    v___x_462_ = l_Lean_FileMap_leanPosToLspPos(v_text_459_, v___x_461_);
    return v___x_462_;
}
pub unsafe fn l_Lean_FileMap_utf8PosToLspPos___boxed(
    mut v_text_463_: *mut leanh::LeanObject,
    mut v_pos_464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_465_ = l_Lean_FileMap_utf8PosToLspPos(v_text_463_, v_pos_464_);
    leanh::lean_dec(v_pos_464_);
    return v_res_465_;
}
pub unsafe fn l_Lean_FileMap_utf8RangeToLspRange(
    mut v_text_466_: *mut leanh::LeanObject,
    mut v_range_467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_start_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_472_: u8 = 0;
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_478_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_468_ = leanh::lean_ctor_get(v_range_467_, 0);
                v_stop_469_ = leanh::lean_ctor_get(v_range_467_, 1);
                v_isSharedCheck_478_ = (!leanh::lean_is_exclusive(v_range_467_)) as u8;
                if v_isSharedCheck_478_ == 0 {
                    v___x_471_ = v_range_467_;
                    v_isShared_472_ = v_isSharedCheck_478_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_469_);
                    leanh::lean_inc(v_start_468_);
                    leanh::lean_dec(v_range_467_);
                    v___x_471_ = leanh::lean_box(0);
                    v_isShared_472_ = v_isSharedCheck_478_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_text_466_);
                v___x_473_ = l_Lean_FileMap_utf8PosToLspPos(v_text_466_, v_start_468_);
                leanh::lean_dec(v_start_468_);
                v___x_474_ = l_Lean_FileMap_utf8PosToLspPos(v_text_466_, v_stop_469_);
                leanh::lean_dec(v_stop_469_);
                if v_isShared_472_ == 0 {
                    leanh::lean_ctor_set(v___x_471_, 1, v___x_474_);
                    leanh::lean_ctor_set(v___x_471_, 0, v___x_473_);
                    v___x_476_ = v___x_471_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_477_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_473_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_477_, 1, v___x_474_);
                    v___x_476_ = v_reuseFailAlloc_477_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_476_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_FileMap_lspRangeOfStx_x3f(
    mut v_text_479_: *mut leanh::LeanObject,
    mut v_stx_480_: *mut leanh::LeanObject,
    mut v_canonicalOnly_481_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_487_: u8 = 0;
    let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_492_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_482_ = l_Lean_Syntax_getRange_x3f(v_stx_480_, v_canonicalOnly_481_);
                if leanh::lean_obj_tag(v___x_482_) == 0 {
                    leanh::lean_dec_ref(v_text_479_);
                    v___x_483_ = leanh::lean_box(0);
                    return v___x_483_;
                } else {
                    v_val_484_ = leanh::lean_ctor_get(v___x_482_, 0);
                    v_isSharedCheck_492_ = (!leanh::lean_is_exclusive(v___x_482_)) as u8;
                    if v_isSharedCheck_492_ == 0 {
                        v___x_486_ = v___x_482_;
                        v_isShared_487_ = v_isSharedCheck_492_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_484_);
                        leanh::lean_dec(v___x_482_);
                        v___x_486_ = leanh::lean_box(0);
                        v_isShared_487_ = v_isSharedCheck_492_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_488_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_479_, v_val_484_);
                if v_isShared_487_ == 0 {
                    leanh::lean_ctor_set(v___x_486_, 0, v___x_488_);
                    v___x_490_ = v___x_486_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_491_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_488_);
                    v___x_490_ = v_reuseFailAlloc_491_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_490_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_FileMap_lspRangeOfStx_x3f___boxed(
    mut v_text_493_: *mut leanh::LeanObject,
    mut v_stx_494_: *mut leanh::LeanObject,
    mut v_canonicalOnly_495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_canonicalOnly_boxed_496_: u8 = 0;
    let mut v_res_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_496_ = (leanh::lean_unbox(v_canonicalOnly_495_) as u8);
    v_res_497_ =
        l_Lean_FileMap_lspRangeOfStx_x3f(v_text_493_, v_stx_494_, v_canonicalOnly_boxed_496_);
    leanh::lean_dec(v_stx_494_);
    return v_res_497_;
}
pub unsafe fn l_Lean_FileMap_lspRangeToUtf8Range(
    mut v_text_498_: *mut leanh::LeanObject,
    mut v_range_499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_start_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_504_: u8 = 0;
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_510_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_500_ = leanh::lean_ctor_get(v_range_499_, 0);
                v_end_501_ = leanh::lean_ctor_get(v_range_499_, 1);
                v_isSharedCheck_510_ = (!leanh::lean_is_exclusive(v_range_499_)) as u8;
                if v_isSharedCheck_510_ == 0 {
                    v___x_503_ = v_range_499_;
                    v_isShared_504_ = v_isSharedCheck_510_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_end_501_);
                    leanh::lean_inc(v_start_500_);
                    leanh::lean_dec(v_range_499_);
                    v___x_503_ = leanh::lean_box(0);
                    v_isShared_504_ = v_isSharedCheck_510_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_505_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_498_, v_start_500_);
                v___x_506_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_498_, v_end_501_);
                if v_isShared_504_ == 0 {
                    leanh::lean_ctor_set(v___x_503_, 1, v___x_506_);
                    leanh::lean_ctor_set(v___x_503_, 0, v___x_505_);
                    v___x_508_ = v___x_503_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_509_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_505_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_509_, 1, v___x_506_);
                    v___x_508_ = v_reuseFailAlloc_509_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_508_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_FileMap_lspRangeToUtf8Range___boxed(
    mut v_text_511_: *mut leanh::LeanObject,
    mut v_range_512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_513_ = l_Lean_FileMap_lspRangeToUtf8Range(v_text_511_, v_range_512_);
    leanh::lean_dec_ref(v_text_511_);
    return v_res_513_;
}
pub unsafe fn l_Lean_DeclarationRange_ofFilePositions(
    mut v_text_514_: *mut leanh::LeanObject,
    mut v_pos_515_: *mut leanh::LeanObject,
    mut v_endPos_516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref(v_pos_515_);
    leanh::lean_inc_ref(v_text_514_);
    v___x_517_ = l_Lean_FileMap_leanPosToLspPos(v_text_514_, v_pos_515_);
    v_character_518_ = leanh::lean_ctor_get(v___x_517_, 1);
    leanh::lean_inc(v_character_518_);
    leanh::lean_dec_ref(v___x_517_);
    leanh::lean_inc_ref(v_endPos_516_);
    v___x_519_ = l_Lean_FileMap_leanPosToLspPos(v_text_514_, v_endPos_516_);
    v_character_520_ = leanh::lean_ctor_get(v___x_519_, 1);
    leanh::lean_inc(v_character_520_);
    leanh::lean_dec_ref(v___x_519_);
    v___x_521_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_521_, 0, v_pos_515_);
    leanh::lean_ctor_set(v___x_521_, 1, v_character_518_);
    leanh::lean_ctor_set(v___x_521_, 2, v_endPos_516_);
    leanh::lean_ctor_set(v___x_521_, 3, v_character_520_);
    return v___x_521_;
}
pub unsafe fn l_Lean_DeclarationRange_ofStringPositions(
    mut v_text_522_: *mut leanh::LeanObject,
    mut v_pos_523_: *mut leanh::LeanObject,
    mut v_endPos_524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_text_522_, 2);
    v___x_525_ = l_Lean_FileMap_toPosition(v_text_522_, v_pos_523_);
    v___x_526_ = l_Lean_FileMap_toPosition(v_text_522_, v_endPos_524_);
    v___x_527_ = l_Lean_DeclarationRange_ofFilePositions(v_text_522_, v___x_525_, v___x_526_);
    return v___x_527_;
}
pub unsafe fn l_Lean_DeclarationRange_ofStringPositions___boxed(
    mut v_text_528_: *mut leanh::LeanObject,
    mut v_pos_529_: *mut leanh::LeanObject,
    mut v_endPos_530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_531_ = l_Lean_DeclarationRange_ofStringPositions(v_text_528_, v_pos_529_, v_endPos_530_);
    leanh::lean_dec(v_endPos_530_);
    leanh::lean_dec(v_pos_529_);
    return v_res_531_;
}
pub unsafe fn l_Lean_DeclarationRange_toLspRange(
    mut v_r_532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pos_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_charUtf16_535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endCharUtf16_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_540_: u8 = 0;
    let mut v_line_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_544_: u8 = 0;
    let mut v___x_545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_555_: u8 = 0;
    let mut v_unused_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_557_: u8 = 0;
    let mut v_unused_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pos_533_ = leanh::lean_ctor_get(v_r_532_, 0);
                leanh::lean_inc_ref(v_pos_533_);
                v_endPos_534_ = leanh::lean_ctor_get(v_r_532_, 2);
                leanh::lean_inc_ref(v_endPos_534_);
                v_charUtf16_535_ = leanh::lean_ctor_get(v_r_532_, 1);
                leanh::lean_inc(v_charUtf16_535_);
                v_endCharUtf16_536_ = leanh::lean_ctor_get(v_r_532_, 3);
                leanh::lean_inc(v_endCharUtf16_536_);
                leanh::lean_dec_ref(v_r_532_);
                v_line_537_ = leanh::lean_ctor_get(v_pos_533_, 0);
                v_isSharedCheck_557_ = (!leanh::lean_is_exclusive(v_pos_533_)) as u8;
                if v_isSharedCheck_557_ == 0 {
                    v_unused_558_ = leanh::lean_ctor_get(v_pos_533_, 1);
                    leanh::lean_dec(v_unused_558_);
                    v___x_539_ = v_pos_533_;
                    v_isShared_540_ = v_isSharedCheck_557_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_line_537_);
                    leanh::lean_dec(v_pos_533_);
                    v___x_539_ = leanh::lean_box(0);
                    v_isShared_540_ = v_isSharedCheck_557_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_line_541_ = leanh::lean_ctor_get(v_endPos_534_, 0);
                v_isSharedCheck_555_ = (!leanh::lean_is_exclusive(v_endPos_534_)) as u8;
                if v_isSharedCheck_555_ == 0 {
                    v_unused_556_ = leanh::lean_ctor_get(v_endPos_534_, 1);
                    leanh::lean_dec(v_unused_556_);
                    v___x_543_ = v_endPos_534_;
                    v_isShared_544_ = v_isSharedCheck_555_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_line_541_);
                    leanh::lean_dec(v_endPos_534_);
                    v___x_543_ = leanh::lean_box(0);
                    v_isShared_544_ = v_isSharedCheck_555_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_545_ = leanh::lean_unsigned_to_nat(1);
                v___x_546_ = lean_nat_sub(v_line_537_, v___x_545_);
                leanh::lean_dec(v_line_537_);
                if v_isShared_544_ == 0 {
                    leanh::lean_ctor_set(v___x_543_, 1, v_charUtf16_535_);
                    leanh::lean_ctor_set(v___x_543_, 0, v___x_546_);
                    v___x_548_ = v___x_543_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_554_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_546_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_554_, 1, v_charUtf16_535_);
                    v___x_548_ = v_reuseFailAlloc_554_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_549_ = lean_nat_sub(v_line_541_, v___x_545_);
                leanh::lean_dec(v_line_541_);
                if v_isShared_540_ == 0 {
                    leanh::lean_ctor_set(v___x_539_, 1, v_endCharUtf16_536_);
                    leanh::lean_ctor_set(v___x_539_, 0, v___x_549_);
                    v___x_551_ = v___x_539_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_553_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_549_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_553_, 1, v_endCharUtf16_536_);
                    v___x_551_ = v_reuseFailAlloc_553_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_552_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_552_, 0, v___x_548_);
                leanh::lean_ctor_set(v___x_552_, 1, v___x_551_);
                return v___x_552_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Lsp_Utf16(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Lsp_BasicAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DeclarationRange(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Lsp_Utf16(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Lsp_Utf16(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Lsp_BasicAux(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_DeclarationRange(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Utf16(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Lsp_Utf16(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Lsp_Utf16(builtin);
}
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
    mut v_c_285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_286_: u32 = 0;
    let mut v_res_287_: u32 = 0;
    let mut v_r_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_286_ = crate::leanh::lean_unbox_uint32(v_c_285_);
    crate::leanh::lean_dec(v_c_285_);
    v_res_287_ = l_Char_utf16Size(v_c_boxed_286_);
    v_r_288_ = crate::leanh::lean_box_uint32(v_res_287_);
    return v_r_288_;
}
pub unsafe fn l___private_Lean_Data_Lsp_Utf16_0__String_csize16(
    mut v_c_289_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_290_: u32 = 0;
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_290_ = l_Char_utf16Size(v_c_289_);
    v___x_291_ = lean_uint32_to_nat(v___x_290_);
    return v___x_291_;
}
pub unsafe fn l___private_Lean_Data_Lsp_Utf16_0__String_csize16___boxed(
    mut v_c_292_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_293_: u32 = 0;
    let mut v_res_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_293_ = crate::leanh::lean_unbox_uint32(v_c_292_);
    crate::leanh::lean_dec(v_c_292_);
    v_res_294_ = l___private_Lean_Data_Lsp_Utf16_0__String_csize16(v_c_boxed_293_);
    return v_res_294_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0___redArg(
    mut v___x_295_: *mut crate::leanh::LeanObject,
    mut v_s_296_: *mut crate::leanh::LeanObject,
    mut v_a_297_: *mut crate::leanh::LeanObject,
    mut v_b_298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: u8 = 0;
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_prevPos_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_304_: u32 = 0;
    let mut v___x_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_299_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_300_ = lean_nat_dec_eq(v_a_297_, v___x_299_);
                if v___x_300_ == 0 {
                    v___x_301_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_302_ = lean_nat_sub(v_a_297_, v___x_301_);
                    crate::leanh::lean_dec(v_a_297_);
                    v_prevPos_303_ = l_String_Slice_posLE(v___x_295_, v___x_302_);
                    v___x_304_ = lean_string_utf8_get_fast(v_s_296_, v_prevPos_303_);
                    v___x_305_ = l___private_Lean_Data_Lsp_Utf16_0__String_csize16(v___x_304_);
                    v___x_306_ = lean_nat_add(v___x_305_, v_b_298_);
                    crate::leanh::lean_dec(v_b_298_);
                    crate::leanh::lean_dec(v___x_305_);
                    v_a_297_ = v_prevPos_303_;
                    v_b_298_ = v___x_306_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_297_);
                    return v_b_298_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0___redArg___boxed(
    mut v___x_308_: *mut crate::leanh::LeanObject,
    mut v_s_309_: *mut crate::leanh::LeanObject,
    mut v_a_310_: *mut crate::leanh::LeanObject,
    mut v_b_311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_312_ = l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0___redArg(
        v___x_308_, v_s_309_, v_a_310_, v_b_311_,
    );
    crate::leanh::lean_dec_ref(v_s_309_);
    crate::leanh::lean_dec_ref(v___x_308_);
    return v_res_312_;
}
pub unsafe fn l_String_utf16Length(
    mut v_s_313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_314_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_315_ = lean_string_utf8_byte_size(v_s_313_);
    crate::leanh::lean_inc_ref(v_s_313_);
    v___x_316_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_316_, 0, v_s_313_);
    crate::leanh::lean_ctor_set(v___x_316_, 1, v___x_314_);
    crate::leanh::lean_ctor_set(v___x_316_, 2, v___x_315_);
    v___x_317_ = l_String_Slice_revPositions(v___x_316_);
    v___x_318_ = l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0___redArg(
        v___x_316_, v_s_313_, v___x_317_, v___x_314_,
    );
    crate::leanh::lean_dec_ref(v_s_313_);
    crate::leanh::lean_dec_ref_known(v___x_316_, 3);
    return v___x_318_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0(
    mut v___x_319_: *mut crate::leanh::LeanObject,
    mut v_s_320_: *mut crate::leanh::LeanObject,
    mut v_inst_321_: *mut crate::leanh::LeanObject,
    mut v_R_322_: *mut crate::leanh::LeanObject,
    mut v_a_323_: *mut crate::leanh::LeanObject,
    mut v_b_324_: *mut crate::leanh::LeanObject,
    mut v_c_325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_326_ = l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0___redArg(
        v___x_319_, v_s_320_, v_a_323_, v_b_324_,
    );
    return v___x_326_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0___boxed(
    mut v___x_327_: *mut crate::leanh::LeanObject,
    mut v_s_328_: *mut crate::leanh::LeanObject,
    mut v_inst_329_: *mut crate::leanh::LeanObject,
    mut v_R_330_: *mut crate::leanh::LeanObject,
    mut v_a_331_: *mut crate::leanh::LeanObject,
    mut v_b_332_: *mut crate::leanh::LeanObject,
    mut v_c_333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_334_ = l_WellFounded_opaqueFix_u2083___at___00String_utf16Length_spec__0(
        v___x_327_,
        v_s_328_,
        v_inst_329_,
        v_R_330_,
        v_a_331_,
        v_b_332_,
        v_c_333_,
    );
    crate::leanh::lean_dec_ref(v_s_328_);
    crate::leanh::lean_dec_ref(v___x_327_);
    return v_res_334_;
}
pub unsafe fn l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux(
    mut v_s_335_: *mut crate::leanh::LeanObject,
    mut v_x_336_: *mut crate::leanh::LeanObject,
    mut v_x_337_: *mut crate::leanh::LeanObject,
    mut v_x_338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_340_: u8 = 0;
    let mut v_one_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: u32 = 0;
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_339_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_340_ = lean_nat_dec_eq(v_x_336_, v_zero_339_);
                if v_isZero_340_ == 1 {
                    crate::leanh::lean_dec(v_x_337_);
                    crate::leanh::lean_dec(v_x_336_);
                    return v_x_338_;
                } else {
                    v_one_341_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_342_ = lean_nat_sub(v_x_336_, v_one_341_);
                    crate::leanh::lean_dec(v_x_336_);
                    v___x_343_ = lean_string_utf8_next(v_s_335_, v_x_337_);
                    v___x_344_ = lean_string_utf8_get(v_s_335_, v_x_337_);
                    crate::leanh::lean_dec(v_x_337_);
                    v___x_345_ = l___private_Lean_Data_Lsp_Utf16_0__String_csize16(v___x_344_);
                    v___x_346_ = lean_nat_add(v_x_338_, v___x_345_);
                    crate::leanh::lean_dec(v___x_345_);
                    crate::leanh::lean_dec(v_x_338_);
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
    mut v_s_348_: *mut crate::leanh::LeanObject,
    mut v_x_349_: *mut crate::leanh::LeanObject,
    mut v_x_350_: *mut crate::leanh::LeanObject,
    mut v_x_351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_352_ = l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux(
        v_s_348_, v_x_349_, v_x_350_, v_x_351_,
    );
    crate::leanh::lean_dec_ref(v_s_348_);
    return v_res_352_;
}
pub unsafe fn l_String_codepointPosToUtf16PosFrom(
    mut v_s_353_: *mut crate::leanh::LeanObject,
    mut v_n_354_: *mut crate::leanh::LeanObject,
    mut v_off_355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_356_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_357_ = l___private_Lean_Data_Lsp_Utf16_0__String_codepointPosToUtf16PosFromAux(
        v_s_353_, v_n_354_, v_off_355_, v___x_356_,
    );
    return v___x_357_;
}
pub unsafe fn l_String_codepointPosToUtf16PosFrom___boxed(
    mut v_s_358_: *mut crate::leanh::LeanObject,
    mut v_n_359_: *mut crate::leanh::LeanObject,
    mut v_off_360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_361_ = l_String_codepointPosToUtf16PosFrom(v_s_358_, v_n_359_, v_off_360_);
    crate::leanh::lean_dec_ref(v_s_358_);
    return v_res_361_;
}
pub unsafe fn l_String_codepointPosToUtf16Pos(
    mut v_s_362_: *mut crate::leanh::LeanObject,
    mut v_pos_363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_364_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_365_ = l_String_codepointPosToUtf16PosFrom(v_s_362_, v_pos_363_, v___x_364_);
    return v___x_365_;
}
pub unsafe fn l_String_codepointPosToUtf16Pos___boxed(
    mut v_s_366_: *mut crate::leanh::LeanObject,
    mut v_pos_367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_368_ = l_String_codepointPosToUtf16Pos(v_s_366_, v_pos_367_);
    crate::leanh::lean_dec_ref(v_s_366_);
    return v_res_368_;
}
pub unsafe fn l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux(
    mut v_s_369_: *mut crate::leanh::LeanObject,
    mut v_x_370_: *mut crate::leanh::LeanObject,
    mut v_x_371_: *mut crate::leanh::LeanObject,
    mut v_x_372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: u8 = 0;
    let mut v___x_375_: u32 = 0;
    let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_373_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_374_ = lean_nat_dec_eq(v_x_370_, v___x_373_);
                if v___x_374_ == 0 {
                    v___x_375_ = lean_string_utf8_get(v_s_369_, v_x_371_);
                    v___x_376_ = l___private_Lean_Data_Lsp_Utf16_0__String_csize16(v___x_375_);
                    v___x_377_ = lean_nat_sub(v_x_370_, v___x_376_);
                    crate::leanh::lean_dec(v___x_376_);
                    crate::leanh::lean_dec(v_x_370_);
                    v___x_378_ = lean_string_utf8_next(v_s_369_, v_x_371_);
                    crate::leanh::lean_dec(v_x_371_);
                    v___x_379_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_380_ = lean_nat_add(v_x_372_, v___x_379_);
                    crate::leanh::lean_dec(v_x_372_);
                    v_x_370_ = v___x_377_;
                    v_x_371_ = v___x_378_;
                    v_x_372_ = v___x_380_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_x_371_);
                    crate::leanh::lean_dec(v_x_370_);
                    return v_x_372_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux___boxed(
    mut v_s_382_: *mut crate::leanh::LeanObject,
    mut v_x_383_: *mut crate::leanh::LeanObject,
    mut v_x_384_: *mut crate::leanh::LeanObject,
    mut v_x_385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_386_ = l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux(
        v_s_382_, v_x_383_, v_x_384_, v_x_385_,
    );
    crate::leanh::lean_dec_ref(v_s_382_);
    return v_res_386_;
}
pub unsafe fn l_String_utf16PosToCodepointPosFrom(
    mut v_s_387_: *mut crate::leanh::LeanObject,
    mut v_utf16pos_388_: *mut crate::leanh::LeanObject,
    mut v_off_389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_390_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_391_ = l___private_Lean_Data_Lsp_Utf16_0__String_utf16PosToCodepointPosFromAux(
        v_s_387_,
        v_utf16pos_388_,
        v_off_389_,
        v___x_390_,
    );
    return v___x_391_;
}
pub unsafe fn l_String_utf16PosToCodepointPosFrom___boxed(
    mut v_s_392_: *mut crate::leanh::LeanObject,
    mut v_utf16pos_393_: *mut crate::leanh::LeanObject,
    mut v_off_394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_395_ = l_String_utf16PosToCodepointPosFrom(v_s_392_, v_utf16pos_393_, v_off_394_);
    crate::leanh::lean_dec_ref(v_s_392_);
    return v_res_395_;
}
pub unsafe fn l_String_utf16PosToCodepointPos(
    mut v_s_396_: *mut crate::leanh::LeanObject,
    mut v_pos_397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_398_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_399_ = l_String_utf16PosToCodepointPosFrom(v_s_396_, v_pos_397_, v___x_398_);
    return v___x_399_;
}
pub unsafe fn l_String_utf16PosToCodepointPos___boxed(
    mut v_s_400_: *mut crate::leanh::LeanObject,
    mut v_pos_401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_402_ = l_String_utf16PosToCodepointPos(v_s_400_, v_pos_401_);
    crate::leanh::lean_dec_ref(v_s_400_);
    return v_res_402_;
}
pub unsafe fn l_String_codepointPosToUtf8PosFrom(
    mut v_s_403_: *mut crate::leanh::LeanObject,
    mut v_x_404_: *mut crate::leanh::LeanObject,
    mut v_x_405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_407_: u8 = 0;
    let mut v_one_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_406_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_407_ = lean_nat_dec_eq(v_x_405_, v_zero_406_);
                if v_isZero_407_ == 1 {
                    crate::leanh::lean_dec(v_x_405_);
                    return v_x_404_;
                } else {
                    v_one_408_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_409_ = lean_nat_sub(v_x_405_, v_one_408_);
                    crate::leanh::lean_dec(v_x_405_);
                    v___x_410_ = lean_string_utf8_next(v_s_403_, v_x_404_);
                    crate::leanh::lean_dec(v_x_404_);
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
    mut v_s_412_: *mut crate::leanh::LeanObject,
    mut v_x_413_: *mut crate::leanh::LeanObject,
    mut v_x_414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_415_ = l_String_codepointPosToUtf8PosFrom(v_s_412_, v_x_413_, v_x_414_);
    crate::leanh::lean_dec_ref(v_s_412_);
    return v_res_415_;
}
pub unsafe fn l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos(
    mut v_text_416_: *mut crate::leanh::LeanObject,
    mut v_line_417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_positions_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: u8 = 0;
    v_positions_418_ = crate::leanh::lean_ctor_get(v_text_416_, 1);
    v___x_419_ = lean_array_get_size(v_positions_418_);
    v___x_420_ = lean_nat_dec_lt(v_line_417_, v___x_419_);
    if v___x_420_ == 0 {
        let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_422_: u8 = 0;
        v___x_421_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_422_ = lean_nat_dec_eq(v___x_419_, v___x_421_);
        if v___x_422_ == 0 {
            let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_423_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_424_ = lean_nat_sub(v___x_419_, v___x_423_);
            v___x_425_ = lean_array_get_borrowed(v___x_421_, v_positions_418_, v___x_424_);
            crate::leanh::lean_dec(v___x_424_);
            crate::leanh::lean_inc(v___x_425_);
            return v___x_425_;
        } else {
            return v___x_421_;
        }
    } else {
        let mut v___x_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_426_ = lean_array_fget_borrowed(v_positions_418_, v_line_417_);
        crate::leanh::lean_inc(v___x_426_);
        return v___x_426_;
    }
}
pub unsafe fn l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos___boxed(
    mut v_text_427_: *mut crate::leanh::LeanObject,
    mut v_line_428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_429_ =
        l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos(v_text_427_, v_line_428_);
    crate::leanh::lean_dec(v_line_428_);
    crate::leanh::lean_dec_ref(v_text_427_);
    return v_res_429_;
}
pub unsafe fn l_Lean_FileMap_lspPosToUtf8Pos(
    mut v_text_430_: *mut crate::leanh::LeanObject,
    mut v_pos_431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_line_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lineStartPos_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_chr_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_line_432_ = crate::leanh::lean_ctor_get(v_pos_431_, 0);
    crate::leanh::lean_inc(v_line_432_);
    v_character_433_ = crate::leanh::lean_ctor_get(v_pos_431_, 1);
    crate::leanh::lean_inc(v_character_433_);
    crate::leanh::lean_dec_ref(v_pos_431_);
    v_source_434_ = crate::leanh::lean_ctor_get(v_text_430_, 0);
    v_lineStartPos_435_ =
        l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos(v_text_430_, v_line_432_);
    crate::leanh::lean_dec(v_line_432_);
    crate::leanh::lean_inc(v_lineStartPos_435_);
    v_chr_436_ =
        l_String_utf16PosToCodepointPosFrom(v_source_434_, v_character_433_, v_lineStartPos_435_);
    v___x_437_ = l_String_codepointPosToUtf8PosFrom(v_source_434_, v_lineStartPos_435_, v_chr_436_);
    return v___x_437_;
}
pub unsafe fn l_Lean_FileMap_lspPosToUtf8Pos___boxed(
    mut v_text_438_: *mut crate::leanh::LeanObject,
    mut v_pos_439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_440_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_438_, v_pos_439_);
    crate::leanh::lean_dec_ref(v_text_438_);
    return v_res_440_;
}
pub unsafe fn l_Lean_FileMap_leanPosToLspPos(
    mut v_text_441_: *mut crate::leanh::LeanObject,
    mut v_x_442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_line_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_column_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_451_: u8 = 0;
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_456_: u8 = 0;
    let mut v_unused_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_line_443_ = crate::leanh::lean_ctor_get(v_x_442_, 0);
                crate::leanh::lean_inc(v_line_443_);
                v_column_444_ = crate::leanh::lean_ctor_get(v_x_442_, 1);
                crate::leanh::lean_inc(v_column_444_);
                crate::leanh::lean_dec_ref(v_x_442_);
                v_source_445_ = crate::leanh::lean_ctor_get(v_text_441_, 0);
                crate::leanh::lean_inc_ref(v_source_445_);
                v___x_446_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_447_ = lean_nat_sub(v_line_443_, v___x_446_);
                crate::leanh::lean_dec(v_line_443_);
                v___x_448_ = l___private_Lean_Data_Lsp_Utf16_0__Lean_FileMap_lineStartPos(
                    v_text_441_,
                    v___x_447_,
                );
                v_isSharedCheck_456_ = (!crate::leanh::lean_is_exclusive(v_text_441_)) as u8;
                if v_isSharedCheck_456_ == 0 {
                    v_unused_457_ = crate::leanh::lean_ctor_get(v_text_441_, 1);
                    crate::leanh::lean_dec(v_unused_457_);
                    v_unused_458_ = crate::leanh::lean_ctor_get(v_text_441_, 0);
                    crate::leanh::lean_dec(v_unused_458_);
                    v___x_450_ = v_text_441_;
                    v_isShared_451_ = v_isSharedCheck_456_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_text_441_);
                    v___x_450_ = crate::leanh::lean_box(0);
                    v_isShared_451_ = v_isSharedCheck_456_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_452_ =
                    l_String_codepointPosToUtf16PosFrom(v_source_445_, v_column_444_, v___x_448_);
                crate::leanh::lean_dec_ref(v_source_445_);
                if v_isShared_451_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_450_, 1, v___x_452_);
                    crate::leanh::lean_ctor_set(v___x_450_, 0, v___x_447_);
                    v___x_454_ = v___x_450_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_455_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_455_, 0, v___x_447_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_455_, 1, v___x_452_);
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
    mut v_text_459_: *mut crate::leanh::LeanObject,
    mut v_pos_460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_text_459_);
    v___x_461_ = l_Lean_FileMap_toPosition(v_text_459_, v_pos_460_);
    v___x_462_ = l_Lean_FileMap_leanPosToLspPos(v_text_459_, v___x_461_);
    return v___x_462_;
}
pub unsafe fn l_Lean_FileMap_utf8PosToLspPos___boxed(
    mut v_text_463_: *mut crate::leanh::LeanObject,
    mut v_pos_464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_465_ = l_Lean_FileMap_utf8PosToLspPos(v_text_463_, v_pos_464_);
    crate::leanh::lean_dec(v_pos_464_);
    return v_res_465_;
}
pub unsafe fn l_Lean_FileMap_utf8RangeToLspRange(
    mut v_text_466_: *mut crate::leanh::LeanObject,
    mut v_range_467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_472_: u8 = 0;
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_478_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_468_ = crate::leanh::lean_ctor_get(v_range_467_, 0);
                v_stop_469_ = crate::leanh::lean_ctor_get(v_range_467_, 1);
                v_isSharedCheck_478_ = (!crate::leanh::lean_is_exclusive(v_range_467_)) as u8;
                if v_isSharedCheck_478_ == 0 {
                    v___x_471_ = v_range_467_;
                    v_isShared_472_ = v_isSharedCheck_478_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_469_);
                    crate::leanh::lean_inc(v_start_468_);
                    crate::leanh::lean_dec(v_range_467_);
                    v___x_471_ = crate::leanh::lean_box(0);
                    v_isShared_472_ = v_isSharedCheck_478_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_text_466_);
                v___x_473_ = l_Lean_FileMap_utf8PosToLspPos(v_text_466_, v_start_468_);
                crate::leanh::lean_dec(v_start_468_);
                v___x_474_ = l_Lean_FileMap_utf8PosToLspPos(v_text_466_, v_stop_469_);
                crate::leanh::lean_dec(v_stop_469_);
                if v_isShared_472_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_471_, 1, v___x_474_);
                    crate::leanh::lean_ctor_set(v___x_471_, 0, v___x_473_);
                    v___x_476_ = v___x_471_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_477_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_477_, 0, v___x_473_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_477_, 1, v___x_474_);
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
    mut v_text_479_: *mut crate::leanh::LeanObject,
    mut v_stx_480_: *mut crate::leanh::LeanObject,
    mut v_canonicalOnly_481_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_487_: u8 = 0;
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_492_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_482_ = l_Lean_Syntax_getRange_x3f(v_stx_480_, v_canonicalOnly_481_);
                if crate::leanh::lean_obj_tag(v___x_482_) == 0 {
                    crate::leanh::lean_dec_ref(v_text_479_);
                    v___x_483_ = crate::leanh::lean_box(0);
                    return v___x_483_;
                } else {
                    v_val_484_ = crate::leanh::lean_ctor_get(v___x_482_, 0);
                    v_isSharedCheck_492_ = (!crate::leanh::lean_is_exclusive(v___x_482_)) as u8;
                    if v_isSharedCheck_492_ == 0 {
                        v___x_486_ = v___x_482_;
                        v_isShared_487_ = v_isSharedCheck_492_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_484_);
                        crate::leanh::lean_dec(v___x_482_);
                        v___x_486_ = crate::leanh::lean_box(0);
                        v_isShared_487_ = v_isSharedCheck_492_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_488_ = l_Lean_FileMap_utf8RangeToLspRange(v_text_479_, v_val_484_);
                if v_isShared_487_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_486_, 0, v___x_488_);
                    v___x_490_ = v___x_486_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_491_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_491_, 0, v___x_488_);
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
    mut v_text_493_: *mut crate::leanh::LeanObject,
    mut v_stx_494_: *mut crate::leanh::LeanObject,
    mut v_canonicalOnly_495_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_canonicalOnly_boxed_496_: u8 = 0;
    let mut v_res_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_canonicalOnly_boxed_496_ = (crate::leanh::lean_unbox(v_canonicalOnly_495_) as u8);
    v_res_497_ =
        l_Lean_FileMap_lspRangeOfStx_x3f(v_text_493_, v_stx_494_, v_canonicalOnly_boxed_496_);
    crate::leanh::lean_dec(v_stx_494_);
    return v_res_497_;
}
pub unsafe fn l_Lean_FileMap_lspRangeToUtf8Range(
    mut v_text_498_: *mut crate::leanh::LeanObject,
    mut v_range_499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_start_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_end_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_504_: u8 = 0;
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_510_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_500_ = crate::leanh::lean_ctor_get(v_range_499_, 0);
                v_end_501_ = crate::leanh::lean_ctor_get(v_range_499_, 1);
                v_isSharedCheck_510_ = (!crate::leanh::lean_is_exclusive(v_range_499_)) as u8;
                if v_isSharedCheck_510_ == 0 {
                    v___x_503_ = v_range_499_;
                    v_isShared_504_ = v_isSharedCheck_510_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_end_501_);
                    crate::leanh::lean_inc(v_start_500_);
                    crate::leanh::lean_dec(v_range_499_);
                    v___x_503_ = crate::leanh::lean_box(0);
                    v_isShared_504_ = v_isSharedCheck_510_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_505_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_498_, v_start_500_);
                v___x_506_ = l_Lean_FileMap_lspPosToUtf8Pos(v_text_498_, v_end_501_);
                if v_isShared_504_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_503_, 1, v___x_506_);
                    crate::leanh::lean_ctor_set(v___x_503_, 0, v___x_505_);
                    v___x_508_ = v___x_503_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_509_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_509_, 0, v___x_505_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_509_, 1, v___x_506_);
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
    mut v_text_511_: *mut crate::leanh::LeanObject,
    mut v_range_512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_513_ = l_Lean_FileMap_lspRangeToUtf8Range(v_text_511_, v_range_512_);
    crate::leanh::lean_dec_ref(v_text_511_);
    return v_res_513_;
}
pub unsafe fn l_Lean_DeclarationRange_ofFilePositions(
    mut v_text_514_: *mut crate::leanh::LeanObject,
    mut v_pos_515_: *mut crate::leanh::LeanObject,
    mut v_endPos_516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_character_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_pos_515_);
    crate::leanh::lean_inc_ref(v_text_514_);
    v___x_517_ = l_Lean_FileMap_leanPosToLspPos(v_text_514_, v_pos_515_);
    v_character_518_ = crate::leanh::lean_ctor_get(v___x_517_, 1);
    crate::leanh::lean_inc(v_character_518_);
    crate::leanh::lean_dec_ref(v___x_517_);
    crate::leanh::lean_inc_ref(v_endPos_516_);
    v___x_519_ = l_Lean_FileMap_leanPosToLspPos(v_text_514_, v_endPos_516_);
    v_character_520_ = crate::leanh::lean_ctor_get(v___x_519_, 1);
    crate::leanh::lean_inc(v_character_520_);
    crate::leanh::lean_dec_ref(v___x_519_);
    v___x_521_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_521_, 0, v_pos_515_);
    crate::leanh::lean_ctor_set(v___x_521_, 1, v_character_518_);
    crate::leanh::lean_ctor_set(v___x_521_, 2, v_endPos_516_);
    crate::leanh::lean_ctor_set(v___x_521_, 3, v_character_520_);
    return v___x_521_;
}
pub unsafe fn l_Lean_DeclarationRange_ofStringPositions(
    mut v_text_522_: *mut crate::leanh::LeanObject,
    mut v_pos_523_: *mut crate::leanh::LeanObject,
    mut v_endPos_524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_text_522_, 2);
    v___x_525_ = l_Lean_FileMap_toPosition(v_text_522_, v_pos_523_);
    v___x_526_ = l_Lean_FileMap_toPosition(v_text_522_, v_endPos_524_);
    v___x_527_ = l_Lean_DeclarationRange_ofFilePositions(v_text_522_, v___x_525_, v___x_526_);
    return v___x_527_;
}
pub unsafe fn l_Lean_DeclarationRange_ofStringPositions___boxed(
    mut v_text_528_: *mut crate::leanh::LeanObject,
    mut v_pos_529_: *mut crate::leanh::LeanObject,
    mut v_endPos_530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_531_ = l_Lean_DeclarationRange_ofStringPositions(v_text_528_, v_pos_529_, v_endPos_530_);
    crate::leanh::lean_dec(v_endPos_530_);
    crate::leanh::lean_dec(v_pos_529_);
    return v_res_531_;
}
pub unsafe fn l_Lean_DeclarationRange_toLspRange(
    mut v_r_532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charUtf16_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endCharUtf16_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_line_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_540_: u8 = 0;
    let mut v_line_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_544_: u8 = 0;
    let mut v___x_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_555_: u8 = 0;
    let mut v_unused_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_557_: u8 = 0;
    let mut v_unused_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pos_533_ = crate::leanh::lean_ctor_get(v_r_532_, 0);
                crate::leanh::lean_inc_ref(v_pos_533_);
                v_endPos_534_ = crate::leanh::lean_ctor_get(v_r_532_, 2);
                crate::leanh::lean_inc_ref(v_endPos_534_);
                v_charUtf16_535_ = crate::leanh::lean_ctor_get(v_r_532_, 1);
                crate::leanh::lean_inc(v_charUtf16_535_);
                v_endCharUtf16_536_ = crate::leanh::lean_ctor_get(v_r_532_, 3);
                crate::leanh::lean_inc(v_endCharUtf16_536_);
                crate::leanh::lean_dec_ref(v_r_532_);
                v_line_537_ = crate::leanh::lean_ctor_get(v_pos_533_, 0);
                v_isSharedCheck_557_ = (!crate::leanh::lean_is_exclusive(v_pos_533_)) as u8;
                if v_isSharedCheck_557_ == 0 {
                    v_unused_558_ = crate::leanh::lean_ctor_get(v_pos_533_, 1);
                    crate::leanh::lean_dec(v_unused_558_);
                    v___x_539_ = v_pos_533_;
                    v_isShared_540_ = v_isSharedCheck_557_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_line_537_);
                    crate::leanh::lean_dec(v_pos_533_);
                    v___x_539_ = crate::leanh::lean_box(0);
                    v_isShared_540_ = v_isSharedCheck_557_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_line_541_ = crate::leanh::lean_ctor_get(v_endPos_534_, 0);
                v_isSharedCheck_555_ = (!crate::leanh::lean_is_exclusive(v_endPos_534_)) as u8;
                if v_isSharedCheck_555_ == 0 {
                    v_unused_556_ = crate::leanh::lean_ctor_get(v_endPos_534_, 1);
                    crate::leanh::lean_dec(v_unused_556_);
                    v___x_543_ = v_endPos_534_;
                    v_isShared_544_ = v_isSharedCheck_555_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_line_541_);
                    crate::leanh::lean_dec(v_endPos_534_);
                    v___x_543_ = crate::leanh::lean_box(0);
                    v_isShared_544_ = v_isSharedCheck_555_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_545_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_546_ = lean_nat_sub(v_line_537_, v___x_545_);
                crate::leanh::lean_dec(v_line_537_);
                if v_isShared_544_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_543_, 1, v_charUtf16_535_);
                    crate::leanh::lean_ctor_set(v___x_543_, 0, v___x_546_);
                    v___x_548_ = v___x_543_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_554_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_546_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_554_, 1, v_charUtf16_535_);
                    v___x_548_ = v_reuseFailAlloc_554_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_549_ = lean_nat_sub(v_line_541_, v___x_545_);
                crate::leanh::lean_dec(v_line_541_);
                if v_isShared_540_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_539_, 1, v_endCharUtf16_536_);
                    crate::leanh::lean_ctor_set(v___x_539_, 0, v___x_549_);
                    v___x_551_ = v___x_539_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_553_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_553_, 0, v___x_549_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_553_, 1, v_endCharUtf16_536_);
                    v___x_551_ = v_reuseFailAlloc_553_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_552_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_552_, 0, v___x_548_);
                crate::leanh::lean_ctor_set(v___x_552_, 1, v___x_551_);
                return v___x_552_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Lsp_Utf16(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Lsp_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_DeclarationRange(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Lsp_Utf16(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Lsp_Utf16(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Lsp_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_DeclarationRange(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Search(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_Utf16(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Lsp_Utf16(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Lsp_Utf16(builtin);
}

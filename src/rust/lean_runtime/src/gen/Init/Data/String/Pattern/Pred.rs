// Lean compiler output
// Module: Init.Data.String.Pattern.Pred
// Imports: Init.Data.String.Pattern.Basic Init.Data.String.Lemmas.IsEmpty Init.Data.String.Termination Init.Omega Init.Data.String.Basic Init.Data.String.Lemmas.Order Init.Data.Option.Lemmas Init.Data.String.Lemmas.FindPos
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Data::String::FindPos::l_String_Slice_posLE;
use crate::r#gen::Init::Data::String::Lemmas::FindPos::{
    initialize_Init_Data_String_Lemmas_FindPos, runtime_initialize_Init_Data_String_Lemmas_FindPos,
};
use crate::r#gen::Init::Data::String::Lemmas::IsEmpty::{
    initialize_Init_Data_String_Lemmas_IsEmpty, runtime_initialize_Init_Data_String_Lemmas_IsEmpty,
};
use crate::r#gen::Init::Data::String::Lemmas::Order::{
    initialize_Init_Data_String_Lemmas_Order, runtime_initialize_Init_Data_String_Lemmas_Order,
};
use crate::r#gen::Init::Data::String::Pattern::Basic::{
    initialize_Init_Data_String_Pattern_Basic,
    l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed,
    l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed,
    runtime_initialize_Init_Data_String_Pattern_Basic,
};
use crate::r#gen::Init::Data::String::Termination::{
    initialize_Init_Data_String_Termination, runtime_initialize_Init_Data_String_Termination,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_add, lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1, lean_box,
    lean_box_uint32, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_unbox,
    lean_unsigned_to_nat,
};
pub static l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___closed__0: *mut LeanObject = core::ptr::addr_of!(l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___closed__0_value) as *mut LeanObject;
pub static l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___closed__0: *mut LeanObject = core::ptr::addr_of!(l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___closed__0_value) as *mut LeanObject;
pub unsafe fn l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__0(
    mut v_p_291_: *mut LeanObject,
    mut v_s_292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_298_: u8 = 0;
    v_str_293_ = lean_ctor_get(v_s_292_, 0);
    v_startInclusive_294_ = lean_ctor_get(v_s_292_, 1);
    v_endExclusive_295_ = lean_ctor_get(v_s_292_, 2);
    v___x_296_ = lean_unsigned_to_nat(0);
    v___x_297_ = lean_nat_sub(v_endExclusive_295_, v_startInclusive_294_);
    v___x_298_ = lean_nat_dec_eq(v___x_296_, v___x_297_);
    lean_dec(v___x_297_);
    if v___x_298_ == 0 {
        let mut v___x_299_: u32 = 0;
        let mut v___x_300_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_302_: u8 = 0;
        v___x_299_ = lean_string_utf8_get_fast(v_str_293_, v_startInclusive_294_);
        v___x_300_ = lean_box_uint32(v___x_299_);
        v___x_301_ = lean_apply_1(v_p_291_, v___x_300_);
        v___x_302_ = (lean_unbox(v___x_301_) as u8);
        if v___x_302_ == 0 {
            let mut v___x_303_: *mut LeanObject = core::ptr::null_mut();
            v___x_303_ = lean_box(0);
            return v___x_303_;
        } else {
            let mut v___x_304_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
            v___x_304_ = lean_string_utf8_next_fast(v_str_293_, v_startInclusive_294_);
            v___x_305_ = lean_nat_sub(v___x_304_, v_startInclusive_294_);
            v___x_306_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_306_, 0, v___x_305_);
            return v___x_306_;
        }
    } else {
        let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_p_291_);
        v___x_307_ = lean_box(0);
        return v___x_307_;
    }
}
pub unsafe fn l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__0___boxed(
    mut v_p_308_: *mut LeanObject,
    mut v_s_309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_310_: *mut LeanObject = core::ptr::null_mut();
    v_res_310_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__0(
        v_p_308_, v_s_309_,
    );
    lean_dec_ref(v_s_309_);
    return v_res_310_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__1(
    mut v_p_311_: *mut LeanObject,
    mut v_s_312_: *mut LeanObject,
    mut v_h_313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_316_: u32 = 0;
    let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_319_: u8 = 0;
    v_str_314_ = lean_ctor_get(v_s_312_, 0);
    v_startInclusive_315_ = lean_ctor_get(v_s_312_, 1);
    v___x_316_ = lean_string_utf8_get_fast(v_str_314_, v_startInclusive_315_);
    v___x_317_ = lean_box_uint32(v___x_316_);
    v___x_318_ = lean_apply_1(v_p_311_, v___x_317_);
    v___x_319_ = (lean_unbox(v___x_318_) as u8);
    if v___x_319_ == 0 {
        let mut v___x_320_: *mut LeanObject = core::ptr::null_mut();
        v___x_320_ = lean_box(0);
        return v___x_320_;
    } else {
        let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
        v___x_321_ = lean_string_utf8_next_fast(v_str_314_, v_startInclusive_315_);
        v___x_322_ = lean_nat_sub(v___x_321_, v_startInclusive_315_);
        v___x_323_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_323_, 0, v___x_322_);
        return v___x_323_;
    }
}
pub unsafe fn l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__1___boxed(
    mut v_p_324_: *mut LeanObject,
    mut v_s_325_: *mut LeanObject,
    mut v_h_326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_327_: *mut LeanObject = core::ptr::null_mut();
    v_res_327_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__1(
        v_p_324_, v_s_325_, v_h_326_,
    );
    lean_dec_ref(v_s_325_);
    return v_res_327_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__2(
    mut v_p_328_: *mut LeanObject,
    mut v_s_329_: *mut LeanObject,
) -> u8 {
    let mut v_str_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_335_: u8 = 0;
    v_str_330_ = lean_ctor_get(v_s_329_, 0);
    v_startInclusive_331_ = lean_ctor_get(v_s_329_, 1);
    v_endExclusive_332_ = lean_ctor_get(v_s_329_, 2);
    v___x_333_ = lean_unsigned_to_nat(0);
    v___x_334_ = lean_nat_sub(v_endExclusive_332_, v_startInclusive_331_);
    v___x_335_ = lean_nat_dec_eq(v___x_333_, v___x_334_);
    lean_dec(v___x_334_);
    if v___x_335_ == 0 {
        let mut v___x_336_: u32 = 0;
        let mut v___x_337_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_339_: u8 = 0;
        v___x_336_ = lean_string_utf8_get_fast(v_str_330_, v_startInclusive_331_);
        v___x_337_ = lean_box_uint32(v___x_336_);
        v___x_338_ = lean_apply_1(v_p_328_, v___x_337_);
        v___x_339_ = (lean_unbox(v___x_338_) as u8);
        return v___x_339_;
    } else {
        let mut v___x_340_: u8 = 0;
        lean_dec_ref(v_p_328_);
        v___x_340_ = 0;
        return v___x_340_;
    }
}
pub unsafe fn l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__2___boxed(
    mut v_p_341_: *mut LeanObject,
    mut v_s_342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_343_: u8 = 0;
    let mut v_r_344_: *mut LeanObject = core::ptr::null_mut();
    v_res_343_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__2(
        v_p_341_, v_s_342_,
    );
    lean_dec_ref(v_s_342_);
    v_r_344_ = lean_box((v_res_343_) as usize);
    return v_r_344_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(
    mut v_p_345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_p_345_, 2);
    v___f_346_ = lean_alloc_closure(
        l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_346_, 0, v_p_345_);
    v___f_347_ = lean_alloc_closure(
        l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__1___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_347_, 0, v_p_345_);
    v___f_348_ = lean_alloc_closure(
        l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool___lam__2___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_348_, 0, v_p_345_);
    v___x_349_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_349_, 0, v___f_346_);
    lean_ctor_set(v___x_349_, 1, v___f_347_);
    lean_ctor_set(v___x_349_, 2, v___f_348_);
    return v___x_349_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_instToForwardSearcherForallCharBoolDefaultForwardSearcher(
    mut v_p_350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
    v___x_351_ = lean_alloc_closure(
        l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_351_, 0, lean_box(0));
    lean_closure_set(v___x_351_, 1, v_p_350_);
    return v___x_351_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__0(
    mut v_inst_352_: *mut LeanObject,
    mut v_s_353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_359_: u8 = 0;
    v_str_354_ = lean_ctor_get(v_s_353_, 0);
    v_startInclusive_355_ = lean_ctor_get(v_s_353_, 1);
    v_endExclusive_356_ = lean_ctor_get(v_s_353_, 2);
    v___x_357_ = lean_unsigned_to_nat(0);
    v___x_358_ = lean_nat_sub(v_endExclusive_356_, v_startInclusive_355_);
    v___x_359_ = lean_nat_dec_eq(v___x_357_, v___x_358_);
    lean_dec(v___x_358_);
    if v___x_359_ == 0 {
        let mut v___x_360_: u32 = 0;
        let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_363_: u8 = 0;
        v___x_360_ = lean_string_utf8_get_fast(v_str_354_, v_startInclusive_355_);
        v___x_361_ = lean_box_uint32(v___x_360_);
        v___x_362_ = lean_apply_1(v_inst_352_, v___x_361_);
        v___x_363_ = (lean_unbox(v___x_362_) as u8);
        if v___x_363_ == 0 {
            let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
            v___x_364_ = lean_box(0);
            return v___x_364_;
        } else {
            let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_366_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
            v___x_365_ = lean_string_utf8_next_fast(v_str_354_, v_startInclusive_355_);
            v___x_366_ = lean_nat_sub(v___x_365_, v_startInclusive_355_);
            v___x_367_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_367_, 0, v___x_366_);
            return v___x_367_;
        }
    } else {
        let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_352_);
        v___x_368_ = lean_box(0);
        return v___x_368_;
    }
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__0___boxed(
    mut v_inst_369_: *mut LeanObject,
    mut v_s_370_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_371_: *mut LeanObject = core::ptr::null_mut();
    v_res_371_ = l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__0(v_inst_369_, v_s_370_);
    lean_dec_ref(v_s_370_);
    return v_res_371_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__1(
    mut v_inst_372_: *mut LeanObject,
    mut v_s_373_: *mut LeanObject,
    mut v_h_374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_377_: u32 = 0;
    let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_380_: u8 = 0;
    v_str_375_ = lean_ctor_get(v_s_373_, 0);
    v_startInclusive_376_ = lean_ctor_get(v_s_373_, 1);
    v___x_377_ = lean_string_utf8_get_fast(v_str_375_, v_startInclusive_376_);
    v___x_378_ = lean_box_uint32(v___x_377_);
    v___x_379_ = lean_apply_1(v_inst_372_, v___x_378_);
    v___x_380_ = (lean_unbox(v___x_379_) as u8);
    if v___x_380_ == 0 {
        let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
        v___x_381_ = lean_box(0);
        return v___x_381_;
    } else {
        let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
        v___x_382_ = lean_string_utf8_next_fast(v_str_375_, v_startInclusive_376_);
        v___x_383_ = lean_nat_sub(v___x_382_, v_startInclusive_376_);
        v___x_384_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_384_, 0, v___x_383_);
        return v___x_384_;
    }
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__1___boxed(
    mut v_inst_385_: *mut LeanObject,
    mut v_s_386_: *mut LeanObject,
    mut v_h_387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_388_: *mut LeanObject = core::ptr::null_mut();
    v_res_388_ = l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__1(v_inst_385_, v_s_386_, v_h_387_);
    lean_dec_ref(v_s_386_);
    return v_res_388_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__2(
    mut v_inst_389_: *mut LeanObject,
    mut v_s_390_: *mut LeanObject,
) -> u8 {
    let mut v_str_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_396_: u8 = 0;
    v_str_391_ = lean_ctor_get(v_s_390_, 0);
    v_startInclusive_392_ = lean_ctor_get(v_s_390_, 1);
    v_endExclusive_393_ = lean_ctor_get(v_s_390_, 2);
    v___x_394_ = lean_unsigned_to_nat(0);
    v___x_395_ = lean_nat_sub(v_endExclusive_393_, v_startInclusive_392_);
    v___x_396_ = lean_nat_dec_eq(v___x_394_, v___x_395_);
    lean_dec(v___x_395_);
    if v___x_396_ == 0 {
        let mut v___x_397_: u32 = 0;
        let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_399_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_400_: u8 = 0;
        v___x_397_ = lean_string_utf8_get_fast(v_str_391_, v_startInclusive_392_);
        v___x_398_ = lean_box_uint32(v___x_397_);
        v___x_399_ = lean_apply_1(v_inst_389_, v___x_398_);
        v___x_400_ = (lean_unbox(v___x_399_) as u8);
        return v___x_400_;
    } else {
        let mut v___x_401_: u8 = 0;
        lean_dec_ref(v_inst_389_);
        v___x_401_ = 0;
        return v___x_401_;
    }
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__2___boxed(
    mut v_inst_402_: *mut LeanObject,
    mut v_s_403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_404_: u8 = 0;
    let mut v_r_405_: *mut LeanObject = core::ptr::null_mut();
    v_res_404_ = l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__2(v_inst_402_, v_s_403_);
    lean_dec_ref(v_s_403_);
    v_r_405_ = lean_box((v_res_404_) as usize);
    return v_r_405_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg(
    mut v_inst_406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_406_, 2);
    v___f_407_ = lean_alloc_closure(l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_407_, 0, v_inst_406_);
    v___f_408_ = lean_alloc_closure(l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__1___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_408_, 0, v_inst_406_);
    v___f_409_ = lean_alloc_closure(l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg___lam__2___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_409_, 0, v_inst_406_);
    v___x_410_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_410_, 0, v___f_407_);
    lean_ctor_set(v___x_410_, 1, v___f_408_);
    lean_ctor_set(v___x_410_, 2, v___f_409_);
    return v___x_410_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred(
    mut v_p_411_: *mut LeanObject,
    mut v_inst_412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
    v___x_413_ = l_String_Slice_Pattern_CharPred_Decidable_instForwardPatternForallCharPropOfDecidablePred___redArg(v_inst_412_);
    return v___x_413_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___lam__0(
    mut v_s_414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_415_: *mut LeanObject = core::ptr::null_mut();
    v___x_415_ = lean_unsigned_to_nat(0);
    return v___x_415_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___lam__0___boxed(
    mut v_s_416_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_417_: *mut LeanObject = core::ptr::null_mut();
    v_res_417_ = l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___lam__0(v_s_416_);
    lean_dec_ref(v_s_416_);
    return v_res_417_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide(
    mut v_p_419_: *mut LeanObject,
    mut v_inst_420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_421_: *mut LeanObject = core::ptr::null_mut();
    v___f_421_ = l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___closed__0;
    return v___f_421_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide___boxed(
    mut v_p_422_: *mut LeanObject,
    mut v_inst_423_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_424_: *mut LeanObject = core::ptr::null_mut();
    v_res_424_ = l_String_Slice_Pattern_CharPred_Decidable_instToForwardSearcherForallCharPropDefaultForwardSearcherForallBoolDecide(v_p_422_, v_inst_423_);
    lean_dec_ref(v_inst_423_);
    return v_res_424_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__0(
    mut v_p_425_: *mut LeanObject,
    mut v_s_426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_432_: u8 = 0;
    v_str_427_ = lean_ctor_get(v_s_426_, 0);
    v_startInclusive_428_ = lean_ctor_get(v_s_426_, 1);
    v_endExclusive_429_ = lean_ctor_get(v_s_426_, 2);
    v___x_430_ = lean_nat_sub(v_endExclusive_429_, v_startInclusive_428_);
    v___x_431_ = lean_unsigned_to_nat(0);
    v___x_432_ = lean_nat_dec_eq(v___x_430_, v___x_431_);
    if v___x_432_ == 0 {
        let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_437_: u32 = 0;
        let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_440_: u8 = 0;
        v___x_433_ = lean_unsigned_to_nat(1);
        v___x_434_ = lean_nat_sub(v___x_430_, v___x_433_);
        lean_dec(v___x_430_);
        v___x_435_ = l_String_Slice_posLE(v_s_426_, v___x_434_);
        v___x_436_ = lean_nat_add(v_startInclusive_428_, v___x_435_);
        v___x_437_ = lean_string_utf8_get_fast(v_str_427_, v___x_436_);
        lean_dec(v___x_436_);
        v___x_438_ = lean_box_uint32(v___x_437_);
        v___x_439_ = lean_apply_1(v_p_425_, v___x_438_);
        v___x_440_ = (lean_unbox(v___x_439_) as u8);
        if v___x_440_ == 0 {
            let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_435_);
            v___x_441_ = lean_box(0);
            return v___x_441_;
        } else {
            let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
            v___x_442_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_442_, 0, v___x_435_);
            return v___x_442_;
        }
    } else {
        let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_430_);
        lean_dec_ref(v_p_425_);
        v___x_443_ = lean_box(0);
        return v___x_443_;
    }
}
pub unsafe fn l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__0___boxed(
    mut v_p_444_: *mut LeanObject,
    mut v_s_445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_446_: *mut LeanObject = core::ptr::null_mut();
    v_res_446_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__0(
        v_p_444_, v_s_445_,
    );
    lean_dec_ref(v_s_445_);
    return v_res_446_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__1(
    mut v_p_447_: *mut LeanObject,
    mut v_s_448_: *mut LeanObject,
    mut v_h_449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_458_: u32 = 0;
    let mut v___x_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_461_: u8 = 0;
    v_str_450_ = lean_ctor_get(v_s_448_, 0);
    v_startInclusive_451_ = lean_ctor_get(v_s_448_, 1);
    v_endExclusive_452_ = lean_ctor_get(v_s_448_, 2);
    v___x_453_ = lean_nat_sub(v_endExclusive_452_, v_startInclusive_451_);
    v___x_454_ = lean_unsigned_to_nat(1);
    v___x_455_ = lean_nat_sub(v___x_453_, v___x_454_);
    lean_dec(v___x_453_);
    v___x_456_ = l_String_Slice_posLE(v_s_448_, v___x_455_);
    v___x_457_ = lean_nat_add(v_startInclusive_451_, v___x_456_);
    v___x_458_ = lean_string_utf8_get_fast(v_str_450_, v___x_457_);
    lean_dec(v___x_457_);
    v___x_459_ = lean_box_uint32(v___x_458_);
    v___x_460_ = lean_apply_1(v_p_447_, v___x_459_);
    v___x_461_ = (lean_unbox(v___x_460_) as u8);
    if v___x_461_ == 0 {
        let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_456_);
        v___x_462_ = lean_box(0);
        return v___x_462_;
    } else {
        let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
        v___x_463_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_463_, 0, v___x_456_);
        return v___x_463_;
    }
}
pub unsafe fn l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__1___boxed(
    mut v_p_464_: *mut LeanObject,
    mut v_s_465_: *mut LeanObject,
    mut v_h_466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_467_: *mut LeanObject = core::ptr::null_mut();
    v_res_467_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__1(
        v_p_464_, v_s_465_, v_h_466_,
    );
    lean_dec_ref(v_s_465_);
    return v_res_467_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__2(
    mut v_p_468_: *mut LeanObject,
    mut v_s_469_: *mut LeanObject,
) -> u8 {
    let mut v_str_470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: u8 = 0;
    v_str_470_ = lean_ctor_get(v_s_469_, 0);
    v_startInclusive_471_ = lean_ctor_get(v_s_469_, 1);
    v_endExclusive_472_ = lean_ctor_get(v_s_469_, 2);
    v___x_473_ = lean_nat_sub(v_endExclusive_472_, v_startInclusive_471_);
    v___x_474_ = lean_unsigned_to_nat(0);
    v___x_475_ = lean_nat_dec_eq(v___x_473_, v___x_474_);
    if v___x_475_ == 0 {
        let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_480_: u32 = 0;
        let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_483_: u8 = 0;
        v___x_476_ = lean_unsigned_to_nat(1);
        v___x_477_ = lean_nat_sub(v___x_473_, v___x_476_);
        lean_dec(v___x_473_);
        v___x_478_ = l_String_Slice_posLE(v_s_469_, v___x_477_);
        v___x_479_ = lean_nat_add(v_startInclusive_471_, v___x_478_);
        lean_dec(v___x_478_);
        v___x_480_ = lean_string_utf8_get_fast(v_str_470_, v___x_479_);
        lean_dec(v___x_479_);
        v___x_481_ = lean_box_uint32(v___x_480_);
        v___x_482_ = lean_apply_1(v_p_468_, v___x_481_);
        v___x_483_ = (lean_unbox(v___x_482_) as u8);
        return v___x_483_;
    } else {
        let mut v___x_484_: u8 = 0;
        lean_dec(v___x_473_);
        lean_dec_ref(v_p_468_);
        v___x_484_ = 0;
        return v___x_484_;
    }
}
pub unsafe fn l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__2___boxed(
    mut v_p_485_: *mut LeanObject,
    mut v_s_486_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_487_: u8 = 0;
    let mut v_r_488_: *mut LeanObject = core::ptr::null_mut();
    v_res_487_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__2(
        v_p_485_, v_s_486_,
    );
    lean_dec_ref(v_s_486_);
    v_r_488_ = lean_box((v_res_487_) as usize);
    return v_r_488_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(
    mut v_p_489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_p_489_, 2);
    v___f_490_ = lean_alloc_closure(
        l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_490_, 0, v_p_489_);
    v___f_491_ = lean_alloc_closure(
        l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__1___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    lean_closure_set(v___f_491_, 0, v_p_489_);
    v___f_492_ = lean_alloc_closure(
        l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool___lam__2___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_492_, 0, v_p_489_);
    v___x_493_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_493_, 0, v___f_490_);
    lean_ctor_set(v___x_493_, 1, v___f_491_);
    lean_ctor_set(v___x_493_, 2, v___f_492_);
    return v___x_493_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_instToBackwardSearcherForallCharBoolDefaultBackwardSearcher(
    mut v_p_494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    v___x_495_ = lean_alloc_closure(
        l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_495_, 0, lean_box(0));
    lean_closure_set(v___x_495_, 1, v_p_494_);
    return v___x_495_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__0(
    mut v_inst_496_: *mut LeanObject,
    mut v_s_497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_503_: u8 = 0;
    v_str_498_ = lean_ctor_get(v_s_497_, 0);
    v_startInclusive_499_ = lean_ctor_get(v_s_497_, 1);
    v_endExclusive_500_ = lean_ctor_get(v_s_497_, 2);
    v___x_501_ = lean_nat_sub(v_endExclusive_500_, v_startInclusive_499_);
    v___x_502_ = lean_unsigned_to_nat(0);
    v___x_503_ = lean_nat_dec_eq(v___x_501_, v___x_502_);
    if v___x_503_ == 0 {
        let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_508_: u32 = 0;
        let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_511_: u8 = 0;
        v___x_504_ = lean_unsigned_to_nat(1);
        v___x_505_ = lean_nat_sub(v___x_501_, v___x_504_);
        lean_dec(v___x_501_);
        v___x_506_ = l_String_Slice_posLE(v_s_497_, v___x_505_);
        v___x_507_ = lean_nat_add(v_startInclusive_499_, v___x_506_);
        v___x_508_ = lean_string_utf8_get_fast(v_str_498_, v___x_507_);
        lean_dec(v___x_507_);
        v___x_509_ = lean_box_uint32(v___x_508_);
        v___x_510_ = lean_apply_1(v_inst_496_, v___x_509_);
        v___x_511_ = (lean_unbox(v___x_510_) as u8);
        if v___x_511_ == 0 {
            let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___x_506_);
            v___x_512_ = lean_box(0);
            return v___x_512_;
        } else {
            let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
            v___x_513_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_513_, 0, v___x_506_);
            return v___x_513_;
        }
    } else {
        let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_501_);
        lean_dec_ref(v_inst_496_);
        v___x_514_ = lean_box(0);
        return v___x_514_;
    }
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__0___boxed(
    mut v_inst_515_: *mut LeanObject,
    mut v_s_516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_517_: *mut LeanObject = core::ptr::null_mut();
    v_res_517_ = l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__0(v_inst_515_, v_s_516_);
    lean_dec_ref(v_s_516_);
    return v_res_517_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__1(
    mut v_inst_518_: *mut LeanObject,
    mut v_s_519_: *mut LeanObject,
    mut v_h_520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_529_: u32 = 0;
    let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_532_: u8 = 0;
    v_str_521_ = lean_ctor_get(v_s_519_, 0);
    v_startInclusive_522_ = lean_ctor_get(v_s_519_, 1);
    v_endExclusive_523_ = lean_ctor_get(v_s_519_, 2);
    v___x_524_ = lean_nat_sub(v_endExclusive_523_, v_startInclusive_522_);
    v___x_525_ = lean_unsigned_to_nat(1);
    v___x_526_ = lean_nat_sub(v___x_524_, v___x_525_);
    lean_dec(v___x_524_);
    v___x_527_ = l_String_Slice_posLE(v_s_519_, v___x_526_);
    v___x_528_ = lean_nat_add(v_startInclusive_522_, v___x_527_);
    v___x_529_ = lean_string_utf8_get_fast(v_str_521_, v___x_528_);
    lean_dec(v___x_528_);
    v___x_530_ = lean_box_uint32(v___x_529_);
    v___x_531_ = lean_apply_1(v_inst_518_, v___x_530_);
    v___x_532_ = (lean_unbox(v___x_531_) as u8);
    if v___x_532_ == 0 {
        let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_527_);
        v___x_533_ = lean_box(0);
        return v___x_533_;
    } else {
        let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
        v___x_534_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_534_, 0, v___x_527_);
        return v___x_534_;
    }
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__1___boxed(
    mut v_inst_535_: *mut LeanObject,
    mut v_s_536_: *mut LeanObject,
    mut v_h_537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_538_: *mut LeanObject = core::ptr::null_mut();
    v_res_538_ = l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__1(v_inst_535_, v_s_536_, v_h_537_);
    lean_dec_ref(v_s_536_);
    return v_res_538_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__2(
    mut v_inst_539_: *mut LeanObject,
    mut v_s_540_: *mut LeanObject,
) -> u8 {
    let mut v_str_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_546_: u8 = 0;
    v_str_541_ = lean_ctor_get(v_s_540_, 0);
    v_startInclusive_542_ = lean_ctor_get(v_s_540_, 1);
    v_endExclusive_543_ = lean_ctor_get(v_s_540_, 2);
    v___x_544_ = lean_nat_sub(v_endExclusive_543_, v_startInclusive_542_);
    v___x_545_ = lean_unsigned_to_nat(0);
    v___x_546_ = lean_nat_dec_eq(v___x_544_, v___x_545_);
    if v___x_546_ == 0 {
        let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_548_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_551_: u32 = 0;
        let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_554_: u8 = 0;
        v___x_547_ = lean_unsigned_to_nat(1);
        v___x_548_ = lean_nat_sub(v___x_544_, v___x_547_);
        lean_dec(v___x_544_);
        v___x_549_ = l_String_Slice_posLE(v_s_540_, v___x_548_);
        v___x_550_ = lean_nat_add(v_startInclusive_542_, v___x_549_);
        lean_dec(v___x_549_);
        v___x_551_ = lean_string_utf8_get_fast(v_str_541_, v___x_550_);
        lean_dec(v___x_550_);
        v___x_552_ = lean_box_uint32(v___x_551_);
        v___x_553_ = lean_apply_1(v_inst_539_, v___x_552_);
        v___x_554_ = (lean_unbox(v___x_553_) as u8);
        return v___x_554_;
    } else {
        let mut v___x_555_: u8 = 0;
        lean_dec(v___x_544_);
        lean_dec_ref(v_inst_539_);
        v___x_555_ = 0;
        return v___x_555_;
    }
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__2___boxed(
    mut v_inst_556_: *mut LeanObject,
    mut v_s_557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_558_: u8 = 0;
    let mut v_r_559_: *mut LeanObject = core::ptr::null_mut();
    v_res_558_ = l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__2(v_inst_556_, v_s_557_);
    lean_dec_ref(v_s_557_);
    v_r_559_ = lean_box((v_res_558_) as usize);
    return v_r_559_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg(
    mut v_inst_560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_560_, 2);
    v___f_561_ = lean_alloc_closure(l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_561_, 0, v_inst_560_);
    v___f_562_ = lean_alloc_closure(l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__1___boxed as *mut core::ffi::c_void, 3, 1);
    lean_closure_set(v___f_562_, 0, v_inst_560_);
    v___f_563_ = lean_alloc_closure(l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg___lam__2___boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_563_, 0, v_inst_560_);
    v___x_564_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_564_, 0, v___f_561_);
    lean_ctor_set(v___x_564_, 1, v___f_562_);
    lean_ctor_set(v___x_564_, 2, v___f_563_);
    return v___x_564_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred(
    mut v_p_565_: *mut LeanObject,
    mut v_inst_566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    v___x_567_ = l_String_Slice_Pattern_CharPred_Decidable_instBackwardPatternForallCharPropOfDecidablePred___redArg(v_inst_566_);
    return v___x_567_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___lam__0(
    mut v_s_568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_startInclusive_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    v_startInclusive_569_ = lean_ctor_get(v_s_568_, 1);
    v_endExclusive_570_ = lean_ctor_get(v_s_568_, 2);
    v___x_571_ = lean_nat_sub(v_endExclusive_570_, v_startInclusive_569_);
    return v___x_571_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___lam__0___boxed(
    mut v_s_572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_573_: *mut LeanObject = core::ptr::null_mut();
    v_res_573_ = l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___lam__0(v_s_572_);
    lean_dec_ref(v_s_572_);
    return v_res_573_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide(
    mut v_p_575_: *mut LeanObject,
    mut v_inst_576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_577_: *mut LeanObject = core::ptr::null_mut();
    v___f_577_ = l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___closed__0;
    return v___f_577_;
}
pub unsafe fn l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide___boxed(
    mut v_p_578_: *mut LeanObject,
    mut v_inst_579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_580_: *mut LeanObject = core::ptr::null_mut();
    v_res_580_ = l_String_Slice_Pattern_CharPred_Decidable_instToBackwardSearcherForallCharPropDefaultBackwardSearcherForallBoolDecide(v_p_578_, v_inst_579_);
    lean_dec_ref(v_inst_579_);
    return v_res_580_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Pattern_Pred(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Pattern_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Termination(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Pattern_Pred(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Pattern_Pred(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Pattern_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Termination(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Pattern_Pred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Pattern_Pred(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_String_Pattern_Pred(builtin);
}

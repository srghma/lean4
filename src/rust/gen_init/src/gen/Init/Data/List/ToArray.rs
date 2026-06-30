// Lean compiler output
// Module: Init.Data.List.ToArray
// Imports: Init.Data.List.Control Init.Data.List.Monadic Init.Data.Array.Basic Init.Data.Array.Set Init.ByCases Init.Data.Array.Bootstrap Init.Data.Bool Init.Data.List.Erase Init.Data.List.Find Init.Data.List.Nat.Erase Init.Data.List.Nat.InsertIdx Init.Data.List.Nat.TakeDrop Init.Data.List.Sublist Init.Data.List.TakeDrop Init.Data.List.Zip Init.Data.Nat.Lemmas Init.Data.Option.Lemmas Init.Omega Init.TacticsExtra
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::Array::Set::{
    initialize_Init_Data_Array_Set, runtime_initialize_Init_Data_Array_Set,
};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::List::Control::{
    initialize_Init_Data_List_Control, runtime_initialize_Init_Data_List_Control,
};
use crate::r#gen::Init::Data::List::Erase::{
    initialize_Init_Data_List_Erase, runtime_initialize_Init_Data_List_Erase,
};
use crate::r#gen::Init::Data::List::Find::{
    initialize_Init_Data_List_Find, runtime_initialize_Init_Data_List_Find,
};
use crate::r#gen::Init::Data::List::Monadic::{
    initialize_Init_Data_List_Monadic, runtime_initialize_Init_Data_List_Monadic,
};
use crate::r#gen::Init::Data::List::Nat::Erase::{
    initialize_Init_Data_List_Nat_Erase, runtime_initialize_Init_Data_List_Nat_Erase,
};
use crate::r#gen::Init::Data::List::Nat::InsertIdx::{
    initialize_Init_Data_List_Nat_InsertIdx, runtime_initialize_Init_Data_List_Nat_InsertIdx,
};
use crate::r#gen::Init::Data::List::Nat::TakeDrop::{
    initialize_Init_Data_List_Nat_TakeDrop, runtime_initialize_Init_Data_List_Nat_TakeDrop,
};
use crate::r#gen::Init::Data::List::Sublist::{
    initialize_Init_Data_List_Sublist, runtime_initialize_Init_Data_List_Sublist,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::List::Zip::{
    initialize_Init_Data_List_Zip, runtime_initialize_Init_Data_List_Zip,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::TacticsExtra::{
    initialize_Init_TacticsExtra, runtime_initialize_Init_TacticsExtra,
};
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___redArg(
    mut v_i_293_: *mut leanh::LeanObject,
    mut v_h__1_294_: *mut leanh::LeanObject,
    mut v_h__2_295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_297_: u8 = 0;
    v_zero_296_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_297_ = lean_nat_dec_eq(v_i_293_, v_zero_296_);
    if v_isZero_297_ == 1 {
        let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_295_);
        v___x_298_ = leanh::lean_apply_1(v_h__1_294_, leanh::lean_box(0));
        return v___x_298_;
    } else {
        let mut v_one_299_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_300_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_294_);
        v_one_299_ = leanh::lean_unsigned_to_nat(1);
        v_n_300_ = lean_nat_sub(v_i_293_, v_one_299_);
        v___x_301_ = leanh::lean_apply_2(v_h__2_295_, v_n_300_, leanh::lean_box(0));
        return v___x_301_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___redArg___boxed(
    mut v_i_302_: *mut leanh::LeanObject,
    mut v_h__1_303_: *mut leanh::LeanObject,
    mut v_h__2_304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_305_ =
        l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___redArg(
            v_i_302_,
            v_h__1_303_,
            v_h__2_304_,
        );
    leanh::lean_dec(v_i_302_);
    return v_res_305_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter(
    mut v_00_u03b1_306_: *mut leanh::LeanObject,
    mut v_as_307_: *mut leanh::LeanObject,
    mut v_motive_308_: *mut leanh::LeanObject,
    mut v_i_309_: *mut leanh::LeanObject,
    mut v_h_310_: *mut leanh::LeanObject,
    mut v_h__1_311_: *mut leanh::LeanObject,
    mut v_h__2_312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_314_: u8 = 0;
    v_zero_313_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_314_ = lean_nat_dec_eq(v_i_309_, v_zero_313_);
    if v_isZero_314_ == 1 {
        let mut v___x_315_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_312_);
        v___x_315_ = leanh::lean_apply_1(v_h__1_311_, leanh::lean_box(0));
        return v___x_315_;
    } else {
        let mut v_one_316_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_317_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_318_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_311_);
        v_one_316_ = leanh::lean_unsigned_to_nat(1);
        v_n_317_ = lean_nat_sub(v_i_309_, v_one_316_);
        v___x_318_ = leanh::lean_apply_2(v_h__2_312_, v_n_317_, leanh::lean_box(0));
        return v___x_318_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___boxed(
    mut v_00_u03b1_319_: *mut leanh::LeanObject,
    mut v_as_320_: *mut leanh::LeanObject,
    mut v_motive_321_: *mut leanh::LeanObject,
    mut v_i_322_: *mut leanh::LeanObject,
    mut v_h_323_: *mut leanh::LeanObject,
    mut v_h__1_324_: *mut leanh::LeanObject,
    mut v_h__2_325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_326_ = l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter(
        v_00_u03b1_319_,
        v_as_320_,
        v_motive_321_,
        v_i_322_,
        v_h_323_,
        v_h__1_324_,
        v_h__2_325_,
    );
    leanh::lean_dec(v_i_322_);
    leanh::lean_dec_ref(v_as_320_);
    return v_res_326_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__1_splitter___redArg(
    mut v_____do__lift_327_: *mut leanh::LeanObject,
    mut v_h__1_328_: *mut leanh::LeanObject,
    mut v_h__2_329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_327_) == 0 {
        let mut v_a_330_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_331_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_329_);
        v_a_330_ = leanh::lean_ctor_get(v_____do__lift_327_, 0);
        leanh::lean_inc(v_a_330_);
        leanh::lean_dec_ref_known(v_____do__lift_327_, 1);
        v___x_331_ = leanh::lean_apply_1(v_h__1_328_, v_a_330_);
        return v___x_331_;
    } else {
        let mut v_a_332_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_333_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_328_);
        v_a_332_ = leanh::lean_ctor_get(v_____do__lift_327_, 0);
        leanh::lean_inc(v_a_332_);
        leanh::lean_dec_ref_known(v_____do__lift_327_, 1);
        v___x_333_ = leanh::lean_apply_1(v_h__2_329_, v_a_332_);
        return v___x_333_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__1_splitter(
    mut v_00_u03b2_334_: *mut leanh::LeanObject,
    mut v_motive_335_: *mut leanh::LeanObject,
    mut v_____do__lift_336_: *mut leanh::LeanObject,
    mut v_h__1_337_: *mut leanh::LeanObject,
    mut v_h__2_338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_336_) == 0 {
        let mut v_a_339_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_340_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_338_);
        v_a_339_ = leanh::lean_ctor_get(v_____do__lift_336_, 0);
        leanh::lean_inc(v_a_339_);
        leanh::lean_dec_ref_known(v_____do__lift_336_, 1);
        v___x_340_ = leanh::lean_apply_1(v_h__1_337_, v_a_339_);
        return v___x_340_;
    } else {
        let mut v_a_341_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_342_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_337_);
        v_a_341_ = leanh::lean_ctor_get(v_____do__lift_336_, 0);
        leanh::lean_inc(v_a_341_);
        leanh::lean_dec_ref_known(v_____do__lift_336_, 1);
        v___x_342_ = leanh::lean_apply_1(v_h__2_338_, v_a_341_);
        return v___x_342_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_forIn_x27__cons_match__1_splitter___redArg(
    mut v_x_343_: *mut leanh::LeanObject,
    mut v_h__1_344_: *mut leanh::LeanObject,
    mut v_h__2_345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_343_) == 0 {
        let mut v_a_346_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_345_);
        v_a_346_ = leanh::lean_ctor_get(v_x_343_, 0);
        leanh::lean_inc(v_a_346_);
        leanh::lean_dec_ref_known(v_x_343_, 1);
        v___x_347_ = leanh::lean_apply_1(v_h__1_344_, v_a_346_);
        return v___x_347_;
    } else {
        let mut v_a_348_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_344_);
        v_a_348_ = leanh::lean_ctor_get(v_x_343_, 0);
        leanh::lean_inc(v_a_348_);
        leanh::lean_dec_ref_known(v_x_343_, 1);
        v___x_349_ = leanh::lean_apply_1(v_h__2_345_, v_a_348_);
        return v___x_349_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_forIn_x27__cons_match__1_splitter(
    mut v_00_u03b2_350_: *mut leanh::LeanObject,
    mut v_motive_351_: *mut leanh::LeanObject,
    mut v_x_352_: *mut leanh::LeanObject,
    mut v_h__1_353_: *mut leanh::LeanObject,
    mut v_h__2_354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_352_) == 0 {
        let mut v_a_355_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_354_);
        v_a_355_ = leanh::lean_ctor_get(v_x_352_, 0);
        leanh::lean_inc(v_a_355_);
        leanh::lean_dec_ref_known(v_x_352_, 1);
        v___x_356_ = leanh::lean_apply_1(v_h__1_353_, v_a_355_);
        return v___x_356_;
    } else {
        let mut v_a_357_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_353_);
        v_a_357_ = leanh::lean_ctor_get(v_x_352_, 0);
        leanh::lean_inc(v_a_357_);
        leanh::lean_dec_ref_known(v_x_352_, 1);
        v___x_358_ = leanh::lean_apply_1(v_h__2_354_, v_a_357_);
        return v___x_358_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__1_splitter___redArg(
    mut v_____do__lift_359_: *mut leanh::LeanObject,
    mut v_h__1_360_: *mut leanh::LeanObject,
    mut v_h__2_361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_359_) == 1 {
        let mut v_val_362_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_361_);
        v_val_362_ = leanh::lean_ctor_get(v_____do__lift_359_, 0);
        leanh::lean_inc(v_val_362_);
        leanh::lean_dec_ref_known(v_____do__lift_359_, 1);
        v___x_363_ = leanh::lean_apply_1(v_h__1_360_, v_val_362_);
        return v___x_363_;
    } else {
        let mut v___x_364_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_360_);
        v___x_364_ =
            leanh::lean_apply_2(v_h__2_361_, v_____do__lift_359_, leanh::lean_box(0));
        return v___x_364_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__1_splitter(
    mut v_00_u03b2_365_: *mut leanh::LeanObject,
    mut v_motive_366_: *mut leanh::LeanObject,
    mut v_____do__lift_367_: *mut leanh::LeanObject,
    mut v_h__1_368_: *mut leanh::LeanObject,
    mut v_h__2_369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_367_) == 1 {
        let mut v_val_370_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_371_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_369_);
        v_val_370_ = leanh::lean_ctor_get(v_____do__lift_367_, 0);
        leanh::lean_inc(v_val_370_);
        leanh::lean_dec_ref_known(v_____do__lift_367_, 1);
        v___x_371_ = leanh::lean_apply_1(v_h__1_368_, v_val_370_);
        return v___x_371_;
    } else {
        let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_368_);
        v___x_372_ =
            leanh::lean_apply_2(v_h__2_369_, v_____do__lift_367_, leanh::lean_box(0));
        return v___x_372_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Break_runK_match__1_splitter___redArg(
    mut v_x_373_: *mut leanh::LeanObject,
    mut v_h__1_374_: *mut leanh::LeanObject,
    mut v_h__2_375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_373_) == 0 {
        let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_374_);
        v___x_376_ = leanh::lean_box(0);
        v___x_377_ = leanh::lean_apply_1(v_h__2_375_, v___x_376_);
        return v___x_377_;
    } else {
        let mut v_val_378_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_375_);
        v_val_378_ = leanh::lean_ctor_get(v_x_373_, 0);
        leanh::lean_inc(v_val_378_);
        leanh::lean_dec_ref_known(v_x_373_, 1);
        v___x_379_ = leanh::lean_apply_1(v_h__1_374_, v_val_378_);
        return v___x_379_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Break_runK_match__1_splitter(
    mut v_00_u03b1_380_: *mut leanh::LeanObject,
    mut v_motive_381_: *mut leanh::LeanObject,
    mut v_x_382_: *mut leanh::LeanObject,
    mut v_h__1_383_: *mut leanh::LeanObject,
    mut v_h__2_384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_382_) == 0 {
        let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_386_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_383_);
        v___x_385_ = leanh::lean_box(0);
        v___x_386_ = leanh::lean_apply_1(v_h__2_384_, v___x_385_);
        return v___x_386_;
    } else {
        let mut v_val_387_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_384_);
        v_val_387_ = leanh::lean_ctor_get(v_x_382_, 0);
        leanh::lean_inc(v_val_387_);
        leanh::lean_dec_ref_known(v_x_382_, 1);
        v___x_388_ = leanh::lean_apply_1(v_h__1_383_, v_val_387_);
        return v___x_388_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_mapA_match__1_splitter___redArg(
    mut v_x_389_: *mut leanh::LeanObject,
    mut v_h__1_390_: *mut leanh::LeanObject,
    mut v_h__2_391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_389_) == 0 {
        let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_391_);
        v___x_392_ = leanh::lean_box(0);
        v___x_393_ = leanh::lean_apply_1(v_h__1_390_, v___x_392_);
        return v___x_393_;
    } else {
        let mut v_head_394_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_395_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_390_);
        v_head_394_ = leanh::lean_ctor_get(v_x_389_, 0);
        leanh::lean_inc(v_head_394_);
        v_tail_395_ = leanh::lean_ctor_get(v_x_389_, 1);
        leanh::lean_inc(v_tail_395_);
        leanh::lean_dec_ref_known(v_x_389_, 2);
        v___x_396_ = leanh::lean_apply_2(v_h__2_391_, v_head_394_, v_tail_395_);
        return v___x_396_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_mapA_match__1_splitter(
    mut v_00_u03b1_397_: *mut leanh::LeanObject,
    mut v_motive_398_: *mut leanh::LeanObject,
    mut v_x_399_: *mut leanh::LeanObject,
    mut v_h__1_400_: *mut leanh::LeanObject,
    mut v_h__2_401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_399_) == 0 {
        let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_401_);
        v___x_402_ = leanh::lean_box(0);
        v___x_403_ = leanh::lean_apply_1(v_h__1_400_, v___x_402_);
        return v___x_403_;
    } else {
        let mut v_head_404_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_405_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_400_);
        v_head_404_ = leanh::lean_ctor_get(v_x_399_, 0);
        leanh::lean_inc(v_head_404_);
        v_tail_405_ = leanh::lean_ctor_get(v_x_399_, 1);
        leanh::lean_inc(v_tail_405_);
        leanh::lean_dec_ref_known(v_x_399_, 2);
        v___x_406_ = leanh::lean_apply_2(v_h__2_401_, v_head_404_, v_tail_405_);
        return v___x_406_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_findSomeM_x3f_match__1_splitter___redArg(
    mut v_____do__lift_407_: *mut leanh::LeanObject,
    mut v_h__1_408_: *mut leanh::LeanObject,
    mut v_h__2_409_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_407_) == 0 {
        let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_408_);
        v___x_410_ = leanh::lean_box(0);
        v___x_411_ = leanh::lean_apply_1(v_h__2_409_, v___x_410_);
        return v___x_411_;
    } else {
        let mut v_val_412_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_409_);
        v_val_412_ = leanh::lean_ctor_get(v_____do__lift_407_, 0);
        leanh::lean_inc(v_val_412_);
        leanh::lean_dec_ref_known(v_____do__lift_407_, 1);
        v___x_413_ = leanh::lean_apply_1(v_h__1_408_, v_val_412_);
        return v___x_413_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_findSomeM_x3f_match__1_splitter(
    mut v_00_u03b2_414_: *mut leanh::LeanObject,
    mut v_motive_415_: *mut leanh::LeanObject,
    mut v_____do__lift_416_: *mut leanh::LeanObject,
    mut v_h__1_417_: *mut leanh::LeanObject,
    mut v_h__2_418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_416_) == 0 {
        let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_417_);
        v___x_419_ = leanh::lean_box(0);
        v___x_420_ = leanh::lean_apply_1(v_h__2_418_, v___x_419_);
        return v___x_420_;
    } else {
        let mut v_val_421_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_418_);
        v_val_421_ = leanh::lean_ctor_get(v_____do__lift_416_, 0);
        leanh::lean_inc(v_val_421_);
        leanh::lean_dec_ref_known(v_____do__lift_416_, 1);
        v___x_422_ = leanh::lean_apply_1(v_h__1_417_, v_val_421_);
        return v___x_422_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg(
    mut v_x_423_: *mut leanh::LeanObject,
    mut v_h__1_424_: *mut leanh::LeanObject,
    mut v_h__2_425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_427_: u8 = 0;
    v_zero_426_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_427_ = lean_nat_dec_eq(v_x_423_, v_zero_426_);
    if v_isZero_427_ == 1 {
        let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_425_);
        v___x_428_ = leanh::lean_apply_1(v_h__1_424_, leanh::lean_box(0));
        return v___x_428_;
    } else {
        let mut v_one_429_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_430_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_424_);
        v_one_429_ = leanh::lean_unsigned_to_nat(1);
        v_n_430_ = lean_nat_sub(v_x_423_, v_one_429_);
        v___x_431_ = leanh::lean_apply_2(v_h__2_425_, v_n_430_, leanh::lean_box(0));
        return v___x_431_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg___boxed(
    mut v_x_432_: *mut leanh::LeanObject,
    mut v_h__1_433_: *mut leanh::LeanObject,
    mut v_h__2_434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_435_ = l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg(
        v_x_432_,
        v_h__1_433_,
        v_h__2_434_,
    );
    leanh::lean_dec(v_x_432_);
    return v_res_435_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter(
    mut v_00_u03b1_436_: *mut leanh::LeanObject,
    mut v_xs_437_: *mut leanh::LeanObject,
    mut v_motive_438_: *mut leanh::LeanObject,
    mut v_x_439_: *mut leanh::LeanObject,
    mut v_x_440_: *mut leanh::LeanObject,
    mut v_h__1_441_: *mut leanh::LeanObject,
    mut v_h__2_442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_444_: u8 = 0;
    v_zero_443_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_444_ = lean_nat_dec_eq(v_x_439_, v_zero_443_);
    if v_isZero_444_ == 1 {
        let mut v___x_445_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_442_);
        v___x_445_ = leanh::lean_apply_1(v_h__1_441_, leanh::lean_box(0));
        return v___x_445_;
    } else {
        let mut v_one_446_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_447_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_441_);
        v_one_446_ = leanh::lean_unsigned_to_nat(1);
        v_n_447_ = lean_nat_sub(v_x_439_, v_one_446_);
        v___x_448_ = leanh::lean_apply_2(v_h__2_442_, v_n_447_, leanh::lean_box(0));
        return v___x_448_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___boxed(
    mut v_00_u03b1_449_: *mut leanh::LeanObject,
    mut v_xs_450_: *mut leanh::LeanObject,
    mut v_motive_451_: *mut leanh::LeanObject,
    mut v_x_452_: *mut leanh::LeanObject,
    mut v_x_453_: *mut leanh::LeanObject,
    mut v_h__1_454_: *mut leanh::LeanObject,
    mut v_h__2_455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_456_ = l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter(
        v_00_u03b1_449_,
        v_xs_450_,
        v_motive_451_,
        v_x_452_,
        v_x_453_,
        v_h__1_454_,
        v_h__2_455_,
    );
    leanh::lean_dec(v_x_452_);
    leanh::lean_dec_ref(v_xs_450_);
    return v_res_456_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter___redArg(
    mut v_r_457_: *mut leanh::LeanObject,
    mut v_h__1_458_: *mut leanh::LeanObject,
    mut v_h__2_459_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_r_457_) == 0 {
        let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_458_);
        v___x_460_ = leanh::lean_box(0);
        v___x_461_ = leanh::lean_apply_1(v_h__2_459_, v___x_460_);
        return v___x_461_;
    } else {
        let mut v_val_462_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_459_);
        v_val_462_ = leanh::lean_ctor_get(v_r_457_, 0);
        leanh::lean_inc(v_val_462_);
        leanh::lean_dec_ref_known(v_r_457_, 1);
        v___x_463_ = leanh::lean_apply_1(v_h__1_458_, v_val_462_);
        return v___x_463_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter(
    mut v_00_u03b2_464_: *mut leanh::LeanObject,
    mut v_motive_465_: *mut leanh::LeanObject,
    mut v_r_466_: *mut leanh::LeanObject,
    mut v_h__1_467_: *mut leanh::LeanObject,
    mut v_h__2_468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_r_466_) == 0 {
        let mut v___x_469_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_467_);
        v___x_469_ = leanh::lean_box(0);
        v___x_470_ = leanh::lean_apply_1(v_h__2_468_, v___x_469_);
        return v___x_470_;
    } else {
        let mut v_val_471_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_468_);
        v_val_471_ = leanh::lean_ctor_get(v_r_466_, 0);
        leanh::lean_inc(v_val_471_);
        leanh::lean_dec_ref_known(v_r_466_, 1);
        v___x_472_ = leanh::lean_apply_1(v_h__1_467_, v_val_471_);
        return v___x_472_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_findM_x3f_match__1_splitter___redArg(
    mut v_x_473_: *mut leanh::LeanObject,
    mut v_h__1_474_: *mut leanh::LeanObject,
    mut v_h__2_475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_473_) == 0 {
        let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_475_);
        v___x_476_ = leanh::lean_box(0);
        v___x_477_ = leanh::lean_apply_1(v_h__1_474_, v___x_476_);
        return v___x_477_;
    } else {
        let mut v_head_478_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_479_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_474_);
        v_head_478_ = leanh::lean_ctor_get(v_x_473_, 0);
        leanh::lean_inc(v_head_478_);
        v_tail_479_ = leanh::lean_ctor_get(v_x_473_, 1);
        leanh::lean_inc(v_tail_479_);
        leanh::lean_dec_ref_known(v_x_473_, 2);
        v___x_480_ = leanh::lean_apply_2(v_h__2_475_, v_head_478_, v_tail_479_);
        return v___x_480_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_findM_x3f_match__1_splitter(
    mut v_00_u03b1_481_: *mut leanh::LeanObject,
    mut v_motive_482_: *mut leanh::LeanObject,
    mut v_x_483_: *mut leanh::LeanObject,
    mut v_h__1_484_: *mut leanh::LeanObject,
    mut v_h__2_485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_483_) == 0 {
        let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_485_);
        v___x_486_ = leanh::lean_box(0);
        v___x_487_ = leanh::lean_apply_1(v_h__1_484_, v___x_486_);
        return v___x_487_;
    } else {
        let mut v_head_488_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_489_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_484_);
        v_head_488_ = leanh::lean_ctor_get(v_x_483_, 0);
        leanh::lean_inc(v_head_488_);
        v_tail_489_ = leanh::lean_ctor_get(v_x_483_, 1);
        leanh::lean_inc(v_tail_489_);
        leanh::lean_dec_ref_known(v_x_483_, 2);
        v___x_490_ = leanh::lean_apply_2(v_h__2_485_, v_head_488_, v_tail_489_);
        return v___x_490_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(
    mut v_____do__lift_491_: u8,
    mut v_h__1_492_: *mut leanh::LeanObject,
    mut v_h__2_493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_____do__lift_491_ == 0 {
        let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_492_);
        v___x_494_ = leanh::lean_box(0);
        v___x_495_ = leanh::lean_apply_1(v_h__2_493_, v___x_494_);
        return v___x_495_;
    } else {
        let mut v___x_496_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_493_);
        v___x_496_ = leanh::lean_box(0);
        v___x_497_ = leanh::lean_apply_1(v_h__1_492_, v___x_496_);
        return v___x_497_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg___boxed(
    mut v_____do__lift_498_: *mut leanh::LeanObject,
    mut v_h__1_499_: *mut leanh::LeanObject,
    mut v_h__2_500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_26__boxed_501_: u8 = 0;
    let mut v_res_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_26__boxed_501_ = (leanh::lean_unbox(v_____do__lift_498_) as u8);
    v_res_502_ = l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(
        v_____do__lift_26__boxed_501_,
        v_h__1_499_,
        v_h__2_500_,
    );
    return v_res_502_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter(
    mut v_motive_503_: *mut leanh::LeanObject,
    mut v_____do__lift_504_: u8,
    mut v_h__1_505_: *mut leanh::LeanObject,
    mut v_h__2_506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_____do__lift_504_ == 0 {
        let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_505_);
        v___x_507_ = leanh::lean_box(0);
        v___x_508_ = leanh::lean_apply_1(v_h__2_506_, v___x_507_);
        return v___x_508_;
    } else {
        let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_506_);
        v___x_509_ = leanh::lean_box(0);
        v___x_510_ = leanh::lean_apply_1(v_h__1_505_, v___x_509_);
        return v___x_510_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___boxed(
    mut v_motive_511_: *mut leanh::LeanObject,
    mut v_____do__lift_512_: *mut leanh::LeanObject,
    mut v_h__1_513_: *mut leanh::LeanObject,
    mut v_h__2_514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_37__boxed_515_: u8 = 0;
    let mut v_res_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_37__boxed_515_ = (leanh::lean_unbox(v_____do__lift_512_) as u8);
    v_res_516_ = l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter(
        v_motive_511_,
        v_____do__lift_37__boxed_515_,
        v_h__1_513_,
        v_h__2_514_,
    );
    return v_res_516_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_517_: *mut leanh::LeanObject,
    mut v_h__1_518_: *mut leanh::LeanObject,
    mut v_h__2_519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_517_) == 0 {
        let mut v___x_520_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_519_);
        v___x_520_ = leanh::lean_box(0);
        v___x_521_ = leanh::lean_apply_1(v_h__1_518_, v___x_520_);
        return v___x_521_;
    } else {
        let mut v_head_522_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_523_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_518_);
        v_head_522_ = leanh::lean_ctor_get(v_x_517_, 0);
        leanh::lean_inc(v_head_522_);
        v_tail_523_ = leanh::lean_ctor_get(v_x_517_, 1);
        leanh::lean_inc(v_tail_523_);
        leanh::lean_dec_ref_known(v_x_517_, 2);
        v___x_524_ = leanh::lean_apply_2(v_h__2_519_, v_head_522_, v_tail_523_);
        return v___x_524_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_525_: *mut leanh::LeanObject,
    mut v_motive_526_: *mut leanh::LeanObject,
    mut v_x_527_: *mut leanh::LeanObject,
    mut v_h__1_528_: *mut leanh::LeanObject,
    mut v_h__2_529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_527_) == 0 {
        let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_531_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_529_);
        v___x_530_ = leanh::lean_box(0);
        v___x_531_ = leanh::lean_apply_1(v_h__1_528_, v___x_530_);
        return v___x_531_;
    } else {
        let mut v_head_532_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_533_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_528_);
        v_head_532_ = leanh::lean_ctor_get(v_x_527_, 0);
        leanh::lean_inc(v_head_532_);
        v_tail_533_ = leanh::lean_ctor_get(v_x_527_, 1);
        leanh::lean_inc(v_tail_533_);
        leanh::lean_dec_ref_known(v_x_527_, 2);
        v___x_534_ = leanh::lean_apply_2(v_h__2_529_, v_head_532_, v_tail_533_);
        return v___x_534_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(
    mut v_x_535_: u8,
    mut v_h__1_536_: *mut leanh::LeanObject,
    mut v_h__2_537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_535_ == 0 {
        let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_539_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_536_);
        v___x_538_ = leanh::lean_box(0);
        v___x_539_ = leanh::lean_apply_1(v_h__2_537_, v___x_538_);
        return v___x_539_;
    } else {
        let mut v___x_540_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_537_);
        v___x_540_ = leanh::lean_box(0);
        v___x_541_ = leanh::lean_apply_1(v_h__1_536_, v___x_540_);
        return v___x_541_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_542_: *mut leanh::LeanObject,
    mut v_h__1_543_: *mut leanh::LeanObject,
    mut v_h__2_544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_26__boxed_545_: u8 = 0;
    let mut v_res_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_545_ = (leanh::lean_unbox(v_x_542_) as u8);
    v_res_546_ = l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(
        v_x_26__boxed_545_,
        v_h__1_543_,
        v_h__2_544_,
    );
    return v_res_546_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter(
    mut v_motive_547_: *mut leanh::LeanObject,
    mut v_x_548_: u8,
    mut v_h__1_549_: *mut leanh::LeanObject,
    mut v_h__2_550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_548_ == 0 {
        let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_549_);
        v___x_551_ = leanh::lean_box(0);
        v___x_552_ = leanh::lean_apply_1(v_h__2_550_, v___x_551_);
        return v___x_552_;
    } else {
        let mut v___x_553_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_550_);
        v___x_553_ = leanh::lean_box(0);
        v___x_554_ = leanh::lean_apply_1(v_h__1_549_, v___x_553_);
        return v___x_554_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___boxed(
    mut v_motive_555_: *mut leanh::LeanObject,
    mut v_x_556_: *mut leanh::LeanObject,
    mut v_h__1_557_: *mut leanh::LeanObject,
    mut v_h__2_558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_37__boxed_559_: u8 = 0;
    let mut v_res_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_559_ = (leanh::lean_unbox(v_x_556_) as u8);
    v_res_560_ = l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter(
        v_motive_555_,
        v_x_37__boxed_559_,
        v_h__1_557_,
        v_h__2_558_,
    );
    return v_res_560_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___redArg(
    mut v_x_561_: *mut leanh::LeanObject,
    mut v_h__1_562_: *mut leanh::LeanObject,
    mut v_h__2_563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_561_) == 0 {
        let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_563_);
        v___x_564_ = leanh::lean_box(0);
        v___x_565_ = leanh::lean_apply_1(v_h__1_562_, v___x_564_);
        return v___x_565_;
    } else {
        let mut v_val_566_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_567_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_562_);
        v_val_566_ = leanh::lean_ctor_get(v_x_561_, 0);
        leanh::lean_inc(v_val_566_);
        leanh::lean_dec_ref_known(v_x_561_, 1);
        v___x_567_ = leanh::lean_apply_1(v_h__2_563_, v_val_566_);
        return v___x_567_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter(
    mut v_00_u03b1_568_: *mut leanh::LeanObject,
    mut v_as_569_: *mut leanh::LeanObject,
    mut v_motive_570_: *mut leanh::LeanObject,
    mut v_x_571_: *mut leanh::LeanObject,
    mut v_h__1_572_: *mut leanh::LeanObject,
    mut v_h__2_573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_571_) == 0 {
        let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_573_);
        v___x_574_ = leanh::lean_box(0);
        v___x_575_ = leanh::lean_apply_1(v_h__1_572_, v___x_574_);
        return v___x_575_;
    } else {
        let mut v_val_576_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_577_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_572_);
        v_val_576_ = leanh::lean_ctor_get(v_x_571_, 0);
        leanh::lean_inc(v_val_576_);
        leanh::lean_dec_ref_known(v_x_571_, 1);
        v___x_577_ = leanh::lean_apply_1(v_h__2_573_, v_val_576_);
        return v___x_577_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___boxed(
    mut v_00_u03b1_578_: *mut leanh::LeanObject,
    mut v_as_579_: *mut leanh::LeanObject,
    mut v_motive_580_: *mut leanh::LeanObject,
    mut v_x_581_: *mut leanh::LeanObject,
    mut v_h__1_582_: *mut leanh::LeanObject,
    mut v_h__2_583_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_584_ = l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter(
        v_00_u03b1_578_,
        v_as_579_,
        v_motive_580_,
        v_x_581_,
        v_h__1_582_,
        v_h__2_583_,
    );
    leanh::lean_dec_ref(v_as_579_);
    return v_res_584_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_ToArray(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Set(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Erase(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Find(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Erase(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_InsertIdx(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_TacticsExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_ToArray(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_ToArray(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Control(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Monadic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Set(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Erase(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Find(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_Erase(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_InsertIdx(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Zip(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_TacticsExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_ToArray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_ToArray(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_ToArray(builtin);
}
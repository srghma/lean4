// Lean compiler output
// Module: Init.Data.List.ToArray
// Imports: Init.Data.List.Control Init.Data.List.Monadic Init.Data.Array.Basic Init.Data.Array.Set Init.ByCases Init.Data.Array.Bootstrap Init.Data.Bool Init.Data.List.Erase Init.Data.List.Find Init.Data.List.Nat.Erase Init.Data.List.Nat.InsertIdx Init.Data.List.Nat.TakeDrop Init.Data.List.Sublist Init.Data.List.TakeDrop Init.Data.List.Zip Init.Data.Nat.Lemmas Init.Data.Option.Lemmas Init.Omega Init.TacticsExtra
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
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___redArg(
    mut v_i_293_: *mut crate::leanh::LeanObject,
    mut v_h__1_294_: *mut crate::leanh::LeanObject,
    mut v_h__2_295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_297_: u8 = 0;
    v_zero_296_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_297_ = lean_nat_dec_eq(v_i_293_, v_zero_296_);
    if v_isZero_297_ == 1 {
        let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_295_);
        v___x_298_ = crate::leanh::lean_apply_1(v_h__1_294_, crate::leanh::lean_box(0));
        return v___x_298_;
    } else {
        let mut v_one_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_294_);
        v_one_299_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_300_ = lean_nat_sub(v_i_293_, v_one_299_);
        v___x_301_ = crate::leanh::lean_apply_2(v_h__2_295_, v_n_300_, crate::leanh::lean_box(0));
        return v___x_301_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___redArg___boxed(
    mut v_i_302_: *mut crate::leanh::LeanObject,
    mut v_h__1_303_: *mut crate::leanh::LeanObject,
    mut v_h__2_304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_305_ =
        l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___redArg(
            v_i_302_,
            v_h__1_303_,
            v_h__2_304_,
        );
    crate::leanh::lean_dec(v_i_302_);
    return v_res_305_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter(
    mut v_00_u03b1_306_: *mut crate::leanh::LeanObject,
    mut v_as_307_: *mut crate::leanh::LeanObject,
    mut v_motive_308_: *mut crate::leanh::LeanObject,
    mut v_i_309_: *mut crate::leanh::LeanObject,
    mut v_h_310_: *mut crate::leanh::LeanObject,
    mut v_h__1_311_: *mut crate::leanh::LeanObject,
    mut v_h__2_312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_314_: u8 = 0;
    v_zero_313_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_314_ = lean_nat_dec_eq(v_i_309_, v_zero_313_);
    if v_isZero_314_ == 1 {
        let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_312_);
        v___x_315_ = crate::leanh::lean_apply_1(v_h__1_311_, crate::leanh::lean_box(0));
        return v___x_315_;
    } else {
        let mut v_one_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_311_);
        v_one_316_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_317_ = lean_nat_sub(v_i_309_, v_one_316_);
        v___x_318_ = crate::leanh::lean_apply_2(v_h__2_312_, v_n_317_, crate::leanh::lean_box(0));
        return v___x_318_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___boxed(
    mut v_00_u03b1_319_: *mut crate::leanh::LeanObject,
    mut v_as_320_: *mut crate::leanh::LeanObject,
    mut v_motive_321_: *mut crate::leanh::LeanObject,
    mut v_i_322_: *mut crate::leanh::LeanObject,
    mut v_h_323_: *mut crate::leanh::LeanObject,
    mut v_h__1_324_: *mut crate::leanh::LeanObject,
    mut v_h__2_325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_326_ = l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter(
        v_00_u03b1_319_,
        v_as_320_,
        v_motive_321_,
        v_i_322_,
        v_h_323_,
        v_h__1_324_,
        v_h__2_325_,
    );
    crate::leanh::lean_dec(v_i_322_);
    crate::leanh::lean_dec_ref(v_as_320_);
    return v_res_326_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__1_splitter___redArg(
    mut v_____do__lift_327_: *mut crate::leanh::LeanObject,
    mut v_h__1_328_: *mut crate::leanh::LeanObject,
    mut v_h__2_329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_327_) == 0 {
        let mut v_a_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_329_);
        v_a_330_ = crate::leanh::lean_ctor_get(v_____do__lift_327_, 0);
        crate::leanh::lean_inc(v_a_330_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_327_, 1);
        v___x_331_ = crate::leanh::lean_apply_1(v_h__1_328_, v_a_330_);
        return v___x_331_;
    } else {
        let mut v_a_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_328_);
        v_a_332_ = crate::leanh::lean_ctor_get(v_____do__lift_327_, 0);
        crate::leanh::lean_inc(v_a_332_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_327_, 1);
        v___x_333_ = crate::leanh::lean_apply_1(v_h__2_329_, v_a_332_);
        return v___x_333_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__1_splitter(
    mut v_00_u03b2_334_: *mut crate::leanh::LeanObject,
    mut v_motive_335_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_336_: *mut crate::leanh::LeanObject,
    mut v_h__1_337_: *mut crate::leanh::LeanObject,
    mut v_h__2_338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_336_) == 0 {
        let mut v_a_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_338_);
        v_a_339_ = crate::leanh::lean_ctor_get(v_____do__lift_336_, 0);
        crate::leanh::lean_inc(v_a_339_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_336_, 1);
        v___x_340_ = crate::leanh::lean_apply_1(v_h__1_337_, v_a_339_);
        return v___x_340_;
    } else {
        let mut v_a_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_337_);
        v_a_341_ = crate::leanh::lean_ctor_get(v_____do__lift_336_, 0);
        crate::leanh::lean_inc(v_a_341_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_336_, 1);
        v___x_342_ = crate::leanh::lean_apply_1(v_h__2_338_, v_a_341_);
        return v___x_342_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_forIn_x27__cons_match__1_splitter___redArg(
    mut v_x_343_: *mut crate::leanh::LeanObject,
    mut v_h__1_344_: *mut crate::leanh::LeanObject,
    mut v_h__2_345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_343_) == 0 {
        let mut v_a_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_345_);
        v_a_346_ = crate::leanh::lean_ctor_get(v_x_343_, 0);
        crate::leanh::lean_inc(v_a_346_);
        crate::leanh::lean_dec_ref_known(v_x_343_, 1);
        v___x_347_ = crate::leanh::lean_apply_1(v_h__1_344_, v_a_346_);
        return v___x_347_;
    } else {
        let mut v_a_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_344_);
        v_a_348_ = crate::leanh::lean_ctor_get(v_x_343_, 0);
        crate::leanh::lean_inc(v_a_348_);
        crate::leanh::lean_dec_ref_known(v_x_343_, 1);
        v___x_349_ = crate::leanh::lean_apply_1(v_h__2_345_, v_a_348_);
        return v___x_349_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_forIn_x27__cons_match__1_splitter(
    mut v_00_u03b2_350_: *mut crate::leanh::LeanObject,
    mut v_motive_351_: *mut crate::leanh::LeanObject,
    mut v_x_352_: *mut crate::leanh::LeanObject,
    mut v_h__1_353_: *mut crate::leanh::LeanObject,
    mut v_h__2_354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_352_) == 0 {
        let mut v_a_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_354_);
        v_a_355_ = crate::leanh::lean_ctor_get(v_x_352_, 0);
        crate::leanh::lean_inc(v_a_355_);
        crate::leanh::lean_dec_ref_known(v_x_352_, 1);
        v___x_356_ = crate::leanh::lean_apply_1(v_h__1_353_, v_a_355_);
        return v___x_356_;
    } else {
        let mut v_a_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_353_);
        v_a_357_ = crate::leanh::lean_ctor_get(v_x_352_, 0);
        crate::leanh::lean_inc(v_a_357_);
        crate::leanh::lean_dec_ref_known(v_x_352_, 1);
        v___x_358_ = crate::leanh::lean_apply_1(v_h__2_354_, v_a_357_);
        return v___x_358_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__1_splitter___redArg(
    mut v_____do__lift_359_: *mut crate::leanh::LeanObject,
    mut v_h__1_360_: *mut crate::leanh::LeanObject,
    mut v_h__2_361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_359_) == 1 {
        let mut v_val_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_361_);
        v_val_362_ = crate::leanh::lean_ctor_get(v_____do__lift_359_, 0);
        crate::leanh::lean_inc(v_val_362_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_359_, 1);
        v___x_363_ = crate::leanh::lean_apply_1(v_h__1_360_, v_val_362_);
        return v___x_363_;
    } else {
        let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_360_);
        v___x_364_ =
            crate::leanh::lean_apply_2(v_h__2_361_, v_____do__lift_359_, crate::leanh::lean_box(0));
        return v___x_364_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__1_splitter(
    mut v_00_u03b2_365_: *mut crate::leanh::LeanObject,
    mut v_motive_366_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_367_: *mut crate::leanh::LeanObject,
    mut v_h__1_368_: *mut crate::leanh::LeanObject,
    mut v_h__2_369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_367_) == 1 {
        let mut v_val_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_369_);
        v_val_370_ = crate::leanh::lean_ctor_get(v_____do__lift_367_, 0);
        crate::leanh::lean_inc(v_val_370_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_367_, 1);
        v___x_371_ = crate::leanh::lean_apply_1(v_h__1_368_, v_val_370_);
        return v___x_371_;
    } else {
        let mut v___x_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_368_);
        v___x_372_ =
            crate::leanh::lean_apply_2(v_h__2_369_, v_____do__lift_367_, crate::leanh::lean_box(0));
        return v___x_372_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Break_runK_match__1_splitter___redArg(
    mut v_x_373_: *mut crate::leanh::LeanObject,
    mut v_h__1_374_: *mut crate::leanh::LeanObject,
    mut v_h__2_375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_373_) == 0 {
        let mut v___x_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_374_);
        v___x_376_ = crate::leanh::lean_box(0);
        v___x_377_ = crate::leanh::lean_apply_1(v_h__2_375_, v___x_376_);
        return v___x_377_;
    } else {
        let mut v_val_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_375_);
        v_val_378_ = crate::leanh::lean_ctor_get(v_x_373_, 0);
        crate::leanh::lean_inc(v_val_378_);
        crate::leanh::lean_dec_ref_known(v_x_373_, 1);
        v___x_379_ = crate::leanh::lean_apply_1(v_h__1_374_, v_val_378_);
        return v___x_379_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Break_runK_match__1_splitter(
    mut v_00_u03b1_380_: *mut crate::leanh::LeanObject,
    mut v_motive_381_: *mut crate::leanh::LeanObject,
    mut v_x_382_: *mut crate::leanh::LeanObject,
    mut v_h__1_383_: *mut crate::leanh::LeanObject,
    mut v_h__2_384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_382_) == 0 {
        let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_383_);
        v___x_385_ = crate::leanh::lean_box(0);
        v___x_386_ = crate::leanh::lean_apply_1(v_h__2_384_, v___x_385_);
        return v___x_386_;
    } else {
        let mut v_val_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_384_);
        v_val_387_ = crate::leanh::lean_ctor_get(v_x_382_, 0);
        crate::leanh::lean_inc(v_val_387_);
        crate::leanh::lean_dec_ref_known(v_x_382_, 1);
        v___x_388_ = crate::leanh::lean_apply_1(v_h__1_383_, v_val_387_);
        return v___x_388_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_mapA_match__1_splitter___redArg(
    mut v_x_389_: *mut crate::leanh::LeanObject,
    mut v_h__1_390_: *mut crate::leanh::LeanObject,
    mut v_h__2_391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_389_) == 0 {
        let mut v___x_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_391_);
        v___x_392_ = crate::leanh::lean_box(0);
        v___x_393_ = crate::leanh::lean_apply_1(v_h__1_390_, v___x_392_);
        return v___x_393_;
    } else {
        let mut v_head_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_390_);
        v_head_394_ = crate::leanh::lean_ctor_get(v_x_389_, 0);
        crate::leanh::lean_inc(v_head_394_);
        v_tail_395_ = crate::leanh::lean_ctor_get(v_x_389_, 1);
        crate::leanh::lean_inc(v_tail_395_);
        crate::leanh::lean_dec_ref_known(v_x_389_, 2);
        v___x_396_ = crate::leanh::lean_apply_2(v_h__2_391_, v_head_394_, v_tail_395_);
        return v___x_396_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_mapA_match__1_splitter(
    mut v_00_u03b1_397_: *mut crate::leanh::LeanObject,
    mut v_motive_398_: *mut crate::leanh::LeanObject,
    mut v_x_399_: *mut crate::leanh::LeanObject,
    mut v_h__1_400_: *mut crate::leanh::LeanObject,
    mut v_h__2_401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_399_) == 0 {
        let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_401_);
        v___x_402_ = crate::leanh::lean_box(0);
        v___x_403_ = crate::leanh::lean_apply_1(v_h__1_400_, v___x_402_);
        return v___x_403_;
    } else {
        let mut v_head_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_400_);
        v_head_404_ = crate::leanh::lean_ctor_get(v_x_399_, 0);
        crate::leanh::lean_inc(v_head_404_);
        v_tail_405_ = crate::leanh::lean_ctor_get(v_x_399_, 1);
        crate::leanh::lean_inc(v_tail_405_);
        crate::leanh::lean_dec_ref_known(v_x_399_, 2);
        v___x_406_ = crate::leanh::lean_apply_2(v_h__2_401_, v_head_404_, v_tail_405_);
        return v___x_406_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_findSomeM_x3f_match__1_splitter___redArg(
    mut v_____do__lift_407_: *mut crate::leanh::LeanObject,
    mut v_h__1_408_: *mut crate::leanh::LeanObject,
    mut v_h__2_409_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_407_) == 0 {
        let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_408_);
        v___x_410_ = crate::leanh::lean_box(0);
        v___x_411_ = crate::leanh::lean_apply_1(v_h__2_409_, v___x_410_);
        return v___x_411_;
    } else {
        let mut v_val_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_409_);
        v_val_412_ = crate::leanh::lean_ctor_get(v_____do__lift_407_, 0);
        crate::leanh::lean_inc(v_val_412_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_407_, 1);
        v___x_413_ = crate::leanh::lean_apply_1(v_h__1_408_, v_val_412_);
        return v___x_413_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_findSomeM_x3f_match__1_splitter(
    mut v_00_u03b2_414_: *mut crate::leanh::LeanObject,
    mut v_motive_415_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_416_: *mut crate::leanh::LeanObject,
    mut v_h__1_417_: *mut crate::leanh::LeanObject,
    mut v_h__2_418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_416_) == 0 {
        let mut v___x_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_417_);
        v___x_419_ = crate::leanh::lean_box(0);
        v___x_420_ = crate::leanh::lean_apply_1(v_h__2_418_, v___x_419_);
        return v___x_420_;
    } else {
        let mut v_val_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_418_);
        v_val_421_ = crate::leanh::lean_ctor_get(v_____do__lift_416_, 0);
        crate::leanh::lean_inc(v_val_421_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_416_, 1);
        v___x_422_ = crate::leanh::lean_apply_1(v_h__1_417_, v_val_421_);
        return v___x_422_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg(
    mut v_x_423_: *mut crate::leanh::LeanObject,
    mut v_h__1_424_: *mut crate::leanh::LeanObject,
    mut v_h__2_425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_427_: u8 = 0;
    v_zero_426_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_427_ = lean_nat_dec_eq(v_x_423_, v_zero_426_);
    if v_isZero_427_ == 1 {
        let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_425_);
        v___x_428_ = crate::leanh::lean_apply_1(v_h__1_424_, crate::leanh::lean_box(0));
        return v___x_428_;
    } else {
        let mut v_one_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_424_);
        v_one_429_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_430_ = lean_nat_sub(v_x_423_, v_one_429_);
        v___x_431_ = crate::leanh::lean_apply_2(v_h__2_425_, v_n_430_, crate::leanh::lean_box(0));
        return v___x_431_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg___boxed(
    mut v_x_432_: *mut crate::leanh::LeanObject,
    mut v_h__1_433_: *mut crate::leanh::LeanObject,
    mut v_h__2_434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_435_ = l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg(
        v_x_432_,
        v_h__1_433_,
        v_h__2_434_,
    );
    crate::leanh::lean_dec(v_x_432_);
    return v_res_435_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter(
    mut v_00_u03b1_436_: *mut crate::leanh::LeanObject,
    mut v_xs_437_: *mut crate::leanh::LeanObject,
    mut v_motive_438_: *mut crate::leanh::LeanObject,
    mut v_x_439_: *mut crate::leanh::LeanObject,
    mut v_x_440_: *mut crate::leanh::LeanObject,
    mut v_h__1_441_: *mut crate::leanh::LeanObject,
    mut v_h__2_442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_444_: u8 = 0;
    v_zero_443_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_444_ = lean_nat_dec_eq(v_x_439_, v_zero_443_);
    if v_isZero_444_ == 1 {
        let mut v___x_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_442_);
        v___x_445_ = crate::leanh::lean_apply_1(v_h__1_441_, crate::leanh::lean_box(0));
        return v___x_445_;
    } else {
        let mut v_one_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_441_);
        v_one_446_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_447_ = lean_nat_sub(v_x_439_, v_one_446_);
        v___x_448_ = crate::leanh::lean_apply_2(v_h__2_442_, v_n_447_, crate::leanh::lean_box(0));
        return v___x_448_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___boxed(
    mut v_00_u03b1_449_: *mut crate::leanh::LeanObject,
    mut v_xs_450_: *mut crate::leanh::LeanObject,
    mut v_motive_451_: *mut crate::leanh::LeanObject,
    mut v_x_452_: *mut crate::leanh::LeanObject,
    mut v_x_453_: *mut crate::leanh::LeanObject,
    mut v_h__1_454_: *mut crate::leanh::LeanObject,
    mut v_h__2_455_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_456_ = l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter(
        v_00_u03b1_449_,
        v_xs_450_,
        v_motive_451_,
        v_x_452_,
        v_x_453_,
        v_h__1_454_,
        v_h__2_455_,
    );
    crate::leanh::lean_dec(v_x_452_);
    crate::leanh::lean_dec_ref(v_xs_450_);
    return v_res_456_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter___redArg(
    mut v_r_457_: *mut crate::leanh::LeanObject,
    mut v_h__1_458_: *mut crate::leanh::LeanObject,
    mut v_h__2_459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_457_) == 0 {
        let mut v___x_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_458_);
        v___x_460_ = crate::leanh::lean_box(0);
        v___x_461_ = crate::leanh::lean_apply_1(v_h__2_459_, v___x_460_);
        return v___x_461_;
    } else {
        let mut v_val_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_459_);
        v_val_462_ = crate::leanh::lean_ctor_get(v_r_457_, 0);
        crate::leanh::lean_inc(v_val_462_);
        crate::leanh::lean_dec_ref_known(v_r_457_, 1);
        v___x_463_ = crate::leanh::lean_apply_1(v_h__1_458_, v_val_462_);
        return v___x_463_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter(
    mut v_00_u03b2_464_: *mut crate::leanh::LeanObject,
    mut v_motive_465_: *mut crate::leanh::LeanObject,
    mut v_r_466_: *mut crate::leanh::LeanObject,
    mut v_h__1_467_: *mut crate::leanh::LeanObject,
    mut v_h__2_468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_466_) == 0 {
        let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_467_);
        v___x_469_ = crate::leanh::lean_box(0);
        v___x_470_ = crate::leanh::lean_apply_1(v_h__2_468_, v___x_469_);
        return v___x_470_;
    } else {
        let mut v_val_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_468_);
        v_val_471_ = crate::leanh::lean_ctor_get(v_r_466_, 0);
        crate::leanh::lean_inc(v_val_471_);
        crate::leanh::lean_dec_ref_known(v_r_466_, 1);
        v___x_472_ = crate::leanh::lean_apply_1(v_h__1_467_, v_val_471_);
        return v___x_472_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_findM_x3f_match__1_splitter___redArg(
    mut v_x_473_: *mut crate::leanh::LeanObject,
    mut v_h__1_474_: *mut crate::leanh::LeanObject,
    mut v_h__2_475_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_473_) == 0 {
        let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_475_);
        v___x_476_ = crate::leanh::lean_box(0);
        v___x_477_ = crate::leanh::lean_apply_1(v_h__1_474_, v___x_476_);
        return v___x_477_;
    } else {
        let mut v_head_478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_474_);
        v_head_478_ = crate::leanh::lean_ctor_get(v_x_473_, 0);
        crate::leanh::lean_inc(v_head_478_);
        v_tail_479_ = crate::leanh::lean_ctor_get(v_x_473_, 1);
        crate::leanh::lean_inc(v_tail_479_);
        crate::leanh::lean_dec_ref_known(v_x_473_, 2);
        v___x_480_ = crate::leanh::lean_apply_2(v_h__2_475_, v_head_478_, v_tail_479_);
        return v___x_480_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_findM_x3f_match__1_splitter(
    mut v_00_u03b1_481_: *mut crate::leanh::LeanObject,
    mut v_motive_482_: *mut crate::leanh::LeanObject,
    mut v_x_483_: *mut crate::leanh::LeanObject,
    mut v_h__1_484_: *mut crate::leanh::LeanObject,
    mut v_h__2_485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_483_) == 0 {
        let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_485_);
        v___x_486_ = crate::leanh::lean_box(0);
        v___x_487_ = crate::leanh::lean_apply_1(v_h__1_484_, v___x_486_);
        return v___x_487_;
    } else {
        let mut v_head_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_484_);
        v_head_488_ = crate::leanh::lean_ctor_get(v_x_483_, 0);
        crate::leanh::lean_inc(v_head_488_);
        v_tail_489_ = crate::leanh::lean_ctor_get(v_x_483_, 1);
        crate::leanh::lean_inc(v_tail_489_);
        crate::leanh::lean_dec_ref_known(v_x_483_, 2);
        v___x_490_ = crate::leanh::lean_apply_2(v_h__2_485_, v_head_488_, v_tail_489_);
        return v___x_490_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(
    mut v_____do__lift_491_: u8,
    mut v_h__1_492_: *mut crate::leanh::LeanObject,
    mut v_h__2_493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_491_ == 0 {
        let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_492_);
        v___x_494_ = crate::leanh::lean_box(0);
        v___x_495_ = crate::leanh::lean_apply_1(v_h__2_493_, v___x_494_);
        return v___x_495_;
    } else {
        let mut v___x_496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_493_);
        v___x_496_ = crate::leanh::lean_box(0);
        v___x_497_ = crate::leanh::lean_apply_1(v_h__1_492_, v___x_496_);
        return v___x_497_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg___boxed(
    mut v_____do__lift_498_: *mut crate::leanh::LeanObject,
    mut v_h__1_499_: *mut crate::leanh::LeanObject,
    mut v_h__2_500_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_26__boxed_501_: u8 = 0;
    let mut v_res_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_26__boxed_501_ = (crate::leanh::lean_unbox(v_____do__lift_498_) as u8);
    v_res_502_ = l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(
        v_____do__lift_26__boxed_501_,
        v_h__1_499_,
        v_h__2_500_,
    );
    return v_res_502_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter(
    mut v_motive_503_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_504_: u8,
    mut v_h__1_505_: *mut crate::leanh::LeanObject,
    mut v_h__2_506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_____do__lift_504_ == 0 {
        let mut v___x_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_505_);
        v___x_507_ = crate::leanh::lean_box(0);
        v___x_508_ = crate::leanh::lean_apply_1(v_h__2_506_, v___x_507_);
        return v___x_508_;
    } else {
        let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_506_);
        v___x_509_ = crate::leanh::lean_box(0);
        v___x_510_ = crate::leanh::lean_apply_1(v_h__1_505_, v___x_509_);
        return v___x_510_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___boxed(
    mut v_motive_511_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_512_: *mut crate::leanh::LeanObject,
    mut v_h__1_513_: *mut crate::leanh::LeanObject,
    mut v_h__2_514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____do__lift_37__boxed_515_: u8 = 0;
    let mut v_res_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_37__boxed_515_ = (crate::leanh::lean_unbox(v_____do__lift_512_) as u8);
    v_res_516_ = l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter(
        v_motive_511_,
        v_____do__lift_37__boxed_515_,
        v_h__1_513_,
        v_h__2_514_,
    );
    return v_res_516_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_517_: *mut crate::leanh::LeanObject,
    mut v_h__1_518_: *mut crate::leanh::LeanObject,
    mut v_h__2_519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_517_) == 0 {
        let mut v___x_520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_519_);
        v___x_520_ = crate::leanh::lean_box(0);
        v___x_521_ = crate::leanh::lean_apply_1(v_h__1_518_, v___x_520_);
        return v___x_521_;
    } else {
        let mut v_head_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_518_);
        v_head_522_ = crate::leanh::lean_ctor_get(v_x_517_, 0);
        crate::leanh::lean_inc(v_head_522_);
        v_tail_523_ = crate::leanh::lean_ctor_get(v_x_517_, 1);
        crate::leanh::lean_inc(v_tail_523_);
        crate::leanh::lean_dec_ref_known(v_x_517_, 2);
        v___x_524_ = crate::leanh::lean_apply_2(v_h__2_519_, v_head_522_, v_tail_523_);
        return v___x_524_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_525_: *mut crate::leanh::LeanObject,
    mut v_motive_526_: *mut crate::leanh::LeanObject,
    mut v_x_527_: *mut crate::leanh::LeanObject,
    mut v_h__1_528_: *mut crate::leanh::LeanObject,
    mut v_h__2_529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_527_) == 0 {
        let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_529_);
        v___x_530_ = crate::leanh::lean_box(0);
        v___x_531_ = crate::leanh::lean_apply_1(v_h__1_528_, v___x_530_);
        return v___x_531_;
    } else {
        let mut v_head_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_528_);
        v_head_532_ = crate::leanh::lean_ctor_get(v_x_527_, 0);
        crate::leanh::lean_inc(v_head_532_);
        v_tail_533_ = crate::leanh::lean_ctor_get(v_x_527_, 1);
        crate::leanh::lean_inc(v_tail_533_);
        crate::leanh::lean_dec_ref_known(v_x_527_, 2);
        v___x_534_ = crate::leanh::lean_apply_2(v_h__2_529_, v_head_532_, v_tail_533_);
        return v___x_534_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(
    mut v_x_535_: u8,
    mut v_h__1_536_: *mut crate::leanh::LeanObject,
    mut v_h__2_537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_535_ == 0 {
        let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_536_);
        v___x_538_ = crate::leanh::lean_box(0);
        v___x_539_ = crate::leanh::lean_apply_1(v_h__2_537_, v___x_538_);
        return v___x_539_;
    } else {
        let mut v___x_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_537_);
        v___x_540_ = crate::leanh::lean_box(0);
        v___x_541_ = crate::leanh::lean_apply_1(v_h__1_536_, v___x_540_);
        return v___x_541_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_542_: *mut crate::leanh::LeanObject,
    mut v_h__1_543_: *mut crate::leanh::LeanObject,
    mut v_h__2_544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26__boxed_545_: u8 = 0;
    let mut v_res_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_545_ = (crate::leanh::lean_unbox(v_x_542_) as u8);
    v_res_546_ = l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(
        v_x_26__boxed_545_,
        v_h__1_543_,
        v_h__2_544_,
    );
    return v_res_546_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter(
    mut v_motive_547_: *mut crate::leanh::LeanObject,
    mut v_x_548_: u8,
    mut v_h__1_549_: *mut crate::leanh::LeanObject,
    mut v_h__2_550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_548_ == 0 {
        let mut v___x_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_549_);
        v___x_551_ = crate::leanh::lean_box(0);
        v___x_552_ = crate::leanh::lean_apply_1(v_h__2_550_, v___x_551_);
        return v___x_552_;
    } else {
        let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_550_);
        v___x_553_ = crate::leanh::lean_box(0);
        v___x_554_ = crate::leanh::lean_apply_1(v_h__1_549_, v___x_553_);
        return v___x_554_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___boxed(
    mut v_motive_555_: *mut crate::leanh::LeanObject,
    mut v_x_556_: *mut crate::leanh::LeanObject,
    mut v_h__1_557_: *mut crate::leanh::LeanObject,
    mut v_h__2_558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_37__boxed_559_: u8 = 0;
    let mut v_res_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_559_ = (crate::leanh::lean_unbox(v_x_556_) as u8);
    v_res_560_ = l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter(
        v_motive_555_,
        v_x_37__boxed_559_,
        v_h__1_557_,
        v_h__2_558_,
    );
    return v_res_560_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___redArg(
    mut v_x_561_: *mut crate::leanh::LeanObject,
    mut v_h__1_562_: *mut crate::leanh::LeanObject,
    mut v_h__2_563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_561_) == 0 {
        let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_563_);
        v___x_564_ = crate::leanh::lean_box(0);
        v___x_565_ = crate::leanh::lean_apply_1(v_h__1_562_, v___x_564_);
        return v___x_565_;
    } else {
        let mut v_val_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_562_);
        v_val_566_ = crate::leanh::lean_ctor_get(v_x_561_, 0);
        crate::leanh::lean_inc(v_val_566_);
        crate::leanh::lean_dec_ref_known(v_x_561_, 1);
        v___x_567_ = crate::leanh::lean_apply_1(v_h__2_563_, v_val_566_);
        return v___x_567_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter(
    mut v_00_u03b1_568_: *mut crate::leanh::LeanObject,
    mut v_as_569_: *mut crate::leanh::LeanObject,
    mut v_motive_570_: *mut crate::leanh::LeanObject,
    mut v_x_571_: *mut crate::leanh::LeanObject,
    mut v_h__1_572_: *mut crate::leanh::LeanObject,
    mut v_h__2_573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_571_) == 0 {
        let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_573_);
        v___x_574_ = crate::leanh::lean_box(0);
        v___x_575_ = crate::leanh::lean_apply_1(v_h__1_572_, v___x_574_);
        return v___x_575_;
    } else {
        let mut v_val_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_572_);
        v_val_576_ = crate::leanh::lean_ctor_get(v_x_571_, 0);
        crate::leanh::lean_inc(v_val_576_);
        crate::leanh::lean_dec_ref_known(v_x_571_, 1);
        v___x_577_ = crate::leanh::lean_apply_1(v_h__2_573_, v_val_576_);
        return v___x_577_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___boxed(
    mut v_00_u03b1_578_: *mut crate::leanh::LeanObject,
    mut v_as_579_: *mut crate::leanh::LeanObject,
    mut v_motive_580_: *mut crate::leanh::LeanObject,
    mut v_x_581_: *mut crate::leanh::LeanObject,
    mut v_h__1_582_: *mut crate::leanh::LeanObject,
    mut v_h__2_583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_584_ = l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter(
        v_00_u03b1_578_,
        v_as_579_,
        v_motive_580_,
        v_x_581_,
        v_h__1_582_,
        v_h__2_583_,
    );
    crate::leanh::lean_dec_ref(v_as_579_);
    return v_res_584_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_ToArray(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Set(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Erase(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Find(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Erase(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_InsertIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_TacticsExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_ToArray(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_ToArray(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Control(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Monadic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Set(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Erase(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Find(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_Erase(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_InsertIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Zip(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_TacticsExtra(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_ToArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_ToArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_ToArray(builtin);
}

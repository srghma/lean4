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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___redArg(
    mut v_i_293_: *mut LeanObject,
    mut v_h__1_294_: *mut LeanObject,
    mut v_h__2_295_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_297_: u8 = 0;
    v_zero_296_ = lean_unsigned_to_nat(0);
    v_isZero_297_ = lean_nat_dec_eq(v_i_293_, v_zero_296_);
    if v_isZero_297_ == 1 {
        let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_295_);
        v___x_298_ = lean_apply_1(v_h__1_294_, lean_box(0));
        return v___x_298_;
    } else {
        let mut v_one_299_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_300_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_294_);
        v_one_299_ = lean_unsigned_to_nat(1);
        v_n_300_ = lean_nat_sub(v_i_293_, v_one_299_);
        v___x_301_ = lean_apply_2(v_h__2_295_, v_n_300_, lean_box(0));
        return v___x_301_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___redArg___boxed(
    mut v_i_302_: *mut LeanObject,
    mut v_h__1_303_: *mut LeanObject,
    mut v_h__2_304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_305_: *mut LeanObject = core::ptr::null_mut();
    v_res_305_ =
        l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___redArg(
            v_i_302_,
            v_h__1_303_,
            v_h__2_304_,
        );
    lean_dec(v_i_302_);
    return v_res_305_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter(
    mut v_00_u03b1_306_: *mut LeanObject,
    mut v_as_307_: *mut LeanObject,
    mut v_motive_308_: *mut LeanObject,
    mut v_i_309_: *mut LeanObject,
    mut v_h_310_: *mut LeanObject,
    mut v_h__1_311_: *mut LeanObject,
    mut v_h__2_312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_314_: u8 = 0;
    v_zero_313_ = lean_unsigned_to_nat(0);
    v_isZero_314_ = lean_nat_dec_eq(v_i_309_, v_zero_313_);
    if v_isZero_314_ == 1 {
        let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_312_);
        v___x_315_ = lean_apply_1(v_h__1_311_, lean_box(0));
        return v___x_315_;
    } else {
        let mut v_one_316_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_317_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_311_);
        v_one_316_ = lean_unsigned_to_nat(1);
        v_n_317_ = lean_nat_sub(v_i_309_, v_one_316_);
        v___x_318_ = lean_apply_2(v_h__2_312_, v_n_317_, lean_box(0));
        return v___x_318_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter___boxed(
    mut v_00_u03b1_319_: *mut LeanObject,
    mut v_as_320_: *mut LeanObject,
    mut v_motive_321_: *mut LeanObject,
    mut v_i_322_: *mut LeanObject,
    mut v_h_323_: *mut LeanObject,
    mut v_h__1_324_: *mut LeanObject,
    mut v_h__2_325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_326_: *mut LeanObject = core::ptr::null_mut();
    v_res_326_ = l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__3_splitter(
        v_00_u03b1_319_,
        v_as_320_,
        v_motive_321_,
        v_i_322_,
        v_h_323_,
        v_h__1_324_,
        v_h__2_325_,
    );
    lean_dec(v_i_322_);
    lean_dec_ref(v_as_320_);
    return v_res_326_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__1_splitter___redArg(
    mut v_____do__lift_327_: *mut LeanObject,
    mut v_h__1_328_: *mut LeanObject,
    mut v_h__2_329_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_327_) == 0 {
        let mut v_a_330_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_329_);
        v_a_330_ = lean_ctor_get(v_____do__lift_327_, 0);
        lean_inc(v_a_330_);
        lean_dec_ref_known(v_____do__lift_327_, 1);
        v___x_331_ = lean_apply_1(v_h__1_328_, v_a_330_);
        return v___x_331_;
    } else {
        let mut v_a_332_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_328_);
        v_a_332_ = lean_ctor_get(v_____do__lift_327_, 0);
        lean_inc(v_a_332_);
        lean_dec_ref_known(v_____do__lift_327_, 1);
        v___x_333_ = lean_apply_1(v_h__2_329_, v_a_332_);
        return v___x_333_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_forIn_x27_loop_match__1_splitter(
    mut v_00_u03b2_334_: *mut LeanObject,
    mut v_motive_335_: *mut LeanObject,
    mut v_____do__lift_336_: *mut LeanObject,
    mut v_h__1_337_: *mut LeanObject,
    mut v_h__2_338_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_336_) == 0 {
        let mut v_a_339_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_338_);
        v_a_339_ = lean_ctor_get(v_____do__lift_336_, 0);
        lean_inc(v_a_339_);
        lean_dec_ref_known(v_____do__lift_336_, 1);
        v___x_340_ = lean_apply_1(v_h__1_337_, v_a_339_);
        return v___x_340_;
    } else {
        let mut v_a_341_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_337_);
        v_a_341_ = lean_ctor_get(v_____do__lift_336_, 0);
        lean_inc(v_a_341_);
        lean_dec_ref_known(v_____do__lift_336_, 1);
        v___x_342_ = lean_apply_1(v_h__2_338_, v_a_341_);
        return v___x_342_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_forIn_x27__cons_match__1_splitter___redArg(
    mut v_x_343_: *mut LeanObject,
    mut v_h__1_344_: *mut LeanObject,
    mut v_h__2_345_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_343_) == 0 {
        let mut v_a_346_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_345_);
        v_a_346_ = lean_ctor_get(v_x_343_, 0);
        lean_inc(v_a_346_);
        lean_dec_ref_known(v_x_343_, 1);
        v___x_347_ = lean_apply_1(v_h__1_344_, v_a_346_);
        return v___x_347_;
    } else {
        let mut v_a_348_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_344_);
        v_a_348_ = lean_ctor_get(v_x_343_, 0);
        lean_inc(v_a_348_);
        lean_dec_ref_known(v_x_343_, 1);
        v___x_349_ = lean_apply_1(v_h__2_345_, v_a_348_);
        return v___x_349_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_forIn_x27__cons_match__1_splitter(
    mut v_00_u03b2_350_: *mut LeanObject,
    mut v_motive_351_: *mut LeanObject,
    mut v_x_352_: *mut LeanObject,
    mut v_h__1_353_: *mut LeanObject,
    mut v_h__2_354_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_352_) == 0 {
        let mut v_a_355_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_354_);
        v_a_355_ = lean_ctor_get(v_x_352_, 0);
        lean_inc(v_a_355_);
        lean_dec_ref_known(v_x_352_, 1);
        v___x_356_ = lean_apply_1(v_h__1_353_, v_a_355_);
        return v___x_356_;
    } else {
        let mut v_a_357_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_353_);
        v_a_357_ = lean_ctor_get(v_x_352_, 0);
        lean_inc(v_a_357_);
        lean_dec_ref_known(v_x_352_, 1);
        v___x_358_ = lean_apply_1(v_h__2_354_, v_a_357_);
        return v___x_358_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__1_splitter___redArg(
    mut v_____do__lift_359_: *mut LeanObject,
    mut v_h__1_360_: *mut LeanObject,
    mut v_h__2_361_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_359_) == 1 {
        let mut v_val_362_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_361_);
        v_val_362_ = lean_ctor_get(v_____do__lift_359_, 0);
        lean_inc(v_val_362_);
        lean_dec_ref_known(v_____do__lift_359_, 1);
        v___x_363_ = lean_apply_1(v_h__1_360_, v_val_362_);
        return v___x_363_;
    } else {
        let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_360_);
        v___x_364_ = lean_apply_2(v_h__2_361_, v_____do__lift_359_, lean_box(0));
        return v___x_364_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_findSomeM_x3f_match__1_splitter(
    mut v_00_u03b2_365_: *mut LeanObject,
    mut v_motive_366_: *mut LeanObject,
    mut v_____do__lift_367_: *mut LeanObject,
    mut v_h__1_368_: *mut LeanObject,
    mut v_h__2_369_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_367_) == 1 {
        let mut v_val_370_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_371_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_369_);
        v_val_370_ = lean_ctor_get(v_____do__lift_367_, 0);
        lean_inc(v_val_370_);
        lean_dec_ref_known(v_____do__lift_367_, 1);
        v___x_371_ = lean_apply_1(v_h__1_368_, v_val_370_);
        return v___x_371_;
    } else {
        let mut v___x_372_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_368_);
        v___x_372_ = lean_apply_2(v_h__2_369_, v_____do__lift_367_, lean_box(0));
        return v___x_372_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Break_runK_match__1_splitter___redArg(
    mut v_x_373_: *mut LeanObject,
    mut v_h__1_374_: *mut LeanObject,
    mut v_h__2_375_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_373_) == 0 {
        let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_374_);
        v___x_376_ = lean_box(0);
        v___x_377_ = lean_apply_1(v_h__2_375_, v___x_376_);
        return v___x_377_;
    } else {
        let mut v_val_378_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_375_);
        v_val_378_ = lean_ctor_get(v_x_373_, 0);
        lean_inc(v_val_378_);
        lean_dec_ref_known(v_x_373_, 1);
        v___x_379_ = lean_apply_1(v_h__1_374_, v_val_378_);
        return v___x_379_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Break_runK_match__1_splitter(
    mut v_00_u03b1_380_: *mut LeanObject,
    mut v_motive_381_: *mut LeanObject,
    mut v_x_382_: *mut LeanObject,
    mut v_h__1_383_: *mut LeanObject,
    mut v_h__2_384_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_382_) == 0 {
        let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_386_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_383_);
        v___x_385_ = lean_box(0);
        v___x_386_ = lean_apply_1(v_h__2_384_, v___x_385_);
        return v___x_386_;
    } else {
        let mut v_val_387_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_384_);
        v_val_387_ = lean_ctor_get(v_x_382_, 0);
        lean_inc(v_val_387_);
        lean_dec_ref_known(v_x_382_, 1);
        v___x_388_ = lean_apply_1(v_h__1_383_, v_val_387_);
        return v___x_388_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_mapA_match__1_splitter___redArg(
    mut v_x_389_: *mut LeanObject,
    mut v_h__1_390_: *mut LeanObject,
    mut v_h__2_391_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_389_) == 0 {
        let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_391_);
        v___x_392_ = lean_box(0);
        v___x_393_ = lean_apply_1(v_h__1_390_, v___x_392_);
        return v___x_393_;
    } else {
        let mut v_head_394_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_395_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_390_);
        v_head_394_ = lean_ctor_get(v_x_389_, 0);
        lean_inc(v_head_394_);
        v_tail_395_ = lean_ctor_get(v_x_389_, 1);
        lean_inc(v_tail_395_);
        lean_dec_ref_known(v_x_389_, 2);
        v___x_396_ = lean_apply_2(v_h__2_391_, v_head_394_, v_tail_395_);
        return v___x_396_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_mapA_match__1_splitter(
    mut v_00_u03b1_397_: *mut LeanObject,
    mut v_motive_398_: *mut LeanObject,
    mut v_x_399_: *mut LeanObject,
    mut v_h__1_400_: *mut LeanObject,
    mut v_h__2_401_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_399_) == 0 {
        let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_401_);
        v___x_402_ = lean_box(0);
        v___x_403_ = lean_apply_1(v_h__1_400_, v___x_402_);
        return v___x_403_;
    } else {
        let mut v_head_404_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_405_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_400_);
        v_head_404_ = lean_ctor_get(v_x_399_, 0);
        lean_inc(v_head_404_);
        v_tail_405_ = lean_ctor_get(v_x_399_, 1);
        lean_inc(v_tail_405_);
        lean_dec_ref_known(v_x_399_, 2);
        v___x_406_ = lean_apply_2(v_h__2_401_, v_head_404_, v_tail_405_);
        return v___x_406_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_findSomeM_x3f_match__1_splitter___redArg(
    mut v_____do__lift_407_: *mut LeanObject,
    mut v_h__1_408_: *mut LeanObject,
    mut v_h__2_409_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_407_) == 0 {
        let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_408_);
        v___x_410_ = lean_box(0);
        v___x_411_ = lean_apply_1(v_h__2_409_, v___x_410_);
        return v___x_411_;
    } else {
        let mut v_val_412_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_409_);
        v_val_412_ = lean_ctor_get(v_____do__lift_407_, 0);
        lean_inc(v_val_412_);
        lean_dec_ref_known(v_____do__lift_407_, 1);
        v___x_413_ = lean_apply_1(v_h__1_408_, v_val_412_);
        return v___x_413_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_findSomeM_x3f_match__1_splitter(
    mut v_00_u03b2_414_: *mut LeanObject,
    mut v_motive_415_: *mut LeanObject,
    mut v_____do__lift_416_: *mut LeanObject,
    mut v_h__1_417_: *mut LeanObject,
    mut v_h__2_418_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_416_) == 0 {
        let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_417_);
        v___x_419_ = lean_box(0);
        v___x_420_ = lean_apply_1(v_h__2_418_, v___x_419_);
        return v___x_420_;
    } else {
        let mut v_val_421_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_418_);
        v_val_421_ = lean_ctor_get(v_____do__lift_416_, 0);
        lean_inc(v_val_421_);
        lean_dec_ref_known(v_____do__lift_416_, 1);
        v___x_422_ = lean_apply_1(v_h__1_417_, v_val_421_);
        return v___x_422_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg(
    mut v_x_423_: *mut LeanObject,
    mut v_h__1_424_: *mut LeanObject,
    mut v_h__2_425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_427_: u8 = 0;
    v_zero_426_ = lean_unsigned_to_nat(0);
    v_isZero_427_ = lean_nat_dec_eq(v_x_423_, v_zero_426_);
    if v_isZero_427_ == 1 {
        let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_425_);
        v___x_428_ = lean_apply_1(v_h__1_424_, lean_box(0));
        return v___x_428_;
    } else {
        let mut v_one_429_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_430_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_424_);
        v_one_429_ = lean_unsigned_to_nat(1);
        v_n_430_ = lean_nat_sub(v_x_423_, v_one_429_);
        v___x_431_ = lean_apply_2(v_h__2_425_, v_n_430_, lean_box(0));
        return v___x_431_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg___boxed(
    mut v_x_432_: *mut LeanObject,
    mut v_h__1_433_: *mut LeanObject,
    mut v_h__2_434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_435_: *mut LeanObject = core::ptr::null_mut();
    v_res_435_ = l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___redArg(
        v_x_432_,
        v_h__1_433_,
        v_h__2_434_,
    );
    lean_dec(v_x_432_);
    return v_res_435_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter(
    mut v_00_u03b1_436_: *mut LeanObject,
    mut v_xs_437_: *mut LeanObject,
    mut v_motive_438_: *mut LeanObject,
    mut v_x_439_: *mut LeanObject,
    mut v_x_440_: *mut LeanObject,
    mut v_h__1_441_: *mut LeanObject,
    mut v_h__2_442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_444_: u8 = 0;
    v_zero_443_ = lean_unsigned_to_nat(0);
    v_isZero_444_ = lean_nat_dec_eq(v_x_439_, v_zero_443_);
    if v_isZero_444_ == 1 {
        let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_442_);
        v___x_445_ = lean_apply_1(v_h__1_441_, lean_box(0));
        return v___x_445_;
    } else {
        let mut v_one_446_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_447_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_448_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_441_);
        v_one_446_ = lean_unsigned_to_nat(1);
        v_n_447_ = lean_nat_sub(v_x_439_, v_one_446_);
        v___x_448_ = lean_apply_2(v_h__2_442_, v_n_447_, lean_box(0));
        return v___x_448_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter___boxed(
    mut v_00_u03b1_449_: *mut LeanObject,
    mut v_xs_450_: *mut LeanObject,
    mut v_motive_451_: *mut LeanObject,
    mut v_x_452_: *mut LeanObject,
    mut v_x_453_: *mut LeanObject,
    mut v_h__1_454_: *mut LeanObject,
    mut v_h__2_455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_456_: *mut LeanObject = core::ptr::null_mut();
    v_res_456_ = l___private_Init_Data_List_ToArray_0__Array_isEqvAux_match__1_splitter(
        v_00_u03b1_449_,
        v_xs_450_,
        v_motive_451_,
        v_x_452_,
        v_x_453_,
        v_h__1_454_,
        v_h__2_455_,
    );
    lean_dec(v_x_452_);
    lean_dec_ref(v_xs_450_);
    return v_res_456_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter___redArg(
    mut v_r_457_: *mut LeanObject,
    mut v_h__1_458_: *mut LeanObject,
    mut v_h__2_459_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_457_) == 0 {
        let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_458_);
        v___x_460_ = lean_box(0);
        v___x_461_ = lean_apply_1(v_h__2_459_, v___x_460_);
        return v___x_461_;
    } else {
        let mut v_val_462_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_459_);
        v_val_462_ = lean_ctor_get(v_r_457_, 0);
        lean_inc(v_val_462_);
        lean_dec_ref_known(v_r_457_, 1);
        v___x_463_ = lean_apply_1(v_h__1_458_, v_val_462_);
        return v___x_463_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_findSomeRevM_x3f_find_match__1_splitter(
    mut v_00_u03b2_464_: *mut LeanObject,
    mut v_motive_465_: *mut LeanObject,
    mut v_r_466_: *mut LeanObject,
    mut v_h__1_467_: *mut LeanObject,
    mut v_h__2_468_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_466_) == 0 {
        let mut v___x_469_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_467_);
        v___x_469_ = lean_box(0);
        v___x_470_ = lean_apply_1(v_h__2_468_, v___x_469_);
        return v___x_470_;
    } else {
        let mut v_val_471_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_468_);
        v_val_471_ = lean_ctor_get(v_r_466_, 0);
        lean_inc(v_val_471_);
        lean_dec_ref_known(v_r_466_, 1);
        v___x_472_ = lean_apply_1(v_h__1_467_, v_val_471_);
        return v___x_472_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_findM_x3f_match__1_splitter___redArg(
    mut v_x_473_: *mut LeanObject,
    mut v_h__1_474_: *mut LeanObject,
    mut v_h__2_475_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_473_) == 0 {
        let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_475_);
        v___x_476_ = lean_box(0);
        v___x_477_ = lean_apply_1(v_h__1_474_, v___x_476_);
        return v___x_477_;
    } else {
        let mut v_head_478_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_479_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_474_);
        v_head_478_ = lean_ctor_get(v_x_473_, 0);
        lean_inc(v_head_478_);
        v_tail_479_ = lean_ctor_get(v_x_473_, 1);
        lean_inc(v_tail_479_);
        lean_dec_ref_known(v_x_473_, 2);
        v___x_480_ = lean_apply_2(v_h__2_475_, v_head_478_, v_tail_479_);
        return v___x_480_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_findM_x3f_match__1_splitter(
    mut v_00_u03b1_481_: *mut LeanObject,
    mut v_motive_482_: *mut LeanObject,
    mut v_x_483_: *mut LeanObject,
    mut v_h__1_484_: *mut LeanObject,
    mut v_h__2_485_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_483_) == 0 {
        let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_485_);
        v___x_486_ = lean_box(0);
        v___x_487_ = lean_apply_1(v_h__1_484_, v___x_486_);
        return v___x_487_;
    } else {
        let mut v_head_488_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_489_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_484_);
        v_head_488_ = lean_ctor_get(v_x_483_, 0);
        lean_inc(v_head_488_);
        v_tail_489_ = lean_ctor_get(v_x_483_, 1);
        lean_inc(v_tail_489_);
        lean_dec_ref_known(v_x_483_, 2);
        v___x_490_ = lean_apply_2(v_h__2_485_, v_head_488_, v_tail_489_);
        return v___x_490_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(
    mut v_____do__lift_491_: u8,
    mut v_h__1_492_: *mut LeanObject,
    mut v_h__2_493_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_491_ == 0 {
        let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_492_);
        v___x_494_ = lean_box(0);
        v___x_495_ = lean_apply_1(v_h__2_493_, v___x_494_);
        return v___x_495_;
    } else {
        let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_493_);
        v___x_496_ = lean_box(0);
        v___x_497_ = lean_apply_1(v_h__1_492_, v___x_496_);
        return v___x_497_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg___boxed(
    mut v_____do__lift_498_: *mut LeanObject,
    mut v_h__1_499_: *mut LeanObject,
    mut v_h__2_500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_26__boxed_501_: u8 = 0;
    let mut v_res_502_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_26__boxed_501_ = (lean_unbox(v_____do__lift_498_) as u8);
    v_res_502_ = l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___redArg(
        v_____do__lift_26__boxed_501_,
        v_h__1_499_,
        v_h__2_500_,
    );
    return v_res_502_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter(
    mut v_motive_503_: *mut LeanObject,
    mut v_____do__lift_504_: u8,
    mut v_h__1_505_: *mut LeanObject,
    mut v_h__2_506_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_504_ == 0 {
        let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_505_);
        v___x_507_ = lean_box(0);
        v___x_508_ = lean_apply_1(v_h__2_506_, v___x_507_);
        return v___x_508_;
    } else {
        let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_506_);
        v___x_509_ = lean_box(0);
        v___x_510_ = lean_apply_1(v_h__1_505_, v___x_509_);
        return v___x_510_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter___boxed(
    mut v_motive_511_: *mut LeanObject,
    mut v_____do__lift_512_: *mut LeanObject,
    mut v_h__1_513_: *mut LeanObject,
    mut v_h__2_514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_37__boxed_515_: u8 = 0;
    let mut v_res_516_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_37__boxed_515_ = (lean_unbox(v_____do__lift_512_) as u8);
    v_res_516_ = l___private_Init_Data_List_ToArray_0__List_anyM_match__1_splitter(
        v_motive_511_,
        v_____do__lift_37__boxed_515_,
        v_h__1_513_,
        v_h__2_514_,
    );
    return v_res_516_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_getLast_x3f_match__1_splitter___redArg(
    mut v_x_517_: *mut LeanObject,
    mut v_h__1_518_: *mut LeanObject,
    mut v_h__2_519_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_517_) == 0 {
        let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_519_);
        v___x_520_ = lean_box(0);
        v___x_521_ = lean_apply_1(v_h__1_518_, v___x_520_);
        return v___x_521_;
    } else {
        let mut v_head_522_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_523_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_518_);
        v_head_522_ = lean_ctor_get(v_x_517_, 0);
        lean_inc(v_head_522_);
        v_tail_523_ = lean_ctor_get(v_x_517_, 1);
        lean_inc(v_tail_523_);
        lean_dec_ref_known(v_x_517_, 2);
        v___x_524_ = lean_apply_2(v_h__2_519_, v_head_522_, v_tail_523_);
        return v___x_524_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_getLast_x3f_match__1_splitter(
    mut v_00_u03b1_525_: *mut LeanObject,
    mut v_motive_526_: *mut LeanObject,
    mut v_x_527_: *mut LeanObject,
    mut v_h__1_528_: *mut LeanObject,
    mut v_h__2_529_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_527_) == 0 {
        let mut v___x_530_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_529_);
        v___x_530_ = lean_box(0);
        v___x_531_ = lean_apply_1(v_h__1_528_, v___x_530_);
        return v___x_531_;
    } else {
        let mut v_head_532_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_533_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_528_);
        v_head_532_ = lean_ctor_get(v_x_527_, 0);
        lean_inc(v_head_532_);
        v_tail_533_ = lean_ctor_get(v_x_527_, 1);
        lean_inc(v_tail_533_);
        lean_dec_ref_known(v_x_527_, 2);
        v___x_534_ = lean_apply_2(v_h__2_529_, v_head_532_, v_tail_533_);
        return v___x_534_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(
    mut v_x_535_: u8,
    mut v_h__1_536_: *mut LeanObject,
    mut v_h__2_537_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_535_ == 0 {
        let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_536_);
        v___x_538_ = lean_box(0);
        v___x_539_ = lean_apply_1(v_h__2_537_, v___x_538_);
        return v___x_539_;
    } else {
        let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_537_);
        v___x_540_ = lean_box(0);
        v___x_541_ = lean_apply_1(v_h__1_536_, v___x_540_);
        return v___x_541_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg___boxed(
    mut v_x_542_: *mut LeanObject,
    mut v_h__1_543_: *mut LeanObject,
    mut v_h__2_544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_26__boxed_545_: u8 = 0;
    let mut v_res_546_: *mut LeanObject = core::ptr::null_mut();
    v_x_26__boxed_545_ = (lean_unbox(v_x_542_) as u8);
    v_res_546_ = l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___redArg(
        v_x_26__boxed_545_,
        v_h__1_543_,
        v_h__2_544_,
    );
    return v_res_546_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter(
    mut v_motive_547_: *mut LeanObject,
    mut v_x_548_: u8,
    mut v_h__1_549_: *mut LeanObject,
    mut v_h__2_550_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_548_ == 0 {
        let mut v___x_551_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_549_);
        v___x_551_ = lean_box(0);
        v___x_552_ = lean_apply_1(v_h__2_550_, v___x_551_);
        return v___x_552_;
    } else {
        let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_550_);
        v___x_553_ = lean_box(0);
        v___x_554_ = lean_apply_1(v_h__1_549_, v___x_553_);
        return v___x_554_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter___boxed(
    mut v_motive_555_: *mut LeanObject,
    mut v_x_556_: *mut LeanObject,
    mut v_h__1_557_: *mut LeanObject,
    mut v_h__2_558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_37__boxed_559_: u8 = 0;
    let mut v_res_560_: *mut LeanObject = core::ptr::null_mut();
    v_x_37__boxed_559_ = (lean_unbox(v_x_556_) as u8);
    v_res_560_ = l___private_Init_Data_List_ToArray_0__List_filter_match__1_splitter(
        v_motive_555_,
        v_x_37__boxed_559_,
        v_h__1_557_,
        v_h__2_558_,
    );
    return v_res_560_;
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___redArg(
    mut v_x_561_: *mut LeanObject,
    mut v_h__1_562_: *mut LeanObject,
    mut v_h__2_563_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_561_) == 0 {
        let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_563_);
        v___x_564_ = lean_box(0);
        v___x_565_ = lean_apply_1(v_h__1_562_, v___x_564_);
        return v___x_565_;
    } else {
        let mut v_val_566_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_562_);
        v_val_566_ = lean_ctor_get(v_x_561_, 0);
        lean_inc(v_val_566_);
        lean_dec_ref_known(v_x_561_, 1);
        v___x_567_ = lean_apply_1(v_h__2_563_, v_val_566_);
        return v___x_567_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter(
    mut v_00_u03b1_568_: *mut LeanObject,
    mut v_as_569_: *mut LeanObject,
    mut v_motive_570_: *mut LeanObject,
    mut v_x_571_: *mut LeanObject,
    mut v_h__1_572_: *mut LeanObject,
    mut v_h__2_573_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_571_) == 0 {
        let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_573_);
        v___x_574_ = lean_box(0);
        v___x_575_ = lean_apply_1(v_h__1_572_, v___x_574_);
        return v___x_575_;
    } else {
        let mut v_val_576_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_572_);
        v_val_576_ = lean_ctor_get(v_x_571_, 0);
        lean_inc(v_val_576_);
        lean_dec_ref_known(v_x_571_, 1);
        v___x_577_ = lean_apply_1(v_h__2_573_, v_val_576_);
        return v___x_577_;
    }
}
pub unsafe fn l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter___boxed(
    mut v_00_u03b1_578_: *mut LeanObject,
    mut v_as_579_: *mut LeanObject,
    mut v_motive_580_: *mut LeanObject,
    mut v_x_581_: *mut LeanObject,
    mut v_h__1_582_: *mut LeanObject,
    mut v_h__2_583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_584_: *mut LeanObject = core::ptr::null_mut();
    v_res_584_ = l___private_Init_Data_List_ToArray_0__Array_erase_match__1_splitter(
        v_00_u03b1_578_,
        v_as_579_,
        v_motive_580_,
        v_x_581_,
        v_h__1_582_,
        v_h__2_583_,
    );
    lean_dec_ref(v_as_579_);
    return v_res_584_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_ToArray(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Set(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Erase(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Find(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Erase(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_InsertIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Sublist(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_TacticsExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_ToArray(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_ToArray(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Monadic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Set(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Erase(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Find(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_Erase(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_InsertIdx(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Sublist(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Zip(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_TacticsExtra(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_ToArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_ToArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_ToArray(builtin);
}

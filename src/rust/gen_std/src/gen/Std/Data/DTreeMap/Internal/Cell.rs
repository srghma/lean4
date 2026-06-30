// Lean compiler output
// Module: Std.Data.DTreeMap.Internal.Cell
// Imports: Std.Data.Internal.List.Associative Init.Data.List.Find
use crate::r#gen::Init::Data::List::Basic::l_List_find_x3f___redArg;
use crate::r#gen::Init::Data::List::Find::{
    initialize_Init_Data_List_Find, runtime_initialize_Init_Data_List_Find,
};
use crate::r#gen::Init::Data::Ord::Basic::l_instDecidableEqOrdering;
use crate::r#gen::Std::Data::Internal::List::Associative::{
    initialize_Std_Data_Internal_List_Associative,
    runtime_initialize_Std_Data_Internal_List_Associative,
};
pub unsafe fn l_Std_DTreeMap_Internal_Cell_ofEq___redArg(
    mut v_k_x27_281_: *mut leanh::LeanObject,
    mut v_v_x27_282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_283_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_283_, 0, v_k_x27_281_);
    leanh::lean_ctor_set(v___x_283_, 1, v_v_x27_282_);
    v___x_284_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_284_, 0, v___x_283_);
    return v___x_284_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_ofEq(
    mut v_00_u03b1_285_: *mut leanh::LeanObject,
    mut v_00_u03b2_286_: *mut leanh::LeanObject,
    mut v_inst_287_: *mut leanh::LeanObject,
    mut v_k_288_: *mut leanh::LeanObject,
    mut v_k_x27_289_: *mut leanh::LeanObject,
    mut v_v_x27_290_: *mut leanh::LeanObject,
    mut v_hcmp_291_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_292_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_x27_289_, v_v_x27_290_);
    return v___x_292_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_ofEq___boxed(
    mut v_00_u03b1_293_: *mut leanh::LeanObject,
    mut v_00_u03b2_294_: *mut leanh::LeanObject,
    mut v_inst_295_: *mut leanh::LeanObject,
    mut v_k_296_: *mut leanh::LeanObject,
    mut v_k_x27_297_: *mut leanh::LeanObject,
    mut v_v_x27_298_: *mut leanh::LeanObject,
    mut v_hcmp_299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_300_ = l_Std_DTreeMap_Internal_Cell_ofEq(
        v_00_u03b1_293_,
        v_00_u03b2_294_,
        v_inst_295_,
        v_k_296_,
        v_k_x27_297_,
        v_v_x27_298_,
        v_hcmp_299_,
    );
    leanh::lean_dec_ref(v_k_296_);
    leanh::lean_dec_ref(v_inst_295_);
    return v_res_300_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_of___redArg(
    mut v_k_301_: *mut leanh::LeanObject,
    mut v_v_302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_303_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_301_, v_v_302_);
    return v___x_303_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_of(
    mut v_00_u03b1_304_: *mut leanh::LeanObject,
    mut v_00_u03b2_305_: *mut leanh::LeanObject,
    mut v_inst_306_: *mut leanh::LeanObject,
    mut v_k_307_: *mut leanh::LeanObject,
    mut v_v_308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_309_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_307_, v_v_308_);
    return v___x_309_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_of___boxed(
    mut v_00_u03b1_310_: *mut leanh::LeanObject,
    mut v_00_u03b2_311_: *mut leanh::LeanObject,
    mut v_inst_312_: *mut leanh::LeanObject,
    mut v_k_313_: *mut leanh::LeanObject,
    mut v_v_314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_315_ = l_Std_DTreeMap_Internal_Cell_of(
        v_00_u03b1_310_,
        v_00_u03b2_311_,
        v_inst_312_,
        v_k_313_,
        v_v_314_,
    );
    leanh::lean_dec_ref(v_inst_312_);
    return v_res_315_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_empty(
    mut v_00_u03b1_316_: *mut leanh::LeanObject,
    mut v_00_u03b2_317_: *mut leanh::LeanObject,
    mut v_inst_318_: *mut leanh::LeanObject,
    mut v_k_319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_320_ = leanh::lean_box(0);
    return v___x_320_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_empty___boxed(
    mut v_00_u03b1_321_: *mut leanh::LeanObject,
    mut v_00_u03b2_322_: *mut leanh::LeanObject,
    mut v_inst_323_: *mut leanh::LeanObject,
    mut v_k_324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_325_ =
        l_Std_DTreeMap_Internal_Cell_empty(v_00_u03b1_321_, v_00_u03b2_322_, v_inst_323_, v_k_324_);
    leanh::lean_dec_ref(v_k_324_);
    leanh::lean_dec_ref(v_inst_323_);
    return v_res_325_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_ofOption___redArg(
    mut v_k_326_: *mut leanh::LeanObject,
    mut v_v_x3f_327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_v_x3f_327_) == 0 {
        let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_k_326_);
        v___x_328_ = leanh::lean_box(0);
        return v___x_328_;
    } else {
        let mut v_val_329_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_330_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_329_ = leanh::lean_ctor_get(v_v_x3f_327_, 0);
        leanh::lean_inc(v_val_329_);
        leanh::lean_dec_ref_known(v_v_x3f_327_, 1);
        v___x_330_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_326_, v_val_329_);
        return v___x_330_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_ofOption(
    mut v_00_u03b1_331_: *mut leanh::LeanObject,
    mut v_00_u03b2_332_: *mut leanh::LeanObject,
    mut v_inst_333_: *mut leanh::LeanObject,
    mut v_k_334_: *mut leanh::LeanObject,
    mut v_v_x3f_335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_336_ = l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_334_, v_v_x3f_335_);
    return v___x_336_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_ofOption___boxed(
    mut v_00_u03b1_337_: *mut leanh::LeanObject,
    mut v_00_u03b2_338_: *mut leanh::LeanObject,
    mut v_inst_339_: *mut leanh::LeanObject,
    mut v_k_340_: *mut leanh::LeanObject,
    mut v_v_x3f_341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_342_ = l_Std_DTreeMap_Internal_Cell_ofOption(
        v_00_u03b1_337_,
        v_00_u03b2_338_,
        v_inst_339_,
        v_k_340_,
        v_v_x3f_341_,
    );
    leanh::lean_dec_ref(v_inst_339_);
    return v_res_342_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_contains___redArg(
    mut v_c_343_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_c_343_) == 0 {
        let mut v___x_344_: u8 = 0;
        v___x_344_ = 0;
        return v___x_344_;
    } else {
        let mut v___x_345_: u8 = 0;
        v___x_345_ = 1;
        return v___x_345_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_contains___redArg___boxed(
    mut v_c_346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_347_: u8 = 0;
    let mut v_r_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_347_ = l_Std_DTreeMap_Internal_Cell_contains___redArg(v_c_346_);
    leanh::lean_dec(v_c_346_);
    v_r_348_ = leanh::lean_box((v_res_347_) as usize);
    return v_r_348_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_contains(
    mut v_00_u03b1_349_: *mut leanh::LeanObject,
    mut v_00_u03b2_350_: *mut leanh::LeanObject,
    mut v_inst_351_: *mut leanh::LeanObject,
    mut v_k_352_: *mut leanh::LeanObject,
    mut v_c_353_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_354_: u8 = 0;
    v___x_354_ = l_Std_DTreeMap_Internal_Cell_contains___redArg(v_c_353_);
    return v___x_354_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_contains___boxed(
    mut v_00_u03b1_355_: *mut leanh::LeanObject,
    mut v_00_u03b2_356_: *mut leanh::LeanObject,
    mut v_inst_357_: *mut leanh::LeanObject,
    mut v_k_358_: *mut leanh::LeanObject,
    mut v_c_359_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_360_: u8 = 0;
    let mut v_r_361_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_360_ = l_Std_DTreeMap_Internal_Cell_contains(
        v_00_u03b1_355_,
        v_00_u03b2_356_,
        v_inst_357_,
        v_k_358_,
        v_c_359_,
    );
    leanh::lean_dec(v_c_359_);
    leanh::lean_dec_ref(v_k_358_);
    leanh::lean_dec_ref(v_inst_357_);
    v_r_361_ = leanh::lean_box((v_res_360_) as usize);
    return v_r_361_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_get_x3f___redArg(
    mut v_c_362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_367_: u8 = 0;
    let mut v_snd_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_372_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_c_362_) == 0 {
                    v___x_363_ = leanh::lean_box(0);
                    return v___x_363_;
                } else {
                    v_val_364_ = leanh::lean_ctor_get(v_c_362_, 0);
                    v_isSharedCheck_372_ = (!leanh::lean_is_exclusive(v_c_362_)) as u8;
                    if v_isSharedCheck_372_ == 0 {
                        v___x_366_ = v_c_362_;
                        v_isShared_367_ = v_isSharedCheck_372_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_364_);
                        leanh::lean_dec(v_c_362_);
                        v___x_366_ = leanh::lean_box(0);
                        v_isShared_367_ = v_isSharedCheck_372_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_368_ = leanh::lean_ctor_get(v_val_364_, 1);
                leanh::lean_inc(v_snd_368_);
                leanh::lean_dec(v_val_364_);
                if v_isShared_367_ == 0 {
                    leanh::lean_ctor_set(v___x_366_, 0, v_snd_368_);
                    v___x_370_ = v___x_366_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_371_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_371_, 0, v_snd_368_);
                    v___x_370_ = v_reuseFailAlloc_371_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_370_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_get_x3f(
    mut v_00_u03b1_373_: *mut leanh::LeanObject,
    mut v_00_u03b2_374_: *mut leanh::LeanObject,
    mut v_inst_375_: *mut leanh::LeanObject,
    mut v_inst_376_: *mut leanh::LeanObject,
    mut v_inst_377_: *mut leanh::LeanObject,
    mut v_k_378_: *mut leanh::LeanObject,
    mut v_c_379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_380_ = l_Std_DTreeMap_Internal_Cell_get_x3f___redArg(v_c_379_);
    return v___x_380_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_get_x3f___boxed(
    mut v_00_u03b1_381_: *mut leanh::LeanObject,
    mut v_00_u03b2_382_: *mut leanh::LeanObject,
    mut v_inst_383_: *mut leanh::LeanObject,
    mut v_inst_384_: *mut leanh::LeanObject,
    mut v_inst_385_: *mut leanh::LeanObject,
    mut v_k_386_: *mut leanh::LeanObject,
    mut v_c_387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_388_ = l_Std_DTreeMap_Internal_Cell_get_x3f(
        v_00_u03b1_381_,
        v_00_u03b2_382_,
        v_inst_383_,
        v_inst_384_,
        v_inst_385_,
        v_k_386_,
        v_c_387_,
    );
    leanh::lean_dec(v_k_386_);
    leanh::lean_dec_ref(v_inst_383_);
    return v_res_388_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_getEntry_x3f___redArg(
    mut v_c_389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_394_: u8 = 0;
    let mut v_fst_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_399_: u8 = 0;
    let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_406_: u8 = 0;
    let mut v_isSharedCheck_407_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_c_389_) == 0 {
                    v___x_390_ = leanh::lean_box(0);
                    return v___x_390_;
                } else {
                    v_val_391_ = leanh::lean_ctor_get(v_c_389_, 0);
                    v_isSharedCheck_407_ = (!leanh::lean_is_exclusive(v_c_389_)) as u8;
                    if v_isSharedCheck_407_ == 0 {
                        v___x_393_ = v_c_389_;
                        v_isShared_394_ = v_isSharedCheck_407_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_391_);
                        leanh::lean_dec(v_c_389_);
                        v___x_393_ = leanh::lean_box(0);
                        v_isShared_394_ = v_isSharedCheck_407_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_395_ = leanh::lean_ctor_get(v_val_391_, 0);
                v_snd_396_ = leanh::lean_ctor_get(v_val_391_, 1);
                v_isSharedCheck_406_ = (!leanh::lean_is_exclusive(v_val_391_)) as u8;
                if v_isSharedCheck_406_ == 0 {
                    v___x_398_ = v_val_391_;
                    v_isShared_399_ = v_isSharedCheck_406_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_396_);
                    leanh::lean_inc(v_fst_395_);
                    leanh::lean_dec(v_val_391_);
                    v___x_398_ = leanh::lean_box(0);
                    v_isShared_399_ = v_isSharedCheck_406_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_399_ == 0 {
                    v___x_401_ = v___x_398_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_405_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_405_, 0, v_fst_395_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_405_, 1, v_snd_396_);
                    v___x_401_ = v_reuseFailAlloc_405_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_394_ == 0 {
                    leanh::lean_ctor_set(v___x_393_, 0, v___x_401_);
                    v___x_403_ = v___x_393_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_404_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
                    v___x_403_ = v_reuseFailAlloc_404_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_403_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_getEntry_x3f(
    mut v_00_u03b1_408_: *mut leanh::LeanObject,
    mut v_00_u03b2_409_: *mut leanh::LeanObject,
    mut v_inst_410_: *mut leanh::LeanObject,
    mut v_k_411_: *mut leanh::LeanObject,
    mut v_c_412_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_413_ = l_Std_DTreeMap_Internal_Cell_getEntry_x3f___redArg(v_c_412_);
    return v___x_413_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_getEntry_x3f___boxed(
    mut v_00_u03b1_414_: *mut leanh::LeanObject,
    mut v_00_u03b2_415_: *mut leanh::LeanObject,
    mut v_inst_416_: *mut leanh::LeanObject,
    mut v_k_417_: *mut leanh::LeanObject,
    mut v_c_418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_419_ = l_Std_DTreeMap_Internal_Cell_getEntry_x3f(
        v_00_u03b1_414_,
        v_00_u03b2_415_,
        v_inst_416_,
        v_k_417_,
        v_c_418_,
    );
    leanh::lean_dec(v_k_417_);
    leanh::lean_dec_ref(v_inst_416_);
    return v_res_419_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(
    mut v_c_420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_425_: u8 = 0;
    let mut v_fst_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_430_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_c_420_) == 0 {
                    v___x_421_ = leanh::lean_box(0);
                    return v___x_421_;
                } else {
                    v_val_422_ = leanh::lean_ctor_get(v_c_420_, 0);
                    v_isSharedCheck_430_ = (!leanh::lean_is_exclusive(v_c_420_)) as u8;
                    if v_isSharedCheck_430_ == 0 {
                        v___x_424_ = v_c_420_;
                        v_isShared_425_ = v_isSharedCheck_430_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_422_);
                        leanh::lean_dec(v_c_420_);
                        v___x_424_ = leanh::lean_box(0);
                        v_isShared_425_ = v_isSharedCheck_430_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_426_ = leanh::lean_ctor_get(v_val_422_, 0);
                leanh::lean_inc(v_fst_426_);
                leanh::lean_dec(v_val_422_);
                if v_isShared_425_ == 0 {
                    leanh::lean_ctor_set(v___x_424_, 0, v_fst_426_);
                    v___x_428_ = v___x_424_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_429_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_429_, 0, v_fst_426_);
                    v___x_428_ = v_reuseFailAlloc_429_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_428_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_getKey_x3f(
    mut v_00_u03b1_431_: *mut leanh::LeanObject,
    mut v_00_u03b2_432_: *mut leanh::LeanObject,
    mut v_inst_433_: *mut leanh::LeanObject,
    mut v_k_434_: *mut leanh::LeanObject,
    mut v_c_435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_436_ = l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(v_c_435_);
    return v___x_436_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_getKey_x3f___boxed(
    mut v_00_u03b1_437_: *mut leanh::LeanObject,
    mut v_00_u03b2_438_: *mut leanh::LeanObject,
    mut v_inst_439_: *mut leanh::LeanObject,
    mut v_k_440_: *mut leanh::LeanObject,
    mut v_c_441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_442_ = l_Std_DTreeMap_Internal_Cell_getKey_x3f(
        v_00_u03b1_437_,
        v_00_u03b2_438_,
        v_inst_439_,
        v_k_440_,
        v_c_441_,
    );
    leanh::lean_dec(v_k_440_);
    leanh::lean_dec_ref(v_inst_439_);
    return v_res_442_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_alter___redArg(
    mut v_k_443_: *mut leanh::LeanObject,
    mut v_f_444_: *mut leanh::LeanObject,
    mut v_c_445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_452_: u8 = 0;
    let mut v_snd_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_459_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_c_445_) == 0 {
                    v___x_446_ = leanh::lean_box(0);
                    v___x_447_ = leanh::lean_apply_1(v_f_444_, v___x_446_);
                    v___x_448_ =
                        l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_443_, v___x_447_);
                    return v___x_448_;
                } else {
                    v_val_449_ = leanh::lean_ctor_get(v_c_445_, 0);
                    v_isSharedCheck_459_ = (!leanh::lean_is_exclusive(v_c_445_)) as u8;
                    if v_isSharedCheck_459_ == 0 {
                        v___x_451_ = v_c_445_;
                        v_isShared_452_ = v_isSharedCheck_459_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_449_);
                        leanh::lean_dec(v_c_445_);
                        v___x_451_ = leanh::lean_box(0);
                        v_isShared_452_ = v_isSharedCheck_459_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_453_ = leanh::lean_ctor_get(v_val_449_, 1);
                leanh::lean_inc(v_snd_453_);
                leanh::lean_dec(v_val_449_);
                if v_isShared_452_ == 0 {
                    leanh::lean_ctor_set(v___x_451_, 0, v_snd_453_);
                    v___x_455_ = v___x_451_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_458_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_458_, 0, v_snd_453_);
                    v___x_455_ = v_reuseFailAlloc_458_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_456_ = leanh::lean_apply_1(v_f_444_, v___x_455_);
                v___x_457_ = l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_443_, v___x_456_);
                return v___x_457_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_alter(
    mut v_00_u03b1_460_: *mut leanh::LeanObject,
    mut v_00_u03b2_461_: *mut leanh::LeanObject,
    mut v_inst_462_: *mut leanh::LeanObject,
    mut v_inst_463_: *mut leanh::LeanObject,
    mut v_inst_464_: *mut leanh::LeanObject,
    mut v_k_465_: *mut leanh::LeanObject,
    mut v_f_466_: *mut leanh::LeanObject,
    mut v_c_467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_468_ = l_Std_DTreeMap_Internal_Cell_alter___redArg(v_k_465_, v_f_466_, v_c_467_);
    return v___x_468_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_alter___boxed(
    mut v_00_u03b1_469_: *mut leanh::LeanObject,
    mut v_00_u03b2_470_: *mut leanh::LeanObject,
    mut v_inst_471_: *mut leanh::LeanObject,
    mut v_inst_472_: *mut leanh::LeanObject,
    mut v_inst_473_: *mut leanh::LeanObject,
    mut v_k_474_: *mut leanh::LeanObject,
    mut v_f_475_: *mut leanh::LeanObject,
    mut v_c_476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_477_ = l_Std_DTreeMap_Internal_Cell_alter(
        v_00_u03b1_469_,
        v_00_u03b2_470_,
        v_inst_471_,
        v_inst_472_,
        v_inst_473_,
        v_k_474_,
        v_f_475_,
        v_c_476_,
    );
    leanh::lean_dec_ref(v_inst_471_);
    return v_res_477_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(
    mut v_c_478_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_483_: u8 = 0;
    let mut v_snd_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_c_478_) == 0 {
                    v___x_479_ = leanh::lean_box(0);
                    return v___x_479_;
                } else {
                    v_val_480_ = leanh::lean_ctor_get(v_c_478_, 0);
                    v_isSharedCheck_488_ = (!leanh::lean_is_exclusive(v_c_478_)) as u8;
                    if v_isSharedCheck_488_ == 0 {
                        v___x_482_ = v_c_478_;
                        v_isShared_483_ = v_isSharedCheck_488_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_480_);
                        leanh::lean_dec(v_c_478_);
                        v___x_482_ = leanh::lean_box(0);
                        v_isShared_483_ = v_isSharedCheck_488_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_484_ = leanh::lean_ctor_get(v_val_480_, 1);
                leanh::lean_inc(v_snd_484_);
                leanh::lean_dec(v_val_480_);
                if v_isShared_483_ == 0 {
                    leanh::lean_ctor_set(v___x_482_, 0, v_snd_484_);
                    v___x_486_ = v___x_482_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_487_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_487_, 0, v_snd_484_);
                    v___x_486_ = v_reuseFailAlloc_487_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_486_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_Const_get_x3f(
    mut v_00_u03b1_489_: *mut leanh::LeanObject,
    mut v_00_u03b2_490_: *mut leanh::LeanObject,
    mut v_inst_491_: *mut leanh::LeanObject,
    mut v_k_492_: *mut leanh::LeanObject,
    mut v_c_493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_494_ = l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(v_c_493_);
    return v___x_494_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_Const_get_x3f___boxed(
    mut v_00_u03b1_495_: *mut leanh::LeanObject,
    mut v_00_u03b2_496_: *mut leanh::LeanObject,
    mut v_inst_497_: *mut leanh::LeanObject,
    mut v_k_498_: *mut leanh::LeanObject,
    mut v_c_499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_500_ = l_Std_DTreeMap_Internal_Cell_Const_get_x3f(
        v_00_u03b1_495_,
        v_00_u03b2_496_,
        v_inst_497_,
        v_k_498_,
        v_c_499_,
    );
    leanh::lean_dec(v_k_498_);
    leanh::lean_dec_ref(v_inst_497_);
    return v_res_500_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_Const_alter___redArg(
    mut v_k_501_: *mut leanh::LeanObject,
    mut v_f_502_: *mut leanh::LeanObject,
    mut v_c_503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_510_: u8 = 0;
    let mut v_snd_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_c_503_) == 0 {
                    v___x_504_ = leanh::lean_box(0);
                    v___x_505_ = leanh::lean_apply_1(v_f_502_, v___x_504_);
                    v___x_506_ =
                        l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_501_, v___x_505_);
                    return v___x_506_;
                } else {
                    v_val_507_ = leanh::lean_ctor_get(v_c_503_, 0);
                    v_isSharedCheck_517_ = (!leanh::lean_is_exclusive(v_c_503_)) as u8;
                    if v_isSharedCheck_517_ == 0 {
                        v___x_509_ = v_c_503_;
                        v_isShared_510_ = v_isSharedCheck_517_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_507_);
                        leanh::lean_dec(v_c_503_);
                        v___x_509_ = leanh::lean_box(0);
                        v_isShared_510_ = v_isSharedCheck_517_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_511_ = leanh::lean_ctor_get(v_val_507_, 1);
                leanh::lean_inc(v_snd_511_);
                leanh::lean_dec(v_val_507_);
                if v_isShared_510_ == 0 {
                    leanh::lean_ctor_set(v___x_509_, 0, v_snd_511_);
                    v___x_513_ = v___x_509_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_516_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_516_, 0, v_snd_511_);
                    v___x_513_ = v_reuseFailAlloc_516_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_514_ = leanh::lean_apply_1(v_f_502_, v___x_513_);
                v___x_515_ = l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_501_, v___x_514_);
                return v___x_515_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_Const_alter(
    mut v_00_u03b1_518_: *mut leanh::LeanObject,
    mut v_00_u03b2_519_: *mut leanh::LeanObject,
    mut v_inst_520_: *mut leanh::LeanObject,
    mut v_inst_521_: *mut leanh::LeanObject,
    mut v_k_522_: *mut leanh::LeanObject,
    mut v_f_523_: *mut leanh::LeanObject,
    mut v_c_524_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_525_ = l_Std_DTreeMap_Internal_Cell_Const_alter___redArg(v_k_522_, v_f_523_, v_c_524_);
    return v___x_525_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_Const_alter___boxed(
    mut v_00_u03b1_526_: *mut leanh::LeanObject,
    mut v_00_u03b2_527_: *mut leanh::LeanObject,
    mut v_inst_528_: *mut leanh::LeanObject,
    mut v_inst_529_: *mut leanh::LeanObject,
    mut v_k_530_: *mut leanh::LeanObject,
    mut v_f_531_: *mut leanh::LeanObject,
    mut v_c_532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_533_ = l_Std_DTreeMap_Internal_Cell_Const_alter(
        v_00_u03b1_526_,
        v_00_u03b2_527_,
        v_inst_528_,
        v_inst_529_,
        v_k_530_,
        v_f_531_,
        v_c_532_,
    );
    leanh::lean_dec_ref(v_inst_528_);
    return v_res_533_;
}
pub unsafe fn l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0(
    mut v_k_534_: *mut leanh::LeanObject,
    mut v_x_535_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fst_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: u8 = 0;
    let mut v___x_539_: u8 = 0;
    let mut v___x_540_: u8 = 0;
    v_fst_536_ = leanh::lean_ctor_get(v_x_535_, 0);
    leanh::lean_inc(v_fst_536_);
    leanh::lean_dec_ref(v_x_535_);
    v___x_537_ = leanh::lean_apply_1(v_k_534_, v_fst_536_);
    v___x_538_ = 1;
    v___x_539_ = (leanh::lean_unbox(v___x_537_) as u8);
    v___x_540_ = l_instDecidableEqOrdering(v___x_539_, v___x_538_);
    return v___x_540_;
}
pub unsafe fn l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0___boxed(
    mut v_k_541_: *mut leanh::LeanObject,
    mut v_x_542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_543_: u8 = 0;
    let mut v_r_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_543_ = l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0(v_k_541_, v_x_542_);
    v_r_544_ = leanh::lean_box((v_res_543_) as usize);
    return v_r_544_;
}
pub unsafe fn l_Std_DTreeMap_Internal_List_findCell___redArg(
    mut v_l_545_: *mut leanh::LeanObject,
    mut v_k_546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_547_ = leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_547_, 0, v_k_546_);
    v___x_548_ = l_List_find_x3f___redArg(v___f_547_, v_l_545_);
    return v___x_548_;
}
pub unsafe fn l_Std_DTreeMap_Internal_List_findCell(
    mut v_00_u03b1_549_: *mut leanh::LeanObject,
    mut v_00_u03b2_550_: *mut leanh::LeanObject,
    mut v_inst_551_: *mut leanh::LeanObject,
    mut v_l_552_: *mut leanh::LeanObject,
    mut v_k_553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_554_ = l_Std_DTreeMap_Internal_List_findCell___redArg(v_l_552_, v_k_553_);
    return v___x_554_;
}
pub unsafe fn l_Std_DTreeMap_Internal_List_findCell___boxed(
    mut v_00_u03b1_555_: *mut leanh::LeanObject,
    mut v_00_u03b2_556_: *mut leanh::LeanObject,
    mut v_inst_557_: *mut leanh::LeanObject,
    mut v_l_558_: *mut leanh::LeanObject,
    mut v_k_559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_560_ = l_Std_DTreeMap_Internal_List_findCell(
        v_00_u03b1_555_,
        v_00_u03b2_556_,
        v_inst_557_,
        v_l_558_,
        v_k_559_,
    );
    leanh::lean_dec_ref(v_inst_557_);
    return v_res_560_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DTreeMap_Internal_Cell(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Internal_List_Associative(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Find(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DTreeMap_Internal_Cell(
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
pub unsafe fn initialize_Std_Data_DTreeMap_Internal_Cell(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Internal_List_Associative(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Find(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Internal_Cell(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DTreeMap_Internal_Cell(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Data_DTreeMap_Internal_Cell(builtin);
}
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
    mut v_k_x27_281_: *mut crate::leanh::LeanObject,
    mut v_v_x27_282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_283_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_283_, 0, v_k_x27_281_);
    crate::leanh::lean_ctor_set(v___x_283_, 1, v_v_x27_282_);
    v___x_284_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_284_, 0, v___x_283_);
    return v___x_284_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_ofEq(
    mut v_00_u03b1_285_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_286_: *mut crate::leanh::LeanObject,
    mut v_inst_287_: *mut crate::leanh::LeanObject,
    mut v_k_288_: *mut crate::leanh::LeanObject,
    mut v_k_x27_289_: *mut crate::leanh::LeanObject,
    mut v_v_x27_290_: *mut crate::leanh::LeanObject,
    mut v_hcmp_291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_292_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_x27_289_, v_v_x27_290_);
    return v___x_292_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_ofEq___boxed(
    mut v_00_u03b1_293_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_294_: *mut crate::leanh::LeanObject,
    mut v_inst_295_: *mut crate::leanh::LeanObject,
    mut v_k_296_: *mut crate::leanh::LeanObject,
    mut v_k_x27_297_: *mut crate::leanh::LeanObject,
    mut v_v_x27_298_: *mut crate::leanh::LeanObject,
    mut v_hcmp_299_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_300_ = l_Std_DTreeMap_Internal_Cell_ofEq(
        v_00_u03b1_293_,
        v_00_u03b2_294_,
        v_inst_295_,
        v_k_296_,
        v_k_x27_297_,
        v_v_x27_298_,
        v_hcmp_299_,
    );
    crate::leanh::lean_dec_ref(v_k_296_);
    crate::leanh::lean_dec_ref(v_inst_295_);
    return v_res_300_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_of___redArg(
    mut v_k_301_: *mut crate::leanh::LeanObject,
    mut v_v_302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_303_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_301_, v_v_302_);
    return v___x_303_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_of(
    mut v_00_u03b1_304_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_305_: *mut crate::leanh::LeanObject,
    mut v_inst_306_: *mut crate::leanh::LeanObject,
    mut v_k_307_: *mut crate::leanh::LeanObject,
    mut v_v_308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_309_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_307_, v_v_308_);
    return v___x_309_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_of___boxed(
    mut v_00_u03b1_310_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_311_: *mut crate::leanh::LeanObject,
    mut v_inst_312_: *mut crate::leanh::LeanObject,
    mut v_k_313_: *mut crate::leanh::LeanObject,
    mut v_v_314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_315_ = l_Std_DTreeMap_Internal_Cell_of(
        v_00_u03b1_310_,
        v_00_u03b2_311_,
        v_inst_312_,
        v_k_313_,
        v_v_314_,
    );
    crate::leanh::lean_dec_ref(v_inst_312_);
    return v_res_315_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_empty(
    mut v_00_u03b1_316_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_317_: *mut crate::leanh::LeanObject,
    mut v_inst_318_: *mut crate::leanh::LeanObject,
    mut v_k_319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_320_ = crate::leanh::lean_box(0);
    return v___x_320_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_empty___boxed(
    mut v_00_u03b1_321_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_322_: *mut crate::leanh::LeanObject,
    mut v_inst_323_: *mut crate::leanh::LeanObject,
    mut v_k_324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_325_ =
        l_Std_DTreeMap_Internal_Cell_empty(v_00_u03b1_321_, v_00_u03b2_322_, v_inst_323_, v_k_324_);
    crate::leanh::lean_dec_ref(v_k_324_);
    crate::leanh::lean_dec_ref(v_inst_323_);
    return v_res_325_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_ofOption___redArg(
    mut v_k_326_: *mut crate::leanh::LeanObject,
    mut v_v_x3f_327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_v_x3f_327_) == 0 {
        let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_k_326_);
        v___x_328_ = crate::leanh::lean_box(0);
        return v___x_328_;
    } else {
        let mut v_val_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_329_ = crate::leanh::lean_ctor_get(v_v_x3f_327_, 0);
        crate::leanh::lean_inc(v_val_329_);
        crate::leanh::lean_dec_ref_known(v_v_x3f_327_, 1);
        v___x_330_ = l_Std_DTreeMap_Internal_Cell_ofEq___redArg(v_k_326_, v_val_329_);
        return v___x_330_;
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_ofOption(
    mut v_00_u03b1_331_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_332_: *mut crate::leanh::LeanObject,
    mut v_inst_333_: *mut crate::leanh::LeanObject,
    mut v_k_334_: *mut crate::leanh::LeanObject,
    mut v_v_x3f_335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_336_ = l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_334_, v_v_x3f_335_);
    return v___x_336_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_ofOption___boxed(
    mut v_00_u03b1_337_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_338_: *mut crate::leanh::LeanObject,
    mut v_inst_339_: *mut crate::leanh::LeanObject,
    mut v_k_340_: *mut crate::leanh::LeanObject,
    mut v_v_x3f_341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_342_ = l_Std_DTreeMap_Internal_Cell_ofOption(
        v_00_u03b1_337_,
        v_00_u03b2_338_,
        v_inst_339_,
        v_k_340_,
        v_v_x3f_341_,
    );
    crate::leanh::lean_dec_ref(v_inst_339_);
    return v_res_342_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_contains___redArg(
    mut v_c_343_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_c_343_) == 0 {
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
    mut v_c_346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_347_: u8 = 0;
    let mut v_r_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_347_ = l_Std_DTreeMap_Internal_Cell_contains___redArg(v_c_346_);
    crate::leanh::lean_dec(v_c_346_);
    v_r_348_ = crate::leanh::lean_box((v_res_347_) as usize);
    return v_r_348_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_contains(
    mut v_00_u03b1_349_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_350_: *mut crate::leanh::LeanObject,
    mut v_inst_351_: *mut crate::leanh::LeanObject,
    mut v_k_352_: *mut crate::leanh::LeanObject,
    mut v_c_353_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_354_: u8 = 0;
    v___x_354_ = l_Std_DTreeMap_Internal_Cell_contains___redArg(v_c_353_);
    return v___x_354_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_contains___boxed(
    mut v_00_u03b1_355_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_356_: *mut crate::leanh::LeanObject,
    mut v_inst_357_: *mut crate::leanh::LeanObject,
    mut v_k_358_: *mut crate::leanh::LeanObject,
    mut v_c_359_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_360_: u8 = 0;
    let mut v_r_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_360_ = l_Std_DTreeMap_Internal_Cell_contains(
        v_00_u03b1_355_,
        v_00_u03b2_356_,
        v_inst_357_,
        v_k_358_,
        v_c_359_,
    );
    crate::leanh::lean_dec(v_c_359_);
    crate::leanh::lean_dec_ref(v_k_358_);
    crate::leanh::lean_dec_ref(v_inst_357_);
    v_r_361_ = crate::leanh::lean_box((v_res_360_) as usize);
    return v_r_361_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_get_x3f___redArg(
    mut v_c_362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_367_: u8 = 0;
    let mut v_snd_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_372_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_c_362_) == 0 {
                    v___x_363_ = crate::leanh::lean_box(0);
                    return v___x_363_;
                } else {
                    v_val_364_ = crate::leanh::lean_ctor_get(v_c_362_, 0);
                    v_isSharedCheck_372_ = (!crate::leanh::lean_is_exclusive(v_c_362_)) as u8;
                    if v_isSharedCheck_372_ == 0 {
                        v___x_366_ = v_c_362_;
                        v_isShared_367_ = v_isSharedCheck_372_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_364_);
                        crate::leanh::lean_dec(v_c_362_);
                        v___x_366_ = crate::leanh::lean_box(0);
                        v_isShared_367_ = v_isSharedCheck_372_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_368_ = crate::leanh::lean_ctor_get(v_val_364_, 1);
                crate::leanh::lean_inc(v_snd_368_);
                crate::leanh::lean_dec(v_val_364_);
                if v_isShared_367_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_366_, 0, v_snd_368_);
                    v___x_370_ = v___x_366_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_371_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_371_, 0, v_snd_368_);
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
    mut v_00_u03b1_373_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_374_: *mut crate::leanh::LeanObject,
    mut v_inst_375_: *mut crate::leanh::LeanObject,
    mut v_inst_376_: *mut crate::leanh::LeanObject,
    mut v_inst_377_: *mut crate::leanh::LeanObject,
    mut v_k_378_: *mut crate::leanh::LeanObject,
    mut v_c_379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_380_ = l_Std_DTreeMap_Internal_Cell_get_x3f___redArg(v_c_379_);
    return v___x_380_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_get_x3f___boxed(
    mut v_00_u03b1_381_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_382_: *mut crate::leanh::LeanObject,
    mut v_inst_383_: *mut crate::leanh::LeanObject,
    mut v_inst_384_: *mut crate::leanh::LeanObject,
    mut v_inst_385_: *mut crate::leanh::LeanObject,
    mut v_k_386_: *mut crate::leanh::LeanObject,
    mut v_c_387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_388_ = l_Std_DTreeMap_Internal_Cell_get_x3f(
        v_00_u03b1_381_,
        v_00_u03b2_382_,
        v_inst_383_,
        v_inst_384_,
        v_inst_385_,
        v_k_386_,
        v_c_387_,
    );
    crate::leanh::lean_dec(v_k_386_);
    crate::leanh::lean_dec_ref(v_inst_383_);
    return v_res_388_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_getEntry_x3f___redArg(
    mut v_c_389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_394_: u8 = 0;
    let mut v_fst_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_399_: u8 = 0;
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_406_: u8 = 0;
    let mut v_isSharedCheck_407_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_c_389_) == 0 {
                    v___x_390_ = crate::leanh::lean_box(0);
                    return v___x_390_;
                } else {
                    v_val_391_ = crate::leanh::lean_ctor_get(v_c_389_, 0);
                    v_isSharedCheck_407_ = (!crate::leanh::lean_is_exclusive(v_c_389_)) as u8;
                    if v_isSharedCheck_407_ == 0 {
                        v___x_393_ = v_c_389_;
                        v_isShared_394_ = v_isSharedCheck_407_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_391_);
                        crate::leanh::lean_dec(v_c_389_);
                        v___x_393_ = crate::leanh::lean_box(0);
                        v_isShared_394_ = v_isSharedCheck_407_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_395_ = crate::leanh::lean_ctor_get(v_val_391_, 0);
                v_snd_396_ = crate::leanh::lean_ctor_get(v_val_391_, 1);
                v_isSharedCheck_406_ = (!crate::leanh::lean_is_exclusive(v_val_391_)) as u8;
                if v_isSharedCheck_406_ == 0 {
                    v___x_398_ = v_val_391_;
                    v_isShared_399_ = v_isSharedCheck_406_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_396_);
                    crate::leanh::lean_inc(v_fst_395_);
                    crate::leanh::lean_dec(v_val_391_);
                    v___x_398_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_405_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_405_, 0, v_fst_395_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_405_, 1, v_snd_396_);
                    v___x_401_ = v_reuseFailAlloc_405_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_394_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_393_, 0, v___x_401_);
                    v___x_403_ = v___x_393_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_404_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_401_);
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
    mut v_00_u03b1_408_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_409_: *mut crate::leanh::LeanObject,
    mut v_inst_410_: *mut crate::leanh::LeanObject,
    mut v_k_411_: *mut crate::leanh::LeanObject,
    mut v_c_412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_413_ = l_Std_DTreeMap_Internal_Cell_getEntry_x3f___redArg(v_c_412_);
    return v___x_413_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_getEntry_x3f___boxed(
    mut v_00_u03b1_414_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_415_: *mut crate::leanh::LeanObject,
    mut v_inst_416_: *mut crate::leanh::LeanObject,
    mut v_k_417_: *mut crate::leanh::LeanObject,
    mut v_c_418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_419_ = l_Std_DTreeMap_Internal_Cell_getEntry_x3f(
        v_00_u03b1_414_,
        v_00_u03b2_415_,
        v_inst_416_,
        v_k_417_,
        v_c_418_,
    );
    crate::leanh::lean_dec(v_k_417_);
    crate::leanh::lean_dec_ref(v_inst_416_);
    return v_res_419_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(
    mut v_c_420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_425_: u8 = 0;
    let mut v_fst_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_430_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_c_420_) == 0 {
                    v___x_421_ = crate::leanh::lean_box(0);
                    return v___x_421_;
                } else {
                    v_val_422_ = crate::leanh::lean_ctor_get(v_c_420_, 0);
                    v_isSharedCheck_430_ = (!crate::leanh::lean_is_exclusive(v_c_420_)) as u8;
                    if v_isSharedCheck_430_ == 0 {
                        v___x_424_ = v_c_420_;
                        v_isShared_425_ = v_isSharedCheck_430_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_422_);
                        crate::leanh::lean_dec(v_c_420_);
                        v___x_424_ = crate::leanh::lean_box(0);
                        v_isShared_425_ = v_isSharedCheck_430_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_426_ = crate::leanh::lean_ctor_get(v_val_422_, 0);
                crate::leanh::lean_inc(v_fst_426_);
                crate::leanh::lean_dec(v_val_422_);
                if v_isShared_425_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_424_, 0, v_fst_426_);
                    v___x_428_ = v___x_424_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_429_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_429_, 0, v_fst_426_);
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
    mut v_00_u03b1_431_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_432_: *mut crate::leanh::LeanObject,
    mut v_inst_433_: *mut crate::leanh::LeanObject,
    mut v_k_434_: *mut crate::leanh::LeanObject,
    mut v_c_435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_436_ = l_Std_DTreeMap_Internal_Cell_getKey_x3f___redArg(v_c_435_);
    return v___x_436_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_getKey_x3f___boxed(
    mut v_00_u03b1_437_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_438_: *mut crate::leanh::LeanObject,
    mut v_inst_439_: *mut crate::leanh::LeanObject,
    mut v_k_440_: *mut crate::leanh::LeanObject,
    mut v_c_441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_442_ = l_Std_DTreeMap_Internal_Cell_getKey_x3f(
        v_00_u03b1_437_,
        v_00_u03b2_438_,
        v_inst_439_,
        v_k_440_,
        v_c_441_,
    );
    crate::leanh::lean_dec(v_k_440_);
    crate::leanh::lean_dec_ref(v_inst_439_);
    return v_res_442_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_alter___redArg(
    mut v_k_443_: *mut crate::leanh::LeanObject,
    mut v_f_444_: *mut crate::leanh::LeanObject,
    mut v_c_445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_452_: u8 = 0;
    let mut v_snd_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_459_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_c_445_) == 0 {
                    v___x_446_ = crate::leanh::lean_box(0);
                    v___x_447_ = crate::leanh::lean_apply_1(v_f_444_, v___x_446_);
                    v___x_448_ =
                        l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_443_, v___x_447_);
                    return v___x_448_;
                } else {
                    v_val_449_ = crate::leanh::lean_ctor_get(v_c_445_, 0);
                    v_isSharedCheck_459_ = (!crate::leanh::lean_is_exclusive(v_c_445_)) as u8;
                    if v_isSharedCheck_459_ == 0 {
                        v___x_451_ = v_c_445_;
                        v_isShared_452_ = v_isSharedCheck_459_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_449_);
                        crate::leanh::lean_dec(v_c_445_);
                        v___x_451_ = crate::leanh::lean_box(0);
                        v_isShared_452_ = v_isSharedCheck_459_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_453_ = crate::leanh::lean_ctor_get(v_val_449_, 1);
                crate::leanh::lean_inc(v_snd_453_);
                crate::leanh::lean_dec(v_val_449_);
                if v_isShared_452_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_451_, 0, v_snd_453_);
                    v___x_455_ = v___x_451_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_458_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_458_, 0, v_snd_453_);
                    v___x_455_ = v_reuseFailAlloc_458_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_456_ = crate::leanh::lean_apply_1(v_f_444_, v___x_455_);
                v___x_457_ = l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_443_, v___x_456_);
                return v___x_457_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_alter(
    mut v_00_u03b1_460_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_461_: *mut crate::leanh::LeanObject,
    mut v_inst_462_: *mut crate::leanh::LeanObject,
    mut v_inst_463_: *mut crate::leanh::LeanObject,
    mut v_inst_464_: *mut crate::leanh::LeanObject,
    mut v_k_465_: *mut crate::leanh::LeanObject,
    mut v_f_466_: *mut crate::leanh::LeanObject,
    mut v_c_467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_468_ = l_Std_DTreeMap_Internal_Cell_alter___redArg(v_k_465_, v_f_466_, v_c_467_);
    return v___x_468_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_alter___boxed(
    mut v_00_u03b1_469_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_470_: *mut crate::leanh::LeanObject,
    mut v_inst_471_: *mut crate::leanh::LeanObject,
    mut v_inst_472_: *mut crate::leanh::LeanObject,
    mut v_inst_473_: *mut crate::leanh::LeanObject,
    mut v_k_474_: *mut crate::leanh::LeanObject,
    mut v_f_475_: *mut crate::leanh::LeanObject,
    mut v_c_476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec_ref(v_inst_471_);
    return v_res_477_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(
    mut v_c_478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_483_: u8 = 0;
    let mut v_snd_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_c_478_) == 0 {
                    v___x_479_ = crate::leanh::lean_box(0);
                    return v___x_479_;
                } else {
                    v_val_480_ = crate::leanh::lean_ctor_get(v_c_478_, 0);
                    v_isSharedCheck_488_ = (!crate::leanh::lean_is_exclusive(v_c_478_)) as u8;
                    if v_isSharedCheck_488_ == 0 {
                        v___x_482_ = v_c_478_;
                        v_isShared_483_ = v_isSharedCheck_488_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_480_);
                        crate::leanh::lean_dec(v_c_478_);
                        v___x_482_ = crate::leanh::lean_box(0);
                        v_isShared_483_ = v_isSharedCheck_488_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_484_ = crate::leanh::lean_ctor_get(v_val_480_, 1);
                crate::leanh::lean_inc(v_snd_484_);
                crate::leanh::lean_dec(v_val_480_);
                if v_isShared_483_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_482_, 0, v_snd_484_);
                    v___x_486_ = v___x_482_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_487_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_487_, 0, v_snd_484_);
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
    mut v_00_u03b1_489_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_490_: *mut crate::leanh::LeanObject,
    mut v_inst_491_: *mut crate::leanh::LeanObject,
    mut v_k_492_: *mut crate::leanh::LeanObject,
    mut v_c_493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_494_ = l_Std_DTreeMap_Internal_Cell_Const_get_x3f___redArg(v_c_493_);
    return v___x_494_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_Const_get_x3f___boxed(
    mut v_00_u03b1_495_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_496_: *mut crate::leanh::LeanObject,
    mut v_inst_497_: *mut crate::leanh::LeanObject,
    mut v_k_498_: *mut crate::leanh::LeanObject,
    mut v_c_499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_500_ = l_Std_DTreeMap_Internal_Cell_Const_get_x3f(
        v_00_u03b1_495_,
        v_00_u03b2_496_,
        v_inst_497_,
        v_k_498_,
        v_c_499_,
    );
    crate::leanh::lean_dec(v_k_498_);
    crate::leanh::lean_dec_ref(v_inst_497_);
    return v_res_500_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_Const_alter___redArg(
    mut v_k_501_: *mut crate::leanh::LeanObject,
    mut v_f_502_: *mut crate::leanh::LeanObject,
    mut v_c_503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_510_: u8 = 0;
    let mut v_snd_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_c_503_) == 0 {
                    v___x_504_ = crate::leanh::lean_box(0);
                    v___x_505_ = crate::leanh::lean_apply_1(v_f_502_, v___x_504_);
                    v___x_506_ =
                        l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_501_, v___x_505_);
                    return v___x_506_;
                } else {
                    v_val_507_ = crate::leanh::lean_ctor_get(v_c_503_, 0);
                    v_isSharedCheck_517_ = (!crate::leanh::lean_is_exclusive(v_c_503_)) as u8;
                    if v_isSharedCheck_517_ == 0 {
                        v___x_509_ = v_c_503_;
                        v_isShared_510_ = v_isSharedCheck_517_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_507_);
                        crate::leanh::lean_dec(v_c_503_);
                        v___x_509_ = crate::leanh::lean_box(0);
                        v_isShared_510_ = v_isSharedCheck_517_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_511_ = crate::leanh::lean_ctor_get(v_val_507_, 1);
                crate::leanh::lean_inc(v_snd_511_);
                crate::leanh::lean_dec(v_val_507_);
                if v_isShared_510_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_509_, 0, v_snd_511_);
                    v___x_513_ = v___x_509_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_516_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_516_, 0, v_snd_511_);
                    v___x_513_ = v_reuseFailAlloc_516_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_514_ = crate::leanh::lean_apply_1(v_f_502_, v___x_513_);
                v___x_515_ = l_Std_DTreeMap_Internal_Cell_ofOption___redArg(v_k_501_, v___x_514_);
                return v___x_515_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_Const_alter(
    mut v_00_u03b1_518_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_519_: *mut crate::leanh::LeanObject,
    mut v_inst_520_: *mut crate::leanh::LeanObject,
    mut v_inst_521_: *mut crate::leanh::LeanObject,
    mut v_k_522_: *mut crate::leanh::LeanObject,
    mut v_f_523_: *mut crate::leanh::LeanObject,
    mut v_c_524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_525_ = l_Std_DTreeMap_Internal_Cell_Const_alter___redArg(v_k_522_, v_f_523_, v_c_524_);
    return v___x_525_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Cell_Const_alter___boxed(
    mut v_00_u03b1_526_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_527_: *mut crate::leanh::LeanObject,
    mut v_inst_528_: *mut crate::leanh::LeanObject,
    mut v_inst_529_: *mut crate::leanh::LeanObject,
    mut v_k_530_: *mut crate::leanh::LeanObject,
    mut v_f_531_: *mut crate::leanh::LeanObject,
    mut v_c_532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_533_ = l_Std_DTreeMap_Internal_Cell_Const_alter(
        v_00_u03b1_526_,
        v_00_u03b2_527_,
        v_inst_528_,
        v_inst_529_,
        v_k_530_,
        v_f_531_,
        v_c_532_,
    );
    crate::leanh::lean_dec_ref(v_inst_528_);
    return v_res_533_;
}
pub unsafe fn l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0(
    mut v_k_534_: *mut crate::leanh::LeanObject,
    mut v_x_535_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_538_: u8 = 0;
    let mut v___x_539_: u8 = 0;
    let mut v___x_540_: u8 = 0;
    v_fst_536_ = crate::leanh::lean_ctor_get(v_x_535_, 0);
    crate::leanh::lean_inc(v_fst_536_);
    crate::leanh::lean_dec_ref(v_x_535_);
    v___x_537_ = crate::leanh::lean_apply_1(v_k_534_, v_fst_536_);
    v___x_538_ = 1;
    v___x_539_ = (crate::leanh::lean_unbox(v___x_537_) as u8);
    v___x_540_ = l_instDecidableEqOrdering(v___x_539_, v___x_538_);
    return v___x_540_;
}
pub unsafe fn l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0___boxed(
    mut v_k_541_: *mut crate::leanh::LeanObject,
    mut v_x_542_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_543_: u8 = 0;
    let mut v_r_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_543_ = l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0(v_k_541_, v_x_542_);
    v_r_544_ = crate::leanh::lean_box((v_res_543_) as usize);
    return v_r_544_;
}
pub unsafe fn l_Std_DTreeMap_Internal_List_findCell___redArg(
    mut v_l_545_: *mut crate::leanh::LeanObject,
    mut v_k_546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_547_ = crate::leanh::lean_alloc_closure(
        l_Std_DTreeMap_Internal_List_findCell___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_547_, 0, v_k_546_);
    v___x_548_ = l_List_find_x3f___redArg(v___f_547_, v_l_545_);
    return v___x_548_;
}
pub unsafe fn l_Std_DTreeMap_Internal_List_findCell(
    mut v_00_u03b1_549_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_550_: *mut crate::leanh::LeanObject,
    mut v_inst_551_: *mut crate::leanh::LeanObject,
    mut v_l_552_: *mut crate::leanh::LeanObject,
    mut v_k_553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_554_ = l_Std_DTreeMap_Internal_List_findCell___redArg(v_l_552_, v_k_553_);
    return v___x_554_;
}
pub unsafe fn l_Std_DTreeMap_Internal_List_findCell___boxed(
    mut v_00_u03b1_555_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_556_: *mut crate::leanh::LeanObject,
    mut v_inst_557_: *mut crate::leanh::LeanObject,
    mut v_l_558_: *mut crate::leanh::LeanObject,
    mut v_k_559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_560_ = l_Std_DTreeMap_Internal_List_findCell(
        v_00_u03b1_555_,
        v_00_u03b2_556_,
        v_inst_557_,
        v_l_558_,
        v_k_559_,
    );
    crate::leanh::lean_dec_ref(v_inst_557_);
    return v_res_560_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Data_DTreeMap_Internal_Cell(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Data_Internal_List_Associative(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Find(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Data_DTreeMap_Internal_Cell(
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
pub unsafe fn initialize_Std_Data_DTreeMap_Internal_Cell(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Data_Internal_List_Associative(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Find(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Data_DTreeMap_Internal_Cell(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Data_DTreeMap_Internal_Cell(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Std_Data_DTreeMap_Internal_Cell(builtin);
}

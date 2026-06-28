// Lean compiler output
// Module: Init.Data.Fin.Fold
// Imports: Init.Control.Lawful.Basic Init.Ext Init.Data.Fin.Lemmas Init.Data.Nat.Lemmas Init.Omega Init.TacticsExtra Init.WFTactics Init.Hints
use crate::r#gen::Init::Control::Lawful::Basic::{
    initialize_Init_Control_Lawful_Basic, runtime_initialize_Init_Control_Lawful_Basic,
};
use crate::r#gen::Init::Data::Fin::Lemmas::{
    initialize_Init_Data_Fin_Lemmas, runtime_initialize_Init_Data_Fin_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::Hints::{initialize_Init_Hints, runtime_initialize_Init_Hints};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::TacticsExtra::{
    initialize_Init_TacticsExtra, runtime_initialize_Init_TacticsExtra,
};
use crate::r#gen::Init::WFTactics::{initialize_Init_WFTactics, runtime_initialize_Init_WFTactics};
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub,
};
pub unsafe fn l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___redArg(
    mut v_n_262_: *mut crate::leanh::LeanObject,
    mut v_f_263_: *mut crate::leanh::LeanObject,
    mut v_x_264_: *mut crate::leanh::LeanObject,
    mut v_i_265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_266_: u8 = 0;
    let mut v___x_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_266_ = lean_nat_dec_lt(v_i_265_, v_n_262_);
                if v___x_266_ == 0 {
                    crate::leanh::lean_dec(v_i_265_);
                    crate::leanh::lean_dec(v_f_263_);
                    return v_x_264_;
                } else {
                    crate::leanh::lean_inc(v_f_263_);
                    crate::leanh::lean_inc(v_i_265_);
                    v___x_267_ = crate::leanh::lean_apply_2(v_f_263_, v_x_264_, v_i_265_);
                    v___x_268_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_269_ = lean_nat_add(v_i_265_, v___x_268_);
                    crate::leanh::lean_dec(v_i_265_);
                    v_x_264_ = v___x_267_;
                    v_i_265_ = v___x_269_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___redArg___boxed(
    mut v_n_271_: *mut crate::leanh::LeanObject,
    mut v_f_272_: *mut crate::leanh::LeanObject,
    mut v_x_273_: *mut crate::leanh::LeanObject,
    mut v_i_274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_275_ = l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___redArg(
        v_n_271_, v_f_272_, v_x_273_, v_i_274_,
    );
    crate::leanh::lean_dec(v_n_271_);
    return v_res_275_;
}
pub unsafe fn l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop(
    mut v_00_u03b1_276_: *mut crate::leanh::LeanObject,
    mut v_n_277_: *mut crate::leanh::LeanObject,
    mut v_f_278_: *mut crate::leanh::LeanObject,
    mut v_x_279_: *mut crate::leanh::LeanObject,
    mut v_i_280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_281_ = l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___redArg(
        v_n_277_, v_f_278_, v_x_279_, v_i_280_,
    );
    return v___x_281_;
}
pub unsafe fn l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___boxed(
    mut v_00_u03b1_282_: *mut crate::leanh::LeanObject,
    mut v_n_283_: *mut crate::leanh::LeanObject,
    mut v_f_284_: *mut crate::leanh::LeanObject,
    mut v_x_285_: *mut crate::leanh::LeanObject,
    mut v_i_286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_287_ = l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop(
        v_00_u03b1_282_,
        v_n_283_,
        v_f_284_,
        v_x_285_,
        v_i_286_,
    );
    crate::leanh::lean_dec(v_n_283_);
    return v_res_287_;
}
pub unsafe fn l_Fin_foldl___redArg(
    mut v_n_288_: *mut crate::leanh::LeanObject,
    mut v_f_289_: *mut crate::leanh::LeanObject,
    mut v_init_290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_291_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_292_ = l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___redArg(
        v_n_288_,
        v_f_289_,
        v_init_290_,
        v___x_291_,
    );
    return v___x_292_;
}
pub unsafe fn l_Fin_foldl___redArg___boxed(
    mut v_n_293_: *mut crate::leanh::LeanObject,
    mut v_f_294_: *mut crate::leanh::LeanObject,
    mut v_init_295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_296_ = l_Fin_foldl___redArg(v_n_293_, v_f_294_, v_init_295_);
    crate::leanh::lean_dec(v_n_293_);
    return v_res_296_;
}
pub unsafe fn l_Fin_foldl(
    mut v_00_u03b1_297_: *mut crate::leanh::LeanObject,
    mut v_n_298_: *mut crate::leanh::LeanObject,
    mut v_f_299_: *mut crate::leanh::LeanObject,
    mut v_init_300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_301_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_302_ = l___private_Init_Data_Fin_Fold_0__Fin_foldl_loop___redArg(
        v_n_298_,
        v_f_299_,
        v_init_300_,
        v___x_301_,
    );
    return v___x_302_;
}
pub unsafe fn l_Fin_foldl___boxed(
    mut v_00_u03b1_303_: *mut crate::leanh::LeanObject,
    mut v_n_304_: *mut crate::leanh::LeanObject,
    mut v_f_305_: *mut crate::leanh::LeanObject,
    mut v_init_306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_307_ = l_Fin_foldl(v_00_u03b1_303_, v_n_304_, v_f_305_, v_init_306_);
    crate::leanh::lean_dec(v_n_304_);
    return v_res_307_;
}
pub unsafe fn l_Fin_foldr_loop___redArg(
    mut v_f_308_: *mut crate::leanh::LeanObject,
    mut v_i_309_: *mut crate::leanh::LeanObject,
    mut v_a_310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_312_: u8 = 0;
    let mut v_one_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_311_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_312_ = lean_nat_dec_eq(v_i_309_, v_zero_311_);
                if v_isZero_312_ == 1 {
                    crate::leanh::lean_dec(v_i_309_);
                    crate::leanh::lean_dec(v_f_308_);
                    return v_a_310_;
                } else {
                    v_one_313_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_314_ = lean_nat_sub(v_i_309_, v_one_313_);
                    crate::leanh::lean_dec(v_i_309_);
                    crate::leanh::lean_inc(v_f_308_);
                    crate::leanh::lean_inc(v_n_314_);
                    v___x_315_ = crate::leanh::lean_apply_2(v_f_308_, v_n_314_, v_a_310_);
                    v_i_309_ = v_n_314_;
                    v_a_310_ = v___x_315_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Fin_foldr_loop(
    mut v_00_u03b1_317_: *mut crate::leanh::LeanObject,
    mut v_n_318_: *mut crate::leanh::LeanObject,
    mut v_f_319_: *mut crate::leanh::LeanObject,
    mut v_i_320_: *mut crate::leanh::LeanObject,
    mut v_a_321_: *mut crate::leanh::LeanObject,
    mut v_a_322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_323_ = l_Fin_foldr_loop___redArg(v_f_319_, v_i_320_, v_a_322_);
    return v___x_323_;
}
pub unsafe fn l_Fin_foldr_loop___boxed(
    mut v_00_u03b1_324_: *mut crate::leanh::LeanObject,
    mut v_n_325_: *mut crate::leanh::LeanObject,
    mut v_f_326_: *mut crate::leanh::LeanObject,
    mut v_i_327_: *mut crate::leanh::LeanObject,
    mut v_a_328_: *mut crate::leanh::LeanObject,
    mut v_a_329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_330_ = l_Fin_foldr_loop(
        v_00_u03b1_324_,
        v_n_325_,
        v_f_326_,
        v_i_327_,
        v_a_328_,
        v_a_329_,
    );
    crate::leanh::lean_dec(v_n_325_);
    return v_res_330_;
}
pub unsafe fn l_Fin_foldr___redArg(
    mut v_n_331_: *mut crate::leanh::LeanObject,
    mut v_f_332_: *mut crate::leanh::LeanObject,
    mut v_init_333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_334_ = l_Fin_foldr_loop___redArg(v_f_332_, v_n_331_, v_init_333_);
    return v___x_334_;
}
pub unsafe fn l_Fin_foldr(
    mut v_00_u03b1_335_: *mut crate::leanh::LeanObject,
    mut v_n_336_: *mut crate::leanh::LeanObject,
    mut v_f_337_: *mut crate::leanh::LeanObject,
    mut v_init_338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_339_ = l_Fin_foldr_loop___redArg(v_f_337_, v_n_336_, v_init_338_);
    return v___x_339_;
}
pub unsafe fn l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg___lam__0___boxed(
    mut v_i_340_: *mut crate::leanh::LeanObject,
    mut v_inst_341_: *mut crate::leanh::LeanObject,
    mut v_n_342_: *mut crate::leanh::LeanObject,
    mut v_f_343_: *mut crate::leanh::LeanObject,
    mut v_x_344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_345_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg___lam__0(
        v_i_340_,
        v_inst_341_,
        v_n_342_,
        v_f_343_,
        v_x_344_,
    );
    crate::leanh::lean_dec(v_i_340_);
    return v_res_345_;
}
pub unsafe fn l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg(
    mut v_inst_346_: *mut crate::leanh::LeanObject,
    mut v_n_347_: *mut crate::leanh::LeanObject,
    mut v_f_348_: *mut crate::leanh::LeanObject,
    mut v_x_349_: *mut crate::leanh::LeanObject,
    mut v_i_350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_351_: u8 = 0;
    v___x_351_ = lean_nat_dec_lt(v_i_350_, v_n_347_);
    if v___x_351_ == 0 {
        let mut v_toApplicative_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_i_350_);
        crate::leanh::lean_dec(v_f_348_);
        crate::leanh::lean_dec(v_n_347_);
        v_toApplicative_352_ = crate::leanh::lean_ctor_get(v_inst_346_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_352_);
        crate::leanh::lean_dec_ref(v_inst_346_);
        v_toPure_353_ = crate::leanh::lean_ctor_get(v_toApplicative_352_, 1);
        crate::leanh::lean_inc(v_toPure_353_);
        crate::leanh::lean_dec_ref(v_toApplicative_352_);
        v___x_354_ = crate::leanh::lean_apply_2(v_toPure_353_, crate::leanh::lean_box(0), v_x_349_);
        return v___x_354_;
    } else {
        let mut v_toBind_355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_355_ = crate::leanh::lean_ctor_get(v_inst_346_, 1);
        crate::leanh::lean_inc(v_toBind_355_);
        crate::leanh::lean_inc(v_f_348_);
        crate::leanh::lean_inc(v_i_350_);
        v___f_356_ = crate::leanh::lean_alloc_closure(
            l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            5,
            4,
        );
        crate::leanh::lean_closure_set(v___f_356_, 0, v_i_350_);
        crate::leanh::lean_closure_set(v___f_356_, 1, v_inst_346_);
        crate::leanh::lean_closure_set(v___f_356_, 2, v_n_347_);
        crate::leanh::lean_closure_set(v___f_356_, 3, v_f_348_);
        v___x_357_ = crate::leanh::lean_apply_2(v_f_348_, v_x_349_, v_i_350_);
        v___x_358_ = crate::leanh::lean_apply_4(
            v_toBind_355_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_357_,
            v___f_356_,
        );
        return v___x_358_;
    }
}
pub unsafe fn l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg___lam__0(
    mut v_i_359_: *mut crate::leanh::LeanObject,
    mut v_inst_360_: *mut crate::leanh::LeanObject,
    mut v_n_361_: *mut crate::leanh::LeanObject,
    mut v_f_362_: *mut crate::leanh::LeanObject,
    mut v_x_363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_364_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_365_ = lean_nat_add(v_i_359_, v___x_364_);
    v___x_366_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg(
        v_inst_360_,
        v_n_361_,
        v_f_362_,
        v_x_363_,
        v___x_365_,
    );
    return v___x_366_;
}
pub unsafe fn l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop(
    mut v_m_367_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_368_: *mut crate::leanh::LeanObject,
    mut v_inst_369_: *mut crate::leanh::LeanObject,
    mut v_n_370_: *mut crate::leanh::LeanObject,
    mut v_f_371_: *mut crate::leanh::LeanObject,
    mut v_x_372_: *mut crate::leanh::LeanObject,
    mut v_i_373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_374_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg(
        v_inst_369_,
        v_n_370_,
        v_f_371_,
        v_x_372_,
        v_i_373_,
    );
    return v___x_374_;
}
pub unsafe fn l_Fin_foldlM___redArg(
    mut v_inst_375_: *mut crate::leanh::LeanObject,
    mut v_n_376_: *mut crate::leanh::LeanObject,
    mut v_f_377_: *mut crate::leanh::LeanObject,
    mut v_init_378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_379_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_380_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg(
        v_inst_375_,
        v_n_376_,
        v_f_377_,
        v_init_378_,
        v___x_379_,
    );
    return v___x_380_;
}
pub unsafe fn l_Fin_foldlM(
    mut v_m_381_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_382_: *mut crate::leanh::LeanObject,
    mut v_inst_383_: *mut crate::leanh::LeanObject,
    mut v_n_384_: *mut crate::leanh::LeanObject,
    mut v_f_385_: *mut crate::leanh::LeanObject,
    mut v_init_386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_387_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_388_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop___redArg(
        v_inst_383_,
        v_n_384_,
        v_f_385_,
        v_init_386_,
        v___x_387_,
    );
    return v___x_388_;
}
pub unsafe fn l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg___boxed(
    mut v_inst_389_: *mut crate::leanh::LeanObject,
    mut v_f_390_: *mut crate::leanh::LeanObject,
    mut v_a_391_: *mut crate::leanh::LeanObject,
    mut v_a_392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_393_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg(
        v_inst_389_,
        v_f_390_,
        v_a_391_,
        v_a_392_,
    );
    crate::leanh::lean_dec(v_a_391_);
    return v_res_393_;
}
pub unsafe fn l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg(
    mut v_inst_394_: *mut crate::leanh::LeanObject,
    mut v_f_395_: *mut crate::leanh::LeanObject,
    mut v_a_396_: *mut crate::leanh::LeanObject,
    mut v_a_397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_402_: u8 = 0;
    v_toApplicative_398_ = crate::leanh::lean_ctor_get(v_inst_394_, 0);
    v_toBind_399_ = crate::leanh::lean_ctor_get(v_inst_394_, 1);
    crate::leanh::lean_inc(v_toBind_399_);
    v_toPure_400_ = crate::leanh::lean_ctor_get(v_toApplicative_398_, 1);
    v_zero_401_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_402_ = lean_nat_dec_eq(v_a_396_, v_zero_401_);
    if v_isZero_402_ == 1 {
        let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_toPure_400_);
        crate::leanh::lean_dec(v_toBind_399_);
        crate::leanh::lean_dec(v_f_395_);
        crate::leanh::lean_dec_ref(v_inst_394_);
        v___x_403_ = crate::leanh::lean_apply_2(v_toPure_400_, crate::leanh::lean_box(0), v_a_397_);
        return v___x_403_;
    } else {
        let mut v_one_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_one_404_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_405_ = lean_nat_sub(v_a_396_, v_one_404_);
        crate::leanh::lean_inc(v_f_395_);
        crate::leanh::lean_inc(v_n_405_);
        v___x_406_ = crate::leanh::lean_apply_2(v_f_395_, v_n_405_, v_a_397_);
        v___x_407_ = crate::leanh::lean_alloc_closure(
            l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg___boxed
                as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___x_407_, 0, v_inst_394_);
        crate::leanh::lean_closure_set(v___x_407_, 1, v_f_395_);
        crate::leanh::lean_closure_set(v___x_407_, 2, v_n_405_);
        v___x_408_ = crate::leanh::lean_apply_4(
            v_toBind_399_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_406_,
            v___x_407_,
        );
        return v___x_408_;
    }
}
pub unsafe fn l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop(
    mut v_m_409_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_410_: *mut crate::leanh::LeanObject,
    mut v_inst_411_: *mut crate::leanh::LeanObject,
    mut v_n_412_: *mut crate::leanh::LeanObject,
    mut v_f_413_: *mut crate::leanh::LeanObject,
    mut v_a_414_: *mut crate::leanh::LeanObject,
    mut v_a_415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_416_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg(
        v_inst_411_,
        v_f_413_,
        v_a_414_,
        v_a_415_,
    );
    return v___x_416_;
}
pub unsafe fn l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___boxed(
    mut v_m_417_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_418_: *mut crate::leanh::LeanObject,
    mut v_inst_419_: *mut crate::leanh::LeanObject,
    mut v_n_420_: *mut crate::leanh::LeanObject,
    mut v_f_421_: *mut crate::leanh::LeanObject,
    mut v_a_422_: *mut crate::leanh::LeanObject,
    mut v_a_423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_424_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop(
        v_m_417_,
        v_00_u03b1_418_,
        v_inst_419_,
        v_n_420_,
        v_f_421_,
        v_a_422_,
        v_a_423_,
    );
    crate::leanh::lean_dec(v_a_422_);
    crate::leanh::lean_dec(v_n_420_);
    return v_res_424_;
}
pub unsafe fn l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter___redArg(
    mut v_x_425_: *mut crate::leanh::LeanObject,
    mut v_x_426_: *mut crate::leanh::LeanObject,
    mut v_h__1_427_: *mut crate::leanh::LeanObject,
    mut v_h__2_428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_430_: u8 = 0;
    v_zero_429_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_430_ = lean_nat_dec_eq(v_x_425_, v_zero_429_);
    if v_isZero_430_ == 1 {
        let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_428_);
        v___x_431_ = crate::leanh::lean_apply_2(v_h__1_427_, crate::leanh::lean_box(0), v_x_426_);
        return v___x_431_;
    } else {
        let mut v_one_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_427_);
        v_one_432_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_433_ = lean_nat_sub(v_x_425_, v_one_432_);
        v___x_434_ =
            crate::leanh::lean_apply_3(v_h__2_428_, v_n_433_, crate::leanh::lean_box(0), v_x_426_);
        return v___x_434_;
    }
}
pub unsafe fn l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter___redArg___boxed(
    mut v_x_435_: *mut crate::leanh::LeanObject,
    mut v_x_436_: *mut crate::leanh::LeanObject,
    mut v_h__1_437_: *mut crate::leanh::LeanObject,
    mut v_h__2_438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_439_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter___redArg(
        v_x_435_,
        v_x_436_,
        v_h__1_437_,
        v_h__2_438_,
    );
    crate::leanh::lean_dec(v_x_435_);
    return v_res_439_;
}
pub unsafe fn l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter(
    mut v_00_u03b1_440_: *mut crate::leanh::LeanObject,
    mut v_n_441_: *mut crate::leanh::LeanObject,
    mut v_motive_442_: *mut crate::leanh::LeanObject,
    mut v_x_443_: *mut crate::leanh::LeanObject,
    mut v_x_444_: *mut crate::leanh::LeanObject,
    mut v_h__1_445_: *mut crate::leanh::LeanObject,
    mut v_h__2_446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_448_: u8 = 0;
    v_zero_447_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_448_ = lean_nat_dec_eq(v_x_443_, v_zero_447_);
    if v_isZero_448_ == 1 {
        let mut v___x_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_446_);
        v___x_449_ = crate::leanh::lean_apply_2(v_h__1_445_, crate::leanh::lean_box(0), v_x_444_);
        return v___x_449_;
    } else {
        let mut v_one_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_445_);
        v_one_450_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_451_ = lean_nat_sub(v_x_443_, v_one_450_);
        v___x_452_ =
            crate::leanh::lean_apply_3(v_h__2_446_, v_n_451_, crate::leanh::lean_box(0), v_x_444_);
        return v___x_452_;
    }
}
pub unsafe fn l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter___boxed(
    mut v_00_u03b1_453_: *mut crate::leanh::LeanObject,
    mut v_n_454_: *mut crate::leanh::LeanObject,
    mut v_motive_455_: *mut crate::leanh::LeanObject,
    mut v_x_456_: *mut crate::leanh::LeanObject,
    mut v_x_457_: *mut crate::leanh::LeanObject,
    mut v_h__1_458_: *mut crate::leanh::LeanObject,
    mut v_h__2_459_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_460_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop_match__1_splitter(
        v_00_u03b1_453_,
        v_n_454_,
        v_motive_455_,
        v_x_456_,
        v_x_457_,
        v_h__1_458_,
        v_h__2_459_,
    );
    crate::leanh::lean_dec(v_x_456_);
    crate::leanh::lean_dec(v_n_454_);
    return v_res_460_;
}
pub unsafe fn l_Fin_foldrM___redArg(
    mut v_inst_461_: *mut crate::leanh::LeanObject,
    mut v_n_462_: *mut crate::leanh::LeanObject,
    mut v_f_463_: *mut crate::leanh::LeanObject,
    mut v_init_464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_465_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg(
        v_inst_461_,
        v_f_463_,
        v_n_462_,
        v_init_464_,
    );
    return v___x_465_;
}
pub unsafe fn l_Fin_foldrM___redArg___boxed(
    mut v_inst_466_: *mut crate::leanh::LeanObject,
    mut v_n_467_: *mut crate::leanh::LeanObject,
    mut v_f_468_: *mut crate::leanh::LeanObject,
    mut v_init_469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_470_ = l_Fin_foldrM___redArg(v_inst_466_, v_n_467_, v_f_468_, v_init_469_);
    crate::leanh::lean_dec(v_n_467_);
    return v_res_470_;
}
pub unsafe fn l_Fin_foldrM(
    mut v_m_471_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_472_: *mut crate::leanh::LeanObject,
    mut v_inst_473_: *mut crate::leanh::LeanObject,
    mut v_n_474_: *mut crate::leanh::LeanObject,
    mut v_f_475_: *mut crate::leanh::LeanObject,
    mut v_init_476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_477_ = l___private_Init_Data_Fin_Fold_0__Fin_foldrM_loop___redArg(
        v_inst_473_,
        v_f_475_,
        v_n_474_,
        v_init_476_,
    );
    return v___x_477_;
}
pub unsafe fn l_Fin_foldrM___boxed(
    mut v_m_478_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_479_: *mut crate::leanh::LeanObject,
    mut v_inst_480_: *mut crate::leanh::LeanObject,
    mut v_n_481_: *mut crate::leanh::LeanObject,
    mut v_f_482_: *mut crate::leanh::LeanObject,
    mut v_init_483_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_484_ = l_Fin_foldrM(
        v_m_478_,
        v_00_u03b1_479_,
        v_inst_480_,
        v_n_481_,
        v_f_482_,
        v_init_483_,
    );
    crate::leanh::lean_dec(v_n_481_);
    return v_res_484_;
}
pub unsafe fn l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter___redArg(
    mut v_x_485_: *mut crate::leanh::LeanObject,
    mut v_x_486_: *mut crate::leanh::LeanObject,
    mut v_h__1_487_: *mut crate::leanh::LeanObject,
    mut v_h__2_488_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_490_: u8 = 0;
    v_zero_489_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_490_ = lean_nat_dec_eq(v_x_485_, v_zero_489_);
    if v_isZero_490_ == 1 {
        let mut v___x_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_488_);
        v___x_491_ = crate::leanh::lean_apply_2(v_h__1_487_, crate::leanh::lean_box(0), v_x_486_);
        return v___x_491_;
    } else {
        let mut v_one_492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_487_);
        v_one_492_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_493_ = lean_nat_sub(v_x_485_, v_one_492_);
        v___x_494_ =
            crate::leanh::lean_apply_3(v_h__2_488_, v_n_493_, crate::leanh::lean_box(0), v_x_486_);
        return v___x_494_;
    }
}
pub unsafe fn l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter___redArg___boxed(
    mut v_x_495_: *mut crate::leanh::LeanObject,
    mut v_x_496_: *mut crate::leanh::LeanObject,
    mut v_h__1_497_: *mut crate::leanh::LeanObject,
    mut v_h__2_498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_499_ = l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter___redArg(
        v_x_495_,
        v_x_496_,
        v_h__1_497_,
        v_h__2_498_,
    );
    crate::leanh::lean_dec(v_x_495_);
    return v_res_499_;
}
pub unsafe fn l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter(
    mut v_00_u03b1_500_: *mut crate::leanh::LeanObject,
    mut v_n_501_: *mut crate::leanh::LeanObject,
    mut v_motive_502_: *mut crate::leanh::LeanObject,
    mut v_x_503_: *mut crate::leanh::LeanObject,
    mut v_x_504_: *mut crate::leanh::LeanObject,
    mut v_x_505_: *mut crate::leanh::LeanObject,
    mut v_h__1_506_: *mut crate::leanh::LeanObject,
    mut v_h__2_507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_509_: u8 = 0;
    v_zero_508_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_509_ = lean_nat_dec_eq(v_x_503_, v_zero_508_);
    if v_isZero_509_ == 1 {
        let mut v___x_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_507_);
        v___x_510_ = crate::leanh::lean_apply_2(v_h__1_506_, crate::leanh::lean_box(0), v_x_505_);
        return v___x_510_;
    } else {
        let mut v_one_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_506_);
        v_one_511_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_512_ = lean_nat_sub(v_x_503_, v_one_511_);
        v___x_513_ =
            crate::leanh::lean_apply_3(v_h__2_507_, v_n_512_, crate::leanh::lean_box(0), v_x_505_);
        return v___x_513_;
    }
}
pub unsafe fn l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter___boxed(
    mut v_00_u03b1_514_: *mut crate::leanh::LeanObject,
    mut v_n_515_: *mut crate::leanh::LeanObject,
    mut v_motive_516_: *mut crate::leanh::LeanObject,
    mut v_x_517_: *mut crate::leanh::LeanObject,
    mut v_x_518_: *mut crate::leanh::LeanObject,
    mut v_x_519_: *mut crate::leanh::LeanObject,
    mut v_h__1_520_: *mut crate::leanh::LeanObject,
    mut v_h__2_521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_522_ = l___private_Init_Data_Fin_Fold_0__Fin_foldr_loop_match__1_splitter(
        v_00_u03b1_514_,
        v_n_515_,
        v_motive_516_,
        v_x_517_,
        v_x_518_,
        v_x_519_,
        v_h__1_520_,
        v_h__2_521_,
    );
    crate::leanh::lean_dec(v_x_517_);
    crate::leanh::lean_dec(v_n_515_);
    return v_res_522_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Fin_Fold(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_Lawful_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
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
    res = runtime_initialize_Init_WFTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Hints(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Fin_Fold(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Fin_Fold(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_Lawful_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
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
    res = initialize_Init_WFTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Hints(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Fold(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Fin_Fold(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Fin_Fold(builtin);
}

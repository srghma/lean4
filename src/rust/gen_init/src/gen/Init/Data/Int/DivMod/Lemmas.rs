// Lean compiler output
// Module: Init.Data.Int.DivMod.Lemmas
// Imports: Init.TacticsExtra Init.Data.Int.DivMod.Basic Init.Data.Nat.Div.Basic Init.NotationExtra Init.ByCases Init.Data.Bool Init.Data.Nat.Div.Lemmas Init.Data.Nat.Lemmas Init.Omega Init.RCases
use crate::ffi::{
    lean_int_dec_eq, lean_int_dec_lt, lean_int_emod, lean_nat_abs, lean_nat_dec_eq, lean_nat_sub,
    lean_nat_to_int,
};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::Int::DivMod::Basic::{
    initialize_Init_Data_Int_DivMod_Basic, runtime_initialize_Init_Data_Int_DivMod_Basic,
};
use crate::r#gen::Init::Data::Nat::Div::Basic::{
    initialize_Init_Data_Nat_Div_Basic, runtime_initialize_Init_Data_Nat_Div_Basic,
};
use crate::r#gen::Init::Data::Nat::Div::Lemmas::{
    initialize_Init_Data_Nat_Div_Lemmas, runtime_initialize_Init_Data_Nat_Div_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::RCases::{initialize_Init_RCases, runtime_initialize_Init_RCases};
use crate::r#gen::Init::TacticsExtra::{
    initialize_Init_TacticsExtra, runtime_initialize_Init_TacticsExtra,
};
static mut l_Int_decidableDvd___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int_decidableDvd___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Int_decidableDvd___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_288_ = leanh::lean_unsigned_to_nat(0);
    v___x_289_ = lean_nat_to_int(v___x_288_);
    return v___x_289_;
}
pub unsafe fn l_Int_decidableDvd(
    mut v_a_290_: *mut leanh::LeanObject,
    mut v_b_291_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: u8 = 0;
    v___x_292_ = lean_int_emod(v_b_291_, v_a_290_);
    v___x_293_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_decidableDvd___closed__0),
        core::ptr::addr_of_mut!(l_Int_decidableDvd___closed__0_once),
        _init_l_Int_decidableDvd___closed__0,
    );
    v___x_294_ = lean_int_dec_eq(v___x_292_, v___x_293_);
    leanh::lean_dec(v___x_292_);
    return v___x_294_;
}
pub unsafe fn l_Int_decidableDvd___boxed(
    mut v_a_295_: *mut leanh::LeanObject,
    mut v_b_296_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_297_: u8 = 0;
    let mut v_r_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_297_ = l_Int_decidableDvd(v_a_295_, v_b_296_);
    leanh::lean_dec(v_b_296_);
    leanh::lean_dec(v_a_295_);
    v_r_298_ = leanh::lean_box((v_res_297_) as usize);
    return v_r_298_;
}
pub unsafe fn _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v_natZero_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_natZero_299_ = leanh::lean_unsigned_to_nat(0);
    v_intZero_300_ = lean_nat_to_int(v_natZero_299_);
    return v_intZero_300_;
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg(
    mut v_x_301_: *mut leanh::LeanObject,
    mut v_x_302_: *mut leanh::LeanObject,
    mut v_h__1_303_: *mut leanh::LeanObject,
    mut v_h__2_304_: *mut leanh::LeanObject,
    mut v_h__3_305_: *mut leanh::LeanObject,
    mut v_h__4_306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_intZero_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_308_: u8 = 0;
    v_intZero_307_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg___closed__0);
    v_isNeg_308_ = lean_int_dec_lt(v_x_301_, v_intZero_307_);
    if v_isNeg_308_ == 0 {
        let mut v_a_309_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_310_: u8 = 0;
        leanh::lean_dec(v_h__4_306_);
        leanh::lean_dec(v_h__3_305_);
        v_a_309_ = lean_nat_abs(v_x_301_);
        v_isNeg_310_ = lean_int_dec_lt(v_x_302_, v_intZero_307_);
        if v_isNeg_310_ == 0 {
            let mut v_a_311_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_312_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_304_);
            v_a_311_ = lean_nat_abs(v_x_302_);
            v___x_312_ = leanh::lean_apply_2(v_h__1_303_, v_a_309_, v_a_311_);
            return v___x_312_;
        } else {
            let mut v_abs_313_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_one_314_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_315_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_303_);
            v_abs_313_ = lean_nat_abs(v_x_302_);
            v_one_314_ = leanh::lean_unsigned_to_nat(1);
            v_a_315_ = lean_nat_sub(v_abs_313_, v_one_314_);
            leanh::lean_dec(v_abs_313_);
            v___x_316_ = leanh::lean_apply_2(v_h__2_304_, v_a_309_, v_a_315_);
            return v___x_316_;
        }
    } else {
        let mut v_abs_317_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_318_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_319_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_320_: u8 = 0;
        leanh::lean_dec(v_h__2_304_);
        leanh::lean_dec(v_h__1_303_);
        v_abs_317_ = lean_nat_abs(v_x_301_);
        v_one_318_ = leanh::lean_unsigned_to_nat(1);
        v_a_319_ = lean_nat_sub(v_abs_317_, v_one_318_);
        leanh::lean_dec(v_abs_317_);
        v_isNeg_320_ = lean_int_dec_lt(v_x_302_, v_intZero_307_);
        if v_isNeg_320_ == 0 {
            let mut v_a_321_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_306_);
            v_a_321_ = lean_nat_abs(v_x_302_);
            v___x_322_ = leanh::lean_apply_2(v_h__3_305_, v_a_319_, v_a_321_);
            return v___x_322_;
        } else {
            let mut v_abs_323_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_324_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_305_);
            v_abs_323_ = lean_nat_abs(v_x_302_);
            v_a_324_ = lean_nat_sub(v_abs_323_, v_one_318_);
            leanh::lean_dec(v_abs_323_);
            v___x_325_ = leanh::lean_apply_2(v_h__4_306_, v_a_319_, v_a_324_);
            return v___x_325_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg___boxed(
    mut v_x_326_: *mut leanh::LeanObject,
    mut v_x_327_: *mut leanh::LeanObject,
    mut v_h__1_328_: *mut leanh::LeanObject,
    mut v_h__2_329_: *mut leanh::LeanObject,
    mut v_h__3_330_: *mut leanh::LeanObject,
    mut v_h__4_331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_332_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg(
        v_x_326_,
        v_x_327_,
        v_h__1_328_,
        v_h__2_329_,
        v_h__3_330_,
        v_h__4_331_,
    );
    leanh::lean_dec(v_x_327_);
    leanh::lean_dec(v_x_326_);
    return v_res_332_;
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter(
    mut v_motive_333_: *mut leanh::LeanObject,
    mut v_x_334_: *mut leanh::LeanObject,
    mut v_x_335_: *mut leanh::LeanObject,
    mut v_h__1_336_: *mut leanh::LeanObject,
    mut v_h__2_337_: *mut leanh::LeanObject,
    mut v_h__3_338_: *mut leanh::LeanObject,
    mut v_h__4_339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_intZero_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_341_: u8 = 0;
    v_intZero_340_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___redArg___closed__0);
    v_isNeg_341_ = lean_int_dec_lt(v_x_334_, v_intZero_340_);
    if v_isNeg_341_ == 0 {
        let mut v_a_342_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_343_: u8 = 0;
        leanh::lean_dec(v_h__4_339_);
        leanh::lean_dec(v_h__3_338_);
        v_a_342_ = lean_nat_abs(v_x_334_);
        v_isNeg_343_ = lean_int_dec_lt(v_x_335_, v_intZero_340_);
        if v_isNeg_343_ == 0 {
            let mut v_a_344_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_337_);
            v_a_344_ = lean_nat_abs(v_x_335_);
            v___x_345_ = leanh::lean_apply_2(v_h__1_336_, v_a_342_, v_a_344_);
            return v___x_345_;
        } else {
            let mut v_abs_346_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_one_347_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_348_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_336_);
            v_abs_346_ = lean_nat_abs(v_x_335_);
            v_one_347_ = leanh::lean_unsigned_to_nat(1);
            v_a_348_ = lean_nat_sub(v_abs_346_, v_one_347_);
            leanh::lean_dec(v_abs_346_);
            v___x_349_ = leanh::lean_apply_2(v_h__2_337_, v_a_342_, v_a_348_);
            return v___x_349_;
        }
    } else {
        let mut v_abs_350_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_351_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_352_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_353_: u8 = 0;
        leanh::lean_dec(v_h__2_337_);
        leanh::lean_dec(v_h__1_336_);
        v_abs_350_ = lean_nat_abs(v_x_334_);
        v_one_351_ = leanh::lean_unsigned_to_nat(1);
        v_a_352_ = lean_nat_sub(v_abs_350_, v_one_351_);
        leanh::lean_dec(v_abs_350_);
        v_isNeg_353_ = lean_int_dec_lt(v_x_335_, v_intZero_340_);
        if v_isNeg_353_ == 0 {
            let mut v_a_354_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_339_);
            v_a_354_ = lean_nat_abs(v_x_335_);
            v___x_355_ = leanh::lean_apply_2(v_h__3_338_, v_a_352_, v_a_354_);
            return v___x_355_;
        } else {
            let mut v_abs_356_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_357_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_358_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_338_);
            v_abs_356_ = lean_nat_abs(v_x_335_);
            v_a_357_ = lean_nat_sub(v_abs_356_, v_one_351_);
            leanh::lean_dec(v_abs_356_);
            v___x_358_ = leanh::lean_apply_2(v_h__4_339_, v_a_352_, v_a_357_);
            return v___x_358_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter___boxed(
    mut v_motive_359_: *mut leanh::LeanObject,
    mut v_x_360_: *mut leanh::LeanObject,
    mut v_x_361_: *mut leanh::LeanObject,
    mut v_h__1_362_: *mut leanh::LeanObject,
    mut v_h__2_363_: *mut leanh::LeanObject,
    mut v_h__3_364_: *mut leanh::LeanObject,
    mut v_h__4_365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_366_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_tdiv_match__1_splitter(
        v_motive_359_,
        v_x_360_,
        v_x_361_,
        v_h__1_362_,
        v_h__2_363_,
        v_h__3_364_,
        v_h__4_365_,
    );
    leanh::lean_dec(v_x_361_);
    leanh::lean_dec(v_x_360_);
    return v_res_366_;
}
pub unsafe fn _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v_natZero_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_natZero_367_ = leanh::lean_unsigned_to_nat(0);
    v_intZero_368_ = lean_nat_to_int(v_natZero_367_);
    return v_intZero_368_;
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg(
    mut v_x_369_: *mut leanh::LeanObject,
    mut v_x_370_: *mut leanh::LeanObject,
    mut v_h__1_371_: *mut leanh::LeanObject,
    mut v_h__2_372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_intZero_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_374_: u8 = 0;
    v_intZero_373_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0);
    v_isNeg_374_ = lean_int_dec_lt(v_x_369_, v_intZero_373_);
    if v_isNeg_374_ == 0 {
        let mut v_a_375_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_372_);
        v_a_375_ = lean_nat_abs(v_x_369_);
        v___x_376_ = leanh::lean_apply_2(v_h__1_371_, v_a_375_, v_x_370_);
        return v___x_376_;
    } else {
        let mut v_abs_377_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_378_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_379_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_371_);
        v_abs_377_ = lean_nat_abs(v_x_369_);
        v_one_378_ = leanh::lean_unsigned_to_nat(1);
        v_a_379_ = lean_nat_sub(v_abs_377_, v_one_378_);
        leanh::lean_dec(v_abs_377_);
        v___x_380_ = leanh::lean_apply_2(v_h__2_372_, v_a_379_, v_x_370_);
        return v___x_380_;
    }
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___boxed(
    mut v_x_381_: *mut leanh::LeanObject,
    mut v_x_382_: *mut leanh::LeanObject,
    mut v_h__1_383_: *mut leanh::LeanObject,
    mut v_h__2_384_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_385_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg(
        v_x_381_,
        v_x_382_,
        v_h__1_383_,
        v_h__2_384_,
    );
    leanh::lean_dec(v_x_381_);
    return v_res_385_;
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter(
    mut v_motive_386_: *mut leanh::LeanObject,
    mut v_x_387_: *mut leanh::LeanObject,
    mut v_x_388_: *mut leanh::LeanObject,
    mut v_h__1_389_: *mut leanh::LeanObject,
    mut v_h__2_390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_intZero_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_392_: u8 = 0;
    v_intZero_391_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___redArg___closed__0);
    v_isNeg_392_ = lean_int_dec_lt(v_x_387_, v_intZero_391_);
    if v_isNeg_392_ == 0 {
        let mut v_a_393_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_390_);
        v_a_393_ = lean_nat_abs(v_x_387_);
        v___x_394_ = leanh::lean_apply_2(v_h__1_389_, v_a_393_, v_x_388_);
        return v___x_394_;
    } else {
        let mut v_abs_395_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_396_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_397_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_389_);
        v_abs_395_ = lean_nat_abs(v_x_387_);
        v_one_396_ = leanh::lean_unsigned_to_nat(1);
        v_a_397_ = lean_nat_sub(v_abs_395_, v_one_396_);
        leanh::lean_dec(v_abs_395_);
        v___x_398_ = leanh::lean_apply_2(v_h__2_390_, v_a_397_, v_x_388_);
        return v___x_398_;
    }
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter___boxed(
    mut v_motive_399_: *mut leanh::LeanObject,
    mut v_x_400_: *mut leanh::LeanObject,
    mut v_x_401_: *mut leanh::LeanObject,
    mut v_h__1_402_: *mut leanh::LeanObject,
    mut v_h__2_403_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_404_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_emod_match__1_splitter(
        v_motive_399_,
        v_x_400_,
        v_x_401_,
        v_h__1_402_,
        v_h__2_403_,
    );
    leanh::lean_dec(v_x_400_);
    return v_res_404_;
}
pub unsafe fn _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v_natZero_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_natZero_405_ = leanh::lean_unsigned_to_nat(0);
    v_intZero_406_ = lean_nat_to_int(v_natZero_405_);
    return v_intZero_406_;
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg(
    mut v_x_407_: *mut leanh::LeanObject,
    mut v_x_408_: *mut leanh::LeanObject,
    mut v_h__1_409_: *mut leanh::LeanObject,
    mut v_h__2_410_: *mut leanh::LeanObject,
    mut v_h__3_411_: *mut leanh::LeanObject,
    mut v_h__4_412_: *mut leanh::LeanObject,
    mut v_h__5_413_: *mut leanh::LeanObject,
    mut v_h__6_414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_natZero_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_417_: u8 = 0;
    v_natZero_415_ = leanh::lean_unsigned_to_nat(0);
    v_intZero_416_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0);
    v_isNeg_417_ = lean_int_dec_lt(v_x_407_, v_intZero_416_);
    if v_isNeg_417_ == 0 {
        let mut v_a_418_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_419_: u8 = 0;
        leanh::lean_dec(v_h__6_414_);
        leanh::lean_dec(v_h__5_413_);
        leanh::lean_dec(v_h__4_412_);
        v_a_418_ = lean_nat_abs(v_x_407_);
        v_isZero_419_ = lean_nat_dec_eq(v_a_418_, v_natZero_415_);
        if v_isZero_419_ == 1 {
            let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_a_418_);
            leanh::lean_dec(v_h__3_411_);
            leanh::lean_dec(v_h__2_410_);
            v___x_420_ = leanh::lean_apply_1(v_h__1_409_, v_x_408_);
            return v___x_420_;
        } else {
            let mut v_isNeg_421_: u8 = 0;
            leanh::lean_dec(v_h__1_409_);
            v_isNeg_421_ = lean_int_dec_lt(v_x_408_, v_intZero_416_);
            if v_isNeg_421_ == 0 {
                let mut v_a_422_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__3_411_);
                v_a_422_ = lean_nat_abs(v_x_408_);
                leanh::lean_dec(v_x_408_);
                v___x_423_ = leanh::lean_apply_3(
                    v_h__2_410_,
                    v_a_418_,
                    v_a_422_,
                    leanh::lean_box(0),
                );
                return v___x_423_;
            } else {
                let mut v_one_424_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_n_425_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_abs_426_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_a_427_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__2_410_);
                v_one_424_ = leanh::lean_unsigned_to_nat(1);
                v_n_425_ = lean_nat_sub(v_a_418_, v_one_424_);
                leanh::lean_dec(v_a_418_);
                v_abs_426_ = lean_nat_abs(v_x_408_);
                leanh::lean_dec(v_x_408_);
                v_a_427_ = lean_nat_sub(v_abs_426_, v_one_424_);
                leanh::lean_dec(v_abs_426_);
                v___x_428_ = leanh::lean_apply_2(v_h__3_411_, v_n_425_, v_a_427_);
                return v___x_428_;
            }
        }
    } else {
        let mut v_abs_429_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_430_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_431_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_432_: u8 = 0;
        leanh::lean_dec(v_h__3_411_);
        leanh::lean_dec(v_h__2_410_);
        leanh::lean_dec(v_h__1_409_);
        v_abs_429_ = lean_nat_abs(v_x_407_);
        v_one_430_ = leanh::lean_unsigned_to_nat(1);
        v_a_431_ = lean_nat_sub(v_abs_429_, v_one_430_);
        leanh::lean_dec(v_abs_429_);
        v_isNeg_432_ = lean_int_dec_lt(v_x_408_, v_intZero_416_);
        if v_isNeg_432_ == 0 {
            let mut v_a_433_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_isZero_434_: u8 = 0;
            leanh::lean_dec(v_h__6_414_);
            v_a_433_ = lean_nat_abs(v_x_408_);
            leanh::lean_dec(v_x_408_);
            v_isZero_434_ = lean_nat_dec_eq(v_a_433_, v_natZero_415_);
            if v_isZero_434_ == 1 {
                let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_a_433_);
                leanh::lean_dec(v_h__5_413_);
                v___x_435_ = leanh::lean_apply_1(v_h__4_412_, v_a_431_);
                return v___x_435_;
            } else {
                let mut v_n_436_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__4_412_);
                v_n_436_ = lean_nat_sub(v_a_433_, v_one_430_);
                leanh::lean_dec(v_a_433_);
                v___x_437_ = leanh::lean_apply_2(v_h__5_413_, v_a_431_, v_n_436_);
                return v___x_437_;
            }
        } else {
            let mut v_abs_438_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_439_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__5_413_);
            leanh::lean_dec(v_h__4_412_);
            v_abs_438_ = lean_nat_abs(v_x_408_);
            leanh::lean_dec(v_x_408_);
            v_a_439_ = lean_nat_sub(v_abs_438_, v_one_430_);
            leanh::lean_dec(v_abs_438_);
            v___x_440_ = leanh::lean_apply_2(v_h__6_414_, v_a_431_, v_a_439_);
            return v___x_440_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___boxed(
    mut v_x_441_: *mut leanh::LeanObject,
    mut v_x_442_: *mut leanh::LeanObject,
    mut v_h__1_443_: *mut leanh::LeanObject,
    mut v_h__2_444_: *mut leanh::LeanObject,
    mut v_h__3_445_: *mut leanh::LeanObject,
    mut v_h__4_446_: *mut leanh::LeanObject,
    mut v_h__5_447_: *mut leanh::LeanObject,
    mut v_h__6_448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_449_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg(
        v_x_441_,
        v_x_442_,
        v_h__1_443_,
        v_h__2_444_,
        v_h__3_445_,
        v_h__4_446_,
        v_h__5_447_,
        v_h__6_448_,
    );
    leanh::lean_dec(v_x_441_);
    return v_res_449_;
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter(
    mut v_motive_450_: *mut leanh::LeanObject,
    mut v_x_451_: *mut leanh::LeanObject,
    mut v_x_452_: *mut leanh::LeanObject,
    mut v_h__1_453_: *mut leanh::LeanObject,
    mut v_h__2_454_: *mut leanh::LeanObject,
    mut v_h__3_455_: *mut leanh::LeanObject,
    mut v_h__4_456_: *mut leanh::LeanObject,
    mut v_h__5_457_: *mut leanh::LeanObject,
    mut v_h__6_458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_natZero_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_461_: u8 = 0;
    v_natZero_459_ = leanh::lean_unsigned_to_nat(0);
    v_intZero_460_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___redArg___closed__0);
    v_isNeg_461_ = lean_int_dec_lt(v_x_451_, v_intZero_460_);
    if v_isNeg_461_ == 0 {
        let mut v_a_462_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_463_: u8 = 0;
        leanh::lean_dec(v_h__6_458_);
        leanh::lean_dec(v_h__5_457_);
        leanh::lean_dec(v_h__4_456_);
        v_a_462_ = lean_nat_abs(v_x_451_);
        v_isZero_463_ = lean_nat_dec_eq(v_a_462_, v_natZero_459_);
        if v_isZero_463_ == 1 {
            let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_a_462_);
            leanh::lean_dec(v_h__3_455_);
            leanh::lean_dec(v_h__2_454_);
            v___x_464_ = leanh::lean_apply_1(v_h__1_453_, v_x_452_);
            return v___x_464_;
        } else {
            let mut v_isNeg_465_: u8 = 0;
            leanh::lean_dec(v_h__1_453_);
            v_isNeg_465_ = lean_int_dec_lt(v_x_452_, v_intZero_460_);
            if v_isNeg_465_ == 0 {
                let mut v_a_466_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__3_455_);
                v_a_466_ = lean_nat_abs(v_x_452_);
                leanh::lean_dec(v_x_452_);
                v___x_467_ = leanh::lean_apply_3(
                    v_h__2_454_,
                    v_a_462_,
                    v_a_466_,
                    leanh::lean_box(0),
                );
                return v___x_467_;
            } else {
                let mut v_one_468_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_n_469_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_abs_470_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_a_471_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__2_454_);
                v_one_468_ = leanh::lean_unsigned_to_nat(1);
                v_n_469_ = lean_nat_sub(v_a_462_, v_one_468_);
                leanh::lean_dec(v_a_462_);
                v_abs_470_ = lean_nat_abs(v_x_452_);
                leanh::lean_dec(v_x_452_);
                v_a_471_ = lean_nat_sub(v_abs_470_, v_one_468_);
                leanh::lean_dec(v_abs_470_);
                v___x_472_ = leanh::lean_apply_2(v_h__3_455_, v_n_469_, v_a_471_);
                return v___x_472_;
            }
        }
    } else {
        let mut v_abs_473_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_474_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_475_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_476_: u8 = 0;
        leanh::lean_dec(v_h__3_455_);
        leanh::lean_dec(v_h__2_454_);
        leanh::lean_dec(v_h__1_453_);
        v_abs_473_ = lean_nat_abs(v_x_451_);
        v_one_474_ = leanh::lean_unsigned_to_nat(1);
        v_a_475_ = lean_nat_sub(v_abs_473_, v_one_474_);
        leanh::lean_dec(v_abs_473_);
        v_isNeg_476_ = lean_int_dec_lt(v_x_452_, v_intZero_460_);
        if v_isNeg_476_ == 0 {
            let mut v_a_477_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_isZero_478_: u8 = 0;
            leanh::lean_dec(v_h__6_458_);
            v_a_477_ = lean_nat_abs(v_x_452_);
            leanh::lean_dec(v_x_452_);
            v_isZero_478_ = lean_nat_dec_eq(v_a_477_, v_natZero_459_);
            if v_isZero_478_ == 1 {
                let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_a_477_);
                leanh::lean_dec(v_h__5_457_);
                v___x_479_ = leanh::lean_apply_1(v_h__4_456_, v_a_475_);
                return v___x_479_;
            } else {
                let mut v_n_480_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__4_456_);
                v_n_480_ = lean_nat_sub(v_a_477_, v_one_474_);
                leanh::lean_dec(v_a_477_);
                v___x_481_ = leanh::lean_apply_2(v_h__5_457_, v_a_475_, v_n_480_);
                return v___x_481_;
            }
        } else {
            let mut v_abs_482_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_483_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__5_457_);
            leanh::lean_dec(v_h__4_456_);
            v_abs_482_ = lean_nat_abs(v_x_452_);
            leanh::lean_dec(v_x_452_);
            v_a_483_ = lean_nat_sub(v_abs_482_, v_one_474_);
            leanh::lean_dec(v_abs_482_);
            v___x_484_ = leanh::lean_apply_2(v_h__6_458_, v_a_475_, v_a_483_);
            return v___x_484_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter___boxed(
    mut v_motive_485_: *mut leanh::LeanObject,
    mut v_x_486_: *mut leanh::LeanObject,
    mut v_x_487_: *mut leanh::LeanObject,
    mut v_h__1_488_: *mut leanh::LeanObject,
    mut v_h__2_489_: *mut leanh::LeanObject,
    mut v_h__3_490_: *mut leanh::LeanObject,
    mut v_h__4_491_: *mut leanh::LeanObject,
    mut v_h__5_492_: *mut leanh::LeanObject,
    mut v_h__6_493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_494_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fdiv_match__1_splitter(
        v_motive_485_,
        v_x_486_,
        v_x_487_,
        v_h__1_488_,
        v_h__2_489_,
        v_h__3_490_,
        v_h__4_491_,
        v_h__5_492_,
        v_h__6_493_,
    );
    leanh::lean_dec(v_x_486_);
    return v_res_494_;
}
pub unsafe fn _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v_natZero_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_natZero_495_ = leanh::lean_unsigned_to_nat(0);
    v_intZero_496_ = lean_nat_to_int(v_natZero_495_);
    return v_intZero_496_;
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg(
    mut v_x_497_: *mut leanh::LeanObject,
    mut v_x_498_: *mut leanh::LeanObject,
    mut v_h__1_499_: *mut leanh::LeanObject,
    mut v_h__2_500_: *mut leanh::LeanObject,
    mut v_h__3_501_: *mut leanh::LeanObject,
    mut v_h__4_502_: *mut leanh::LeanObject,
    mut v_h__5_503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_natZero_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_506_: u8 = 0;
    v_natZero_504_ = leanh::lean_unsigned_to_nat(0);
    v_intZero_505_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0);
    v_isNeg_506_ = lean_int_dec_lt(v_x_497_, v_intZero_505_);
    if v_isNeg_506_ == 0 {
        let mut v_a_507_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_508_: u8 = 0;
        leanh::lean_dec(v_h__5_503_);
        leanh::lean_dec(v_h__4_502_);
        v_a_507_ = lean_nat_abs(v_x_497_);
        v_isZero_508_ = lean_nat_dec_eq(v_a_507_, v_natZero_504_);
        if v_isZero_508_ == 1 {
            let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_a_507_);
            leanh::lean_dec(v_h__3_501_);
            leanh::lean_dec(v_h__2_500_);
            v___x_509_ = leanh::lean_apply_1(v_h__1_499_, v_x_498_);
            return v___x_509_;
        } else {
            let mut v_isNeg_510_: u8 = 0;
            leanh::lean_dec(v_h__1_499_);
            v_isNeg_510_ = lean_int_dec_lt(v_x_498_, v_intZero_505_);
            if v_isNeg_510_ == 0 {
                let mut v_a_511_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_512_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__3_501_);
                v_a_511_ = lean_nat_abs(v_x_498_);
                leanh::lean_dec(v_x_498_);
                v___x_512_ = leanh::lean_apply_3(
                    v_h__2_500_,
                    v_a_507_,
                    v_a_511_,
                    leanh::lean_box(0),
                );
                return v___x_512_;
            } else {
                let mut v_one_513_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_n_514_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_abs_515_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_a_516_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_517_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__2_500_);
                v_one_513_ = leanh::lean_unsigned_to_nat(1);
                v_n_514_ = lean_nat_sub(v_a_507_, v_one_513_);
                leanh::lean_dec(v_a_507_);
                v_abs_515_ = lean_nat_abs(v_x_498_);
                leanh::lean_dec(v_x_498_);
                v_a_516_ = lean_nat_sub(v_abs_515_, v_one_513_);
                leanh::lean_dec(v_abs_515_);
                v___x_517_ = leanh::lean_apply_2(v_h__3_501_, v_n_514_, v_a_516_);
                return v___x_517_;
            }
        }
    } else {
        let mut v_abs_518_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_519_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_520_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_521_: u8 = 0;
        leanh::lean_dec(v_h__3_501_);
        leanh::lean_dec(v_h__2_500_);
        leanh::lean_dec(v_h__1_499_);
        v_abs_518_ = lean_nat_abs(v_x_497_);
        v_one_519_ = leanh::lean_unsigned_to_nat(1);
        v_a_520_ = lean_nat_sub(v_abs_518_, v_one_519_);
        leanh::lean_dec(v_abs_518_);
        v_isNeg_521_ = lean_int_dec_lt(v_x_498_, v_intZero_505_);
        if v_isNeg_521_ == 0 {
            let mut v_a_522_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__5_503_);
            v_a_522_ = lean_nat_abs(v_x_498_);
            leanh::lean_dec(v_x_498_);
            v___x_523_ = leanh::lean_apply_2(v_h__4_502_, v_a_520_, v_a_522_);
            return v___x_523_;
        } else {
            let mut v_abs_524_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_525_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_502_);
            v_abs_524_ = lean_nat_abs(v_x_498_);
            leanh::lean_dec(v_x_498_);
            v_a_525_ = lean_nat_sub(v_abs_524_, v_one_519_);
            leanh::lean_dec(v_abs_524_);
            v___x_526_ = leanh::lean_apply_2(v_h__5_503_, v_a_520_, v_a_525_);
            return v___x_526_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___boxed(
    mut v_x_527_: *mut leanh::LeanObject,
    mut v_x_528_: *mut leanh::LeanObject,
    mut v_h__1_529_: *mut leanh::LeanObject,
    mut v_h__2_530_: *mut leanh::LeanObject,
    mut v_h__3_531_: *mut leanh::LeanObject,
    mut v_h__4_532_: *mut leanh::LeanObject,
    mut v_h__5_533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_534_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg(
        v_x_527_,
        v_x_528_,
        v_h__1_529_,
        v_h__2_530_,
        v_h__3_531_,
        v_h__4_532_,
        v_h__5_533_,
    );
    leanh::lean_dec(v_x_527_);
    return v_res_534_;
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter(
    mut v_motive_535_: *mut leanh::LeanObject,
    mut v_x_536_: *mut leanh::LeanObject,
    mut v_x_537_: *mut leanh::LeanObject,
    mut v_h__1_538_: *mut leanh::LeanObject,
    mut v_h__2_539_: *mut leanh::LeanObject,
    mut v_h__3_540_: *mut leanh::LeanObject,
    mut v_h__4_541_: *mut leanh::LeanObject,
    mut v_h__5_542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_natZero_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_545_: u8 = 0;
    v_natZero_543_ = leanh::lean_unsigned_to_nat(0);
    v_intZero_544_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___redArg___closed__0);
    v_isNeg_545_ = lean_int_dec_lt(v_x_536_, v_intZero_544_);
    if v_isNeg_545_ == 0 {
        let mut v_a_546_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_547_: u8 = 0;
        leanh::lean_dec(v_h__5_542_);
        leanh::lean_dec(v_h__4_541_);
        v_a_546_ = lean_nat_abs(v_x_536_);
        v_isZero_547_ = lean_nat_dec_eq(v_a_546_, v_natZero_543_);
        if v_isZero_547_ == 1 {
            let mut v___x_548_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_a_546_);
            leanh::lean_dec(v_h__3_540_);
            leanh::lean_dec(v_h__2_539_);
            v___x_548_ = leanh::lean_apply_1(v_h__1_538_, v_x_537_);
            return v___x_548_;
        } else {
            let mut v_isNeg_549_: u8 = 0;
            leanh::lean_dec(v_h__1_538_);
            v_isNeg_549_ = lean_int_dec_lt(v_x_537_, v_intZero_544_);
            if v_isNeg_549_ == 0 {
                let mut v_a_550_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_551_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__3_540_);
                v_a_550_ = lean_nat_abs(v_x_537_);
                leanh::lean_dec(v_x_537_);
                v___x_551_ = leanh::lean_apply_3(
                    v_h__2_539_,
                    v_a_546_,
                    v_a_550_,
                    leanh::lean_box(0),
                );
                return v___x_551_;
            } else {
                let mut v_one_552_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_n_553_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_abs_554_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_a_555_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__2_539_);
                v_one_552_ = leanh::lean_unsigned_to_nat(1);
                v_n_553_ = lean_nat_sub(v_a_546_, v_one_552_);
                leanh::lean_dec(v_a_546_);
                v_abs_554_ = lean_nat_abs(v_x_537_);
                leanh::lean_dec(v_x_537_);
                v_a_555_ = lean_nat_sub(v_abs_554_, v_one_552_);
                leanh::lean_dec(v_abs_554_);
                v___x_556_ = leanh::lean_apply_2(v_h__3_540_, v_n_553_, v_a_555_);
                return v___x_556_;
            }
        }
    } else {
        let mut v_abs_557_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_558_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_559_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_560_: u8 = 0;
        leanh::lean_dec(v_h__3_540_);
        leanh::lean_dec(v_h__2_539_);
        leanh::lean_dec(v_h__1_538_);
        v_abs_557_ = lean_nat_abs(v_x_536_);
        v_one_558_ = leanh::lean_unsigned_to_nat(1);
        v_a_559_ = lean_nat_sub(v_abs_557_, v_one_558_);
        leanh::lean_dec(v_abs_557_);
        v_isNeg_560_ = lean_int_dec_lt(v_x_537_, v_intZero_544_);
        if v_isNeg_560_ == 0 {
            let mut v_a_561_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__5_542_);
            v_a_561_ = lean_nat_abs(v_x_537_);
            leanh::lean_dec(v_x_537_);
            v___x_562_ = leanh::lean_apply_2(v_h__4_541_, v_a_559_, v_a_561_);
            return v___x_562_;
        } else {
            let mut v_abs_563_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_564_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_541_);
            v_abs_563_ = lean_nat_abs(v_x_537_);
            leanh::lean_dec(v_x_537_);
            v_a_564_ = lean_nat_sub(v_abs_563_, v_one_558_);
            leanh::lean_dec(v_abs_563_);
            v___x_565_ = leanh::lean_apply_2(v_h__5_542_, v_a_559_, v_a_564_);
            return v___x_565_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter___boxed(
    mut v_motive_566_: *mut leanh::LeanObject,
    mut v_x_567_: *mut leanh::LeanObject,
    mut v_x_568_: *mut leanh::LeanObject,
    mut v_h__1_569_: *mut leanh::LeanObject,
    mut v_h__2_570_: *mut leanh::LeanObject,
    mut v_h__3_571_: *mut leanh::LeanObject,
    mut v_h__4_572_: *mut leanh::LeanObject,
    mut v_h__5_573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_574_ = l___private_Init_Data_Int_DivMod_Lemmas_0__Int_fmod_match__1_splitter(
        v_motive_566_,
        v_x_567_,
        v_x_568_,
        v_h__1_569_,
        v_h__2_570_,
        v_h__3_571_,
        v_h__4_572_,
        v_h__5_573_,
    );
    leanh::lean_dec(v_x_567_);
    return v_res_574_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Int_DivMod_Lemmas(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_TacticsExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_RCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Int_DivMod_Lemmas(
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
pub unsafe fn initialize_Init_Data_Int_DivMod_Lemmas(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_TacticsExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Div_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Div_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_RCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Int_DivMod_Lemmas(builtin);
}
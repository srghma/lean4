// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.Let
// Imports: Lean.Meta.Sym.DSimp.DSimpM Lean.Meta.Sym.AbstractS Lean.Meta.Sym.InstantiateS
use crate::ffi::{lean_array_push, lean_sym_dsimp};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp, l_Lean_Meta_mkLetFVars,
};
use crate::r#gen::Lean::Meta::Sym::AbstractS::{
    initialize_Lean_Meta_Sym_AbstractS, runtime_initialize_Lean_Meta_Sym_AbstractS,
};
use crate::r#gen::Lean::Meta::Sym::DSimp::DSimpM::{
    initialize_Lean_Meta_Sym_DSimp_DSimpM, runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM,
};
use crate::r#gen::Lean::Meta::Sym::InstantiateS::{
    initialize_Lean_Meta_Sym_InstantiateS, l_Lean_Meta_Sym_instantiateRevBetaS___redArg,
    runtime_initialize_Lean_Meta_Sym_InstantiateS,
};
pub static l_Lean_Meta_Sym_DSimp_dsimpLet___closed__0_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_Sym_DSimp_dsimpLet___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_dsimpLet___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0(
    mut v_k_348_: *mut leanh::LeanObject,
    mut v___y_349_: *mut leanh::LeanObject,
    mut v___y_350_: *mut leanh::LeanObject,
    mut v___y_351_: *mut leanh::LeanObject,
    mut v___y_352_: *mut leanh::LeanObject,
    mut v___y_353_: *mut leanh::LeanObject,
    mut v_b_354_: *mut leanh::LeanObject,
    mut v___y_355_: *mut leanh::LeanObject,
    mut v___y_356_: *mut leanh::LeanObject,
    mut v___y_357_: *mut leanh::LeanObject,
    mut v___y_358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_358_);
    leanh::lean_inc_ref(v___y_357_);
    leanh::lean_inc(v___y_356_);
    leanh::lean_inc_ref(v___y_355_);
    leanh::lean_inc(v___y_353_);
    leanh::lean_inc_ref(v___y_352_);
    leanh::lean_inc(v___y_351_);
    leanh::lean_inc(v___y_350_);
    leanh::lean_inc(v___y_349_);
    v___x_360_ = leanh::lean_apply_11(
        v_k_348_,
        v_b_354_,
        v___y_349_,
        v___y_350_,
        v___y_351_,
        v___y_352_,
        v___y_353_,
        v___y_355_,
        v___y_356_,
        v___y_357_,
        v___y_358_,
        leanh::lean_box(0),
    );
    return v___x_360_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0___boxed(
    mut v_k_361_: *mut leanh::LeanObject,
    mut v___y_362_: *mut leanh::LeanObject,
    mut v___y_363_: *mut leanh::LeanObject,
    mut v___y_364_: *mut leanh::LeanObject,
    mut v___y_365_: *mut leanh::LeanObject,
    mut v___y_366_: *mut leanh::LeanObject,
    mut v_b_367_: *mut leanh::LeanObject,
    mut v___y_368_: *mut leanh::LeanObject,
    mut v___y_369_: *mut leanh::LeanObject,
    mut v___y_370_: *mut leanh::LeanObject,
    mut v___y_371_: *mut leanh::LeanObject,
    mut v___y_372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_373_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0(v_k_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v_b_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
    leanh::lean_dec(v___y_371_);
    leanh::lean_dec_ref(v___y_370_);
    leanh::lean_dec(v___y_369_);
    leanh::lean_dec_ref(v___y_368_);
    leanh::lean_dec(v___y_366_);
    leanh::lean_dec_ref(v___y_365_);
    leanh::lean_dec(v___y_364_);
    leanh::lean_dec(v___y_363_);
    leanh::lean_dec(v___y_362_);
    return v_res_373_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(
    mut v_name_374_: *mut leanh::LeanObject,
    mut v_type_375_: *mut leanh::LeanObject,
    mut v_val_376_: *mut leanh::LeanObject,
    mut v_k_377_: *mut leanh::LeanObject,
    mut v_nondep_378_: u8,
    mut v_kind_379_: u8,
    mut v___y_380_: *mut leanh::LeanObject,
    mut v___y_381_: *mut leanh::LeanObject,
    mut v___y_382_: *mut leanh::LeanObject,
    mut v___y_383_: *mut leanh::LeanObject,
    mut v___y_384_: *mut leanh::LeanObject,
    mut v___y_385_: *mut leanh::LeanObject,
    mut v___y_386_: *mut leanh::LeanObject,
    mut v___y_387_: *mut leanh::LeanObject,
    mut v___y_388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_395_: u8 = 0;
    let mut v___x_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_399_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_384_);
                leanh::lean_inc_ref(v___y_383_);
                leanh::lean_inc(v___y_382_);
                leanh::lean_inc(v___y_381_);
                leanh::lean_inc(v___y_380_);
                v___f_390_ = leanh::lean_alloc_closure(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 12, 6);
                leanh::lean_closure_set(v___f_390_, 0, v_k_377_);
                leanh::lean_closure_set(v___f_390_, 1, v___y_380_);
                leanh::lean_closure_set(v___f_390_, 2, v___y_381_);
                leanh::lean_closure_set(v___f_390_, 3, v___y_382_);
                leanh::lean_closure_set(v___f_390_, 4, v___y_383_);
                leanh::lean_closure_set(v___f_390_, 5, v___y_384_);
                v___x_391_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    leanh::lean_box(0),
                    v_name_374_,
                    v_type_375_,
                    v_val_376_,
                    v___f_390_,
                    v_nondep_378_,
                    v_kind_379_,
                    v___y_385_,
                    v___y_386_,
                    v___y_387_,
                    v___y_388_,
                );
                if leanh::lean_obj_tag(v___x_391_) == 0 {
                    return v___x_391_;
                } else {
                    v_a_392_ = leanh::lean_ctor_get(v___x_391_, 0);
                    v_isSharedCheck_399_ = (!leanh::lean_is_exclusive(v___x_391_)) as u8;
                    if v_isSharedCheck_399_ == 0 {
                        v___x_394_ = v___x_391_;
                        v_isShared_395_ = v_isSharedCheck_399_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_392_);
                        leanh::lean_dec(v___x_391_);
                        v___x_394_ = leanh::lean_box(0);
                        v_isShared_395_ = v_isSharedCheck_399_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_395_ == 0 {
                    v___x_397_ = v___x_394_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_398_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
                    v___x_397_ = v_reuseFailAlloc_398_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_397_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___boxed(
    mut v_name_400_: *mut leanh::LeanObject,
    mut v_type_401_: *mut leanh::LeanObject,
    mut v_val_402_: *mut leanh::LeanObject,
    mut v_k_403_: *mut leanh::LeanObject,
    mut v_nondep_404_: *mut leanh::LeanObject,
    mut v_kind_405_: *mut leanh::LeanObject,
    mut v___y_406_: *mut leanh::LeanObject,
    mut v___y_407_: *mut leanh::LeanObject,
    mut v___y_408_: *mut leanh::LeanObject,
    mut v___y_409_: *mut leanh::LeanObject,
    mut v___y_410_: *mut leanh::LeanObject,
    mut v___y_411_: *mut leanh::LeanObject,
    mut v___y_412_: *mut leanh::LeanObject,
    mut v___y_413_: *mut leanh::LeanObject,
    mut v___y_414_: *mut leanh::LeanObject,
    mut v___y_415_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_nondep_boxed_416_: u8 = 0;
    let mut v_kind_boxed_417_: u8 = 0;
    let mut v_res_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_416_ = (leanh::lean_unbox(v_nondep_404_) as u8);
    v_kind_boxed_417_ = (leanh::lean_unbox(v_kind_405_) as u8);
    v_res_418_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_name_400_, v_type_401_, v_val_402_, v_k_403_, v_nondep_boxed_416_, v_kind_boxed_417_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
    leanh::lean_dec(v___y_414_);
    leanh::lean_dec_ref(v___y_413_);
    leanh::lean_dec(v___y_412_);
    leanh::lean_dec_ref(v___y_411_);
    leanh::lean_dec(v___y_410_);
    leanh::lean_dec_ref(v___y_409_);
    leanh::lean_dec(v___y_408_);
    leanh::lean_dec(v___y_407_);
    leanh::lean_dec(v___y_406_);
    return v_res_418_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0(
    mut v_00_u03b1_419_: *mut leanh::LeanObject,
    mut v_name_420_: *mut leanh::LeanObject,
    mut v_type_421_: *mut leanh::LeanObject,
    mut v_val_422_: *mut leanh::LeanObject,
    mut v_k_423_: *mut leanh::LeanObject,
    mut v_nondep_424_: u8,
    mut v_kind_425_: u8,
    mut v___y_426_: *mut leanh::LeanObject,
    mut v___y_427_: *mut leanh::LeanObject,
    mut v___y_428_: *mut leanh::LeanObject,
    mut v___y_429_: *mut leanh::LeanObject,
    mut v___y_430_: *mut leanh::LeanObject,
    mut v___y_431_: *mut leanh::LeanObject,
    mut v___y_432_: *mut leanh::LeanObject,
    mut v___y_433_: *mut leanh::LeanObject,
    mut v___y_434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_436_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_name_420_, v_type_421_, v_val_422_, v_k_423_, v_nondep_424_, v_kind_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
    return v___x_436_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_00_u03b1_437_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_name_438_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_type_439_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_val_440_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_k_441_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_nondep_442_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_kind_443_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_444_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_445_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_446_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_447_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_448_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_449_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_450_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_451_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_452_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_453_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_nondep_boxed_454_: u8 = 0;
    let mut v_kind_boxed_455_: u8 = 0;
    let mut v_res_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_454_ = (leanh::lean_unbox(v_nondep_442_) as u8);
    v_kind_boxed_455_ = (leanh::lean_unbox(v_kind_443_) as u8);
    v_res_456_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0(v_00_u03b1_437_, v_name_438_, v_type_439_, v_val_440_, v_k_441_, v_nondep_boxed_454_, v_kind_boxed_455_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
    leanh::lean_dec(v___y_452_);
    leanh::lean_dec_ref(v___y_451_);
    leanh::lean_dec(v___y_450_);
    leanh::lean_dec_ref(v___y_449_);
    leanh::lean_dec(v___y_448_);
    leanh::lean_dec_ref(v___y_447_);
    leanh::lean_dec(v___y_446_);
    leanh::lean_dec(v___y_445_);
    leanh::lean_dec(v___y_444_);
    return v_res_456_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0___boxed(
    mut v_fvars_457_: *mut leanh::LeanObject,
    mut v_body_458_: *mut leanh::LeanObject,
    mut v_modified_459_: *mut leanh::LeanObject,
    mut v_x_460_: *mut leanh::LeanObject,
    mut v___y_461_: *mut leanh::LeanObject,
    mut v___y_462_: *mut leanh::LeanObject,
    mut v___y_463_: *mut leanh::LeanObject,
    mut v___y_464_: *mut leanh::LeanObject,
    mut v___y_465_: *mut leanh::LeanObject,
    mut v___y_466_: *mut leanh::LeanObject,
    mut v___y_467_: *mut leanh::LeanObject,
    mut v___y_468_: *mut leanh::LeanObject,
    mut v___y_469_: *mut leanh::LeanObject,
    mut v___y_470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_modified_boxed_471_: u8 = 0;
    let mut v_res_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_modified_boxed_471_ = (leanh::lean_unbox(v_modified_459_) as u8);
    v_res_472_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0(
        v_fvars_457_,
        v_body_458_,
        v_modified_boxed_471_,
        v_x_460_,
        v___y_461_,
        v___y_462_,
        v___y_463_,
        v___y_464_,
        v___y_465_,
        v___y_466_,
        v___y_467_,
        v___y_468_,
        v___y_469_,
    );
    leanh::lean_dec(v___y_469_);
    leanh::lean_dec_ref(v___y_468_);
    leanh::lean_dec(v___y_467_);
    leanh::lean_dec_ref(v___y_466_);
    leanh::lean_dec(v___y_465_);
    leanh::lean_dec_ref(v___y_464_);
    leanh::lean_dec(v___y_463_);
    leanh::lean_dec(v___y_462_);
    leanh::lean_dec(v___y_461_);
    return v_res_472_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1(
    mut v_fvars_473_: *mut leanh::LeanObject,
    mut v_body_474_: *mut leanh::LeanObject,
    mut v_x_475_: *mut leanh::LeanObject,
    mut v___y_476_: *mut leanh::LeanObject,
    mut v___y_477_: *mut leanh::LeanObject,
    mut v___y_478_: *mut leanh::LeanObject,
    mut v___y_479_: *mut leanh::LeanObject,
    mut v___y_480_: *mut leanh::LeanObject,
    mut v___y_481_: *mut leanh::LeanObject,
    mut v___y_482_: *mut leanh::LeanObject,
    mut v___y_483_: *mut leanh::LeanObject,
    mut v___y_484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: u8 = 0;
    let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_486_ = lean_array_push(v_fvars_473_, v_x_475_);
    v___x_487_ = 1;
    v___x_488_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(
        v_body_474_,
        v___x_486_,
        v___x_487_,
        v___y_476_,
        v___y_477_,
        v___y_478_,
        v___y_479_,
        v___y_480_,
        v___y_481_,
        v___y_482_,
        v___y_483_,
        v___y_484_,
    );
    return v___x_488_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1___boxed(
    mut v_fvars_489_: *mut leanh::LeanObject,
    mut v_body_490_: *mut leanh::LeanObject,
    mut v_x_491_: *mut leanh::LeanObject,
    mut v___y_492_: *mut leanh::LeanObject,
    mut v___y_493_: *mut leanh::LeanObject,
    mut v___y_494_: *mut leanh::LeanObject,
    mut v___y_495_: *mut leanh::LeanObject,
    mut v___y_496_: *mut leanh::LeanObject,
    mut v___y_497_: *mut leanh::LeanObject,
    mut v___y_498_: *mut leanh::LeanObject,
    mut v___y_499_: *mut leanh::LeanObject,
    mut v___y_500_: *mut leanh::LeanObject,
    mut v___y_501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_502_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1(
        v_fvars_489_,
        v_body_490_,
        v_x_491_,
        v___y_492_,
        v___y_493_,
        v___y_494_,
        v___y_495_,
        v___y_496_,
        v___y_497_,
        v___y_498_,
        v___y_499_,
        v___y_500_,
    );
    leanh::lean_dec(v___y_500_);
    leanh::lean_dec_ref(v___y_499_);
    leanh::lean_dec(v___y_498_);
    leanh::lean_dec_ref(v___y_497_);
    leanh::lean_dec(v___y_496_);
    leanh::lean_dec_ref(v___y_495_);
    leanh::lean_dec(v___y_494_);
    leanh::lean_dec(v___y_493_);
    leanh::lean_dec(v___y_492_);
    return v_res_502_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(
    mut v_e_503_: *mut leanh::LeanObject,
    mut v_fvars_504_: *mut leanh::LeanObject,
    mut v_modified_505_: u8,
    mut v_a_506_: *mut leanh::LeanObject,
    mut v_a_507_: *mut leanh::LeanObject,
    mut v_a_508_: *mut leanh::LeanObject,
    mut v_a_509_: *mut leanh::LeanObject,
    mut v_a_510_: *mut leanh::LeanObject,
    mut v_a_511_: *mut leanh::LeanObject,
    mut v_a_512_: *mut leanh::LeanObject,
    mut v_a_513_: *mut leanh::LeanObject,
    mut v_a_514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_520_: u8 = 0;
    let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: u8 = 0;
    let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: u8 = 0;
    let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: u8 = 0;
    let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: u8 = 0;
    let mut v___x_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_550_: u8 = 0;
    let mut v___x_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_554_: u8 = 0;
    let mut v_a_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_558_: u8 = 0;
    let mut v___x_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_562_: u8 = 0;
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_569_: u8 = 0;
    let mut v___x_571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_572_: u8 = 0;
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: u8 = 0;
    let mut v___x_580_: u8 = 0;
    let mut v___x_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_585_: u8 = 0;
    let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_590_: u8 = 0;
    let mut v_a_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_594_: u8 = 0;
    let mut v___x_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_598_: u8 = 0;
    let mut v_isSharedCheck_599_: u8 = 0;
    let mut v_e_x27_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_603_: u8 = 0;
    let mut v___x_604_: u8 = 0;
    let mut v___x_605_: u8 = 0;
    let mut v___x_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_610_: u8 = 0;
    let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_617_: u8 = 0;
    let mut v_a_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_621_: u8 = 0;
    let mut v___x_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_625_: u8 = 0;
    let mut v_isSharedCheck_626_: u8 = 0;
    let mut v_isSharedCheck_627_: u8 = 0;
    let mut v_a_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_631_: u8 = 0;
    let mut v___x_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_635_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_e_503_) == 8 {
                    v_declName_516_ = leanh::lean_ctor_get(v_e_503_, 0);
                    leanh::lean_inc(v_declName_516_);
                    v_type_517_ = leanh::lean_ctor_get(v_e_503_, 1);
                    leanh::lean_inc_ref_n(v_type_517_, 2);
                    v_value_518_ = leanh::lean_ctor_get(v_e_503_, 2);
                    leanh::lean_inc_ref(v_value_518_);
                    v_body_519_ = leanh::lean_ctor_get(v_e_503_, 3);
                    leanh::lean_inc_ref(v_body_519_);
                    v_nondep_520_ = leanh::lean_ctor_get_uint8(
                        v_e_503_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    leanh::lean_dec_ref_known(v_e_503_, 4);
                    v___x_521_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(
                        v_type_517_,
                        v_fvars_504_,
                        v_a_510_,
                    );
                    if leanh::lean_obj_tag(v___x_521_) == 0 {
                        v_a_522_ = leanh::lean_ctor_get(v___x_521_, 0);
                        leanh::lean_inc(v_a_522_);
                        leanh::lean_dec_ref_known(v___x_521_, 1);
                        leanh::lean_inc(v_a_514_);
                        leanh::lean_inc_ref(v_a_513_);
                        leanh::lean_inc(v_a_512_);
                        leanh::lean_inc_ref(v_a_511_);
                        leanh::lean_inc(v_a_510_);
                        leanh::lean_inc_ref(v_a_509_);
                        leanh::lean_inc(v_a_508_);
                        leanh::lean_inc(v_a_507_);
                        leanh::lean_inc(v_a_506_);
                        v___x_523_ = lean_sym_dsimp(
                            v_a_522_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_,
                            v_a_512_, v_a_513_, v_a_514_,
                        );
                        if leanh::lean_obj_tag(v___x_523_) == 0 {
                            v_a_524_ = leanh::lean_ctor_get(v___x_523_, 0);
                            leanh::lean_inc(v_a_524_);
                            leanh::lean_dec_ref_known(v___x_523_, 1);
                            leanh::lean_inc_ref(v_value_518_);
                            v___x_525_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(
                                v_value_518_,
                                v_fvars_504_,
                                v_a_510_,
                            );
                            if leanh::lean_obj_tag(v___x_525_) == 0 {
                                v_a_526_ = leanh::lean_ctor_get(v___x_525_, 0);
                                leanh::lean_inc(v_a_526_);
                                leanh::lean_dec_ref_known(v___x_525_, 1);
                                leanh::lean_inc(v_a_514_);
                                leanh::lean_inc_ref(v_a_513_);
                                leanh::lean_inc(v_a_512_);
                                leanh::lean_inc_ref(v_a_511_);
                                leanh::lean_inc(v_a_510_);
                                leanh::lean_inc_ref(v_a_509_);
                                leanh::lean_inc(v_a_508_);
                                leanh::lean_inc(v_a_507_);
                                leanh::lean_inc(v_a_506_);
                                v___x_527_ = lean_sym_dsimp(
                                    v_a_526_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_,
                                    v_a_511_, v_a_512_, v_a_513_, v_a_514_,
                                );
                                if leanh::lean_obj_tag(v___x_527_) == 0 {
                                    if leanh::lean_obj_tag(v_a_524_) == 0 {
                                        leanh::lean_dec_ref_known(v_a_524_, 0);
                                        v_a_528_ = leanh::lean_ctor_get(v___x_527_, 0);
                                        leanh::lean_inc(v_a_528_);
                                        leanh::lean_dec_ref_known(v___x_527_, 1);
                                        if leanh::lean_obj_tag(v_a_528_) == 0 {
                                            leanh::lean_dec_ref_known(v_a_528_, 0);
                                            v___x_529_ =
                                                leanh::lean_box((v_modified_505_) as usize);
                                            v___f_530_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0___boxed as *mut core::ffi::c_void, 14, 3);
                                            leanh::lean_closure_set(
                                                v___f_530_,
                                                0,
                                                v_fvars_504_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_530_,
                                                1,
                                                v_body_519_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_530_, 2, v___x_529_,
                                            );
                                            v___x_531_ = 0;
                                            v___x_532_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_516_, v_type_517_, v_value_518_, v___f_530_, v_nondep_520_, v___x_531_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
                                            return v___x_532_;
                                        } else {
                                            leanh::lean_dec_ref(v_value_518_);
                                            v_e_x27_533_ = leanh::lean_ctor_get(v_a_528_, 0);
                                            leanh::lean_inc_ref(v_e_x27_533_);
                                            leanh::lean_dec_ref_known(v_a_528_, 1);
                                            v___f_534_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1___boxed as *mut core::ffi::c_void, 13, 2);
                                            leanh::lean_closure_set(
                                                v___f_534_,
                                                0,
                                                v_fvars_504_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_534_,
                                                1,
                                                v_body_519_,
                                            );
                                            v___x_535_ = 0;
                                            v___x_536_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_516_, v_type_517_, v_e_x27_533_, v___f_534_, v_nondep_520_, v___x_535_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
                                            return v___x_536_;
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v_type_517_);
                                        v_a_537_ = leanh::lean_ctor_get(v___x_527_, 0);
                                        leanh::lean_inc(v_a_537_);
                                        leanh::lean_dec_ref_known(v___x_527_, 1);
                                        if leanh::lean_obj_tag(v_a_537_) == 0 {
                                            leanh::lean_dec_ref_known(v_a_537_, 0);
                                            v_e_x27_538_ = leanh::lean_ctor_get(v_a_524_, 0);
                                            leanh::lean_inc_ref(v_e_x27_538_);
                                            leanh::lean_dec_ref_known(v_a_524_, 1);
                                            v___f_539_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1___boxed as *mut core::ffi::c_void, 13, 2);
                                            leanh::lean_closure_set(
                                                v___f_539_,
                                                0,
                                                v_fvars_504_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_539_,
                                                1,
                                                v_body_519_,
                                            );
                                            v___x_540_ = 0;
                                            v___x_541_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_516_, v_e_x27_538_, v_value_518_, v___f_539_, v_nondep_520_, v___x_540_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
                                            return v___x_541_;
                                        } else {
                                            leanh::lean_dec_ref(v_value_518_);
                                            v_e_x27_542_ = leanh::lean_ctor_get(v_a_524_, 0);
                                            leanh::lean_inc_ref(v_e_x27_542_);
                                            leanh::lean_dec_ref_known(v_a_524_, 1);
                                            v_e_x27_543_ = leanh::lean_ctor_get(v_a_537_, 0);
                                            leanh::lean_inc_ref(v_e_x27_543_);
                                            leanh::lean_dec_ref_known(v_a_537_, 1);
                                            v___f_544_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1___boxed as *mut core::ffi::c_void, 13, 2);
                                            leanh::lean_closure_set(
                                                v___f_544_,
                                                0,
                                                v_fvars_504_,
                                            );
                                            leanh::lean_closure_set(
                                                v___f_544_,
                                                1,
                                                v_body_519_,
                                            );
                                            v___x_545_ = 0;
                                            v___x_546_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_516_, v_e_x27_542_, v_e_x27_543_, v___f_544_, v_nondep_520_, v___x_545_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
                                            return v___x_546_;
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_a_524_);
                                    leanh::lean_dec_ref(v_body_519_);
                                    leanh::lean_dec_ref(v_value_518_);
                                    leanh::lean_dec_ref(v_type_517_);
                                    leanh::lean_dec(v_declName_516_);
                                    leanh::lean_dec_ref(v_fvars_504_);
                                    return v___x_527_;
                                }
                            } else {
                                leanh::lean_dec(v_a_524_);
                                leanh::lean_dec_ref(v_body_519_);
                                leanh::lean_dec_ref(v_value_518_);
                                leanh::lean_dec_ref(v_type_517_);
                                leanh::lean_dec(v_declName_516_);
                                leanh::lean_dec_ref(v_fvars_504_);
                                v_a_547_ = leanh::lean_ctor_get(v___x_525_, 0);
                                v_isSharedCheck_554_ =
                                    (!leanh::lean_is_exclusive(v___x_525_)) as u8;
                                if v_isSharedCheck_554_ == 0 {
                                    v___x_549_ = v___x_525_;
                                    v_isShared_550_ = v_isSharedCheck_554_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_547_);
                                    leanh::lean_dec(v___x_525_);
                                    v___x_549_ = leanh::lean_box(0);
                                    v_isShared_550_ = v_isSharedCheck_554_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_body_519_);
                            leanh::lean_dec_ref(v_value_518_);
                            leanh::lean_dec_ref(v_type_517_);
                            leanh::lean_dec(v_declName_516_);
                            leanh::lean_dec_ref(v_fvars_504_);
                            return v___x_523_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_body_519_);
                        leanh::lean_dec_ref(v_value_518_);
                        leanh::lean_dec_ref(v_type_517_);
                        leanh::lean_dec(v_declName_516_);
                        leanh::lean_dec_ref(v_fvars_504_);
                        v_a_555_ = leanh::lean_ctor_get(v___x_521_, 0);
                        v_isSharedCheck_562_ = (!leanh::lean_is_exclusive(v___x_521_)) as u8;
                        if v_isSharedCheck_562_ == 0 {
                            v___x_557_ = v___x_521_;
                            v_isShared_558_ = v_isSharedCheck_562_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_555_);
                            leanh::lean_dec(v___x_521_);
                            v___x_557_ = leanh::lean_box(0);
                            v_isShared_558_ = v_isSharedCheck_562_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc_ref(v_e_503_);
                    v___x_563_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(
                        v_e_503_,
                        v_fvars_504_,
                        v_a_510_,
                    );
                    if leanh::lean_obj_tag(v___x_563_) == 0 {
                        v_a_564_ = leanh::lean_ctor_get(v___x_563_, 0);
                        leanh::lean_inc(v_a_564_);
                        leanh::lean_dec_ref_known(v___x_563_, 1);
                        leanh::lean_inc(v_a_514_);
                        leanh::lean_inc_ref(v_a_513_);
                        leanh::lean_inc(v_a_512_);
                        leanh::lean_inc_ref(v_a_511_);
                        leanh::lean_inc(v_a_510_);
                        leanh::lean_inc_ref(v_a_509_);
                        leanh::lean_inc(v_a_508_);
                        leanh::lean_inc(v_a_507_);
                        leanh::lean_inc(v_a_506_);
                        v___x_565_ = lean_sym_dsimp(
                            v_a_564_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_,
                            v_a_512_, v_a_513_, v_a_514_,
                        );
                        if leanh::lean_obj_tag(v___x_565_) == 0 {
                            v_a_566_ = leanh::lean_ctor_get(v___x_565_, 0);
                            v_isSharedCheck_627_ =
                                (!leanh::lean_is_exclusive(v___x_565_)) as u8;
                            if v_isSharedCheck_627_ == 0 {
                                v___x_568_ = v___x_565_;
                                v_isShared_569_ = v_isSharedCheck_627_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_566_);
                                leanh::lean_dec(v___x_565_);
                                v___x_568_ = leanh::lean_box(0);
                                v_isShared_569_ = v_isSharedCheck_627_;
                                state = 5;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v_fvars_504_);
                            leanh::lean_dec_ref(v_e_503_);
                            return v___x_565_;
                        }
                    } else {
                        leanh::lean_dec_ref(v_fvars_504_);
                        leanh::lean_dec_ref(v_e_503_);
                        v_a_628_ = leanh::lean_ctor_get(v___x_563_, 0);
                        v_isSharedCheck_635_ = (!leanh::lean_is_exclusive(v___x_563_)) as u8;
                        if v_isSharedCheck_635_ == 0 {
                            v___x_630_ = v___x_563_;
                            v_isShared_631_ = v_isSharedCheck_635_;
                            state = 19;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_628_);
                            leanh::lean_dec(v___x_563_);
                            v___x_630_ = leanh::lean_box(0);
                            v_isShared_631_ = v_isSharedCheck_635_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_550_ == 0 {
                    v___x_552_ = v___x_549_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_553_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
                    v___x_552_ = v_reuseFailAlloc_553_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_552_;
            }
            3 => {
                if v_isShared_558_ == 0 {
                    v___x_560_ = v___x_557_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_561_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
                    v___x_560_ = v_reuseFailAlloc_561_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_560_;
            }
            5 => {
                if leanh::lean_obj_tag(v_a_566_) == 0 {
                    v_isSharedCheck_599_ = (!leanh::lean_is_exclusive(v_a_566_)) as u8;
                    if v_isSharedCheck_599_ == 0 {
                        v___x_571_ = v_a_566_;
                        v_isShared_572_ = v_isSharedCheck_599_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_566_);
                        v___x_571_ = leanh::lean_box(0);
                        v_isShared_572_ = v_isSharedCheck_599_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_568_);
                    leanh::lean_dec_ref(v_e_503_);
                    v_e_x27_600_ = leanh::lean_ctor_get(v_a_566_, 0);
                    v_isSharedCheck_626_ = (!leanh::lean_is_exclusive(v_a_566_)) as u8;
                    if v_isSharedCheck_626_ == 0 {
                        v___x_602_ = v_a_566_;
                        v_isShared_603_ = v_isSharedCheck_626_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_e_x27_600_);
                        leanh::lean_dec(v_a_566_);
                        v___x_602_ = leanh::lean_box(0);
                        v_isShared_603_ = v_isSharedCheck_626_;
                        state = 13;
                        continue;
                    }
                }
            }
            6 => {
                if v_modified_505_ == 0 {
                    leanh::lean_dec_ref(v_fvars_504_);
                    leanh::lean_dec_ref(v_e_503_);
                    if v_isShared_572_ == 0 {
                        v___x_574_ = v___x_571_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_578_ = leanh::lean_alloc_ctor(0, 0, (1) as u32);
                        v___x_574_ = v_reuseFailAlloc_578_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_571_);
                    leanh::lean_del_object(v___x_568_);
                    v___x_579_ = 0;
                    v___x_580_ = 1;
                    v___x_581_ = l_Lean_Meta_mkLetFVars(
                        v_fvars_504_,
                        v_e_503_,
                        v___x_579_,
                        v___x_579_,
                        v___x_580_,
                        v_a_511_,
                        v_a_512_,
                        v_a_513_,
                        v_a_514_,
                    );
                    leanh::lean_dec_ref(v_fvars_504_);
                    if leanh::lean_obj_tag(v___x_581_) == 0 {
                        v_a_582_ = leanh::lean_ctor_get(v___x_581_, 0);
                        v_isSharedCheck_590_ = (!leanh::lean_is_exclusive(v___x_581_)) as u8;
                        if v_isSharedCheck_590_ == 0 {
                            v___x_584_ = v___x_581_;
                            v_isShared_585_ = v_isSharedCheck_590_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_582_);
                            leanh::lean_dec(v___x_581_);
                            v___x_584_ = leanh::lean_box(0);
                            v_isShared_585_ = v_isSharedCheck_590_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v_a_591_ = leanh::lean_ctor_get(v___x_581_, 0);
                        v_isSharedCheck_598_ = (!leanh::lean_is_exclusive(v___x_581_)) as u8;
                        if v_isSharedCheck_598_ == 0 {
                            v___x_593_ = v___x_581_;
                            v_isShared_594_ = v_isSharedCheck_598_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_591_);
                            leanh::lean_dec(v___x_581_);
                            v___x_593_ = leanh::lean_box(0);
                            v_isShared_594_ = v_isSharedCheck_598_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            7 => {
                leanh::lean_ctor_set_uint8(v___x_574_, 0 as u32, v_modified_505_);
                if v_isShared_569_ == 0 {
                    leanh::lean_ctor_set(v___x_568_, 0, v___x_574_);
                    v___x_576_ = v___x_568_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_577_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
                    v___x_576_ = v_reuseFailAlloc_577_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_576_;
            }
            9 => {
                v___x_586_ = leanh::lean_alloc_ctor(1, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_586_, 0, v_a_582_);
                leanh::lean_ctor_set_uint8(
                    v___x_586_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_579_,
                );
                if v_isShared_585_ == 0 {
                    leanh::lean_ctor_set(v___x_584_, 0, v___x_586_);
                    v___x_588_ = v___x_584_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_589_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
                    v___x_588_ = v_reuseFailAlloc_589_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_588_;
            }
            11 => {
                if v_isShared_594_ == 0 {
                    v___x_596_ = v___x_593_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_597_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
                    v___x_596_ = v_reuseFailAlloc_597_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_596_;
            }
            13 => {
                v___x_604_ = 0;
                v___x_605_ = 1;
                v___x_606_ = l_Lean_Meta_mkLetFVars(
                    v_fvars_504_,
                    v_e_x27_600_,
                    v___x_604_,
                    v___x_604_,
                    v___x_605_,
                    v_a_511_,
                    v_a_512_,
                    v_a_513_,
                    v_a_514_,
                );
                leanh::lean_dec_ref(v_fvars_504_);
                if leanh::lean_obj_tag(v___x_606_) == 0 {
                    v_a_607_ = leanh::lean_ctor_get(v___x_606_, 0);
                    v_isSharedCheck_617_ = (!leanh::lean_is_exclusive(v___x_606_)) as u8;
                    if v_isSharedCheck_617_ == 0 {
                        v___x_609_ = v___x_606_;
                        v_isShared_610_ = v_isSharedCheck_617_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_607_);
                        leanh::lean_dec(v___x_606_);
                        v___x_609_ = leanh::lean_box(0);
                        v_isShared_610_ = v_isSharedCheck_617_;
                        state = 14;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_602_);
                    v_a_618_ = leanh::lean_ctor_get(v___x_606_, 0);
                    v_isSharedCheck_625_ = (!leanh::lean_is_exclusive(v___x_606_)) as u8;
                    if v_isSharedCheck_625_ == 0 {
                        v___x_620_ = v___x_606_;
                        v_isShared_621_ = v_isSharedCheck_625_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_618_);
                        leanh::lean_dec(v___x_606_);
                        v___x_620_ = leanh::lean_box(0);
                        v_isShared_621_ = v_isSharedCheck_625_;
                        state = 17;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_603_ == 0 {
                    leanh::lean_ctor_set(v___x_602_, 0, v_a_607_);
                    v___x_612_ = v___x_602_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_616_ = leanh::lean_alloc_ctor(1, 1, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_607_);
                    v___x_612_ = v_reuseFailAlloc_616_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                leanh::lean_ctor_set_uint8(
                    v___x_612_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_604_,
                );
                if v_isShared_610_ == 0 {
                    leanh::lean_ctor_set(v___x_609_, 0, v___x_612_);
                    v___x_614_ = v___x_609_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_615_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_612_);
                    v___x_614_ = v_reuseFailAlloc_615_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_614_;
            }
            17 => {
                if v_isShared_621_ == 0 {
                    v___x_623_ = v___x_620_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_624_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
                    v___x_623_ = v_reuseFailAlloc_624_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_623_;
            }
            19 => {
                if v_isShared_631_ == 0 {
                    v___x_633_ = v___x_630_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_634_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
                    v___x_633_ = v_reuseFailAlloc_634_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_633_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0(
    mut v_fvars_636_: *mut leanh::LeanObject,
    mut v_body_637_: *mut leanh::LeanObject,
    mut v_modified_638_: u8,
    mut v_x_639_: *mut leanh::LeanObject,
    mut v___y_640_: *mut leanh::LeanObject,
    mut v___y_641_: *mut leanh::LeanObject,
    mut v___y_642_: *mut leanh::LeanObject,
    mut v___y_643_: *mut leanh::LeanObject,
    mut v___y_644_: *mut leanh::LeanObject,
    mut v___y_645_: *mut leanh::LeanObject,
    mut v___y_646_: *mut leanh::LeanObject,
    mut v___y_647_: *mut leanh::LeanObject,
    mut v___y_648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_650_ = lean_array_push(v_fvars_636_, v_x_639_);
    v___x_651_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(
        v_body_637_,
        v___x_650_,
        v_modified_638_,
        v___y_640_,
        v___y_641_,
        v___y_642_,
        v___y_643_,
        v___y_644_,
        v___y_645_,
        v___y_646_,
        v___y_647_,
        v___y_648_,
    );
    return v___x_651_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___boxed(
    mut v_e_652_: *mut leanh::LeanObject,
    mut v_fvars_653_: *mut leanh::LeanObject,
    mut v_modified_654_: *mut leanh::LeanObject,
    mut v_a_655_: *mut leanh::LeanObject,
    mut v_a_656_: *mut leanh::LeanObject,
    mut v_a_657_: *mut leanh::LeanObject,
    mut v_a_658_: *mut leanh::LeanObject,
    mut v_a_659_: *mut leanh::LeanObject,
    mut v_a_660_: *mut leanh::LeanObject,
    mut v_a_661_: *mut leanh::LeanObject,
    mut v_a_662_: *mut leanh::LeanObject,
    mut v_a_663_: *mut leanh::LeanObject,
    mut v_a_664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_modified_boxed_665_: u8 = 0;
    let mut v_res_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_modified_boxed_665_ = (leanh::lean_unbox(v_modified_654_) as u8);
    v_res_666_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(
        v_e_652_,
        v_fvars_653_,
        v_modified_boxed_665_,
        v_a_655_,
        v_a_656_,
        v_a_657_,
        v_a_658_,
        v_a_659_,
        v_a_660_,
        v_a_661_,
        v_a_662_,
        v_a_663_,
    );
    leanh::lean_dec(v_a_663_);
    leanh::lean_dec_ref(v_a_662_);
    leanh::lean_dec(v_a_661_);
    leanh::lean_dec_ref(v_a_660_);
    leanh::lean_dec(v_a_659_);
    leanh::lean_dec_ref(v_a_658_);
    leanh::lean_dec(v_a_657_);
    leanh::lean_dec(v_a_656_);
    leanh::lean_dec(v_a_655_);
    return v_res_666_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_dsimpLet(
    mut v_e_669_: *mut leanh::LeanObject,
    mut v_a_670_: *mut leanh::LeanObject,
    mut v_a_671_: *mut leanh::LeanObject,
    mut v_a_672_: *mut leanh::LeanObject,
    mut v_a_673_: *mut leanh::LeanObject,
    mut v_a_674_: *mut leanh::LeanObject,
    mut v_a_675_: *mut leanh::LeanObject,
    mut v_a_676_: *mut leanh::LeanObject,
    mut v_a_677_: *mut leanh::LeanObject,
    mut v_a_678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: u8 = 0;
    let mut v___x_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_680_ = l_Lean_Meta_Sym_DSimp_dsimpLet___closed__0;
    v___x_681_ = 0;
    v___x_682_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(
        v_e_669_, v___x_680_, v___x_681_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_,
        v_a_675_, v_a_676_, v_a_677_, v_a_678_,
    );
    return v___x_682_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_dsimpLet___boxed(
    mut v_e_683_: *mut leanh::LeanObject,
    mut v_a_684_: *mut leanh::LeanObject,
    mut v_a_685_: *mut leanh::LeanObject,
    mut v_a_686_: *mut leanh::LeanObject,
    mut v_a_687_: *mut leanh::LeanObject,
    mut v_a_688_: *mut leanh::LeanObject,
    mut v_a_689_: *mut leanh::LeanObject,
    mut v_a_690_: *mut leanh::LeanObject,
    mut v_a_691_: *mut leanh::LeanObject,
    mut v_a_692_: *mut leanh::LeanObject,
    mut v_a_693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_694_ = l_Lean_Meta_Sym_DSimp_dsimpLet(
        v_e_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_,
        v_a_692_,
    );
    leanh::lean_dec(v_a_692_);
    leanh::lean_dec_ref(v_a_691_);
    leanh::lean_dec(v_a_690_);
    leanh::lean_dec_ref(v_a_689_);
    leanh::lean_dec(v_a_688_);
    leanh::lean_dec_ref(v_a_687_);
    leanh::lean_dec(v_a_686_);
    leanh::lean_dec(v_a_685_);
    leanh::lean_dec(v_a_684_);
    return v_res_694_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_DSimp_Let(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_AbstractS(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_DSimp_Let(
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
pub unsafe fn initialize_Lean_Meta_Sym_DSimp_Let(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_AbstractS(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_Let(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_DSimp_Let(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_DSimp_Let(builtin);
}
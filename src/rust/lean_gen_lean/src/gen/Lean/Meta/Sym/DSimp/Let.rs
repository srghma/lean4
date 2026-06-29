// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.Let
// Imports: Lean.Meta.Sym.DSimp.DSimpM Lean.Meta.Sym.AbstractS Lean.Meta.Sym.InstantiateS
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
use crate::lean_imports_rs::Init::Prelude::lean_array_push;
use crate::lean_imports_rs::Lean::Meta::Sym::DSimp::DSimpM::lean_sym_dsimp;
pub static l_Lean_Meta_Sym_DSimp_dsimpLet___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_Sym_DSimp_dsimpLet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_dsimpLet___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0(
    mut v_k_348_: *mut crate::leanh::LeanObject,
    mut v___y_349_: *mut crate::leanh::LeanObject,
    mut v___y_350_: *mut crate::leanh::LeanObject,
    mut v___y_351_: *mut crate::leanh::LeanObject,
    mut v___y_352_: *mut crate::leanh::LeanObject,
    mut v___y_353_: *mut crate::leanh::LeanObject,
    mut v_b_354_: *mut crate::leanh::LeanObject,
    mut v___y_355_: *mut crate::leanh::LeanObject,
    mut v___y_356_: *mut crate::leanh::LeanObject,
    mut v___y_357_: *mut crate::leanh::LeanObject,
    mut v___y_358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_358_);
    crate::leanh::lean_inc_ref(v___y_357_);
    crate::leanh::lean_inc(v___y_356_);
    crate::leanh::lean_inc_ref(v___y_355_);
    crate::leanh::lean_inc(v___y_353_);
    crate::leanh::lean_inc_ref(v___y_352_);
    crate::leanh::lean_inc(v___y_351_);
    crate::leanh::lean_inc(v___y_350_);
    crate::leanh::lean_inc(v___y_349_);
    v___x_360_ = crate::leanh::lean_apply_11(
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
        crate::leanh::lean_box(0),
    );
    return v___x_360_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0___boxed(
    mut v_k_361_: *mut crate::leanh::LeanObject,
    mut v___y_362_: *mut crate::leanh::LeanObject,
    mut v___y_363_: *mut crate::leanh::LeanObject,
    mut v___y_364_: *mut crate::leanh::LeanObject,
    mut v___y_365_: *mut crate::leanh::LeanObject,
    mut v___y_366_: *mut crate::leanh::LeanObject,
    mut v_b_367_: *mut crate::leanh::LeanObject,
    mut v___y_368_: *mut crate::leanh::LeanObject,
    mut v___y_369_: *mut crate::leanh::LeanObject,
    mut v___y_370_: *mut crate::leanh::LeanObject,
    mut v___y_371_: *mut crate::leanh::LeanObject,
    mut v___y_372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_373_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0(v_k_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v_b_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
    crate::leanh::lean_dec(v___y_371_);
    crate::leanh::lean_dec_ref(v___y_370_);
    crate::leanh::lean_dec(v___y_369_);
    crate::leanh::lean_dec_ref(v___y_368_);
    crate::leanh::lean_dec(v___y_366_);
    crate::leanh::lean_dec_ref(v___y_365_);
    crate::leanh::lean_dec(v___y_364_);
    crate::leanh::lean_dec(v___y_363_);
    crate::leanh::lean_dec(v___y_362_);
    return v_res_373_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(
    mut v_name_374_: *mut crate::leanh::LeanObject,
    mut v_type_375_: *mut crate::leanh::LeanObject,
    mut v_val_376_: *mut crate::leanh::LeanObject,
    mut v_k_377_: *mut crate::leanh::LeanObject,
    mut v_nondep_378_: u8,
    mut v_kind_379_: u8,
    mut v___y_380_: *mut crate::leanh::LeanObject,
    mut v___y_381_: *mut crate::leanh::LeanObject,
    mut v___y_382_: *mut crate::leanh::LeanObject,
    mut v___y_383_: *mut crate::leanh::LeanObject,
    mut v___y_384_: *mut crate::leanh::LeanObject,
    mut v___y_385_: *mut crate::leanh::LeanObject,
    mut v___y_386_: *mut crate::leanh::LeanObject,
    mut v___y_387_: *mut crate::leanh::LeanObject,
    mut v___y_388_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_395_: u8 = 0;
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_399_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_384_);
                crate::leanh::lean_inc_ref(v___y_383_);
                crate::leanh::lean_inc(v___y_382_);
                crate::leanh::lean_inc(v___y_381_);
                crate::leanh::lean_inc(v___y_380_);
                v___f_390_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 12, 6);
                crate::leanh::lean_closure_set(v___f_390_, 0, v_k_377_);
                crate::leanh::lean_closure_set(v___f_390_, 1, v___y_380_);
                crate::leanh::lean_closure_set(v___f_390_, 2, v___y_381_);
                crate::leanh::lean_closure_set(v___f_390_, 3, v___y_382_);
                crate::leanh::lean_closure_set(v___f_390_, 4, v___y_383_);
                crate::leanh::lean_closure_set(v___f_390_, 5, v___y_384_);
                v___x_391_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    crate::leanh::lean_box(0),
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
                if crate::leanh::lean_obj_tag(v___x_391_) == 0 {
                    return v___x_391_;
                } else {
                    v_a_392_ = crate::leanh::lean_ctor_get(v___x_391_, 0);
                    v_isSharedCheck_399_ = (!crate::leanh::lean_is_exclusive(v___x_391_)) as u8;
                    if v_isSharedCheck_399_ == 0 {
                        v___x_394_ = v___x_391_;
                        v_isShared_395_ = v_isSharedCheck_399_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_392_);
                        crate::leanh::lean_dec(v___x_391_);
                        v___x_394_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_398_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
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
    mut v_name_400_: *mut crate::leanh::LeanObject,
    mut v_type_401_: *mut crate::leanh::LeanObject,
    mut v_val_402_: *mut crate::leanh::LeanObject,
    mut v_k_403_: *mut crate::leanh::LeanObject,
    mut v_nondep_404_: *mut crate::leanh::LeanObject,
    mut v_kind_405_: *mut crate::leanh::LeanObject,
    mut v___y_406_: *mut crate::leanh::LeanObject,
    mut v___y_407_: *mut crate::leanh::LeanObject,
    mut v___y_408_: *mut crate::leanh::LeanObject,
    mut v___y_409_: *mut crate::leanh::LeanObject,
    mut v___y_410_: *mut crate::leanh::LeanObject,
    mut v___y_411_: *mut crate::leanh::LeanObject,
    mut v___y_412_: *mut crate::leanh::LeanObject,
    mut v___y_413_: *mut crate::leanh::LeanObject,
    mut v___y_414_: *mut crate::leanh::LeanObject,
    mut v___y_415_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_nondep_boxed_416_: u8 = 0;
    let mut v_kind_boxed_417_: u8 = 0;
    let mut v_res_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_416_ = (crate::leanh::lean_unbox(v_nondep_404_) as u8);
    v_kind_boxed_417_ = (crate::leanh::lean_unbox(v_kind_405_) as u8);
    v_res_418_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_name_400_, v_type_401_, v_val_402_, v_k_403_, v_nondep_boxed_416_, v_kind_boxed_417_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
    crate::leanh::lean_dec(v___y_414_);
    crate::leanh::lean_dec_ref(v___y_413_);
    crate::leanh::lean_dec(v___y_412_);
    crate::leanh::lean_dec_ref(v___y_411_);
    crate::leanh::lean_dec(v___y_410_);
    crate::leanh::lean_dec_ref(v___y_409_);
    crate::leanh::lean_dec(v___y_408_);
    crate::leanh::lean_dec(v___y_407_);
    crate::leanh::lean_dec(v___y_406_);
    return v_res_418_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0(
    mut v_00_u03b1_419_: *mut crate::leanh::LeanObject,
    mut v_name_420_: *mut crate::leanh::LeanObject,
    mut v_type_421_: *mut crate::leanh::LeanObject,
    mut v_val_422_: *mut crate::leanh::LeanObject,
    mut v_k_423_: *mut crate::leanh::LeanObject,
    mut v_nondep_424_: u8,
    mut v_kind_425_: u8,
    mut v___y_426_: *mut crate::leanh::LeanObject,
    mut v___y_427_: *mut crate::leanh::LeanObject,
    mut v___y_428_: *mut crate::leanh::LeanObject,
    mut v___y_429_: *mut crate::leanh::LeanObject,
    mut v___y_430_: *mut crate::leanh::LeanObject,
    mut v___y_431_: *mut crate::leanh::LeanObject,
    mut v___y_432_: *mut crate::leanh::LeanObject,
    mut v___y_433_: *mut crate::leanh::LeanObject,
    mut v___y_434_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_436_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_name_420_, v_type_421_, v_val_422_, v_k_423_, v_nondep_424_, v_kind_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
    return v___x_436_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_00_u03b1_437_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_name_438_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_type_439_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_val_440_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_k_441_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_nondep_442_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_kind_443_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_444_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_445_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_446_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_447_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_448_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_449_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_450_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_451_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_452_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_453_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_nondep_boxed_454_: u8 = 0;
    let mut v_kind_boxed_455_: u8 = 0;
    let mut v_res_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_nondep_boxed_454_ = (crate::leanh::lean_unbox(v_nondep_442_) as u8);
    v_kind_boxed_455_ = (crate::leanh::lean_unbox(v_kind_443_) as u8);
    v_res_456_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0(v_00_u03b1_437_, v_name_438_, v_type_439_, v_val_440_, v_k_441_, v_nondep_boxed_454_, v_kind_boxed_455_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
    crate::leanh::lean_dec(v___y_452_);
    crate::leanh::lean_dec_ref(v___y_451_);
    crate::leanh::lean_dec(v___y_450_);
    crate::leanh::lean_dec_ref(v___y_449_);
    crate::leanh::lean_dec(v___y_448_);
    crate::leanh::lean_dec_ref(v___y_447_);
    crate::leanh::lean_dec(v___y_446_);
    crate::leanh::lean_dec(v___y_445_);
    crate::leanh::lean_dec(v___y_444_);
    return v_res_456_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0___boxed(
    mut v_fvars_457_: *mut crate::leanh::LeanObject,
    mut v_body_458_: *mut crate::leanh::LeanObject,
    mut v_modified_459_: *mut crate::leanh::LeanObject,
    mut v_x_460_: *mut crate::leanh::LeanObject,
    mut v___y_461_: *mut crate::leanh::LeanObject,
    mut v___y_462_: *mut crate::leanh::LeanObject,
    mut v___y_463_: *mut crate::leanh::LeanObject,
    mut v___y_464_: *mut crate::leanh::LeanObject,
    mut v___y_465_: *mut crate::leanh::LeanObject,
    mut v___y_466_: *mut crate::leanh::LeanObject,
    mut v___y_467_: *mut crate::leanh::LeanObject,
    mut v___y_468_: *mut crate::leanh::LeanObject,
    mut v___y_469_: *mut crate::leanh::LeanObject,
    mut v___y_470_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modified_boxed_471_: u8 = 0;
    let mut v_res_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modified_boxed_471_ = (crate::leanh::lean_unbox(v_modified_459_) as u8);
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
    crate::leanh::lean_dec(v___y_469_);
    crate::leanh::lean_dec_ref(v___y_468_);
    crate::leanh::lean_dec(v___y_467_);
    crate::leanh::lean_dec_ref(v___y_466_);
    crate::leanh::lean_dec(v___y_465_);
    crate::leanh::lean_dec_ref(v___y_464_);
    crate::leanh::lean_dec(v___y_463_);
    crate::leanh::lean_dec(v___y_462_);
    crate::leanh::lean_dec(v___y_461_);
    return v_res_472_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1(
    mut v_fvars_473_: *mut crate::leanh::LeanObject,
    mut v_body_474_: *mut crate::leanh::LeanObject,
    mut v_x_475_: *mut crate::leanh::LeanObject,
    mut v___y_476_: *mut crate::leanh::LeanObject,
    mut v___y_477_: *mut crate::leanh::LeanObject,
    mut v___y_478_: *mut crate::leanh::LeanObject,
    mut v___y_479_: *mut crate::leanh::LeanObject,
    mut v___y_480_: *mut crate::leanh::LeanObject,
    mut v___y_481_: *mut crate::leanh::LeanObject,
    mut v___y_482_: *mut crate::leanh::LeanObject,
    mut v___y_483_: *mut crate::leanh::LeanObject,
    mut v___y_484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: u8 = 0;
    let mut v___x_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_fvars_489_: *mut crate::leanh::LeanObject,
    mut v_body_490_: *mut crate::leanh::LeanObject,
    mut v_x_491_: *mut crate::leanh::LeanObject,
    mut v___y_492_: *mut crate::leanh::LeanObject,
    mut v___y_493_: *mut crate::leanh::LeanObject,
    mut v___y_494_: *mut crate::leanh::LeanObject,
    mut v___y_495_: *mut crate::leanh::LeanObject,
    mut v___y_496_: *mut crate::leanh::LeanObject,
    mut v___y_497_: *mut crate::leanh::LeanObject,
    mut v___y_498_: *mut crate::leanh::LeanObject,
    mut v___y_499_: *mut crate::leanh::LeanObject,
    mut v___y_500_: *mut crate::leanh::LeanObject,
    mut v___y_501_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_500_);
    crate::leanh::lean_dec_ref(v___y_499_);
    crate::leanh::lean_dec(v___y_498_);
    crate::leanh::lean_dec_ref(v___y_497_);
    crate::leanh::lean_dec(v___y_496_);
    crate::leanh::lean_dec_ref(v___y_495_);
    crate::leanh::lean_dec(v___y_494_);
    crate::leanh::lean_dec(v___y_493_);
    crate::leanh::lean_dec(v___y_492_);
    return v_res_502_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(
    mut v_e_503_: *mut crate::leanh::LeanObject,
    mut v_fvars_504_: *mut crate::leanh::LeanObject,
    mut v_modified_505_: u8,
    mut v_a_506_: *mut crate::leanh::LeanObject,
    mut v_a_507_: *mut crate::leanh::LeanObject,
    mut v_a_508_: *mut crate::leanh::LeanObject,
    mut v_a_509_: *mut crate::leanh::LeanObject,
    mut v_a_510_: *mut crate::leanh::LeanObject,
    mut v_a_511_: *mut crate::leanh::LeanObject,
    mut v_a_512_: *mut crate::leanh::LeanObject,
    mut v_a_513_: *mut crate::leanh::LeanObject,
    mut v_a_514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_declName_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_520_: u8 = 0;
    let mut v___x_521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_531_: u8 = 0;
    let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_535_: u8 = 0;
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_540_: u8 = 0;
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_545_: u8 = 0;
    let mut v___x_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_550_: u8 = 0;
    let mut v___x_552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_554_: u8 = 0;
    let mut v_a_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_558_: u8 = 0;
    let mut v___x_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_562_: u8 = 0;
    let mut v___x_563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_569_: u8 = 0;
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_572_: u8 = 0;
    let mut v___x_574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_579_: u8 = 0;
    let mut v___x_580_: u8 = 0;
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_585_: u8 = 0;
    let mut v___x_586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_590_: u8 = 0;
    let mut v_a_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_594_: u8 = 0;
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_598_: u8 = 0;
    let mut v_isSharedCheck_599_: u8 = 0;
    let mut v_e_x27_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_603_: u8 = 0;
    let mut v___x_604_: u8 = 0;
    let mut v___x_605_: u8 = 0;
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_610_: u8 = 0;
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_617_: u8 = 0;
    let mut v_a_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_621_: u8 = 0;
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_625_: u8 = 0;
    let mut v_isSharedCheck_626_: u8 = 0;
    let mut v_isSharedCheck_627_: u8 = 0;
    let mut v_a_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_631_: u8 = 0;
    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_635_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_e_503_) == 8 {
                    v_declName_516_ = crate::leanh::lean_ctor_get(v_e_503_, 0);
                    crate::leanh::lean_inc(v_declName_516_);
                    v_type_517_ = crate::leanh::lean_ctor_get(v_e_503_, 1);
                    crate::leanh::lean_inc_ref_n(v_type_517_, 2);
                    v_value_518_ = crate::leanh::lean_ctor_get(v_e_503_, 2);
                    crate::leanh::lean_inc_ref(v_value_518_);
                    v_body_519_ = crate::leanh::lean_ctor_get(v_e_503_, 3);
                    crate::leanh::lean_inc_ref(v_body_519_);
                    v_nondep_520_ = crate::leanh::lean_ctor_get_uint8(
                        v_e_503_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
                    );
                    crate::leanh::lean_dec_ref_known(v_e_503_, 4);
                    v___x_521_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(
                        v_type_517_,
                        v_fvars_504_,
                        v_a_510_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_521_) == 0 {
                        v_a_522_ = crate::leanh::lean_ctor_get(v___x_521_, 0);
                        crate::leanh::lean_inc(v_a_522_);
                        crate::leanh::lean_dec_ref_known(v___x_521_, 1);
                        crate::leanh::lean_inc(v_a_514_);
                        crate::leanh::lean_inc_ref(v_a_513_);
                        crate::leanh::lean_inc(v_a_512_);
                        crate::leanh::lean_inc_ref(v_a_511_);
                        crate::leanh::lean_inc(v_a_510_);
                        crate::leanh::lean_inc_ref(v_a_509_);
                        crate::leanh::lean_inc(v_a_508_);
                        crate::leanh::lean_inc(v_a_507_);
                        crate::leanh::lean_inc(v_a_506_);
                        v___x_523_ = lean_sym_dsimp(
                            v_a_522_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_,
                            v_a_512_, v_a_513_, v_a_514_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_523_) == 0 {
                            v_a_524_ = crate::leanh::lean_ctor_get(v___x_523_, 0);
                            crate::leanh::lean_inc(v_a_524_);
                            crate::leanh::lean_dec_ref_known(v___x_523_, 1);
                            crate::leanh::lean_inc_ref(v_value_518_);
                            v___x_525_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(
                                v_value_518_,
                                v_fvars_504_,
                                v_a_510_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_525_) == 0 {
                                v_a_526_ = crate::leanh::lean_ctor_get(v___x_525_, 0);
                                crate::leanh::lean_inc(v_a_526_);
                                crate::leanh::lean_dec_ref_known(v___x_525_, 1);
                                crate::leanh::lean_inc(v_a_514_);
                                crate::leanh::lean_inc_ref(v_a_513_);
                                crate::leanh::lean_inc(v_a_512_);
                                crate::leanh::lean_inc_ref(v_a_511_);
                                crate::leanh::lean_inc(v_a_510_);
                                crate::leanh::lean_inc_ref(v_a_509_);
                                crate::leanh::lean_inc(v_a_508_);
                                crate::leanh::lean_inc(v_a_507_);
                                crate::leanh::lean_inc(v_a_506_);
                                v___x_527_ = lean_sym_dsimp(
                                    v_a_526_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_,
                                    v_a_511_, v_a_512_, v_a_513_, v_a_514_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_527_) == 0 {
                                    if crate::leanh::lean_obj_tag(v_a_524_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v_a_524_, 0);
                                        v_a_528_ = crate::leanh::lean_ctor_get(v___x_527_, 0);
                                        crate::leanh::lean_inc(v_a_528_);
                                        crate::leanh::lean_dec_ref_known(v___x_527_, 1);
                                        if crate::leanh::lean_obj_tag(v_a_528_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v_a_528_, 0);
                                            v___x_529_ =
                                                crate::leanh::lean_box((v_modified_505_) as usize);
                                            v___f_530_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0___boxed as *mut core::ffi::c_void, 14, 3);
                                            crate::leanh::lean_closure_set(
                                                v___f_530_,
                                                0,
                                                v_fvars_504_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_530_,
                                                1,
                                                v_body_519_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_530_, 2, v___x_529_,
                                            );
                                            v___x_531_ = 0;
                                            v___x_532_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_516_, v_type_517_, v_value_518_, v___f_530_, v_nondep_520_, v___x_531_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
                                            return v___x_532_;
                                        } else {
                                            crate::leanh::lean_dec_ref(v_value_518_);
                                            v_e_x27_533_ = crate::leanh::lean_ctor_get(v_a_528_, 0);
                                            crate::leanh::lean_inc_ref(v_e_x27_533_);
                                            crate::leanh::lean_dec_ref_known(v_a_528_, 1);
                                            v___f_534_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1___boxed as *mut core::ffi::c_void, 13, 2);
                                            crate::leanh::lean_closure_set(
                                                v___f_534_,
                                                0,
                                                v_fvars_504_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_534_,
                                                1,
                                                v_body_519_,
                                            );
                                            v___x_535_ = 0;
                                            v___x_536_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_516_, v_type_517_, v_e_x27_533_, v___f_534_, v_nondep_520_, v___x_535_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
                                            return v___x_536_;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_type_517_);
                                        v_a_537_ = crate::leanh::lean_ctor_get(v___x_527_, 0);
                                        crate::leanh::lean_inc(v_a_537_);
                                        crate::leanh::lean_dec_ref_known(v___x_527_, 1);
                                        if crate::leanh::lean_obj_tag(v_a_537_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v_a_537_, 0);
                                            v_e_x27_538_ = crate::leanh::lean_ctor_get(v_a_524_, 0);
                                            crate::leanh::lean_inc_ref(v_e_x27_538_);
                                            crate::leanh::lean_dec_ref_known(v_a_524_, 1);
                                            v___f_539_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1___boxed as *mut core::ffi::c_void, 13, 2);
                                            crate::leanh::lean_closure_set(
                                                v___f_539_,
                                                0,
                                                v_fvars_504_,
                                            );
                                            crate::leanh::lean_closure_set(
                                                v___f_539_,
                                                1,
                                                v_body_519_,
                                            );
                                            v___x_540_ = 0;
                                            v___x_541_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_516_, v_e_x27_538_, v_value_518_, v___f_539_, v_nondep_520_, v___x_540_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
                                            return v___x_541_;
                                        } else {
                                            crate::leanh::lean_dec_ref(v_value_518_);
                                            v_e_x27_542_ = crate::leanh::lean_ctor_get(v_a_524_, 0);
                                            crate::leanh::lean_inc_ref(v_e_x27_542_);
                                            crate::leanh::lean_dec_ref_known(v_a_524_, 1);
                                            v_e_x27_543_ = crate::leanh::lean_ctor_get(v_a_537_, 0);
                                            crate::leanh::lean_inc_ref(v_e_x27_543_);
                                            crate::leanh::lean_dec_ref_known(v_a_537_, 1);
                                            v___f_544_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1___boxed as *mut core::ffi::c_void, 13, 2);
                                            crate::leanh::lean_closure_set(
                                                v___f_544_,
                                                0,
                                                v_fvars_504_,
                                            );
                                            crate::leanh::lean_closure_set(
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
                                    crate::leanh::lean_dec(v_a_524_);
                                    crate::leanh::lean_dec_ref(v_body_519_);
                                    crate::leanh::lean_dec_ref(v_value_518_);
                                    crate::leanh::lean_dec_ref(v_type_517_);
                                    crate::leanh::lean_dec(v_declName_516_);
                                    crate::leanh::lean_dec_ref(v_fvars_504_);
                                    return v___x_527_;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_524_);
                                crate::leanh::lean_dec_ref(v_body_519_);
                                crate::leanh::lean_dec_ref(v_value_518_);
                                crate::leanh::lean_dec_ref(v_type_517_);
                                crate::leanh::lean_dec(v_declName_516_);
                                crate::leanh::lean_dec_ref(v_fvars_504_);
                                v_a_547_ = crate::leanh::lean_ctor_get(v___x_525_, 0);
                                v_isSharedCheck_554_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_525_)) as u8;
                                if v_isSharedCheck_554_ == 0 {
                                    v___x_549_ = v___x_525_;
                                    v_isShared_550_ = v_isSharedCheck_554_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_547_);
                                    crate::leanh::lean_dec(v___x_525_);
                                    v___x_549_ = crate::leanh::lean_box(0);
                                    v_isShared_550_ = v_isSharedCheck_554_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_body_519_);
                            crate::leanh::lean_dec_ref(v_value_518_);
                            crate::leanh::lean_dec_ref(v_type_517_);
                            crate::leanh::lean_dec(v_declName_516_);
                            crate::leanh::lean_dec_ref(v_fvars_504_);
                            return v___x_523_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_body_519_);
                        crate::leanh::lean_dec_ref(v_value_518_);
                        crate::leanh::lean_dec_ref(v_type_517_);
                        crate::leanh::lean_dec(v_declName_516_);
                        crate::leanh::lean_dec_ref(v_fvars_504_);
                        v_a_555_ = crate::leanh::lean_ctor_get(v___x_521_, 0);
                        v_isSharedCheck_562_ = (!crate::leanh::lean_is_exclusive(v___x_521_)) as u8;
                        if v_isSharedCheck_562_ == 0 {
                            v___x_557_ = v___x_521_;
                            v_isShared_558_ = v_isSharedCheck_562_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_555_);
                            crate::leanh::lean_dec(v___x_521_);
                            v___x_557_ = crate::leanh::lean_box(0);
                            v_isShared_558_ = v_isSharedCheck_562_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_e_503_);
                    v___x_563_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(
                        v_e_503_,
                        v_fvars_504_,
                        v_a_510_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_563_) == 0 {
                        v_a_564_ = crate::leanh::lean_ctor_get(v___x_563_, 0);
                        crate::leanh::lean_inc(v_a_564_);
                        crate::leanh::lean_dec_ref_known(v___x_563_, 1);
                        crate::leanh::lean_inc(v_a_514_);
                        crate::leanh::lean_inc_ref(v_a_513_);
                        crate::leanh::lean_inc(v_a_512_);
                        crate::leanh::lean_inc_ref(v_a_511_);
                        crate::leanh::lean_inc(v_a_510_);
                        crate::leanh::lean_inc_ref(v_a_509_);
                        crate::leanh::lean_inc(v_a_508_);
                        crate::leanh::lean_inc(v_a_507_);
                        crate::leanh::lean_inc(v_a_506_);
                        v___x_565_ = lean_sym_dsimp(
                            v_a_564_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_,
                            v_a_512_, v_a_513_, v_a_514_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_565_) == 0 {
                            v_a_566_ = crate::leanh::lean_ctor_get(v___x_565_, 0);
                            v_isSharedCheck_627_ =
                                (!crate::leanh::lean_is_exclusive(v___x_565_)) as u8;
                            if v_isSharedCheck_627_ == 0 {
                                v___x_568_ = v___x_565_;
                                v_isShared_569_ = v_isSharedCheck_627_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_566_);
                                crate::leanh::lean_dec(v___x_565_);
                                v___x_568_ = crate::leanh::lean_box(0);
                                v_isShared_569_ = v_isSharedCheck_627_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_fvars_504_);
                            crate::leanh::lean_dec_ref(v_e_503_);
                            return v___x_565_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_fvars_504_);
                        crate::leanh::lean_dec_ref(v_e_503_);
                        v_a_628_ = crate::leanh::lean_ctor_get(v___x_563_, 0);
                        v_isSharedCheck_635_ = (!crate::leanh::lean_is_exclusive(v___x_563_)) as u8;
                        if v_isSharedCheck_635_ == 0 {
                            v___x_630_ = v___x_563_;
                            v_isShared_631_ = v_isSharedCheck_635_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_628_);
                            crate::leanh::lean_dec(v___x_563_);
                            v___x_630_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_553_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
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
                    v_reuseFailAlloc_561_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
                    v___x_560_ = v_reuseFailAlloc_561_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_560_;
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_566_) == 0 {
                    v_isSharedCheck_599_ = (!crate::leanh::lean_is_exclusive(v_a_566_)) as u8;
                    if v_isSharedCheck_599_ == 0 {
                        v___x_571_ = v_a_566_;
                        v_isShared_572_ = v_isSharedCheck_599_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_a_566_);
                        v___x_571_ = crate::leanh::lean_box(0);
                        v_isShared_572_ = v_isSharedCheck_599_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_568_);
                    crate::leanh::lean_dec_ref(v_e_503_);
                    v_e_x27_600_ = crate::leanh::lean_ctor_get(v_a_566_, 0);
                    v_isSharedCheck_626_ = (!crate::leanh::lean_is_exclusive(v_a_566_)) as u8;
                    if v_isSharedCheck_626_ == 0 {
                        v___x_602_ = v_a_566_;
                        v_isShared_603_ = v_isSharedCheck_626_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_e_x27_600_);
                        crate::leanh::lean_dec(v_a_566_);
                        v___x_602_ = crate::leanh::lean_box(0);
                        v_isShared_603_ = v_isSharedCheck_626_;
                        state = 13;
                        continue;
                    }
                }
            }
            6 => {
                if v_modified_505_ == 0 {
                    crate::leanh::lean_dec_ref(v_fvars_504_);
                    crate::leanh::lean_dec_ref(v_e_503_);
                    if v_isShared_572_ == 0 {
                        v___x_574_ = v___x_571_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_578_ = crate::leanh::lean_alloc_ctor(0, 0, (1) as u32);
                        v___x_574_ = v_reuseFailAlloc_578_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_571_);
                    crate::leanh::lean_del_object(v___x_568_);
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
                    crate::leanh::lean_dec_ref(v_fvars_504_);
                    if crate::leanh::lean_obj_tag(v___x_581_) == 0 {
                        v_a_582_ = crate::leanh::lean_ctor_get(v___x_581_, 0);
                        v_isSharedCheck_590_ = (!crate::leanh::lean_is_exclusive(v___x_581_)) as u8;
                        if v_isSharedCheck_590_ == 0 {
                            v___x_584_ = v___x_581_;
                            v_isShared_585_ = v_isSharedCheck_590_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_582_);
                            crate::leanh::lean_dec(v___x_581_);
                            v___x_584_ = crate::leanh::lean_box(0);
                            v_isShared_585_ = v_isSharedCheck_590_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v_a_591_ = crate::leanh::lean_ctor_get(v___x_581_, 0);
                        v_isSharedCheck_598_ = (!crate::leanh::lean_is_exclusive(v___x_581_)) as u8;
                        if v_isSharedCheck_598_ == 0 {
                            v___x_593_ = v___x_581_;
                            v_isShared_594_ = v_isSharedCheck_598_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_591_);
                            crate::leanh::lean_dec(v___x_581_);
                            v___x_593_ = crate::leanh::lean_box(0);
                            v_isShared_594_ = v_isSharedCheck_598_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            7 => {
                crate::leanh::lean_ctor_set_uint8(v___x_574_, 0 as u32, v_modified_505_);
                if v_isShared_569_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_568_, 0, v___x_574_);
                    v___x_576_ = v___x_568_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_577_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
                    v___x_576_ = v_reuseFailAlloc_577_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_576_;
            }
            9 => {
                v___x_586_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_586_, 0, v_a_582_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_586_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_579_,
                );
                if v_isShared_585_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_584_, 0, v___x_586_);
                    v___x_588_ = v___x_584_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_589_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
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
                    v_reuseFailAlloc_597_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
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
                crate::leanh::lean_dec_ref(v_fvars_504_);
                if crate::leanh::lean_obj_tag(v___x_606_) == 0 {
                    v_a_607_ = crate::leanh::lean_ctor_get(v___x_606_, 0);
                    v_isSharedCheck_617_ = (!crate::leanh::lean_is_exclusive(v___x_606_)) as u8;
                    if v_isSharedCheck_617_ == 0 {
                        v___x_609_ = v___x_606_;
                        v_isShared_610_ = v_isSharedCheck_617_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_607_);
                        crate::leanh::lean_dec(v___x_606_);
                        v___x_609_ = crate::leanh::lean_box(0);
                        v_isShared_610_ = v_isSharedCheck_617_;
                        state = 14;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_602_);
                    v_a_618_ = crate::leanh::lean_ctor_get(v___x_606_, 0);
                    v_isSharedCheck_625_ = (!crate::leanh::lean_is_exclusive(v___x_606_)) as u8;
                    if v_isSharedCheck_625_ == 0 {
                        v___x_620_ = v___x_606_;
                        v_isShared_621_ = v_isSharedCheck_625_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_618_);
                        crate::leanh::lean_dec(v___x_606_);
                        v___x_620_ = crate::leanh::lean_box(0);
                        v_isShared_621_ = v_isSharedCheck_625_;
                        state = 17;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_603_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_602_, 0, v_a_607_);
                    v___x_612_ = v___x_602_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_616_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_607_);
                    v___x_612_ = v_reuseFailAlloc_616_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_612_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_604_,
                );
                if v_isShared_610_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_609_, 0, v___x_612_);
                    v___x_614_ = v___x_609_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_615_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_612_);
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
                    v_reuseFailAlloc_624_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
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
                    v_reuseFailAlloc_634_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
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
    mut v_fvars_636_: *mut crate::leanh::LeanObject,
    mut v_body_637_: *mut crate::leanh::LeanObject,
    mut v_modified_638_: u8,
    mut v_x_639_: *mut crate::leanh::LeanObject,
    mut v___y_640_: *mut crate::leanh::LeanObject,
    mut v___y_641_: *mut crate::leanh::LeanObject,
    mut v___y_642_: *mut crate::leanh::LeanObject,
    mut v___y_643_: *mut crate::leanh::LeanObject,
    mut v___y_644_: *mut crate::leanh::LeanObject,
    mut v___y_645_: *mut crate::leanh::LeanObject,
    mut v___y_646_: *mut crate::leanh::LeanObject,
    mut v___y_647_: *mut crate::leanh::LeanObject,
    mut v___y_648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_e_652_: *mut crate::leanh::LeanObject,
    mut v_fvars_653_: *mut crate::leanh::LeanObject,
    mut v_modified_654_: *mut crate::leanh::LeanObject,
    mut v_a_655_: *mut crate::leanh::LeanObject,
    mut v_a_656_: *mut crate::leanh::LeanObject,
    mut v_a_657_: *mut crate::leanh::LeanObject,
    mut v_a_658_: *mut crate::leanh::LeanObject,
    mut v_a_659_: *mut crate::leanh::LeanObject,
    mut v_a_660_: *mut crate::leanh::LeanObject,
    mut v_a_661_: *mut crate::leanh::LeanObject,
    mut v_a_662_: *mut crate::leanh::LeanObject,
    mut v_a_663_: *mut crate::leanh::LeanObject,
    mut v_a_664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_modified_boxed_665_: u8 = 0;
    let mut v_res_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_modified_boxed_665_ = (crate::leanh::lean_unbox(v_modified_654_) as u8);
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
    crate::leanh::lean_dec(v_a_663_);
    crate::leanh::lean_dec_ref(v_a_662_);
    crate::leanh::lean_dec(v_a_661_);
    crate::leanh::lean_dec_ref(v_a_660_);
    crate::leanh::lean_dec(v_a_659_);
    crate::leanh::lean_dec_ref(v_a_658_);
    crate::leanh::lean_dec(v_a_657_);
    crate::leanh::lean_dec(v_a_656_);
    crate::leanh::lean_dec(v_a_655_);
    return v_res_666_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_dsimpLet(
    mut v_e_669_: *mut crate::leanh::LeanObject,
    mut v_a_670_: *mut crate::leanh::LeanObject,
    mut v_a_671_: *mut crate::leanh::LeanObject,
    mut v_a_672_: *mut crate::leanh::LeanObject,
    mut v_a_673_: *mut crate::leanh::LeanObject,
    mut v_a_674_: *mut crate::leanh::LeanObject,
    mut v_a_675_: *mut crate::leanh::LeanObject,
    mut v_a_676_: *mut crate::leanh::LeanObject,
    mut v_a_677_: *mut crate::leanh::LeanObject,
    mut v_a_678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: u8 = 0;
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_680_ = l_Lean_Meta_Sym_DSimp_dsimpLet___closed__0;
    v___x_681_ = 0;
    v___x_682_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(
        v_e_669_, v___x_680_, v___x_681_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_,
        v_a_675_, v_a_676_, v_a_677_, v_a_678_,
    );
    return v___x_682_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_dsimpLet___boxed(
    mut v_e_683_: *mut crate::leanh::LeanObject,
    mut v_a_684_: *mut crate::leanh::LeanObject,
    mut v_a_685_: *mut crate::leanh::LeanObject,
    mut v_a_686_: *mut crate::leanh::LeanObject,
    mut v_a_687_: *mut crate::leanh::LeanObject,
    mut v_a_688_: *mut crate::leanh::LeanObject,
    mut v_a_689_: *mut crate::leanh::LeanObject,
    mut v_a_690_: *mut crate::leanh::LeanObject,
    mut v_a_691_: *mut crate::leanh::LeanObject,
    mut v_a_692_: *mut crate::leanh::LeanObject,
    mut v_a_693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_694_ = l_Lean_Meta_Sym_DSimp_dsimpLet(
        v_e_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_,
        v_a_692_,
    );
    crate::leanh::lean_dec(v_a_692_);
    crate::leanh::lean_dec_ref(v_a_691_);
    crate::leanh::lean_dec(v_a_690_);
    crate::leanh::lean_dec_ref(v_a_689_);
    crate::leanh::lean_dec(v_a_688_);
    crate::leanh::lean_dec_ref(v_a_687_);
    crate::leanh::lean_dec(v_a_686_);
    crate::leanh::lean_dec(v_a_685_);
    crate::leanh::lean_dec(v_a_684_);
    return v_res_694_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_DSimp_Let(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_AbstractS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_DSimp_Let(
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
pub unsafe fn initialize_Lean_Meta_Sym_DSimp_Let(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_AbstractS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_Let(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_DSimp_Let(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_DSimp_Let(builtin);
}

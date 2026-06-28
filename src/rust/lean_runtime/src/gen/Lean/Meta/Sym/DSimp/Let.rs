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
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::lean_imports_rs::Lean::Meta::Sym::DSimp::DSimpM::lean_sym_dsimp;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_11, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
    lean_unbox,
};
pub static l_Lean_Meta_Sym_DSimp_dsimpLet___closed__0_value: LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_Sym_DSimp_dsimpLet___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_dsimpLet___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0(
    mut v_k_348_: *mut LeanObject,
    mut v___y_349_: *mut LeanObject,
    mut v___y_350_: *mut LeanObject,
    mut v___y_351_: *mut LeanObject,
    mut v___y_352_: *mut LeanObject,
    mut v___y_353_: *mut LeanObject,
    mut v_b_354_: *mut LeanObject,
    mut v___y_355_: *mut LeanObject,
    mut v___y_356_: *mut LeanObject,
    mut v___y_357_: *mut LeanObject,
    mut v___y_358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_358_);
    lean_inc_ref(v___y_357_);
    lean_inc(v___y_356_);
    lean_inc_ref(v___y_355_);
    lean_inc(v___y_353_);
    lean_inc_ref(v___y_352_);
    lean_inc(v___y_351_);
    lean_inc(v___y_350_);
    lean_inc(v___y_349_);
    v___x_360_ = lean_apply_11(
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
        lean_box(0),
    );
    return v___x_360_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0___boxed(
    mut v_k_361_: *mut LeanObject,
    mut v___y_362_: *mut LeanObject,
    mut v___y_363_: *mut LeanObject,
    mut v___y_364_: *mut LeanObject,
    mut v___y_365_: *mut LeanObject,
    mut v___y_366_: *mut LeanObject,
    mut v_b_367_: *mut LeanObject,
    mut v___y_368_: *mut LeanObject,
    mut v___y_369_: *mut LeanObject,
    mut v___y_370_: *mut LeanObject,
    mut v___y_371_: *mut LeanObject,
    mut v___y_372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_373_: *mut LeanObject = core::ptr::null_mut();
    v_res_373_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0(v_k_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v_b_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
    lean_dec(v___y_371_);
    lean_dec_ref(v___y_370_);
    lean_dec(v___y_369_);
    lean_dec_ref(v___y_368_);
    lean_dec(v___y_366_);
    lean_dec_ref(v___y_365_);
    lean_dec(v___y_364_);
    lean_dec(v___y_363_);
    lean_dec(v___y_362_);
    return v_res_373_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(
    mut v_name_374_: *mut LeanObject,
    mut v_type_375_: *mut LeanObject,
    mut v_val_376_: *mut LeanObject,
    mut v_k_377_: *mut LeanObject,
    mut v_nondep_378_: u8,
    mut v_kind_379_: u8,
    mut v___y_380_: *mut LeanObject,
    mut v___y_381_: *mut LeanObject,
    mut v___y_382_: *mut LeanObject,
    mut v___y_383_: *mut LeanObject,
    mut v___y_384_: *mut LeanObject,
    mut v___y_385_: *mut LeanObject,
    mut v___y_386_: *mut LeanObject,
    mut v___y_387_: *mut LeanObject,
    mut v___y_388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_395_: u8 = 0;
    let mut v___x_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_399_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_384_);
                lean_inc_ref(v___y_383_);
                lean_inc(v___y_382_);
                lean_inc(v___y_381_);
                lean_inc(v___y_380_);
                v___f_390_ = lean_alloc_closure(l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 12, 6);
                lean_closure_set(v___f_390_, 0, v_k_377_);
                lean_closure_set(v___f_390_, 1, v___y_380_);
                lean_closure_set(v___f_390_, 2, v___y_381_);
                lean_closure_set(v___f_390_, 3, v___y_382_);
                lean_closure_set(v___f_390_, 4, v___y_383_);
                lean_closure_set(v___f_390_, 5, v___y_384_);
                v___x_391_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(
                    lean_box(0),
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
                if lean_obj_tag(v___x_391_) == 0 {
                    return v___x_391_;
                } else {
                    v_a_392_ = lean_ctor_get(v___x_391_, 0);
                    v_isSharedCheck_399_ = (!lean_is_exclusive(v___x_391_)) as u8;
                    if v_isSharedCheck_399_ == 0 {
                        v___x_394_ = v___x_391_;
                        v_isShared_395_ = v_isSharedCheck_399_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_392_);
                        lean_dec(v___x_391_);
                        v___x_394_ = lean_box(0);
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
                    v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
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
    mut v_name_400_: *mut LeanObject,
    mut v_type_401_: *mut LeanObject,
    mut v_val_402_: *mut LeanObject,
    mut v_k_403_: *mut LeanObject,
    mut v_nondep_404_: *mut LeanObject,
    mut v_kind_405_: *mut LeanObject,
    mut v___y_406_: *mut LeanObject,
    mut v___y_407_: *mut LeanObject,
    mut v___y_408_: *mut LeanObject,
    mut v___y_409_: *mut LeanObject,
    mut v___y_410_: *mut LeanObject,
    mut v___y_411_: *mut LeanObject,
    mut v___y_412_: *mut LeanObject,
    mut v___y_413_: *mut LeanObject,
    mut v___y_414_: *mut LeanObject,
    mut v___y_415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nondep_boxed_416_: u8 = 0;
    let mut v_kind_boxed_417_: u8 = 0;
    let mut v_res_418_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_416_ = (lean_unbox(v_nondep_404_) as u8);
    v_kind_boxed_417_ = (lean_unbox(v_kind_405_) as u8);
    v_res_418_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_name_400_, v_type_401_, v_val_402_, v_k_403_, v_nondep_boxed_416_, v_kind_boxed_417_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_);
    lean_dec(v___y_414_);
    lean_dec_ref(v___y_413_);
    lean_dec(v___y_412_);
    lean_dec_ref(v___y_411_);
    lean_dec(v___y_410_);
    lean_dec_ref(v___y_409_);
    lean_dec(v___y_408_);
    lean_dec(v___y_407_);
    lean_dec(v___y_406_);
    return v_res_418_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0(
    mut v_00_u03b1_419_: *mut LeanObject,
    mut v_name_420_: *mut LeanObject,
    mut v_type_421_: *mut LeanObject,
    mut v_val_422_: *mut LeanObject,
    mut v_k_423_: *mut LeanObject,
    mut v_nondep_424_: u8,
    mut v_kind_425_: u8,
    mut v___y_426_: *mut LeanObject,
    mut v___y_427_: *mut LeanObject,
    mut v___y_428_: *mut LeanObject,
    mut v___y_429_: *mut LeanObject,
    mut v___y_430_: *mut LeanObject,
    mut v___y_431_: *mut LeanObject,
    mut v___y_432_: *mut LeanObject,
    mut v___y_433_: *mut LeanObject,
    mut v___y_434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    v___x_436_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_name_420_, v_type_421_, v_val_422_, v_k_423_, v_nondep_424_, v_kind_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_);
    return v___x_436_;
}
pub unsafe fn l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03b1_437_: *mut LeanObject = *_args.add(0);
    let mut v_name_438_: *mut LeanObject = *_args.add(1);
    let mut v_type_439_: *mut LeanObject = *_args.add(2);
    let mut v_val_440_: *mut LeanObject = *_args.add(3);
    let mut v_k_441_: *mut LeanObject = *_args.add(4);
    let mut v_nondep_442_: *mut LeanObject = *_args.add(5);
    let mut v_kind_443_: *mut LeanObject = *_args.add(6);
    let mut v___y_444_: *mut LeanObject = *_args.add(7);
    let mut v___y_445_: *mut LeanObject = *_args.add(8);
    let mut v___y_446_: *mut LeanObject = *_args.add(9);
    let mut v___y_447_: *mut LeanObject = *_args.add(10);
    let mut v___y_448_: *mut LeanObject = *_args.add(11);
    let mut v___y_449_: *mut LeanObject = *_args.add(12);
    let mut v___y_450_: *mut LeanObject = *_args.add(13);
    let mut v___y_451_: *mut LeanObject = *_args.add(14);
    let mut v___y_452_: *mut LeanObject = *_args.add(15);
    let mut v___y_453_: *mut LeanObject = *_args.add(16);
    let mut v_nondep_boxed_454_: u8 = 0;
    let mut v_kind_boxed_455_: u8 = 0;
    let mut v_res_456_: *mut LeanObject = core::ptr::null_mut();
    v_nondep_boxed_454_ = (lean_unbox(v_nondep_442_) as u8);
    v_kind_boxed_455_ = (lean_unbox(v_kind_443_) as u8);
    v_res_456_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0(v_00_u03b1_437_, v_name_438_, v_type_439_, v_val_440_, v_k_441_, v_nondep_boxed_454_, v_kind_boxed_455_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
    lean_dec(v___y_452_);
    lean_dec_ref(v___y_451_);
    lean_dec(v___y_450_);
    lean_dec_ref(v___y_449_);
    lean_dec(v___y_448_);
    lean_dec_ref(v___y_447_);
    lean_dec(v___y_446_);
    lean_dec(v___y_445_);
    lean_dec(v___y_444_);
    return v_res_456_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0___boxed(
    mut v_fvars_457_: *mut LeanObject,
    mut v_body_458_: *mut LeanObject,
    mut v_modified_459_: *mut LeanObject,
    mut v_x_460_: *mut LeanObject,
    mut v___y_461_: *mut LeanObject,
    mut v___y_462_: *mut LeanObject,
    mut v___y_463_: *mut LeanObject,
    mut v___y_464_: *mut LeanObject,
    mut v___y_465_: *mut LeanObject,
    mut v___y_466_: *mut LeanObject,
    mut v___y_467_: *mut LeanObject,
    mut v___y_468_: *mut LeanObject,
    mut v___y_469_: *mut LeanObject,
    mut v___y_470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modified_boxed_471_: u8 = 0;
    let mut v_res_472_: *mut LeanObject = core::ptr::null_mut();
    v_modified_boxed_471_ = (lean_unbox(v_modified_459_) as u8);
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
    lean_dec(v___y_469_);
    lean_dec_ref(v___y_468_);
    lean_dec(v___y_467_);
    lean_dec_ref(v___y_466_);
    lean_dec(v___y_465_);
    lean_dec_ref(v___y_464_);
    lean_dec(v___y_463_);
    lean_dec(v___y_462_);
    lean_dec(v___y_461_);
    return v_res_472_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1(
    mut v_fvars_473_: *mut LeanObject,
    mut v_body_474_: *mut LeanObject,
    mut v_x_475_: *mut LeanObject,
    mut v___y_476_: *mut LeanObject,
    mut v___y_477_: *mut LeanObject,
    mut v___y_478_: *mut LeanObject,
    mut v___y_479_: *mut LeanObject,
    mut v___y_480_: *mut LeanObject,
    mut v___y_481_: *mut LeanObject,
    mut v___y_482_: *mut LeanObject,
    mut v___y_483_: *mut LeanObject,
    mut v___y_484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_487_: u8 = 0;
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_fvars_489_: *mut LeanObject,
    mut v_body_490_: *mut LeanObject,
    mut v_x_491_: *mut LeanObject,
    mut v___y_492_: *mut LeanObject,
    mut v___y_493_: *mut LeanObject,
    mut v___y_494_: *mut LeanObject,
    mut v___y_495_: *mut LeanObject,
    mut v___y_496_: *mut LeanObject,
    mut v___y_497_: *mut LeanObject,
    mut v___y_498_: *mut LeanObject,
    mut v___y_499_: *mut LeanObject,
    mut v___y_500_: *mut LeanObject,
    mut v___y_501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_502_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_500_);
    lean_dec_ref(v___y_499_);
    lean_dec(v___y_498_);
    lean_dec_ref(v___y_497_);
    lean_dec(v___y_496_);
    lean_dec_ref(v___y_495_);
    lean_dec(v___y_494_);
    lean_dec(v___y_493_);
    lean_dec(v___y_492_);
    return v_res_502_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(
    mut v_e_503_: *mut LeanObject,
    mut v_fvars_504_: *mut LeanObject,
    mut v_modified_505_: u8,
    mut v_a_506_: *mut LeanObject,
    mut v_a_507_: *mut LeanObject,
    mut v_a_508_: *mut LeanObject,
    mut v_a_509_: *mut LeanObject,
    mut v_a_510_: *mut LeanObject,
    mut v_a_511_: *mut LeanObject,
    mut v_a_512_: *mut LeanObject,
    mut v_a_513_: *mut LeanObject,
    mut v_a_514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_declName_516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nondep_520_: u8 = 0;
    let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_531_: u8 = 0;
    let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x27_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_535_: u8 = 0;
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x27_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_540_: u8 = 0;
    let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x27_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x27_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_545_: u8 = 0;
    let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_550_: u8 = 0;
    let mut v___x_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_554_: u8 = 0;
    let mut v_a_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_558_: u8 = 0;
    let mut v___x_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_562_: u8 = 0;
    let mut v___x_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_569_: u8 = 0;
    let mut v___x_571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_572_: u8 = 0;
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_579_: u8 = 0;
    let mut v___x_580_: u8 = 0;
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_585_: u8 = 0;
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_590_: u8 = 0;
    let mut v_a_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_594_: u8 = 0;
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_598_: u8 = 0;
    let mut v_isSharedCheck_599_: u8 = 0;
    let mut v_e_x27_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_603_: u8 = 0;
    let mut v___x_604_: u8 = 0;
    let mut v___x_605_: u8 = 0;
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_610_: u8 = 0;
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_617_: u8 = 0;
    let mut v_a_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_621_: u8 = 0;
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_625_: u8 = 0;
    let mut v_isSharedCheck_626_: u8 = 0;
    let mut v_isSharedCheck_627_: u8 = 0;
    let mut v_a_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_631_: u8 = 0;
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_635_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_503_) == 8 {
                    v_declName_516_ = lean_ctor_get(v_e_503_, 0);
                    lean_inc(v_declName_516_);
                    v_type_517_ = lean_ctor_get(v_e_503_, 1);
                    lean_inc_ref_n(v_type_517_, 2);
                    v_value_518_ = lean_ctor_get(v_e_503_, 2);
                    lean_inc_ref(v_value_518_);
                    v_body_519_ = lean_ctor_get(v_e_503_, 3);
                    lean_inc_ref(v_body_519_);
                    v_nondep_520_ = lean_ctor_get_uint8(
                        v_e_503_,
                        (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
                    );
                    lean_dec_ref_known(v_e_503_, 4);
                    v___x_521_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(
                        v_type_517_,
                        v_fvars_504_,
                        v_a_510_,
                    );
                    if lean_obj_tag(v___x_521_) == 0 {
                        v_a_522_ = lean_ctor_get(v___x_521_, 0);
                        lean_inc(v_a_522_);
                        lean_dec_ref_known(v___x_521_, 1);
                        lean_inc(v_a_514_);
                        lean_inc_ref(v_a_513_);
                        lean_inc(v_a_512_);
                        lean_inc_ref(v_a_511_);
                        lean_inc(v_a_510_);
                        lean_inc_ref(v_a_509_);
                        lean_inc(v_a_508_);
                        lean_inc(v_a_507_);
                        lean_inc(v_a_506_);
                        v___x_523_ = lean_sym_dsimp(
                            v_a_522_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_,
                            v_a_512_, v_a_513_, v_a_514_,
                        );
                        if lean_obj_tag(v___x_523_) == 0 {
                            v_a_524_ = lean_ctor_get(v___x_523_, 0);
                            lean_inc(v_a_524_);
                            lean_dec_ref_known(v___x_523_, 1);
                            lean_inc_ref(v_value_518_);
                            v___x_525_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(
                                v_value_518_,
                                v_fvars_504_,
                                v_a_510_,
                            );
                            if lean_obj_tag(v___x_525_) == 0 {
                                v_a_526_ = lean_ctor_get(v___x_525_, 0);
                                lean_inc(v_a_526_);
                                lean_dec_ref_known(v___x_525_, 1);
                                lean_inc(v_a_514_);
                                lean_inc_ref(v_a_513_);
                                lean_inc(v_a_512_);
                                lean_inc_ref(v_a_511_);
                                lean_inc(v_a_510_);
                                lean_inc_ref(v_a_509_);
                                lean_inc(v_a_508_);
                                lean_inc(v_a_507_);
                                lean_inc(v_a_506_);
                                v___x_527_ = lean_sym_dsimp(
                                    v_a_526_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_,
                                    v_a_511_, v_a_512_, v_a_513_, v_a_514_,
                                );
                                if lean_obj_tag(v___x_527_) == 0 {
                                    if lean_obj_tag(v_a_524_) == 0 {
                                        lean_dec_ref_known(v_a_524_, 0);
                                        v_a_528_ = lean_ctor_get(v___x_527_, 0);
                                        lean_inc(v_a_528_);
                                        lean_dec_ref_known(v___x_527_, 1);
                                        if lean_obj_tag(v_a_528_) == 0 {
                                            lean_dec_ref_known(v_a_528_, 0);
                                            v___x_529_ = lean_box((v_modified_505_) as usize);
                                            v___f_530_ = lean_alloc_closure(l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__0___boxed as *mut core::ffi::c_void, 14, 3);
                                            lean_closure_set(v___f_530_, 0, v_fvars_504_);
                                            lean_closure_set(v___f_530_, 1, v_body_519_);
                                            lean_closure_set(v___f_530_, 2, v___x_529_);
                                            v___x_531_ = 0;
                                            v___x_532_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_516_, v_type_517_, v_value_518_, v___f_530_, v_nondep_520_, v___x_531_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
                                            return v___x_532_;
                                        } else {
                                            lean_dec_ref(v_value_518_);
                                            v_e_x27_533_ = lean_ctor_get(v_a_528_, 0);
                                            lean_inc_ref(v_e_x27_533_);
                                            lean_dec_ref_known(v_a_528_, 1);
                                            v___f_534_ = lean_alloc_closure(l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1___boxed as *mut core::ffi::c_void, 13, 2);
                                            lean_closure_set(v___f_534_, 0, v_fvars_504_);
                                            lean_closure_set(v___f_534_, 1, v_body_519_);
                                            v___x_535_ = 0;
                                            v___x_536_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_516_, v_type_517_, v_e_x27_533_, v___f_534_, v_nondep_520_, v___x_535_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
                                            return v___x_536_;
                                        }
                                    } else {
                                        lean_dec_ref(v_type_517_);
                                        v_a_537_ = lean_ctor_get(v___x_527_, 0);
                                        lean_inc(v_a_537_);
                                        lean_dec_ref_known(v___x_527_, 1);
                                        if lean_obj_tag(v_a_537_) == 0 {
                                            lean_dec_ref_known(v_a_537_, 0);
                                            v_e_x27_538_ = lean_ctor_get(v_a_524_, 0);
                                            lean_inc_ref(v_e_x27_538_);
                                            lean_dec_ref_known(v_a_524_, 1);
                                            v___f_539_ = lean_alloc_closure(l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1___boxed as *mut core::ffi::c_void, 13, 2);
                                            lean_closure_set(v___f_539_, 0, v_fvars_504_);
                                            lean_closure_set(v___f_539_, 1, v_body_519_);
                                            v___x_540_ = 0;
                                            v___x_541_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_516_, v_e_x27_538_, v_value_518_, v___f_539_, v_nondep_520_, v___x_540_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
                                            return v___x_541_;
                                        } else {
                                            lean_dec_ref(v_value_518_);
                                            v_e_x27_542_ = lean_ctor_get(v_a_524_, 0);
                                            lean_inc_ref(v_e_x27_542_);
                                            lean_dec_ref_known(v_a_524_, 1);
                                            v_e_x27_543_ = lean_ctor_get(v_a_537_, 0);
                                            lean_inc_ref(v_e_x27_543_);
                                            lean_dec_ref_known(v_a_537_, 1);
                                            v___f_544_ = lean_alloc_closure(l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go___lam__1___boxed as *mut core::ffi::c_void, 13, 2);
                                            lean_closure_set(v___f_544_, 0, v_fvars_504_);
                                            lean_closure_set(v___f_544_, 1, v_body_519_);
                                            v___x_545_ = 0;
                                            v___x_546_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go_spec__0___redArg(v_declName_516_, v_e_x27_542_, v_e_x27_543_, v___f_544_, v_nondep_520_, v___x_545_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_, v_a_512_, v_a_513_, v_a_514_);
                                            return v___x_546_;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_524_);
                                    lean_dec_ref(v_body_519_);
                                    lean_dec_ref(v_value_518_);
                                    lean_dec_ref(v_type_517_);
                                    lean_dec(v_declName_516_);
                                    lean_dec_ref(v_fvars_504_);
                                    return v___x_527_;
                                }
                            } else {
                                lean_dec(v_a_524_);
                                lean_dec_ref(v_body_519_);
                                lean_dec_ref(v_value_518_);
                                lean_dec_ref(v_type_517_);
                                lean_dec(v_declName_516_);
                                lean_dec_ref(v_fvars_504_);
                                v_a_547_ = lean_ctor_get(v___x_525_, 0);
                                v_isSharedCheck_554_ = (!lean_is_exclusive(v___x_525_)) as u8;
                                if v_isSharedCheck_554_ == 0 {
                                    v___x_549_ = v___x_525_;
                                    v_isShared_550_ = v_isSharedCheck_554_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_547_);
                                    lean_dec(v___x_525_);
                                    v___x_549_ = lean_box(0);
                                    v_isShared_550_ = v_isSharedCheck_554_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_body_519_);
                            lean_dec_ref(v_value_518_);
                            lean_dec_ref(v_type_517_);
                            lean_dec(v_declName_516_);
                            lean_dec_ref(v_fvars_504_);
                            return v___x_523_;
                        }
                    } else {
                        lean_dec_ref(v_body_519_);
                        lean_dec_ref(v_value_518_);
                        lean_dec_ref(v_type_517_);
                        lean_dec(v_declName_516_);
                        lean_dec_ref(v_fvars_504_);
                        v_a_555_ = lean_ctor_get(v___x_521_, 0);
                        v_isSharedCheck_562_ = (!lean_is_exclusive(v___x_521_)) as u8;
                        if v_isSharedCheck_562_ == 0 {
                            v___x_557_ = v___x_521_;
                            v_isShared_558_ = v_isSharedCheck_562_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_555_);
                            lean_dec(v___x_521_);
                            v___x_557_ = lean_box(0);
                            v_isShared_558_ = v_isSharedCheck_562_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc_ref(v_e_503_);
                    v___x_563_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(
                        v_e_503_,
                        v_fvars_504_,
                        v_a_510_,
                    );
                    if lean_obj_tag(v___x_563_) == 0 {
                        v_a_564_ = lean_ctor_get(v___x_563_, 0);
                        lean_inc(v_a_564_);
                        lean_dec_ref_known(v___x_563_, 1);
                        lean_inc(v_a_514_);
                        lean_inc_ref(v_a_513_);
                        lean_inc(v_a_512_);
                        lean_inc_ref(v_a_511_);
                        lean_inc(v_a_510_);
                        lean_inc_ref(v_a_509_);
                        lean_inc(v_a_508_);
                        lean_inc(v_a_507_);
                        lean_inc(v_a_506_);
                        v___x_565_ = lean_sym_dsimp(
                            v_a_564_, v_a_506_, v_a_507_, v_a_508_, v_a_509_, v_a_510_, v_a_511_,
                            v_a_512_, v_a_513_, v_a_514_,
                        );
                        if lean_obj_tag(v___x_565_) == 0 {
                            v_a_566_ = lean_ctor_get(v___x_565_, 0);
                            v_isSharedCheck_627_ = (!lean_is_exclusive(v___x_565_)) as u8;
                            if v_isSharedCheck_627_ == 0 {
                                v___x_568_ = v___x_565_;
                                v_isShared_569_ = v_isSharedCheck_627_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_566_);
                                lean_dec(v___x_565_);
                                v___x_568_ = lean_box(0);
                                v_isShared_569_ = v_isSharedCheck_627_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_fvars_504_);
                            lean_dec_ref(v_e_503_);
                            return v___x_565_;
                        }
                    } else {
                        lean_dec_ref(v_fvars_504_);
                        lean_dec_ref(v_e_503_);
                        v_a_628_ = lean_ctor_get(v___x_563_, 0);
                        v_isSharedCheck_635_ = (!lean_is_exclusive(v___x_563_)) as u8;
                        if v_isSharedCheck_635_ == 0 {
                            v___x_630_ = v___x_563_;
                            v_isShared_631_ = v_isSharedCheck_635_;
                            state = 19;
                            continue;
                        } else {
                            lean_inc(v_a_628_);
                            lean_dec(v___x_563_);
                            v___x_630_ = lean_box(0);
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
                    v_reuseFailAlloc_553_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_553_, 0, v_a_547_);
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
                    v_reuseFailAlloc_561_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_561_, 0, v_a_555_);
                    v___x_560_ = v_reuseFailAlloc_561_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_560_;
            }
            5 => {
                if lean_obj_tag(v_a_566_) == 0 {
                    v_isSharedCheck_599_ = (!lean_is_exclusive(v_a_566_)) as u8;
                    if v_isSharedCheck_599_ == 0 {
                        v___x_571_ = v_a_566_;
                        v_isShared_572_ = v_isSharedCheck_599_;
                        state = 6;
                        continue;
                    } else {
                        lean_dec(v_a_566_);
                        v___x_571_ = lean_box(0);
                        v_isShared_572_ = v_isSharedCheck_599_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_568_);
                    lean_dec_ref(v_e_503_);
                    v_e_x27_600_ = lean_ctor_get(v_a_566_, 0);
                    v_isSharedCheck_626_ = (!lean_is_exclusive(v_a_566_)) as u8;
                    if v_isSharedCheck_626_ == 0 {
                        v___x_602_ = v_a_566_;
                        v_isShared_603_ = v_isSharedCheck_626_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_e_x27_600_);
                        lean_dec(v_a_566_);
                        v___x_602_ = lean_box(0);
                        v_isShared_603_ = v_isSharedCheck_626_;
                        state = 13;
                        continue;
                    }
                }
            }
            6 => {
                if v_modified_505_ == 0 {
                    lean_dec_ref(v_fvars_504_);
                    lean_dec_ref(v_e_503_);
                    if v_isShared_572_ == 0 {
                        v___x_574_ = v___x_571_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_578_ = lean_alloc_ctor(0, 0, (1) as u32);
                        v___x_574_ = v_reuseFailAlloc_578_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_571_);
                    lean_del_object(v___x_568_);
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
                    lean_dec_ref(v_fvars_504_);
                    if lean_obj_tag(v___x_581_) == 0 {
                        v_a_582_ = lean_ctor_get(v___x_581_, 0);
                        v_isSharedCheck_590_ = (!lean_is_exclusive(v___x_581_)) as u8;
                        if v_isSharedCheck_590_ == 0 {
                            v___x_584_ = v___x_581_;
                            v_isShared_585_ = v_isSharedCheck_590_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_582_);
                            lean_dec(v___x_581_);
                            v___x_584_ = lean_box(0);
                            v_isShared_585_ = v_isSharedCheck_590_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v_a_591_ = lean_ctor_get(v___x_581_, 0);
                        v_isSharedCheck_598_ = (!lean_is_exclusive(v___x_581_)) as u8;
                        if v_isSharedCheck_598_ == 0 {
                            v___x_593_ = v___x_581_;
                            v_isShared_594_ = v_isSharedCheck_598_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_591_);
                            lean_dec(v___x_581_);
                            v___x_593_ = lean_box(0);
                            v_isShared_594_ = v_isSharedCheck_598_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            7 => {
                lean_ctor_set_uint8(v___x_574_, 0 as u32, v_modified_505_);
                if v_isShared_569_ == 0 {
                    lean_ctor_set(v___x_568_, 0, v___x_574_);
                    v___x_576_ = v___x_568_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_577_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_577_, 0, v___x_574_);
                    v___x_576_ = v_reuseFailAlloc_577_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_576_;
            }
            9 => {
                v___x_586_ = lean_alloc_ctor(1, 1, (1) as u32);
                lean_ctor_set(v___x_586_, 0, v_a_582_);
                lean_ctor_set_uint8(
                    v___x_586_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_579_,
                );
                if v_isShared_585_ == 0 {
                    lean_ctor_set(v___x_584_, 0, v___x_586_);
                    v___x_588_ = v___x_584_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_589_, 0, v___x_586_);
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
                    v_reuseFailAlloc_597_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_597_, 0, v_a_591_);
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
                lean_dec_ref(v_fvars_504_);
                if lean_obj_tag(v___x_606_) == 0 {
                    v_a_607_ = lean_ctor_get(v___x_606_, 0);
                    v_isSharedCheck_617_ = (!lean_is_exclusive(v___x_606_)) as u8;
                    if v_isSharedCheck_617_ == 0 {
                        v___x_609_ = v___x_606_;
                        v_isShared_610_ = v_isSharedCheck_617_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_607_);
                        lean_dec(v___x_606_);
                        v___x_609_ = lean_box(0);
                        v_isShared_610_ = v_isSharedCheck_617_;
                        state = 14;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_602_);
                    v_a_618_ = lean_ctor_get(v___x_606_, 0);
                    v_isSharedCheck_625_ = (!lean_is_exclusive(v___x_606_)) as u8;
                    if v_isSharedCheck_625_ == 0 {
                        v___x_620_ = v___x_606_;
                        v_isShared_621_ = v_isSharedCheck_625_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_618_);
                        lean_dec(v___x_606_);
                        v___x_620_ = lean_box(0);
                        v_isShared_621_ = v_isSharedCheck_625_;
                        state = 17;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_603_ == 0 {
                    lean_ctor_set(v___x_602_, 0, v_a_607_);
                    v___x_612_ = v___x_602_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_616_ = lean_alloc_ctor(1, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_616_, 0, v_a_607_);
                    v___x_612_ = v_reuseFailAlloc_616_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                lean_ctor_set_uint8(
                    v___x_612_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_604_,
                );
                if v_isShared_610_ == 0 {
                    lean_ctor_set(v___x_609_, 0, v___x_612_);
                    v___x_614_ = v___x_609_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_615_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_615_, 0, v___x_612_);
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
                    v_reuseFailAlloc_624_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_624_, 0, v_a_618_);
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
                    v_reuseFailAlloc_634_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_634_, 0, v_a_628_);
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
    mut v_fvars_636_: *mut LeanObject,
    mut v_body_637_: *mut LeanObject,
    mut v_modified_638_: u8,
    mut v_x_639_: *mut LeanObject,
    mut v___y_640_: *mut LeanObject,
    mut v___y_641_: *mut LeanObject,
    mut v___y_642_: *mut LeanObject,
    mut v___y_643_: *mut LeanObject,
    mut v___y_644_: *mut LeanObject,
    mut v___y_645_: *mut LeanObject,
    mut v___y_646_: *mut LeanObject,
    mut v___y_647_: *mut LeanObject,
    mut v___y_648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_e_652_: *mut LeanObject,
    mut v_fvars_653_: *mut LeanObject,
    mut v_modified_654_: *mut LeanObject,
    mut v_a_655_: *mut LeanObject,
    mut v_a_656_: *mut LeanObject,
    mut v_a_657_: *mut LeanObject,
    mut v_a_658_: *mut LeanObject,
    mut v_a_659_: *mut LeanObject,
    mut v_a_660_: *mut LeanObject,
    mut v_a_661_: *mut LeanObject,
    mut v_a_662_: *mut LeanObject,
    mut v_a_663_: *mut LeanObject,
    mut v_a_664_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modified_boxed_665_: u8 = 0;
    let mut v_res_666_: *mut LeanObject = core::ptr::null_mut();
    v_modified_boxed_665_ = (lean_unbox(v_modified_654_) as u8);
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
    lean_dec(v_a_663_);
    lean_dec_ref(v_a_662_);
    lean_dec(v_a_661_);
    lean_dec_ref(v_a_660_);
    lean_dec(v_a_659_);
    lean_dec_ref(v_a_658_);
    lean_dec(v_a_657_);
    lean_dec(v_a_656_);
    lean_dec(v_a_655_);
    return v_res_666_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_dsimpLet(
    mut v_e_669_: *mut LeanObject,
    mut v_a_670_: *mut LeanObject,
    mut v_a_671_: *mut LeanObject,
    mut v_a_672_: *mut LeanObject,
    mut v_a_673_: *mut LeanObject,
    mut v_a_674_: *mut LeanObject,
    mut v_a_675_: *mut LeanObject,
    mut v_a_676_: *mut LeanObject,
    mut v_a_677_: *mut LeanObject,
    mut v_a_678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: u8 = 0;
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    v___x_680_ = l_Lean_Meta_Sym_DSimp_dsimpLet___closed__0;
    v___x_681_ = 0;
    v___x_682_ = l___private_Lean_Meta_Sym_DSimp_Let_0__Lean_Meta_Sym_DSimp_dsimpLet_go(
        v_e_669_, v___x_680_, v___x_681_, v_a_670_, v_a_671_, v_a_672_, v_a_673_, v_a_674_,
        v_a_675_, v_a_676_, v_a_677_, v_a_678_,
    );
    return v___x_682_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_dsimpLet___boxed(
    mut v_e_683_: *mut LeanObject,
    mut v_a_684_: *mut LeanObject,
    mut v_a_685_: *mut LeanObject,
    mut v_a_686_: *mut LeanObject,
    mut v_a_687_: *mut LeanObject,
    mut v_a_688_: *mut LeanObject,
    mut v_a_689_: *mut LeanObject,
    mut v_a_690_: *mut LeanObject,
    mut v_a_691_: *mut LeanObject,
    mut v_a_692_: *mut LeanObject,
    mut v_a_693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_694_: *mut LeanObject = core::ptr::null_mut();
    v_res_694_ = l_Lean_Meta_Sym_DSimp_dsimpLet(
        v_e_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_, v_a_688_, v_a_689_, v_a_690_, v_a_691_,
        v_a_692_,
    );
    lean_dec(v_a_692_);
    lean_dec_ref(v_a_691_);
    lean_dec(v_a_690_);
    lean_dec_ref(v_a_689_);
    lean_dec(v_a_688_);
    lean_dec_ref(v_a_687_);
    lean_dec(v_a_686_);
    lean_dec(v_a_685_);
    lean_dec(v_a_684_);
    return v_res_694_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_DSimp_Let(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_AbstractS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_DSimp_Let(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_DSimp_Let(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_AbstractS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_Let(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_DSimp_Let(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_DSimp_Let(builtin);
}

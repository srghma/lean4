// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.Forall
// Imports: Lean.Meta.Sym.DSimp.DSimpM Lean.Meta.Sym.AbstractS Lean.Meta.Sym.InstantiateS
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp;
use crate::r#gen::Lean::Meta::Sym::AbstractS::{
    initialize_Lean_Meta_Sym_AbstractS, l_Lean_Meta_Sym_mkForallFVarsS,
    runtime_initialize_Lean_Meta_Sym_AbstractS,
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
pub static l_Lean_Meta_Sym_DSimp_dsimpForall___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Meta_Sym_DSimp_dsimpForall___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_dsimpForall___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg___lam__0(
    mut v_k_319_: *mut LeanObject,
    mut v___y_320_: *mut LeanObject,
    mut v___y_321_: *mut LeanObject,
    mut v___y_322_: *mut LeanObject,
    mut v___y_323_: *mut LeanObject,
    mut v___y_324_: *mut LeanObject,
    mut v_b_325_: *mut LeanObject,
    mut v___y_326_: *mut LeanObject,
    mut v___y_327_: *mut LeanObject,
    mut v___y_328_: *mut LeanObject,
    mut v___y_329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_329_);
    lean_inc_ref(v___y_328_);
    lean_inc(v___y_327_);
    lean_inc_ref(v___y_326_);
    lean_inc(v___y_324_);
    lean_inc_ref(v___y_323_);
    lean_inc(v___y_322_);
    lean_inc(v___y_321_);
    lean_inc(v___y_320_);
    v___x_331_ = lean_apply_11(
        v_k_319_,
        v_b_325_,
        v___y_320_,
        v___y_321_,
        v___y_322_,
        v___y_323_,
        v___y_324_,
        v___y_326_,
        v___y_327_,
        v___y_328_,
        v___y_329_,
        lean_box(0),
    );
    return v___x_331_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg___lam__0___boxed(
    mut v_k_332_: *mut LeanObject,
    mut v___y_333_: *mut LeanObject,
    mut v___y_334_: *mut LeanObject,
    mut v___y_335_: *mut LeanObject,
    mut v___y_336_: *mut LeanObject,
    mut v___y_337_: *mut LeanObject,
    mut v_b_338_: *mut LeanObject,
    mut v___y_339_: *mut LeanObject,
    mut v___y_340_: *mut LeanObject,
    mut v___y_341_: *mut LeanObject,
    mut v___y_342_: *mut LeanObject,
    mut v___y_343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_344_: *mut LeanObject = core::ptr::null_mut();
    v_res_344_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg___lam__0(v_k_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v_b_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_);
    lean_dec(v___y_342_);
    lean_dec_ref(v___y_341_);
    lean_dec(v___y_340_);
    lean_dec_ref(v___y_339_);
    lean_dec(v___y_337_);
    lean_dec_ref(v___y_336_);
    lean_dec(v___y_335_);
    lean_dec(v___y_334_);
    lean_dec(v___y_333_);
    return v_res_344_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg(
    mut v_name_345_: *mut LeanObject,
    mut v_bi_346_: u8,
    mut v_type_347_: *mut LeanObject,
    mut v_k_348_: *mut LeanObject,
    mut v_kind_349_: u8,
    mut v___y_350_: *mut LeanObject,
    mut v___y_351_: *mut LeanObject,
    mut v___y_352_: *mut LeanObject,
    mut v___y_353_: *mut LeanObject,
    mut v___y_354_: *mut LeanObject,
    mut v___y_355_: *mut LeanObject,
    mut v___y_356_: *mut LeanObject,
    mut v___y_357_: *mut LeanObject,
    mut v___y_358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_365_: u8 = 0;
    let mut v___x_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_369_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_354_);
                lean_inc_ref(v___y_353_);
                lean_inc(v___y_352_);
                lean_inc(v___y_351_);
                lean_inc(v___y_350_);
                v___f_360_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 12, 6);
                lean_closure_set(v___f_360_, 0, v_k_348_);
                lean_closure_set(v___f_360_, 1, v___y_350_);
                lean_closure_set(v___f_360_, 2, v___y_351_);
                lean_closure_set(v___f_360_, 3, v___y_352_);
                lean_closure_set(v___f_360_, 4, v___y_353_);
                lean_closure_set(v___f_360_, 5, v___y_354_);
                v___x_361_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
                    v_name_345_,
                    v_bi_346_,
                    v_type_347_,
                    v___f_360_,
                    v_kind_349_,
                    v___y_355_,
                    v___y_356_,
                    v___y_357_,
                    v___y_358_,
                );
                if lean_obj_tag(v___x_361_) == 0 {
                    return v___x_361_;
                } else {
                    v_a_362_ = lean_ctor_get(v___x_361_, 0);
                    v_isSharedCheck_369_ = (!lean_is_exclusive(v___x_361_)) as u8;
                    if v_isSharedCheck_369_ == 0 {
                        v___x_364_ = v___x_361_;
                        v_isShared_365_ = v_isSharedCheck_369_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_362_);
                        lean_dec(v___x_361_);
                        v___x_364_ = lean_box(0);
                        v_isShared_365_ = v_isSharedCheck_369_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_365_ == 0 {
                    v___x_367_ = v___x_364_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_368_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_368_, 0, v_a_362_);
                    v___x_367_ = v_reuseFailAlloc_368_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_367_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg___boxed(
    mut v_name_370_: *mut LeanObject,
    mut v_bi_371_: *mut LeanObject,
    mut v_type_372_: *mut LeanObject,
    mut v_k_373_: *mut LeanObject,
    mut v_kind_374_: *mut LeanObject,
    mut v___y_375_: *mut LeanObject,
    mut v___y_376_: *mut LeanObject,
    mut v___y_377_: *mut LeanObject,
    mut v___y_378_: *mut LeanObject,
    mut v___y_379_: *mut LeanObject,
    mut v___y_380_: *mut LeanObject,
    mut v___y_381_: *mut LeanObject,
    mut v___y_382_: *mut LeanObject,
    mut v___y_383_: *mut LeanObject,
    mut v___y_384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_385_: u8 = 0;
    let mut v_kind_boxed_386_: u8 = 0;
    let mut v_res_387_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_385_ = (lean_unbox(v_bi_371_) as u8);
    v_kind_boxed_386_ = (lean_unbox(v_kind_374_) as u8);
    v_res_387_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg(v_name_370_, v_bi_boxed_385_, v_type_372_, v_k_373_, v_kind_boxed_386_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_);
    lean_dec(v___y_383_);
    lean_dec_ref(v___y_382_);
    lean_dec(v___y_381_);
    lean_dec_ref(v___y_380_);
    lean_dec(v___y_379_);
    lean_dec_ref(v___y_378_);
    lean_dec(v___y_377_);
    lean_dec(v___y_376_);
    lean_dec(v___y_375_);
    return v_res_387_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0(
    mut v_00_u03b1_388_: *mut LeanObject,
    mut v_name_389_: *mut LeanObject,
    mut v_bi_390_: u8,
    mut v_type_391_: *mut LeanObject,
    mut v_k_392_: *mut LeanObject,
    mut v_kind_393_: u8,
    mut v___y_394_: *mut LeanObject,
    mut v___y_395_: *mut LeanObject,
    mut v___y_396_: *mut LeanObject,
    mut v___y_397_: *mut LeanObject,
    mut v___y_398_: *mut LeanObject,
    mut v___y_399_: *mut LeanObject,
    mut v___y_400_: *mut LeanObject,
    mut v___y_401_: *mut LeanObject,
    mut v___y_402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_404_: *mut LeanObject = core::ptr::null_mut();
    v___x_404_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg(v_name_389_, v_bi_390_, v_type_391_, v_k_392_, v_kind_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_);
    return v___x_404_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___boxed(
    mut v_00_u03b1_405_: *mut LeanObject,
    mut v_name_406_: *mut LeanObject,
    mut v_bi_407_: *mut LeanObject,
    mut v_type_408_: *mut LeanObject,
    mut v_k_409_: *mut LeanObject,
    mut v_kind_410_: *mut LeanObject,
    mut v___y_411_: *mut LeanObject,
    mut v___y_412_: *mut LeanObject,
    mut v___y_413_: *mut LeanObject,
    mut v___y_414_: *mut LeanObject,
    mut v___y_415_: *mut LeanObject,
    mut v___y_416_: *mut LeanObject,
    mut v___y_417_: *mut LeanObject,
    mut v___y_418_: *mut LeanObject,
    mut v___y_419_: *mut LeanObject,
    mut v___y_420_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_421_: u8 = 0;
    let mut v_kind_boxed_422_: u8 = 0;
    let mut v_res_423_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_421_ = (lean_unbox(v_bi_407_) as u8);
    v_kind_boxed_422_ = (lean_unbox(v_kind_410_) as u8);
    v_res_423_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0(v_00_u03b1_405_, v_name_406_, v_bi_boxed_421_, v_type_408_, v_k_409_, v_kind_boxed_422_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
    lean_dec(v___y_419_);
    lean_dec_ref(v___y_418_);
    lean_dec(v___y_417_);
    lean_dec_ref(v___y_416_);
    lean_dec(v___y_415_);
    lean_dec_ref(v___y_414_);
    lean_dec(v___y_413_);
    lean_dec(v___y_412_);
    lean_dec(v___y_411_);
    return v_res_423_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__0___boxed(
    mut v_fvars_424_: *mut LeanObject,
    mut v_body_425_: *mut LeanObject,
    mut v_modified_426_: *mut LeanObject,
    mut v_x_427_: *mut LeanObject,
    mut v___y_428_: *mut LeanObject,
    mut v___y_429_: *mut LeanObject,
    mut v___y_430_: *mut LeanObject,
    mut v___y_431_: *mut LeanObject,
    mut v___y_432_: *mut LeanObject,
    mut v___y_433_: *mut LeanObject,
    mut v___y_434_: *mut LeanObject,
    mut v___y_435_: *mut LeanObject,
    mut v___y_436_: *mut LeanObject,
    mut v___y_437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modified_boxed_438_: u8 = 0;
    let mut v_res_439_: *mut LeanObject = core::ptr::null_mut();
    v_modified_boxed_438_ = (lean_unbox(v_modified_426_) as u8);
    v_res_439_ =
        l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__0(
            v_fvars_424_,
            v_body_425_,
            v_modified_boxed_438_,
            v_x_427_,
            v___y_428_,
            v___y_429_,
            v___y_430_,
            v___y_431_,
            v___y_432_,
            v___y_433_,
            v___y_434_,
            v___y_435_,
            v___y_436_,
        );
    lean_dec(v___y_436_);
    lean_dec_ref(v___y_435_);
    lean_dec(v___y_434_);
    lean_dec_ref(v___y_433_);
    lean_dec(v___y_432_);
    lean_dec_ref(v___y_431_);
    lean_dec(v___y_430_);
    lean_dec(v___y_429_);
    lean_dec(v___y_428_);
    return v_res_439_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__1(
    mut v_fvars_440_: *mut LeanObject,
    mut v_body_441_: *mut LeanObject,
    mut v_x_442_: *mut LeanObject,
    mut v___y_443_: *mut LeanObject,
    mut v___y_444_: *mut LeanObject,
    mut v___y_445_: *mut LeanObject,
    mut v___y_446_: *mut LeanObject,
    mut v___y_447_: *mut LeanObject,
    mut v___y_448_: *mut LeanObject,
    mut v___y_449_: *mut LeanObject,
    mut v___y_450_: *mut LeanObject,
    mut v___y_451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_454_: u8 = 0;
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    v___x_453_ = lean_array_push(v_fvars_440_, v_x_442_);
    v___x_454_ = 1;
    v___x_455_ = l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go(
        v_body_441_,
        v___x_453_,
        v___x_454_,
        v___y_443_,
        v___y_444_,
        v___y_445_,
        v___y_446_,
        v___y_447_,
        v___y_448_,
        v___y_449_,
        v___y_450_,
        v___y_451_,
    );
    return v___x_455_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__1___boxed(
    mut v_fvars_456_: *mut LeanObject,
    mut v_body_457_: *mut LeanObject,
    mut v_x_458_: *mut LeanObject,
    mut v___y_459_: *mut LeanObject,
    mut v___y_460_: *mut LeanObject,
    mut v___y_461_: *mut LeanObject,
    mut v___y_462_: *mut LeanObject,
    mut v___y_463_: *mut LeanObject,
    mut v___y_464_: *mut LeanObject,
    mut v___y_465_: *mut LeanObject,
    mut v___y_466_: *mut LeanObject,
    mut v___y_467_: *mut LeanObject,
    mut v___y_468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_469_: *mut LeanObject = core::ptr::null_mut();
    v_res_469_ =
        l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__1(
            v_fvars_456_,
            v_body_457_,
            v_x_458_,
            v___y_459_,
            v___y_460_,
            v___y_461_,
            v___y_462_,
            v___y_463_,
            v___y_464_,
            v___y_465_,
            v___y_466_,
            v___y_467_,
        );
    lean_dec(v___y_467_);
    lean_dec_ref(v___y_466_);
    lean_dec(v___y_465_);
    lean_dec_ref(v___y_464_);
    lean_dec(v___y_463_);
    lean_dec_ref(v___y_462_);
    lean_dec(v___y_461_);
    lean_dec(v___y_460_);
    lean_dec(v___y_459_);
    return v_res_469_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go(
    mut v_e_470_: *mut LeanObject,
    mut v_fvars_471_: *mut LeanObject,
    mut v_modified_472_: u8,
    mut v_a_473_: *mut LeanObject,
    mut v_a_474_: *mut LeanObject,
    mut v_a_475_: *mut LeanObject,
    mut v_a_476_: *mut LeanObject,
    mut v_a_477_: *mut LeanObject,
    mut v_a_478_: *mut LeanObject,
    mut v_a_479_: *mut LeanObject,
    mut v_a_480_: *mut LeanObject,
    mut v_a_481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_binderName_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_486_: u8 = 0;
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: u8 = 0;
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x27_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_497_: u8 = 0;
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_502_: u8 = 0;
    let mut v___x_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_506_: u8 = 0;
    let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_513_: u8 = 0;
    let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_516_: u8 = 0;
    let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_527_: u8 = 0;
    let mut v___x_528_: u8 = 0;
    let mut v___x_529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_533_: u8 = 0;
    let mut v_a_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_537_: u8 = 0;
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_541_: u8 = 0;
    let mut v_isSharedCheck_542_: u8 = 0;
    let mut v_e_x27_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_546_: u8 = 0;
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_551_: u8 = 0;
    let mut v___x_552_: u8 = 0;
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_559_: u8 = 0;
    let mut v_a_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_563_: u8 = 0;
    let mut v___x_565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_567_: u8 = 0;
    let mut v_isSharedCheck_568_: u8 = 0;
    let mut v_isSharedCheck_569_: u8 = 0;
    let mut v_a_570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_573_: u8 = 0;
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_577_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_470_) == 7 {
                    v_binderName_483_ = lean_ctor_get(v_e_470_, 0);
                    lean_inc(v_binderName_483_);
                    v_binderType_484_ = lean_ctor_get(v_e_470_, 1);
                    lean_inc_ref_n(v_binderType_484_, 2);
                    v_body_485_ = lean_ctor_get(v_e_470_, 2);
                    lean_inc_ref(v_body_485_);
                    v_binderInfo_486_ = lean_ctor_get_uint8(
                        v_e_470_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_dec_ref_known(v_e_470_, 3);
                    v___x_487_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(
                        v_binderType_484_,
                        v_fvars_471_,
                        v_a_477_,
                    );
                    if lean_obj_tag(v___x_487_) == 0 {
                        v_a_488_ = lean_ctor_get(v___x_487_, 0);
                        lean_inc(v_a_488_);
                        lean_dec_ref_known(v___x_487_, 1);
                        lean_inc(v_a_481_);
                        lean_inc_ref(v_a_480_);
                        lean_inc(v_a_479_);
                        lean_inc_ref(v_a_478_);
                        lean_inc(v_a_477_);
                        lean_inc_ref(v_a_476_);
                        lean_inc(v_a_475_);
                        lean_inc(v_a_474_);
                        lean_inc(v_a_473_);
                        v___x_489_ = lean_sym_dsimp(
                            v_a_488_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_,
                            v_a_479_, v_a_480_, v_a_481_,
                        );
                        if lean_obj_tag(v___x_489_) == 0 {
                            v_a_490_ = lean_ctor_get(v___x_489_, 0);
                            lean_inc(v_a_490_);
                            lean_dec_ref_known(v___x_489_, 1);
                            if lean_obj_tag(v_a_490_) == 0 {
                                lean_dec_ref_known(v_a_490_, 0);
                                v___x_491_ = lean_box((v_modified_472_) as usize);
                                v___f_492_ = lean_alloc_closure(l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__0___boxed as *mut core::ffi::c_void, 14, 3);
                                lean_closure_set(v___f_492_, 0, v_fvars_471_);
                                lean_closure_set(v___f_492_, 1, v_body_485_);
                                lean_closure_set(v___f_492_, 2, v___x_491_);
                                v___x_493_ = 0;
                                v___x_494_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg(v_binderName_483_, v_binderInfo_486_, v_binderType_484_, v___f_492_, v___x_493_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
                                return v___x_494_;
                            } else {
                                lean_dec_ref(v_binderType_484_);
                                v_e_x27_495_ = lean_ctor_get(v_a_490_, 0);
                                lean_inc_ref(v_e_x27_495_);
                                lean_dec_ref_known(v_a_490_, 1);
                                v___f_496_ = lean_alloc_closure(l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__1___boxed as *mut core::ffi::c_void, 13, 2);
                                lean_closure_set(v___f_496_, 0, v_fvars_471_);
                                lean_closure_set(v___f_496_, 1, v_body_485_);
                                v___x_497_ = 0;
                                v___x_498_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go_spec__0___redArg(v_binderName_483_, v_binderInfo_486_, v_e_x27_495_, v___f_496_, v___x_497_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_, v_a_479_, v_a_480_, v_a_481_);
                                return v___x_498_;
                            }
                        } else {
                            lean_dec_ref(v_body_485_);
                            lean_dec_ref(v_binderType_484_);
                            lean_dec(v_binderName_483_);
                            lean_dec_ref(v_fvars_471_);
                            return v___x_489_;
                        }
                    } else {
                        lean_dec_ref(v_body_485_);
                        lean_dec_ref(v_binderType_484_);
                        lean_dec(v_binderName_483_);
                        lean_dec_ref(v_fvars_471_);
                        v_a_499_ = lean_ctor_get(v___x_487_, 0);
                        v_isSharedCheck_506_ = (!lean_is_exclusive(v___x_487_)) as u8;
                        if v_isSharedCheck_506_ == 0 {
                            v___x_501_ = v___x_487_;
                            v_isShared_502_ = v_isSharedCheck_506_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_499_);
                            lean_dec(v___x_487_);
                            v___x_501_ = lean_box(0);
                            v_isShared_502_ = v_isSharedCheck_506_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_inc_ref(v_e_470_);
                    v___x_507_ = l_Lean_Meta_Sym_instantiateRevBetaS___redArg(
                        v_e_470_,
                        v_fvars_471_,
                        v_a_477_,
                    );
                    if lean_obj_tag(v___x_507_) == 0 {
                        v_a_508_ = lean_ctor_get(v___x_507_, 0);
                        lean_inc(v_a_508_);
                        lean_dec_ref_known(v___x_507_, 1);
                        lean_inc(v_a_481_);
                        lean_inc_ref(v_a_480_);
                        lean_inc(v_a_479_);
                        lean_inc_ref(v_a_478_);
                        lean_inc(v_a_477_);
                        lean_inc_ref(v_a_476_);
                        lean_inc(v_a_475_);
                        lean_inc(v_a_474_);
                        lean_inc(v_a_473_);
                        v___x_509_ = lean_sym_dsimp(
                            v_a_508_, v_a_473_, v_a_474_, v_a_475_, v_a_476_, v_a_477_, v_a_478_,
                            v_a_479_, v_a_480_, v_a_481_,
                        );
                        if lean_obj_tag(v___x_509_) == 0 {
                            v_a_510_ = lean_ctor_get(v___x_509_, 0);
                            v_isSharedCheck_569_ = (!lean_is_exclusive(v___x_509_)) as u8;
                            if v_isSharedCheck_569_ == 0 {
                                v___x_512_ = v___x_509_;
                                v_isShared_513_ = v_isSharedCheck_569_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_510_);
                                lean_dec(v___x_509_);
                                v___x_512_ = lean_box(0);
                                v_isShared_513_ = v_isSharedCheck_569_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_fvars_471_);
                            lean_dec_ref(v_e_470_);
                            return v___x_509_;
                        }
                    } else {
                        lean_dec_ref(v_fvars_471_);
                        lean_dec_ref(v_e_470_);
                        v_a_570_ = lean_ctor_get(v___x_507_, 0);
                        v_isSharedCheck_577_ = (!lean_is_exclusive(v___x_507_)) as u8;
                        if v_isSharedCheck_577_ == 0 {
                            v___x_572_ = v___x_507_;
                            v_isShared_573_ = v_isSharedCheck_577_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_570_);
                            lean_dec(v___x_507_);
                            v___x_572_ = lean_box(0);
                            v_isShared_573_ = v_isSharedCheck_577_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_502_ == 0 {
                    v___x_504_ = v___x_501_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_505_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_505_, 0, v_a_499_);
                    v___x_504_ = v_reuseFailAlloc_505_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_504_;
            }
            3 => {
                if lean_obj_tag(v_a_510_) == 0 {
                    v_isSharedCheck_542_ = (!lean_is_exclusive(v_a_510_)) as u8;
                    if v_isSharedCheck_542_ == 0 {
                        v___x_515_ = v_a_510_;
                        v_isShared_516_ = v_isSharedCheck_542_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_a_510_);
                        v___x_515_ = lean_box(0);
                        v_isShared_516_ = v_isSharedCheck_542_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_512_);
                    lean_dec_ref(v_e_470_);
                    v_e_x27_543_ = lean_ctor_get(v_a_510_, 0);
                    v_isSharedCheck_568_ = (!lean_is_exclusive(v_a_510_)) as u8;
                    if v_isSharedCheck_568_ == 0 {
                        v___x_545_ = v_a_510_;
                        v_isShared_546_ = v_isSharedCheck_568_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_e_x27_543_);
                        lean_dec(v_a_510_);
                        v___x_545_ = lean_box(0);
                        v_isShared_546_ = v_isSharedCheck_568_;
                        state = 11;
                        continue;
                    }
                }
            }
            4 => {
                if v_modified_472_ == 0 {
                    lean_dec_ref(v_fvars_471_);
                    lean_dec_ref(v_e_470_);
                    if v_isShared_516_ == 0 {
                        v___x_518_ = v___x_515_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 0, (1) as u32);
                        v___x_518_ = v_reuseFailAlloc_522_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_515_);
                    lean_del_object(v___x_512_);
                    v___x_523_ = l_Lean_Meta_Sym_mkForallFVarsS(
                        v_fvars_471_,
                        v_e_470_,
                        v_a_476_,
                        v_a_477_,
                        v_a_478_,
                        v_a_479_,
                        v_a_480_,
                        v_a_481_,
                    );
                    lean_dec_ref(v_fvars_471_);
                    if lean_obj_tag(v___x_523_) == 0 {
                        v_a_524_ = lean_ctor_get(v___x_523_, 0);
                        v_isSharedCheck_533_ = (!lean_is_exclusive(v___x_523_)) as u8;
                        if v_isSharedCheck_533_ == 0 {
                            v___x_526_ = v___x_523_;
                            v_isShared_527_ = v_isSharedCheck_533_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_524_);
                            lean_dec(v___x_523_);
                            v___x_526_ = lean_box(0);
                            v_isShared_527_ = v_isSharedCheck_533_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v_a_534_ = lean_ctor_get(v___x_523_, 0);
                        v_isSharedCheck_541_ = (!lean_is_exclusive(v___x_523_)) as u8;
                        if v_isSharedCheck_541_ == 0 {
                            v___x_536_ = v___x_523_;
                            v_isShared_537_ = v_isSharedCheck_541_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_534_);
                            lean_dec(v___x_523_);
                            v___x_536_ = lean_box(0);
                            v_isShared_537_ = v_isSharedCheck_541_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            5 => {
                lean_ctor_set_uint8(v___x_518_, 0 as u32, v_modified_472_);
                if v_isShared_513_ == 0 {
                    lean_ctor_set(v___x_512_, 0, v___x_518_);
                    v___x_520_ = v___x_512_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
                    v___x_520_ = v_reuseFailAlloc_521_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_520_;
            }
            7 => {
                v___x_528_ = 0;
                v___x_529_ = lean_alloc_ctor(1, 1, (1) as u32);
                lean_ctor_set(v___x_529_, 0, v_a_524_);
                lean_ctor_set_uint8(
                    v___x_529_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_528_,
                );
                if v_isShared_527_ == 0 {
                    lean_ctor_set(v___x_526_, 0, v___x_529_);
                    v___x_531_ = v___x_526_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
                    v___x_531_ = v_reuseFailAlloc_532_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_531_;
            }
            9 => {
                if v_isShared_537_ == 0 {
                    v___x_539_ = v___x_536_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_540_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
                    v___x_539_ = v_reuseFailAlloc_540_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_539_;
            }
            11 => {
                v___x_547_ = l_Lean_Meta_Sym_mkForallFVarsS(
                    v_fvars_471_,
                    v_e_x27_543_,
                    v_a_476_,
                    v_a_477_,
                    v_a_478_,
                    v_a_479_,
                    v_a_480_,
                    v_a_481_,
                );
                lean_dec_ref(v_fvars_471_);
                if lean_obj_tag(v___x_547_) == 0 {
                    v_a_548_ = lean_ctor_get(v___x_547_, 0);
                    v_isSharedCheck_559_ = (!lean_is_exclusive(v___x_547_)) as u8;
                    if v_isSharedCheck_559_ == 0 {
                        v___x_550_ = v___x_547_;
                        v_isShared_551_ = v_isSharedCheck_559_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_548_);
                        lean_dec(v___x_547_);
                        v___x_550_ = lean_box(0);
                        v_isShared_551_ = v_isSharedCheck_559_;
                        state = 12;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_545_);
                    v_a_560_ = lean_ctor_get(v___x_547_, 0);
                    v_isSharedCheck_567_ = (!lean_is_exclusive(v___x_547_)) as u8;
                    if v_isSharedCheck_567_ == 0 {
                        v___x_562_ = v___x_547_;
                        v_isShared_563_ = v_isSharedCheck_567_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_560_);
                        lean_dec(v___x_547_);
                        v___x_562_ = lean_box(0);
                        v_isShared_563_ = v_isSharedCheck_567_;
                        state = 15;
                        continue;
                    }
                }
            }
            12 => {
                v___x_552_ = 0;
                if v_isShared_546_ == 0 {
                    lean_ctor_set(v___x_545_, 0, v_a_548_);
                    v___x_554_ = v___x_545_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 1, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_558_, 0, v_a_548_);
                    v___x_554_ = v_reuseFailAlloc_558_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                lean_ctor_set_uint8(
                    v___x_554_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_552_,
                );
                if v_isShared_551_ == 0 {
                    lean_ctor_set(v___x_550_, 0, v___x_554_);
                    v___x_556_ = v___x_550_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_554_);
                    v___x_556_ = v_reuseFailAlloc_557_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_556_;
            }
            15 => {
                if v_isShared_563_ == 0 {
                    v___x_565_ = v___x_562_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_566_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_566_, 0, v_a_560_);
                    v___x_565_ = v_reuseFailAlloc_566_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_565_;
            }
            17 => {
                if v_isShared_573_ == 0 {
                    v___x_575_ = v___x_572_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_576_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_576_, 0, v_a_570_);
                    v___x_575_ = v_reuseFailAlloc_576_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_575_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___lam__0(
    mut v_fvars_578_: *mut LeanObject,
    mut v_body_579_: *mut LeanObject,
    mut v_modified_580_: u8,
    mut v_x_581_: *mut LeanObject,
    mut v___y_582_: *mut LeanObject,
    mut v___y_583_: *mut LeanObject,
    mut v___y_584_: *mut LeanObject,
    mut v___y_585_: *mut LeanObject,
    mut v___y_586_: *mut LeanObject,
    mut v___y_587_: *mut LeanObject,
    mut v___y_588_: *mut LeanObject,
    mut v___y_589_: *mut LeanObject,
    mut v___y_590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    v___x_592_ = lean_array_push(v_fvars_578_, v_x_581_);
    v___x_593_ = l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go(
        v_body_579_,
        v___x_592_,
        v_modified_580_,
        v___y_582_,
        v___y_583_,
        v___y_584_,
        v___y_585_,
        v___y_586_,
        v___y_587_,
        v___y_588_,
        v___y_589_,
        v___y_590_,
    );
    return v___x_593_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go___boxed(
    mut v_e_594_: *mut LeanObject,
    mut v_fvars_595_: *mut LeanObject,
    mut v_modified_596_: *mut LeanObject,
    mut v_a_597_: *mut LeanObject,
    mut v_a_598_: *mut LeanObject,
    mut v_a_599_: *mut LeanObject,
    mut v_a_600_: *mut LeanObject,
    mut v_a_601_: *mut LeanObject,
    mut v_a_602_: *mut LeanObject,
    mut v_a_603_: *mut LeanObject,
    mut v_a_604_: *mut LeanObject,
    mut v_a_605_: *mut LeanObject,
    mut v_a_606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_modified_boxed_607_: u8 = 0;
    let mut v_res_608_: *mut LeanObject = core::ptr::null_mut();
    v_modified_boxed_607_ = (lean_unbox(v_modified_596_) as u8);
    v_res_608_ = l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go(
        v_e_594_,
        v_fvars_595_,
        v_modified_boxed_607_,
        v_a_597_,
        v_a_598_,
        v_a_599_,
        v_a_600_,
        v_a_601_,
        v_a_602_,
        v_a_603_,
        v_a_604_,
        v_a_605_,
    );
    lean_dec(v_a_605_);
    lean_dec_ref(v_a_604_);
    lean_dec(v_a_603_);
    lean_dec_ref(v_a_602_);
    lean_dec(v_a_601_);
    lean_dec_ref(v_a_600_);
    lean_dec(v_a_599_);
    lean_dec(v_a_598_);
    lean_dec(v_a_597_);
    return v_res_608_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_dsimpForall(
    mut v_e_611_: *mut LeanObject,
    mut v_a_612_: *mut LeanObject,
    mut v_a_613_: *mut LeanObject,
    mut v_a_614_: *mut LeanObject,
    mut v_a_615_: *mut LeanObject,
    mut v_a_616_: *mut LeanObject,
    mut v_a_617_: *mut LeanObject,
    mut v_a_618_: *mut LeanObject,
    mut v_a_619_: *mut LeanObject,
    mut v_a_620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: u8 = 0;
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    v___x_622_ = l_Lean_Meta_Sym_DSimp_dsimpForall___closed__0;
    v___x_623_ = 0;
    v___x_624_ = l___private_Lean_Meta_Sym_DSimp_Forall_0__Lean_Meta_Sym_DSimp_dsimpForall_go(
        v_e_611_, v___x_622_, v___x_623_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_,
        v_a_617_, v_a_618_, v_a_619_, v_a_620_,
    );
    return v___x_624_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_dsimpForall___boxed(
    mut v_e_625_: *mut LeanObject,
    mut v_a_626_: *mut LeanObject,
    mut v_a_627_: *mut LeanObject,
    mut v_a_628_: *mut LeanObject,
    mut v_a_629_: *mut LeanObject,
    mut v_a_630_: *mut LeanObject,
    mut v_a_631_: *mut LeanObject,
    mut v_a_632_: *mut LeanObject,
    mut v_a_633_: *mut LeanObject,
    mut v_a_634_: *mut LeanObject,
    mut v_a_635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_636_: *mut LeanObject = core::ptr::null_mut();
    v_res_636_ = l_Lean_Meta_Sym_DSimp_dsimpForall(
        v_e_625_, v_a_626_, v_a_627_, v_a_628_, v_a_629_, v_a_630_, v_a_631_, v_a_632_, v_a_633_,
        v_a_634_,
    );
    lean_dec(v_a_634_);
    lean_dec_ref(v_a_633_);
    lean_dec(v_a_632_);
    lean_dec_ref(v_a_631_);
    lean_dec(v_a_630_);
    lean_dec_ref(v_a_629_);
    lean_dec(v_a_628_);
    lean_dec(v_a_627_);
    lean_dec(v_a_626_);
    return v_res_636_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_DSimp_Forall(builtin: u8) -> *mut LeanObject {
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
pub unsafe fn meta_initialize_Lean_Meta_Sym_DSimp_Forall(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_DSimp_Forall(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lean_Meta_Sym_DSimp_Forall(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_DSimp_Forall(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_DSimp_Forall(builtin);
}

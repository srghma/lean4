// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.App
// Imports: Lean.Meta.Sym.DSimp.DSimpM Lean.Meta.Sym.DSimp.Result Lean.Meta.Sym.AlphaShareBuilder Lean.Meta.Sym.ProofInstInfo Init.Omega
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub,
    lean_panic_fn_borrowed, lean_st_ref_get, lean_sym_dsimp,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
};
use crate::r#gen::Lean::Meta::Sym::AlphaShareBuilder::{
    initialize_Lean_Meta_Sym_AlphaShareBuilder, l_Lean_Meta_Sym_Internal_Sym_assertShared,
    l_Lean_Meta_Sym_Internal_Sym_share1___redArg,
    runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder,
};
use crate::r#gen::Lean::Meta::Sym::DSimp::DSimpM::{
    initialize_Lean_Meta_Sym_DSimp_DSimpM, l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM,
    runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM,
};
use crate::r#gen::Lean::Meta::Sym::DSimp::Result::{
    initialize_Lean_Meta_Sym_DSimp_Result, runtime_initialize_Lean_Meta_Sym_DSimp_Result,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Sym::ProofInstInfo::{
    initialize_Lean_Meta_Sym_ProofInstInfo, l_Lean_Meta_Sym_getProofInstInfoOfExpr_x3f___redArg,
    runtime_initialize_Lean_Meta_Sym_ProofInstInfo,
};
static mut l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 68, 83, 105, 109, 112, 46, 65, 112, 112, 0]};
static mut l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__1_value: crate::leanh::LeanStringObject<71> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 71, m_capacity: 71, m_length: 70, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 68, 83, 105, 109, 112, 46, 65, 112, 112, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 83, 121, 109, 46, 68, 83, 105, 109, 112, 46, 100, 115, 105, 109, 112, 65, 112, 112, 65, 114, 103, 115, 46, 103, 111, 0]};
static mut l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__2_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__4_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0 + 8) as u16, other: 0, tag: 0 }, m_objs: [0 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__4_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(
    mut v_f_322_: *mut crate::leanh::LeanObject,
    mut v_a_323_: *mut crate::leanh::LeanObject,
    mut v___y_324_: *mut crate::leanh::LeanObject,
    mut v___y_325_: *mut crate::leanh::LeanObject,
    mut v___y_326_: *mut crate::leanh::LeanObject,
    mut v___y_327_: *mut crate::leanh::LeanObject,
    mut v___y_328_: *mut crate::leanh::LeanObject,
    mut v___y_329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_336_: u8 = 0;
    let mut v___x_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_342_: u8 = 0;
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_346_: u8 = 0;
    let mut v_a_347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_350_: u8 = 0;
    let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_354_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_335_ = lean_st_ref_get(v___y_325_);
                v_debug_336_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_335_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                crate::leanh::lean_dec(v___x_335_);
                if v_debug_336_ == 0 {
                    v___y_332_ = v___y_325_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_f_322_);
                    v___x_337_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                        v_f_322_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_,
                        v___y_329_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_337_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_337_, 1);
                        crate::leanh::lean_inc_ref(v_a_323_);
                        v___x_338_ = l_Lean_Meta_Sym_Internal_Sym_assertShared(
                            v_a_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_,
                            v___y_329_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_338_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_338_, 1);
                            v___y_332_ = v___y_325_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_a_323_);
                            crate::leanh::lean_dec_ref(v_f_322_);
                            v_a_339_ = crate::leanh::lean_ctor_get(v___x_338_, 0);
                            v_isSharedCheck_346_ =
                                (!crate::leanh::lean_is_exclusive(v___x_338_)) as u8;
                            if v_isSharedCheck_346_ == 0 {
                                v___x_341_ = v___x_338_;
                                v_isShared_342_ = v_isSharedCheck_346_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_339_);
                                crate::leanh::lean_dec(v___x_338_);
                                v___x_341_ = crate::leanh::lean_box(0);
                                v_isShared_342_ = v_isSharedCheck_346_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_a_323_);
                        crate::leanh::lean_dec_ref(v_f_322_);
                        v_a_347_ = crate::leanh::lean_ctor_get(v___x_337_, 0);
                        v_isSharedCheck_354_ = (!crate::leanh::lean_is_exclusive(v___x_337_)) as u8;
                        if v_isSharedCheck_354_ == 0 {
                            v___x_349_ = v___x_337_;
                            v_isShared_350_ = v_isSharedCheck_354_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_347_);
                            crate::leanh::lean_dec(v___x_337_);
                            v___x_349_ = crate::leanh::lean_box(0);
                            v_isShared_350_ = v_isSharedCheck_354_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_333_ = l_Lean_Expr_app___override(v_f_322_, v_a_323_);
                v___x_334_ = l_Lean_Meta_Sym_Internal_Sym_share1___redArg(v___x_333_, v___y_332_);
                return v___x_334_;
            }
            2 => {
                if v_isShared_342_ == 0 {
                    v___x_344_ = v___x_341_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_345_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_345_, 0, v_a_339_);
                    v___x_344_ = v_reuseFailAlloc_345_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_344_;
            }
            4 => {
                if v_isShared_350_ == 0 {
                    v___x_352_ = v___x_349_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_353_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_353_, 0, v_a_347_);
                    v___x_352_ = v_reuseFailAlloc_353_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_352_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg___boxed(
    mut v_f_355_: *mut crate::leanh::LeanObject,
    mut v_a_356_: *mut crate::leanh::LeanObject,
    mut v___y_357_: *mut crate::leanh::LeanObject,
    mut v___y_358_: *mut crate::leanh::LeanObject,
    mut v___y_359_: *mut crate::leanh::LeanObject,
    mut v___y_360_: *mut crate::leanh::LeanObject,
    mut v___y_361_: *mut crate::leanh::LeanObject,
    mut v___y_362_: *mut crate::leanh::LeanObject,
    mut v___y_363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_364_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(v_f_355_, v_a_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_);
    crate::leanh::lean_dec(v___y_362_);
    crate::leanh::lean_dec_ref(v___y_361_);
    crate::leanh::lean_dec(v___y_360_);
    crate::leanh::lean_dec_ref(v___y_359_);
    crate::leanh::lean_dec(v___y_358_);
    crate::leanh::lean_dec_ref(v___y_357_);
    return v_res_364_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0(
    mut v_f_365_: *mut crate::leanh::LeanObject,
    mut v_a_366_: *mut crate::leanh::LeanObject,
    mut v___y_367_: *mut crate::leanh::LeanObject,
    mut v___y_368_: *mut crate::leanh::LeanObject,
    mut v___y_369_: *mut crate::leanh::LeanObject,
    mut v___y_370_: *mut crate::leanh::LeanObject,
    mut v___y_371_: *mut crate::leanh::LeanObject,
    mut v___y_372_: *mut crate::leanh::LeanObject,
    mut v___y_373_: *mut crate::leanh::LeanObject,
    mut v___y_374_: *mut crate::leanh::LeanObject,
    mut v___y_375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_377_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(v_f_365_, v_a_366_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
    return v___x_377_;
}
pub unsafe fn l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___boxed(
    mut v_f_378_: *mut crate::leanh::LeanObject,
    mut v_a_379_: *mut crate::leanh::LeanObject,
    mut v___y_380_: *mut crate::leanh::LeanObject,
    mut v___y_381_: *mut crate::leanh::LeanObject,
    mut v___y_382_: *mut crate::leanh::LeanObject,
    mut v___y_383_: *mut crate::leanh::LeanObject,
    mut v___y_384_: *mut crate::leanh::LeanObject,
    mut v___y_385_: *mut crate::leanh::LeanObject,
    mut v___y_386_: *mut crate::leanh::LeanObject,
    mut v___y_387_: *mut crate::leanh::LeanObject,
    mut v___y_388_: *mut crate::leanh::LeanObject,
    mut v___y_389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_390_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0(v_f_378_, v_a_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
    crate::leanh::lean_dec(v___y_388_);
    crate::leanh::lean_dec_ref(v___y_387_);
    crate::leanh::lean_dec(v___y_386_);
    crate::leanh::lean_dec_ref(v___y_385_);
    crate::leanh::lean_dec(v___y_384_);
    crate::leanh::lean_dec_ref(v___y_383_);
    crate::leanh::lean_dec(v___y_382_);
    crate::leanh::lean_dec(v___y_381_);
    crate::leanh::lean_dec(v___y_380_);
    return v_res_390_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_391_ = l_Lean_Meta_Sym_DSimp_instInhabitedDSimpM(crate::leanh::lean_box(0));
    return v___x_391_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1(
    mut v_msg_392_: *mut crate::leanh::LeanObject,
    mut v___y_393_: *mut crate::leanh::LeanObject,
    mut v___y_394_: *mut crate::leanh::LeanObject,
    mut v___y_395_: *mut crate::leanh::LeanObject,
    mut v___y_396_: *mut crate::leanh::LeanObject,
    mut v___y_397_: *mut crate::leanh::LeanObject,
    mut v___y_398_: *mut crate::leanh::LeanObject,
    mut v___y_399_: *mut crate::leanh::LeanObject,
    mut v___y_400_: *mut crate::leanh::LeanObject,
    mut v___y_401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_12019__overap_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_403_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___closed__0);
    v___x_12019__overap_404_ = lean_panic_fn_borrowed(v___x_403_, v_msg_392_);
    crate::leanh::lean_inc(v___y_401_);
    crate::leanh::lean_inc_ref(v___y_400_);
    crate::leanh::lean_inc(v___y_399_);
    crate::leanh::lean_inc_ref(v___y_398_);
    crate::leanh::lean_inc(v___y_397_);
    crate::leanh::lean_inc_ref(v___y_396_);
    crate::leanh::lean_inc(v___y_395_);
    crate::leanh::lean_inc(v___y_394_);
    crate::leanh::lean_inc(v___y_393_);
    v___x_405_ = crate::leanh::lean_apply_10(
        v___x_12019__overap_404_,
        v___y_393_,
        v___y_394_,
        v___y_395_,
        v___y_396_,
        v___y_397_,
        v___y_398_,
        v___y_399_,
        v___y_400_,
        v___y_401_,
        crate::leanh::lean_box(0),
    );
    return v___x_405_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1___boxed(
    mut v_msg_406_: *mut crate::leanh::LeanObject,
    mut v___y_407_: *mut crate::leanh::LeanObject,
    mut v___y_408_: *mut crate::leanh::LeanObject,
    mut v___y_409_: *mut crate::leanh::LeanObject,
    mut v___y_410_: *mut crate::leanh::LeanObject,
    mut v___y_411_: *mut crate::leanh::LeanObject,
    mut v___y_412_: *mut crate::leanh::LeanObject,
    mut v___y_413_: *mut crate::leanh::LeanObject,
    mut v___y_414_: *mut crate::leanh::LeanObject,
    mut v___y_415_: *mut crate::leanh::LeanObject,
    mut v___y_416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_417_ = l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1(v_msg_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
    crate::leanh::lean_dec(v___y_415_);
    crate::leanh::lean_dec_ref(v___y_414_);
    crate::leanh::lean_dec(v___y_413_);
    crate::leanh::lean_dec_ref(v___y_412_);
    crate::leanh::lean_dec(v___y_411_);
    crate::leanh::lean_dec_ref(v___y_410_);
    crate::leanh::lean_dec(v___y_409_);
    crate::leanh::lean_dec(v___y_408_);
    crate::leanh::lean_dec(v___y_407_);
    return v_res_417_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_421_ =
        l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__2;
    v___x_422_ = crate::leanh::lean_unsigned_to_nat(24);
    v___x_423_ = crate::leanh::lean_unsigned_to_nat(51);
    v___x_424_ =
        l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__1;
    v___x_425_ =
        l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__0;
    v___x_426_ =
        l_mkPanicMessageWithDecl(v___x_425_, v___x_424_, v___x_423_, v___x_422_, v___x_421_);
    return v___x_426_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go(
    mut v_argsInfo_x3f_429_: *mut crate::leanh::LeanObject,
    mut v_i_430_: *mut crate::leanh::LeanObject,
    mut v_e_431_: *mut crate::leanh::LeanObject,
    mut v_a_432_: *mut crate::leanh::LeanObject,
    mut v_a_433_: *mut crate::leanh::LeanObject,
    mut v_a_434_: *mut crate::leanh::LeanObject,
    mut v_a_435_: *mut crate::leanh::LeanObject,
    mut v_a_436_: *mut crate::leanh::LeanObject,
    mut v_a_437_: *mut crate::leanh::LeanObject,
    mut v_a_438_: *mut crate::leanh::LeanObject,
    mut v_a_439_: *mut crate::leanh::LeanObject,
    mut v_a_440_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_443_: u8 = 0;
    let mut v_a_445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_468_: u8 = 0;
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_474_: u8 = 0;
    let mut v___x_476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_478_: u8 = 0;
    let mut v_fn_479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_492_: u8 = 0;
    let mut v___x_493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_498_: u8 = 0;
    let mut v___x_500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_502_: u8 = 0;
    let mut v___y_504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_514_: u8 = 0;
    let mut v___x_515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_520_: u8 = 0;
    let mut v___x_522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_524_: u8 = 0;
    let mut v___x_525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_531_: u8 = 0;
    let mut v_ar_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_545_: u8 = 0;
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_552_: u8 = 0;
    let mut v_e_x27_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: u8 = 0;
    let mut v___x_555_: u8 = 0;
    let mut v_e_x27_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_557_: u8 = 0;
    let mut v___x_558_: u8 = 0;
    let mut v_e_x27_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_561_: u8 = 0;
    let mut v___x_562_: u8 = 0;
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_570_: u8 = 0;
    let mut v___x_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isProof_572_: u8 = 0;
    let mut v_isInstance_573_: u8 = 0;
    let mut v_isSharedCheck_574_: u8 = 0;
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_442_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_443_ = lean_nat_dec_eq(v_i_430_, v___x_442_);
                if v___x_443_ == 0 {
                    if crate::leanh::lean_obj_tag(v_e_431_) == 5 {
                        v_fn_479_ = crate::leanh::lean_ctor_get(v_e_431_, 0);
                        v_arg_480_ = crate::leanh::lean_ctor_get(v_e_431_, 1);
                        v___x_525_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_526_ = lean_nat_sub(v_i_430_, v___x_525_);
                        crate::leanh::lean_inc_ref(v_fn_479_);
                        v___x_527_ = l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go(v_argsInfo_x3f_429_, v___x_526_, v_fn_479_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
                        if crate::leanh::lean_obj_tag(v___x_527_) == 0 {
                            v_a_528_ = crate::leanh::lean_ctor_get(v___x_527_, 0);
                            v_isSharedCheck_574_ =
                                (!crate::leanh::lean_is_exclusive(v___x_527_)) as u8;
                            if v_isSharedCheck_574_ == 0 {
                                v___x_530_ = v___x_527_;
                                v_isShared_531_ = v_isSharedCheck_574_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_528_);
                                crate::leanh::lean_dec(v___x_527_);
                                v___x_530_ = crate::leanh::lean_box(0);
                                v_isShared_531_ = v_isSharedCheck_574_;
                                state = 13;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_526_);
                            crate::leanh::lean_dec_ref_known(v_e_431_, 2);
                            return v___x_527_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_431_);
                        v___x_575_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__3_once), _init_l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__3);
                        v___x_576_ = l_panic___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__1(v___x_575_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_, v_a_438_, v_a_439_, v_a_440_);
                        return v___x_576_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_431_);
                    v___x_577_ = l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__4;
                    v___x_578_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_578_, 0, v___x_577_);
                    return v___x_578_;
                }
            }
            1 => {
                v___x_446_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_446_, 0, v_a_445_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_446_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_443_,
                );
                v___x_447_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_447_, 0, v___x_446_);
                return v___x_447_;
            }
            2 => {
                v___x_450_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_450_, 0, v_a_449_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_450_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_443_,
                );
                v___x_451_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_451_, 0, v___x_450_);
                return v___x_451_;
            }
            3 => {
                v___x_454_ = crate::leanh::lean_alloc_ctor(1, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_454_, 0, v_a_453_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_454_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_443_,
                );
                v___x_455_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_455_, 0, v___x_454_);
                return v___x_455_;
            }
            4 => {
                if v___y_468_ == 0 {
                    crate::leanh::lean_dec_ref(v_e_431_);
                    v___x_469_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(v___y_467_, v___y_461_, v___y_459_, v___y_458_, v___y_463_, v___y_466_, v___y_457_, v___y_462_);
                    if crate::leanh::lean_obj_tag(v___x_469_) == 0 {
                        v_a_470_ = crate::leanh::lean_ctor_get(v___x_469_, 0);
                        crate::leanh::lean_inc(v_a_470_);
                        crate::leanh::lean_dec_ref_known(v___x_469_, 1);
                        v_a_453_ = v_a_470_;
                        state = 3;
                        continue;
                    } else {
                        v_a_471_ = crate::leanh::lean_ctor_get(v___x_469_, 0);
                        v_isSharedCheck_478_ = (!crate::leanh::lean_is_exclusive(v___x_469_)) as u8;
                        if v_isSharedCheck_478_ == 0 {
                            v___x_473_ = v___x_469_;
                            v_isShared_474_ = v_isSharedCheck_478_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_471_);
                            crate::leanh::lean_dec(v___x_469_);
                            v___x_473_ = crate::leanh::lean_box(0);
                            v_isShared_474_ = v_isSharedCheck_478_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_467_);
                    crate::leanh::lean_dec_ref(v___y_461_);
                    v_a_453_ = v_e_431_;
                    state = 3;
                    continue;
                }
            }
            5 => {
                if v_isShared_474_ == 0 {
                    v___x_476_ = v___x_473_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_477_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
                    v___x_476_ = v_reuseFailAlloc_477_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_476_;
            }
            7 => {
                if v___y_492_ == 0 {
                    crate::leanh::lean_inc_ref(v_arg_480_);
                    crate::leanh::lean_dec_ref_known(v_e_431_, 2);
                    v___x_493_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(v___y_491_, v_arg_480_, v___y_484_, v___y_483_, v___y_487_, v___y_490_, v___y_482_, v___y_486_);
                    if crate::leanh::lean_obj_tag(v___x_493_) == 0 {
                        v_a_494_ = crate::leanh::lean_ctor_get(v___x_493_, 0);
                        crate::leanh::lean_inc(v_a_494_);
                        crate::leanh::lean_dec_ref_known(v___x_493_, 1);
                        v_a_445_ = v_a_494_;
                        state = 1;
                        continue;
                    } else {
                        v_a_495_ = crate::leanh::lean_ctor_get(v___x_493_, 0);
                        v_isSharedCheck_502_ = (!crate::leanh::lean_is_exclusive(v___x_493_)) as u8;
                        if v_isSharedCheck_502_ == 0 {
                            v___x_497_ = v___x_493_;
                            v_isShared_498_ = v_isSharedCheck_502_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_495_);
                            crate::leanh::lean_dec(v___x_493_);
                            v___x_497_ = crate::leanh::lean_box(0);
                            v_isShared_498_ = v_isSharedCheck_502_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_491_);
                    v_a_445_ = v_e_431_;
                    state = 1;
                    continue;
                }
            }
            8 => {
                if v_isShared_498_ == 0 {
                    v___x_500_ = v___x_497_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_501_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_501_, 0, v_a_495_);
                    v___x_500_ = v_reuseFailAlloc_501_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_500_;
            }
            10 => {
                if v___y_514_ == 0 {
                    crate::leanh::lean_inc_ref(v_fn_479_);
                    crate::leanh::lean_dec_ref_known(v_e_431_, 2);
                    v___x_515_ = l_Lean_Meta_Sym_Internal_mkAppS___at___00__private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go_spec__0___redArg(v_fn_479_, v___y_512_, v___y_506_, v___y_505_, v___y_509_, v___y_513_, v___y_504_, v___y_508_);
                    if crate::leanh::lean_obj_tag(v___x_515_) == 0 {
                        v_a_516_ = crate::leanh::lean_ctor_get(v___x_515_, 0);
                        crate::leanh::lean_inc(v_a_516_);
                        crate::leanh::lean_dec_ref_known(v___x_515_, 1);
                        v_a_449_ = v_a_516_;
                        state = 2;
                        continue;
                    } else {
                        v_a_517_ = crate::leanh::lean_ctor_get(v___x_515_, 0);
                        v_isSharedCheck_524_ = (!crate::leanh::lean_is_exclusive(v___x_515_)) as u8;
                        if v_isSharedCheck_524_ == 0 {
                            v___x_519_ = v___x_515_;
                            v_isShared_520_ = v_isSharedCheck_524_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_517_);
                            crate::leanh::lean_dec(v___x_515_);
                            v___x_519_ = crate::leanh::lean_box(0);
                            v_isShared_520_ = v_isSharedCheck_524_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_512_);
                    v_a_449_ = v_e_431_;
                    state = 2;
                    continue;
                }
            }
            11 => {
                if v_isShared_520_ == 0 {
                    v___x_522_ = v___x_519_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_523_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_523_, 0, v_a_517_);
                    v___x_522_ = v_reuseFailAlloc_523_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_522_;
            }
            13 => {
                if crate::leanh::lean_obj_tag(v_argsInfo_x3f_429_) == 0 {
                    crate::leanh::lean_dec(v___x_526_);
                    state = 18;
                    continue;
                } else {
                    v_val_568_ = crate::leanh::lean_ctor_get(v_argsInfo_x3f_429_, 0);
                    v___x_569_ = lean_array_get_size(v_val_568_);
                    v___x_570_ = lean_nat_dec_lt(v___x_526_, v___x_569_);
                    if v___x_570_ == 0 {
                        crate::leanh::lean_dec(v___x_526_);
                        state = 18;
                        continue;
                    } else {
                        v___x_571_ = lean_array_fget_borrowed(v_val_568_, v___x_526_);
                        crate::leanh::lean_dec(v___x_526_);
                        v_isProof_572_ = crate::leanh::lean_ctor_get_uint8(v___x_571_, 0 as u32);
                        if v_isProof_572_ == 0 {
                            v_isInstance_573_ =
                                crate::leanh::lean_ctor_get_uint8(v___x_571_, 1 as u32);
                            if v_isInstance_573_ == 0 {
                                state = 18;
                                continue;
                            } else {
                                state = 19;
                                continue;
                            }
                        } else {
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            14 => {
                if crate::leanh::lean_obj_tag(v_a_528_) == 0 {
                    crate::leanh::lean_dec_ref_known(v_a_528_, 0);
                    if crate::leanh::lean_obj_tag(v_ar_533_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_e_431_, 2);
                        v_isSharedCheck_552_ = (!crate::leanh::lean_is_exclusive(v_ar_533_)) as u8;
                        if v_isSharedCheck_552_ == 0 {
                            v___x_544_ = v_ar_533_;
                            v_isShared_545_ = v_isSharedCheck_552_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_ar_533_);
                            v___x_544_ = crate::leanh::lean_box(0);
                            v_isShared_545_ = v_isSharedCheck_552_;
                            state = 15;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_530_);
                        v_e_x27_553_ = crate::leanh::lean_ctor_get(v_ar_533_, 0);
                        crate::leanh::lean_inc_ref(v_e_x27_553_);
                        crate::leanh::lean_dec_ref_known(v_ar_533_, 1);
                        v___x_554_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v_fn_479_, v_fn_479_,
                            );
                        if v___x_554_ == 0 {
                            v___y_504_ = v___y_541_;
                            v___y_505_ = v___y_538_;
                            v___y_506_ = v___y_537_;
                            v___y_507_ = v___y_536_;
                            v___y_508_ = v___y_542_;
                            v___y_509_ = v___y_539_;
                            v___y_510_ = v___y_535_;
                            v___y_511_ = v___y_534_;
                            v___y_512_ = v_e_x27_553_;
                            v___y_513_ = v___y_540_;
                            v___y_514_ = v___x_554_;
                            state = 10;
                            continue;
                        } else {
                            v___x_555_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_480_, v_e_x27_553_);
                            v___y_504_ = v___y_541_;
                            v___y_505_ = v___y_538_;
                            v___y_506_ = v___y_537_;
                            v___y_507_ = v___y_536_;
                            v___y_508_ = v___y_542_;
                            v___y_509_ = v___y_539_;
                            v___y_510_ = v___y_535_;
                            v___y_511_ = v___y_534_;
                            v___y_512_ = v_e_x27_553_;
                            v___y_513_ = v___y_540_;
                            v___y_514_ = v___x_555_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_530_);
                    if crate::leanh::lean_obj_tag(v_ar_533_) == 0 {
                        crate::leanh::lean_dec_ref_known(v_ar_533_, 0);
                        v_e_x27_556_ = crate::leanh::lean_ctor_get(v_a_528_, 0);
                        crate::leanh::lean_inc_ref(v_e_x27_556_);
                        crate::leanh::lean_dec_ref_known(v_a_528_, 1);
                        v___x_557_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v_fn_479_,
                                v_e_x27_556_,
                            );
                        if v___x_557_ == 0 {
                            v___y_482_ = v___y_541_;
                            v___y_483_ = v___y_538_;
                            v___y_484_ = v___y_537_;
                            v___y_485_ = v___y_536_;
                            v___y_486_ = v___y_542_;
                            v___y_487_ = v___y_539_;
                            v___y_488_ = v___y_535_;
                            v___y_489_ = v___y_534_;
                            v___y_490_ = v___y_540_;
                            v___y_491_ = v_e_x27_556_;
                            v___y_492_ = v___x_557_;
                            state = 7;
                            continue;
                        } else {
                            v___x_558_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_480_, v_arg_480_);
                            v___y_482_ = v___y_541_;
                            v___y_483_ = v___y_538_;
                            v___y_484_ = v___y_537_;
                            v___y_485_ = v___y_536_;
                            v___y_486_ = v___y_542_;
                            v___y_487_ = v___y_539_;
                            v___y_488_ = v___y_535_;
                            v___y_489_ = v___y_534_;
                            v___y_490_ = v___y_540_;
                            v___y_491_ = v_e_x27_556_;
                            v___y_492_ = v___x_558_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v_e_x27_559_ = crate::leanh::lean_ctor_get(v_a_528_, 0);
                        crate::leanh::lean_inc_ref(v_e_x27_559_);
                        crate::leanh::lean_dec_ref_known(v_a_528_, 1);
                        v_e_x27_560_ = crate::leanh::lean_ctor_get(v_ar_533_, 0);
                        crate::leanh::lean_inc_ref(v_e_x27_560_);
                        crate::leanh::lean_dec_ref_known(v_ar_533_, 1);
                        v___x_561_ =
                            l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                                v_fn_479_,
                                v_e_x27_559_,
                            );
                        if v___x_561_ == 0 {
                            v___y_457_ = v___y_541_;
                            v___y_458_ = v___y_538_;
                            v___y_459_ = v___y_537_;
                            v___y_460_ = v___y_536_;
                            v___y_461_ = v_e_x27_560_;
                            v___y_462_ = v___y_542_;
                            v___y_463_ = v___y_539_;
                            v___y_464_ = v___y_535_;
                            v___y_465_ = v___y_534_;
                            v___y_466_ = v___y_540_;
                            v___y_467_ = v_e_x27_559_;
                            v___y_468_ = v___x_561_;
                            state = 4;
                            continue;
                        } else {
                            v___x_562_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_arg_480_, v_e_x27_560_);
                            v___y_457_ = v___y_541_;
                            v___y_458_ = v___y_538_;
                            v___y_459_ = v___y_537_;
                            v___y_460_ = v___y_536_;
                            v___y_461_ = v_e_x27_560_;
                            v___y_462_ = v___y_542_;
                            v___y_463_ = v___y_539_;
                            v___y_464_ = v___y_535_;
                            v___y_465_ = v___y_534_;
                            v___y_466_ = v___y_540_;
                            v___y_467_ = v_e_x27_559_;
                            v___y_468_ = v___x_562_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            15 => {
                if v_isShared_545_ == 0 {
                    v___x_547_ = v___x_544_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_551_ = crate::leanh::lean_alloc_ctor(0, 0, (1) as u32);
                    v___x_547_ = v_reuseFailAlloc_551_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                crate::leanh::lean_ctor_set_uint8(v___x_547_, 0 as u32, v___x_443_);
                if v_isShared_531_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_530_, 0, v___x_547_);
                    v___x_549_ = v___x_530_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_550_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_550_, 0, v___x_547_);
                    v___x_549_ = v_reuseFailAlloc_550_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_549_;
            }
            18 => {
                crate::leanh::lean_inc(v_a_440_);
                crate::leanh::lean_inc_ref(v_a_439_);
                crate::leanh::lean_inc(v_a_438_);
                crate::leanh::lean_inc_ref(v_a_437_);
                crate::leanh::lean_inc(v_a_436_);
                crate::leanh::lean_inc_ref(v_a_435_);
                crate::leanh::lean_inc(v_a_434_);
                crate::leanh::lean_inc(v_a_433_);
                crate::leanh::lean_inc(v_a_432_);
                crate::leanh::lean_inc_ref(v_arg_480_);
                v___x_564_ = lean_sym_dsimp(
                    v_arg_480_, v_a_432_, v_a_433_, v_a_434_, v_a_435_, v_a_436_, v_a_437_,
                    v_a_438_, v_a_439_, v_a_440_,
                );
                if crate::leanh::lean_obj_tag(v___x_564_) == 0 {
                    v_a_565_ = crate::leanh::lean_ctor_get(v___x_564_, 0);
                    crate::leanh::lean_inc(v_a_565_);
                    crate::leanh::lean_dec_ref_known(v___x_564_, 1);
                    v_ar_533_ = v_a_565_;
                    v___y_534_ = v_a_432_;
                    v___y_535_ = v_a_433_;
                    v___y_536_ = v_a_434_;
                    v___y_537_ = v_a_435_;
                    v___y_538_ = v_a_436_;
                    v___y_539_ = v_a_437_;
                    v___y_540_ = v_a_438_;
                    v___y_541_ = v_a_439_;
                    v___y_542_ = v_a_440_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_530_);
                    crate::leanh::lean_dec(v_a_528_);
                    crate::leanh::lean_dec_ref_known(v_e_431_, 2);
                    return v___x_564_;
                }
            }
            19 => {
                v___x_567_ = crate::leanh::lean_alloc_ctor(0, 0, (1) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_567_, 0 as u32, v___x_443_);
                v_ar_533_ = v___x_567_;
                v___y_534_ = v_a_432_;
                v___y_535_ = v_a_433_;
                v___y_536_ = v_a_434_;
                v___y_537_ = v_a_435_;
                v___y_538_ = v_a_436_;
                v___y_539_ = v_a_437_;
                v___y_540_ = v_a_438_;
                v___y_541_ = v_a_439_;
                v___y_542_ = v_a_440_;
                state = 14;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___boxed(
    mut v_argsInfo_x3f_579_: *mut crate::leanh::LeanObject,
    mut v_i_580_: *mut crate::leanh::LeanObject,
    mut v_e_581_: *mut crate::leanh::LeanObject,
    mut v_a_582_: *mut crate::leanh::LeanObject,
    mut v_a_583_: *mut crate::leanh::LeanObject,
    mut v_a_584_: *mut crate::leanh::LeanObject,
    mut v_a_585_: *mut crate::leanh::LeanObject,
    mut v_a_586_: *mut crate::leanh::LeanObject,
    mut v_a_587_: *mut crate::leanh::LeanObject,
    mut v_a_588_: *mut crate::leanh::LeanObject,
    mut v_a_589_: *mut crate::leanh::LeanObject,
    mut v_a_590_: *mut crate::leanh::LeanObject,
    mut v_a_591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_592_ = l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go(
        v_argsInfo_x3f_579_,
        v_i_580_,
        v_e_581_,
        v_a_582_,
        v_a_583_,
        v_a_584_,
        v_a_585_,
        v_a_586_,
        v_a_587_,
        v_a_588_,
        v_a_589_,
        v_a_590_,
    );
    crate::leanh::lean_dec(v_a_590_);
    crate::leanh::lean_dec_ref(v_a_589_);
    crate::leanh::lean_dec(v_a_588_);
    crate::leanh::lean_dec_ref(v_a_587_);
    crate::leanh::lean_dec(v_a_586_);
    crate::leanh::lean_dec_ref(v_a_585_);
    crate::leanh::lean_dec(v_a_584_);
    crate::leanh::lean_dec(v_a_583_);
    crate::leanh::lean_dec(v_a_582_);
    crate::leanh::lean_dec(v_i_580_);
    crate::leanh::lean_dec(v_argsInfo_x3f_579_);
    return v_res_592_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_dsimpAppArgs(
    mut v_e_593_: *mut crate::leanh::LeanObject,
    mut v_a_594_: *mut crate::leanh::LeanObject,
    mut v_a_595_: *mut crate::leanh::LeanObject,
    mut v_a_596_: *mut crate::leanh::LeanObject,
    mut v_a_597_: *mut crate::leanh::LeanObject,
    mut v_a_598_: *mut crate::leanh::LeanObject,
    mut v_a_599_: *mut crate::leanh::LeanObject,
    mut v_a_600_: *mut crate::leanh::LeanObject,
    mut v_a_601_: *mut crate::leanh::LeanObject,
    mut v_a_602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_numArgs_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: u8 = 0;
    let mut v_f_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_615_: u8 = 0;
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_620_: u8 = 0;
    let mut v_a_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_624_: u8 = 0;
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_628_: u8 = 0;
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_numArgs_604_ = l_Lean_Expr_getAppNumArgs(v_e_593_);
                v___x_605_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_606_ = lean_nat_dec_eq(v_numArgs_604_, v___x_605_);
                if v___x_606_ == 0 {
                    v_f_607_ = l_Lean_Expr_getAppFn(v_e_593_);
                    v___x_608_ = l_Lean_Meta_Sym_getProofInstInfoOfExpr_x3f___redArg(
                        v_f_607_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_608_) == 0 {
                        v_a_609_ = crate::leanh::lean_ctor_get(v___x_608_, 0);
                        crate::leanh::lean_inc(v_a_609_);
                        crate::leanh::lean_dec_ref_known(v___x_608_, 1);
                        if crate::leanh::lean_obj_tag(v_a_609_) == 0 {
                            v___x_610_ = crate::leanh::lean_box(0);
                            v___x_611_ = l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go(v___x_610_, v_numArgs_604_, v_e_593_, v_a_594_, v_a_595_, v_a_596_, v_a_597_, v_a_598_, v_a_599_, v_a_600_, v_a_601_, v_a_602_);
                            crate::leanh::lean_dec(v_numArgs_604_);
                            return v___x_611_;
                        } else {
                            v_val_612_ = crate::leanh::lean_ctor_get(v_a_609_, 0);
                            v_isSharedCheck_620_ =
                                (!crate::leanh::lean_is_exclusive(v_a_609_)) as u8;
                            if v_isSharedCheck_620_ == 0 {
                                v___x_614_ = v_a_609_;
                                v_isShared_615_ = v_isSharedCheck_620_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_val_612_);
                                crate::leanh::lean_dec(v_a_609_);
                                v___x_614_ = crate::leanh::lean_box(0);
                                v_isShared_615_ = v_isSharedCheck_620_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_numArgs_604_);
                        crate::leanh::lean_dec_ref(v_e_593_);
                        v_a_621_ = crate::leanh::lean_ctor_get(v___x_608_, 0);
                        v_isSharedCheck_628_ = (!crate::leanh::lean_is_exclusive(v___x_608_)) as u8;
                        if v_isSharedCheck_628_ == 0 {
                            v___x_623_ = v___x_608_;
                            v_isShared_624_ = v_isSharedCheck_628_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_621_);
                            crate::leanh::lean_dec(v___x_608_);
                            v___x_623_ = crate::leanh::lean_box(0);
                            v_isShared_624_ = v_isSharedCheck_628_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_numArgs_604_);
                    crate::leanh::lean_dec_ref(v_e_593_);
                    v___x_629_ = l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go___closed__4;
                    v___x_630_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_630_, 0, v___x_629_);
                    return v___x_630_;
                }
            }
            1 => {
                if v_isShared_615_ == 0 {
                    v___x_617_ = v___x_614_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_619_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_619_, 0, v_val_612_);
                    v___x_617_ = v_reuseFailAlloc_619_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_618_ =
                    l___private_Lean_Meta_Sym_DSimp_App_0__Lean_Meta_Sym_DSimp_dsimpAppArgs_go(
                        v___x_617_,
                        v_numArgs_604_,
                        v_e_593_,
                        v_a_594_,
                        v_a_595_,
                        v_a_596_,
                        v_a_597_,
                        v_a_598_,
                        v_a_599_,
                        v_a_600_,
                        v_a_601_,
                        v_a_602_,
                    );
                crate::leanh::lean_dec(v_numArgs_604_);
                crate::leanh::lean_dec_ref(v___x_617_);
                return v___x_618_;
            }
            3 => {
                if v_isShared_624_ == 0 {
                    v___x_626_ = v___x_623_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_627_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_627_, 0, v_a_621_);
                    v___x_626_ = v_reuseFailAlloc_627_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_626_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_dsimpAppArgs___boxed(
    mut v_e_631_: *mut crate::leanh::LeanObject,
    mut v_a_632_: *mut crate::leanh::LeanObject,
    mut v_a_633_: *mut crate::leanh::LeanObject,
    mut v_a_634_: *mut crate::leanh::LeanObject,
    mut v_a_635_: *mut crate::leanh::LeanObject,
    mut v_a_636_: *mut crate::leanh::LeanObject,
    mut v_a_637_: *mut crate::leanh::LeanObject,
    mut v_a_638_: *mut crate::leanh::LeanObject,
    mut v_a_639_: *mut crate::leanh::LeanObject,
    mut v_a_640_: *mut crate::leanh::LeanObject,
    mut v_a_641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_642_ = l_Lean_Meta_Sym_DSimp_dsimpAppArgs(
        v_e_631_, v_a_632_, v_a_633_, v_a_634_, v_a_635_, v_a_636_, v_a_637_, v_a_638_, v_a_639_,
        v_a_640_,
    );
    crate::leanh::lean_dec(v_a_640_);
    crate::leanh::lean_dec_ref(v_a_639_);
    crate::leanh::lean_dec(v_a_638_);
    crate::leanh::lean_dec_ref(v_a_637_);
    crate::leanh::lean_dec(v_a_636_);
    crate::leanh::lean_dec_ref(v_a_635_);
    crate::leanh::lean_dec(v_a_634_);
    crate::leanh::lean_dec(v_a_633_);
    crate::leanh::lean_dec(v_a_632_);
    return v_res_642_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_DSimp_App(
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
    res = runtime_initialize_Lean_Meta_Sym_DSimp_Result(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_ProofInstInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_DSimp_App(
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
pub unsafe fn initialize_Lean_Meta_Sym_DSimp_App(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Lean_Meta_Sym_DSimp_Result(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_ProofInstInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_App(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_DSimp_App(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_DSimp_App(builtin);
}

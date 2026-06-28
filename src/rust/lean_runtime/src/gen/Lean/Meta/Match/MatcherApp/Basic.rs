// Lean compiler output
// Module: Lean.Meta.Match.MatcherApp.Basic
// Imports: Lean.Meta.Match.MatcherInfo
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Prelude::{
    l_Array_extract___redArg, l_List_lengthTR___redArg, l_instInhabitedOfMonad___redArg,
    l_panic___redArg,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::AuxRecursor::l_Lean_isCasesOnRecursor;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_getPrefix;
use crate::r#gen::Lean::Declaration::l_Lean_InductiveVal_numCtors;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_app___override,
    l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isApp,
    l_Lean_Expr_sort___override, l_Lean_instInhabitedExpr, l_Lean_mkAppN, l_Lean_mkConst,
};
use crate::r#gen::Lean::Meta::Match::MatcherInfo::{
    initialize_Lean_Meta_Match_MatcherInfo, l_Lean_Meta_Match_MatcherInfo_altNumParams,
    l_Lean_Meta_Match_MatcherInfo_arity, l_Lean_Meta_Match_MatcherInfo_getMotivePos,
    l_Lean_Meta_Match_MatcherInfo_numAlts, l_Lean_Meta_Match_instInhabitedAltParamInfo_default,
    l_Lean_Meta_getMatcherInfo_x3f___redArg, runtime_initialize_Lean_Meta_Match_MatcherInfo,
};
use crate::r#gen::Lean::MonadEnv::l_Lean_getConstInfo___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_mk_array};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_array_get_size, lean_array_mk, lean_array_to_list, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__0_value: LeanStringObject<
    33,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 77, 97, 116, 99, 104, 46, 77, 97, 116, 99, 104,
        101, 114, 65, 112, 112, 46, 66, 97, 115, 105, 99, 0,
    ],
};
static mut l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__1_value: LeanStringObject<
    27,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 109, 97, 116, 99, 104, 77, 97, 116, 99, 104,
        101, 114, 65, 112, 112, 63, 0,
    ],
};
static mut l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__2_value: LeanStringObject<
    21,
> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        101, 120, 112, 101, 99, 116, 101, 100, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111,
        114, 0,
    ],
};
static mut l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__1_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__0(
    mut v_inst_283_: *mut LeanObject,
    mut v_____r_284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_285_ = lean_ctor_get(v_inst_283_, 0);
    lean_inc_ref(v_toApplicative_285_);
    lean_dec_ref(v_inst_283_);
    v_toPure_286_ = lean_ctor_get(v_toApplicative_285_, 1);
    lean_inc(v_toPure_286_);
    lean_dec_ref(v_toApplicative_285_);
    v___x_287_ = lean_box(0);
    v___x_288_ = lean_apply_2(v_toPure_286_, lean_box(0), v___x_287_);
    return v___x_288_;
}
pub unsafe fn _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__3()
-> *mut LeanObject {
    let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
    v___x_292_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__2;
    v___x_293_ = lean_unsigned_to_nat(53);
    v___x_294_ = lean_unsigned_to_nat(62);
    v___x_295_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__1;
    v___x_296_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__0;
    v___x_297_ =
        l_mkPanicMessageWithDecl(v___x_296_, v___x_295_, v___x_294_, v___x_293_, v___x_292_);
    return v___x_297_;
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1(
    mut v_toApplicative_298_: *mut LeanObject,
    mut v_inst_299_: *mut LeanObject,
    mut v_____x_300_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____x_300_) == 6 {
        let mut v_val_301_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_302_: *mut LeanObject = core::ptr::null_mut();
        let mut v_numFields_303_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_304_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_305_: u8 = 0;
        let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_299_);
        v_val_301_ = lean_ctor_get(v_____x_300_, 0);
        v_toPure_302_ = lean_ctor_get(v_toApplicative_298_, 1);
        lean_inc(v_toPure_302_);
        lean_dec_ref(v_toApplicative_298_);
        v_numFields_303_ = lean_ctor_get(v_val_301_, 4);
        v___x_304_ = lean_unsigned_to_nat(0);
        v___x_305_ = 0;
        lean_inc(v_numFields_303_);
        v___x_306_ = lean_alloc_ctor(0, 2, (1) as u32);
        lean_ctor_set(v___x_306_, 0, v_numFields_303_);
        lean_ctor_set(v___x_306_, 1, v___x_304_);
        lean_ctor_set_uint8(
            v___x_306_,
            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            v___x_305_,
        );
        v___x_307_ = lean_apply_2(v_toPure_302_, lean_box(0), v___x_306_);
        return v___x_307_;
    } else {
        let mut v___x_308_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_310_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_311_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toApplicative_298_);
        v___x_308_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
        v___x_309_ = l_instInhabitedOfMonad___redArg(v_inst_299_, v___x_308_);
        v___x_310_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__3),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__3_once
            ),
            _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__3,
        );
        v___x_311_ = l_panic___redArg(v___x_309_, v___x_310_);
        lean_dec(v___x_309_);
        return v___x_311_;
    }
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___boxed(
    mut v_toApplicative_312_: *mut LeanObject,
    mut v_inst_313_: *mut LeanObject,
    mut v_____x_314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_315_: *mut LeanObject = core::ptr::null_mut();
    v_res_315_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1(
        v_toApplicative_312_,
        v_inst_313_,
        v_____x_314_,
    );
    lean_dec_ref(v_____x_314_);
    return v_res_315_;
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__2(
    mut v_inst_316_: *mut LeanObject,
    mut v_inst_317_: *mut LeanObject,
    mut v_inst_318_: *mut LeanObject,
    mut v_toBind_319_: *mut LeanObject,
    mut v___f_320_: *mut LeanObject,
    mut v_ctor_321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    v___x_322_ = l_Lean_getConstInfo___redArg(v_inst_316_, v_inst_317_, v_inst_318_, v_ctor_321_);
    v___x_323_ = lean_apply_4(
        v_toBind_319_,
        lean_box(0),
        lean_box(0),
        v___x_322_,
        v___f_320_,
    );
    return v___x_323_;
}
pub unsafe fn _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0()
-> *mut LeanObject {
    let mut v___x_324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
    v___x_324_ = lean_box(0);
    v___x_325_ = lean_unsigned_to_nat(16);
    v___x_326_ = lean_mk_array(v___x_325_, v___x_324_);
    return v___x_326_;
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3(
    mut v_toApplicative_327_: *mut LeanObject,
    mut v_params_328_: *mut LeanObject,
    mut v_discrs_329_: *mut LeanObject,
    mut v___x_330_: *mut LeanObject,
    mut v___y_331_: *mut LeanObject,
    mut v_discrInfos_332_: *mut LeanObject,
    mut v_us_333_: *mut LeanObject,
    mut v_alts_334_: *mut LeanObject,
    mut v___x_335_: *mut LeanObject,
    mut v_declName_336_: *mut LeanObject,
    mut v_motive_337_: *mut LeanObject,
    mut v_altInfos_338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_339_ = lean_ctor_get(v_toApplicative_327_, 1);
    lean_inc(v_toPure_339_);
    lean_dec_ref(v_toApplicative_327_);
    v_start_340_ = lean_ctor_get(v_params_328_, 1);
    v_stop_341_ = lean_ctor_get(v_params_328_, 2);
    v_start_342_ = lean_ctor_get(v_discrs_329_, 1);
    v_stop_343_ = lean_ctor_get(v_discrs_329_, 2);
    v___x_344_ = lean_nat_sub(v_stop_341_, v_start_340_);
    v___x_345_ = lean_nat_sub(v_stop_343_, v_start_342_);
    v___x_346_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0_once),
        _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0,
    );
    v___x_347_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_347_, 0, v___x_330_);
    lean_ctor_set(v___x_347_, 1, v___x_346_);
    v___x_348_ = lean_alloc_ctor(0, 6, (0) as u32);
    lean_ctor_set(v___x_348_, 0, v___x_344_);
    lean_ctor_set(v___x_348_, 1, v___x_345_);
    lean_ctor_set(v___x_348_, 2, v_altInfos_338_);
    lean_ctor_set(v___x_348_, 3, v___y_331_);
    lean_ctor_set(v___x_348_, 4, v_discrInfos_332_);
    lean_ctor_set(v___x_348_, 5, v___x_347_);
    v___x_349_ = lean_array_mk(v_us_333_);
    v___x_350_ = l_Subarray_copy___redArg(v_params_328_);
    v___x_351_ = l_Subarray_copy___redArg(v_discrs_329_);
    v___x_352_ = l_Subarray_copy___redArg(v_alts_334_);
    v___x_353_ = l_Subarray_copy___redArg(v___x_335_);
    v___x_354_ = lean_alloc_ctor(0, 8, (0) as u32);
    lean_ctor_set(v___x_354_, 0, v___x_348_);
    lean_ctor_set(v___x_354_, 1, v_declName_336_);
    lean_ctor_set(v___x_354_, 2, v___x_349_);
    lean_ctor_set(v___x_354_, 3, v___x_350_);
    lean_ctor_set(v___x_354_, 4, v_motive_337_);
    lean_ctor_set(v___x_354_, 5, v___x_351_);
    lean_ctor_set(v___x_354_, 6, v___x_352_);
    lean_ctor_set(v___x_354_, 7, v___x_353_);
    v___x_355_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_355_, 0, v___x_354_);
    v___x_356_ = lean_apply_2(v_toPure_339_, lean_box(0), v___x_355_);
    return v___x_356_;
}
pub unsafe fn _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0()
-> *mut LeanObject {
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_358_: *mut LeanObject = core::ptr::null_mut();
    v___x_357_ = lean_box(0);
    v_dummy_358_ = l_Lean_Expr_sort___override(v___x_357_);
    return v_dummy_358_;
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4(
    mut v_e_361_: *mut LeanObject,
    mut v_toApplicative_362_: *mut LeanObject,
    mut v_us_363_: *mut LeanObject,
    mut v_declName_364_: *mut LeanObject,
    mut v_inst_365_: *mut LeanObject,
    mut v___f_366_: *mut LeanObject,
    mut v_toBind_367_: *mut LeanObject,
    mut v_____x_368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numIndices_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctors_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_386_: u8 = 0;
    let mut v_toPure_387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_motive_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discrs_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discrInfos_397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_404_: usize = 0;
    let mut v___x_405_: usize = 0;
    let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelParams_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_415_: u8 = 0;
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_417_: u8 = 0;
    let mut v_toPure_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____x_368_) == 5 {
                    v_val_369_ = lean_ctor_get(v_____x_368_, 0);
                    lean_inc_ref(v_val_369_);
                    lean_dec_ref_known(v_____x_368_, 1);
                    v_toConstantVal_370_ = lean_ctor_get(v_val_369_, 0);
                    lean_inc_ref(v_toConstantVal_370_);
                    v_numParams_371_ = lean_ctor_get(v_val_369_, 1);
                    lean_inc(v_numParams_371_);
                    v_numIndices_372_ = lean_ctor_get(v_val_369_, 2);
                    lean_inc(v_numIndices_372_);
                    v_ctors_373_ = lean_ctor_get(v_val_369_, 4);
                    lean_inc(v_ctors_373_);
                    v_nargs_374_ = l_Lean_Expr_getAppNumArgs(v_e_361_);
                    v_dummy_375_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0_once
                        ),
                        _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0,
                    );
                    lean_inc(v_nargs_374_);
                    v___x_376_ = lean_mk_array(v_nargs_374_, v_dummy_375_);
                    v___x_377_ = lean_unsigned_to_nat(1);
                    v___x_378_ = lean_nat_sub(v_nargs_374_, v___x_377_);
                    lean_dec(v_nargs_374_);
                    v_args_379_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_e_361_, v___x_376_, v___x_378_,
                    );
                    v___x_380_ = lean_nat_add(v_numParams_371_, v___x_377_);
                    v___x_381_ = lean_nat_add(v___x_380_, v_numIndices_372_);
                    v___x_382_ = lean_nat_add(v___x_381_, v___x_377_);
                    lean_dec(v___x_381_);
                    v___x_383_ = l_Lean_InductiveVal_numCtors(v_val_369_);
                    lean_dec_ref(v_val_369_);
                    v___x_384_ = lean_nat_add(v___x_382_, v___x_383_);
                    lean_dec(v___x_383_);
                    v___x_385_ = lean_array_get_size(v_args_379_);
                    v___x_386_ = lean_nat_dec_le(v___x_384_, v___x_385_);
                    if v___x_386_ == 0 {
                        lean_dec(v___x_384_);
                        lean_dec(v___x_382_);
                        lean_dec(v___x_380_);
                        lean_dec_ref(v_args_379_);
                        lean_dec(v_ctors_373_);
                        lean_dec(v_numIndices_372_);
                        lean_dec(v_numParams_371_);
                        lean_dec_ref(v_toConstantVal_370_);
                        lean_dec(v_toBind_367_);
                        lean_dec(v___f_366_);
                        lean_dec_ref(v_inst_365_);
                        lean_dec(v_declName_364_);
                        lean_dec(v_us_363_);
                        v_toPure_387_ = lean_ctor_get(v_toApplicative_362_, 1);
                        lean_inc(v_toPure_387_);
                        lean_dec_ref(v_toApplicative_362_);
                        v___x_388_ = lean_box(0);
                        v___x_389_ = lean_apply_2(v_toPure_387_, lean_box(0), v___x_388_);
                        return v___x_389_;
                    } else {
                        v___x_390_ = lean_unsigned_to_nat(0);
                        lean_inc(v_numParams_371_);
                        lean_inc_ref_n(v_args_379_, 3);
                        v_params_391_ =
                            l_Array_toSubarray___redArg(v_args_379_, v___x_390_, v_numParams_371_);
                        v___x_392_ = l_Lean_instInhabitedExpr;
                        v_motive_393_ = lean_array_get(v___x_392_, v_args_379_, v_numParams_371_);
                        lean_dec(v_numParams_371_);
                        lean_inc(v___x_382_);
                        v_discrs_394_ =
                            l_Array_toSubarray___redArg(v_args_379_, v___x_380_, v___x_382_);
                        v___x_395_ = lean_nat_add(v_numIndices_372_, v___x_377_);
                        lean_dec(v_numIndices_372_);
                        v___x_396_ = lean_box(0);
                        v_discrInfos_397_ = lean_mk_array(v___x_395_, v___x_396_);
                        lean_inc(v___x_384_);
                        v_alts_398_ =
                            l_Array_toSubarray___redArg(v_args_379_, v___x_382_, v___x_384_);
                        v___x_417_ = lean_nat_dec_le(v___x_384_, v___x_390_);
                        if v___x_417_ == 0 {
                            v_lower_409_ = v___x_384_;
                            v_upper_410_ = v___x_385_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_384_);
                            v_lower_409_ = v___x_390_;
                            v_upper_410_ = v___x_385_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_____x_368_);
                    lean_dec(v_toBind_367_);
                    lean_dec(v___f_366_);
                    lean_dec_ref(v_inst_365_);
                    lean_dec(v_declName_364_);
                    lean_dec(v_us_363_);
                    lean_dec_ref(v_e_361_);
                    v_toPure_418_ = lean_ctor_get(v_toApplicative_362_, 1);
                    lean_inc(v_toPure_418_);
                    lean_dec_ref(v_toApplicative_362_);
                    v___x_419_ = lean_box(0);
                    v___x_420_ = lean_apply_2(v_toPure_418_, lean_box(0), v___x_419_);
                    return v___x_420_;
                }
            }
            1 => {
                v___f_402_ = lean_alloc_closure(
                    l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3 as *mut core::ffi::c_void,
                    12,
                    11,
                );
                lean_closure_set(v___f_402_, 0, v_toApplicative_362_);
                lean_closure_set(v___f_402_, 1, v_params_391_);
                lean_closure_set(v___f_402_, 2, v_discrs_394_);
                lean_closure_set(v___f_402_, 3, v___x_390_);
                lean_closure_set(v___f_402_, 4, v___y_401_);
                lean_closure_set(v___f_402_, 5, v_discrInfos_397_);
                lean_closure_set(v___f_402_, 6, v_us_363_);
                lean_closure_set(v___f_402_, 7, v_alts_398_);
                lean_closure_set(v___f_402_, 8, v___y_400_);
                lean_closure_set(v___f_402_, 9, v_declName_364_);
                lean_closure_set(v___f_402_, 10, v_motive_393_);
                v___x_403_ = lean_array_mk(v_ctors_373_);
                v_sz_404_ = lean_array_size(v___x_403_);
                v___x_405_ = 0usize;
                v___x_406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    lean_box(0),
                    lean_box(0),
                    lean_box(0),
                    v_inst_365_,
                    v___f_366_,
                    v_sz_404_,
                    v___x_405_,
                    v___x_403_,
                );
                v___x_407_ = lean_apply_4(
                    v_toBind_367_,
                    lean_box(0),
                    lean_box(0),
                    v___x_406_,
                    v___f_402_,
                );
                return v___x_407_;
            }
            2 => {
                v_levelParams_411_ = lean_ctor_get(v_toConstantVal_370_, 1);
                lean_inc(v_levelParams_411_);
                lean_dec_ref(v_toConstantVal_370_);
                v___x_412_ = l_Array_toSubarray___redArg(v_args_379_, v_lower_409_, v_upper_410_);
                v___x_413_ = l_List_lengthTR___redArg(v_levelParams_411_);
                lean_dec(v_levelParams_411_);
                v___x_414_ = l_List_lengthTR___redArg(v_us_363_);
                v___x_415_ = lean_nat_dec_eq(v___x_413_, v___x_414_);
                lean_dec(v___x_414_);
                lean_dec(v___x_413_);
                if v___x_415_ == 0 {
                    v___x_416_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__1;
                    v___y_400_ = v___x_412_;
                    v___y_401_ = v___x_416_;
                    state = 1;
                    continue;
                } else {
                    v___y_400_ = v___x_412_;
                    v___y_401_ = v___x_396_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5(
    mut v___f_421_: *mut LeanObject,
    mut v_alsoCasesOn_422_: u8,
    mut v_declName_423_: *mut LeanObject,
    mut v_inst_424_: *mut LeanObject,
    mut v_inst_425_: *mut LeanObject,
    mut v_inst_426_: *mut LeanObject,
    mut v_toBind_427_: *mut LeanObject,
    mut v___f_428_: *mut LeanObject,
    mut v_____do__lift_429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_433_: u8 = 0;
    let mut v_indName_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_alsoCasesOn_422_ == 0 {
                    lean_dec_ref(v_____do__lift_429_);
                    lean_dec(v___f_428_);
                    lean_dec(v_toBind_427_);
                    lean_dec_ref(v_inst_426_);
                    lean_dec_ref(v_inst_425_);
                    lean_dec_ref(v_inst_424_);
                    lean_dec(v_declName_423_);
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_declName_423_);
                    v___x_433_ = l_Lean_isCasesOnRecursor(v_____do__lift_429_, v_declName_423_);
                    if v___x_433_ == 0 {
                        lean_dec(v___f_428_);
                        lean_dec(v_toBind_427_);
                        lean_dec_ref(v_inst_426_);
                        lean_dec_ref(v_inst_425_);
                        lean_dec_ref(v_inst_424_);
                        lean_dec(v_declName_423_);
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___f_421_);
                        v_indName_434_ = l_Lean_Name_getPrefix(v_declName_423_);
                        lean_dec(v_declName_423_);
                        v___x_435_ = l_Lean_getConstInfo___redArg(
                            v_inst_424_,
                            v_inst_425_,
                            v_inst_426_,
                            v_indName_434_,
                        );
                        v___x_436_ = lean_apply_4(
                            v_toBind_427_,
                            lean_box(0),
                            lean_box(0),
                            v___x_435_,
                            v___f_428_,
                        );
                        return v___x_436_;
                    }
                }
            }
            1 => {
                v___x_431_ = lean_box(0);
                v___x_432_ = lean_apply_1(v___f_421_, v___x_431_);
                return v___x_432_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5___boxed(
    mut v___f_437_: *mut LeanObject,
    mut v_alsoCasesOn_438_: *mut LeanObject,
    mut v_declName_439_: *mut LeanObject,
    mut v_inst_440_: *mut LeanObject,
    mut v_inst_441_: *mut LeanObject,
    mut v_inst_442_: *mut LeanObject,
    mut v_toBind_443_: *mut LeanObject,
    mut v___f_444_: *mut LeanObject,
    mut v_____do__lift_445_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_alsoCasesOn_boxed_446_: u8 = 0;
    let mut v_res_447_: *mut LeanObject = core::ptr::null_mut();
    v_alsoCasesOn_boxed_446_ = (lean_unbox(v_alsoCasesOn_438_) as u8);
    v_res_447_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5(
        v___f_437_,
        v_alsoCasesOn_boxed_446_,
        v_declName_439_,
        v_inst_440_,
        v_inst_441_,
        v_inst_442_,
        v_toBind_443_,
        v___f_444_,
        v_____do__lift_445_,
    );
    return v_res_447_;
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__6(
    mut v_e_448_: *mut LeanObject,
    mut v_toApplicative_449_: *mut LeanObject,
    mut v_us_450_: *mut LeanObject,
    mut v_declName_451_: *mut LeanObject,
    mut v_inst_452_: *mut LeanObject,
    mut v_toBind_453_: *mut LeanObject,
    mut v___f_454_: *mut LeanObject,
    mut v_____do__lift_455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_val_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_459_: u8 = 0;
    let mut v_dummy_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_468_: u8 = 0;
    let mut v_toPure_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numParams_470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numDiscrs_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_496_: u8 = 0;
    let mut v_getEnv_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_455_) == 1 {
                    lean_dec(v___f_454_);
                    lean_dec(v_toBind_453_);
                    lean_dec_ref(v_inst_452_);
                    v_val_456_ = lean_ctor_get(v_____do__lift_455_, 0);
                    v_isSharedCheck_496_ = (!lean_is_exclusive(v_____do__lift_455_)) as u8;
                    if v_isSharedCheck_496_ == 0 {
                        v___x_458_ = v_____do__lift_455_;
                        v_isShared_459_ = v_isSharedCheck_496_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_456_);
                        lean_dec(v_____do__lift_455_);
                        v___x_458_ = lean_box(0);
                        v_isShared_459_ = v_isSharedCheck_496_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_____do__lift_455_);
                    lean_dec(v_declName_451_);
                    lean_dec(v_us_450_);
                    lean_dec_ref(v_toApplicative_449_);
                    lean_dec_ref(v_e_448_);
                    v_getEnv_497_ = lean_ctor_get(v_inst_452_, 0);
                    lean_inc(v_getEnv_497_);
                    lean_dec_ref(v_inst_452_);
                    v___x_498_ = lean_apply_4(
                        v_toBind_453_,
                        lean_box(0),
                        lean_box(0),
                        v_getEnv_497_,
                        v___f_454_,
                    );
                    return v___x_498_;
                }
            }
            1 => {
                v_dummy_460_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0_once
                    ),
                    _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0,
                );
                v_nargs_461_ = l_Lean_Expr_getAppNumArgs(v_e_448_);
                lean_inc(v_nargs_461_);
                v___x_462_ = lean_mk_array(v_nargs_461_, v_dummy_460_);
                v___x_463_ = lean_unsigned_to_nat(1);
                v___x_464_ = lean_nat_sub(v_nargs_461_, v___x_463_);
                lean_dec(v_nargs_461_);
                v_args_465_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_448_, v___x_462_, v___x_464_,
                );
                v___x_466_ = lean_array_get_size(v_args_465_);
                v___x_467_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_456_);
                v___x_468_ = lean_nat_dec_lt(v___x_466_, v___x_467_);
                lean_dec(v___x_467_);
                if v___x_468_ == 0 {
                    v_toPure_469_ = lean_ctor_get(v_toApplicative_449_, 1);
                    lean_inc(v_toPure_469_);
                    lean_dec_ref(v_toApplicative_449_);
                    v_numParams_470_ = lean_ctor_get(v_val_456_, 0);
                    v_numDiscrs_471_ = lean_ctor_get(v_val_456_, 1);
                    v___x_472_ = lean_array_mk(v_us_450_);
                    v___x_473_ = lean_unsigned_to_nat(0);
                    lean_inc(v_numParams_470_);
                    v___x_474_ =
                        l_Array_extract___redArg(v_args_465_, v___x_473_, v_numParams_470_);
                    v___x_475_ = l_Lean_instInhabitedExpr;
                    v___x_476_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_456_);
                    v___x_477_ = lean_array_get(v___x_475_, v_args_465_, v___x_476_);
                    lean_dec(v___x_476_);
                    v___x_478_ = lean_nat_add(v_numParams_470_, v___x_463_);
                    v___x_479_ = lean_nat_add(v___x_478_, v_numDiscrs_471_);
                    lean_inc(v___x_479_);
                    lean_inc_ref_n(v_args_465_, 2);
                    v___x_480_ = l_Array_toSubarray___redArg(v_args_465_, v___x_478_, v___x_479_);
                    v___x_481_ = l_Subarray_copy___redArg(v___x_480_);
                    v___x_482_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_456_);
                    v___x_483_ = lean_nat_add(v___x_479_, v___x_482_);
                    lean_dec(v___x_482_);
                    lean_inc(v___x_483_);
                    v___x_484_ = l_Array_toSubarray___redArg(v_args_465_, v___x_479_, v___x_483_);
                    v___x_485_ = l_Subarray_copy___redArg(v___x_484_);
                    v___x_486_ = l_Array_toSubarray___redArg(v_args_465_, v___x_483_, v___x_466_);
                    v___x_487_ = l_Subarray_copy___redArg(v___x_486_);
                    v___x_488_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v___x_488_, 0, v_val_456_);
                    lean_ctor_set(v___x_488_, 1, v_declName_451_);
                    lean_ctor_set(v___x_488_, 2, v___x_472_);
                    lean_ctor_set(v___x_488_, 3, v___x_474_);
                    lean_ctor_set(v___x_488_, 4, v___x_477_);
                    lean_ctor_set(v___x_488_, 5, v___x_481_);
                    lean_ctor_set(v___x_488_, 6, v___x_485_);
                    lean_ctor_set(v___x_488_, 7, v___x_487_);
                    if v_isShared_459_ == 0 {
                        lean_ctor_set(v___x_458_, 0, v___x_488_);
                        v___x_490_ = v___x_458_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_488_);
                        v___x_490_ = v_reuseFailAlloc_492_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_args_465_);
                    lean_del_object(v___x_458_);
                    lean_dec(v_val_456_);
                    lean_dec(v_declName_451_);
                    lean_dec(v_us_450_);
                    v_toPure_493_ = lean_ctor_get(v_toApplicative_449_, 1);
                    lean_inc(v_toPure_493_);
                    lean_dec_ref(v_toApplicative_449_);
                    v___x_494_ = lean_box(0);
                    v___x_495_ = lean_apply_2(v_toPure_493_, lean_box(0), v___x_494_);
                    return v___x_495_;
                }
            }
            2 => {
                v___x_491_ = lean_apply_2(v_toPure_469_, lean_box(0), v___x_490_);
                return v___x_491_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___redArg(
    mut v_inst_499_: *mut LeanObject,
    mut v_inst_500_: *mut LeanObject,
    mut v_inst_501_: *mut LeanObject,
    mut v_e_502_: *mut LeanObject,
    mut v_alsoCasesOn_503_: u8,
) -> *mut LeanObject {
    let mut v___x_504_: u8 = 0;
    v___x_504_ = l_Lean_Expr_isApp(v_e_502_);
    if v___x_504_ == 0 {
        let mut v_toApplicative_505_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_506_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_e_502_);
        lean_dec_ref(v_inst_501_);
        lean_dec_ref(v_inst_500_);
        v_toApplicative_505_ = lean_ctor_get(v_inst_499_, 0);
        lean_inc_ref(v_toApplicative_505_);
        lean_dec_ref(v_inst_499_);
        v_toPure_506_ = lean_ctor_get(v_toApplicative_505_, 1);
        lean_inc(v_toPure_506_);
        lean_dec_ref(v_toApplicative_505_);
        v___x_507_ = lean_box(0);
        v___x_508_ = lean_apply_2(v_toPure_506_, lean_box(0), v___x_507_);
        return v___x_508_;
    } else {
        let mut v___f_509_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
        lean_inc_ref(v_inst_499_);
        v___f_509_ = lean_alloc_closure(
            l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_509_, 0, v_inst_499_);
        v___x_510_ = l_Lean_Expr_getAppFn(v_e_502_);
        if lean_obj_tag(v___x_510_) == 4 {
            let mut v_declName_511_: *mut LeanObject = core::ptr::null_mut();
            let mut v_us_512_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toApplicative_513_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toBind_514_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_515_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_516_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_517_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_519_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_520_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_521_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_522_: *mut LeanObject = core::ptr::null_mut();
            v_declName_511_ = lean_ctor_get(v___x_510_, 0);
            lean_inc_n(v_declName_511_, 4);
            v_us_512_ = lean_ctor_get(v___x_510_, 1);
            lean_inc_n(v_us_512_, 2);
            lean_dec_ref_known(v___x_510_, 2);
            v_toApplicative_513_ = lean_ctor_get(v_inst_499_, 0);
            v_toBind_514_ = lean_ctor_get(v_inst_499_, 1);
            lean_inc_n(v_toBind_514_, 5);
            lean_inc_ref_n(v_inst_499_, 4);
            lean_inc_ref_n(v_toApplicative_513_, 3);
            v___f_515_ = lean_alloc_closure(
                l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
                3,
                2,
            );
            lean_closure_set(v___f_515_, 0, v_toApplicative_513_);
            lean_closure_set(v___f_515_, 1, v_inst_499_);
            lean_inc_ref(v_inst_501_);
            lean_inc_ref_n(v_inst_500_, 3);
            v___f_516_ = lean_alloc_closure(
                l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__2 as *mut core::ffi::c_void,
                6,
                5,
            );
            lean_closure_set(v___f_516_, 0, v_inst_499_);
            lean_closure_set(v___f_516_, 1, v_inst_500_);
            lean_closure_set(v___f_516_, 2, v_inst_501_);
            lean_closure_set(v___f_516_, 3, v_toBind_514_);
            lean_closure_set(v___f_516_, 4, v___f_515_);
            lean_inc_ref(v_e_502_);
            v___f_517_ = lean_alloc_closure(
                l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4 as *mut core::ffi::c_void,
                8,
                7,
            );
            lean_closure_set(v___f_517_, 0, v_e_502_);
            lean_closure_set(v___f_517_, 1, v_toApplicative_513_);
            lean_closure_set(v___f_517_, 2, v_us_512_);
            lean_closure_set(v___f_517_, 3, v_declName_511_);
            lean_closure_set(v___f_517_, 4, v_inst_499_);
            lean_closure_set(v___f_517_, 5, v___f_516_);
            lean_closure_set(v___f_517_, 6, v_toBind_514_);
            v___x_518_ = lean_box((v_alsoCasesOn_503_) as usize);
            v___f_519_ = lean_alloc_closure(
                l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5___boxed as *mut core::ffi::c_void,
                9,
                8,
            );
            lean_closure_set(v___f_519_, 0, v___f_509_);
            lean_closure_set(v___f_519_, 1, v___x_518_);
            lean_closure_set(v___f_519_, 2, v_declName_511_);
            lean_closure_set(v___f_519_, 3, v_inst_499_);
            lean_closure_set(v___f_519_, 4, v_inst_500_);
            lean_closure_set(v___f_519_, 5, v_inst_501_);
            lean_closure_set(v___f_519_, 6, v_toBind_514_);
            lean_closure_set(v___f_519_, 7, v___f_517_);
            v___f_520_ = lean_alloc_closure(
                l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__6 as *mut core::ffi::c_void,
                8,
                7,
            );
            lean_closure_set(v___f_520_, 0, v_e_502_);
            lean_closure_set(v___f_520_, 1, v_toApplicative_513_);
            lean_closure_set(v___f_520_, 2, v_us_512_);
            lean_closure_set(v___f_520_, 3, v_declName_511_);
            lean_closure_set(v___f_520_, 4, v_inst_500_);
            lean_closure_set(v___f_520_, 5, v_toBind_514_);
            lean_closure_set(v___f_520_, 6, v___f_519_);
            v___x_521_ =
                l_Lean_Meta_getMatcherInfo_x3f___redArg(v_inst_499_, v_inst_500_, v_declName_511_);
            v___x_522_ = lean_apply_4(
                v_toBind_514_,
                lean_box(0),
                lean_box(0),
                v___x_521_,
                v___f_520_,
            );
            return v___x_522_;
        } else {
            let mut v___x_523_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v___x_510_);
            lean_dec_ref(v___f_509_);
            lean_dec_ref(v_e_502_);
            lean_dec_ref(v_inst_501_);
            lean_dec_ref(v_inst_500_);
            v___x_523_ = lean_box(0);
            v___x_524_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__0(v_inst_499_, v___x_523_);
            return v___x_524_;
        }
    }
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___redArg___boxed(
    mut v_inst_525_: *mut LeanObject,
    mut v_inst_526_: *mut LeanObject,
    mut v_inst_527_: *mut LeanObject,
    mut v_e_528_: *mut LeanObject,
    mut v_alsoCasesOn_529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_alsoCasesOn_boxed_530_: u8 = 0;
    let mut v_res_531_: *mut LeanObject = core::ptr::null_mut();
    v_alsoCasesOn_boxed_530_ = (lean_unbox(v_alsoCasesOn_529_) as u8);
    v_res_531_ = l_Lean_Meta_matchMatcherApp_x3f___redArg(
        v_inst_525_,
        v_inst_526_,
        v_inst_527_,
        v_e_528_,
        v_alsoCasesOn_boxed_530_,
    );
    return v_res_531_;
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f(
    mut v_m_532_: *mut LeanObject,
    mut v_inst_533_: *mut LeanObject,
    mut v_inst_534_: *mut LeanObject,
    mut v_inst_535_: *mut LeanObject,
    mut v_e_536_: *mut LeanObject,
    mut v_alsoCasesOn_537_: u8,
) -> *mut LeanObject {
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    v___x_538_ = l_Lean_Meta_matchMatcherApp_x3f___redArg(
        v_inst_533_,
        v_inst_534_,
        v_inst_535_,
        v_e_536_,
        v_alsoCasesOn_537_,
    );
    return v___x_538_;
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___boxed(
    mut v_m_539_: *mut LeanObject,
    mut v_inst_540_: *mut LeanObject,
    mut v_inst_541_: *mut LeanObject,
    mut v_inst_542_: *mut LeanObject,
    mut v_e_543_: *mut LeanObject,
    mut v_alsoCasesOn_544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_alsoCasesOn_boxed_545_: u8 = 0;
    let mut v_res_546_: *mut LeanObject = core::ptr::null_mut();
    v_alsoCasesOn_boxed_545_ = (lean_unbox(v_alsoCasesOn_544_) as u8);
    v_res_546_ = l_Lean_Meta_matchMatcherApp_x3f(
        v_m_539_,
        v_inst_540_,
        v_inst_541_,
        v_inst_542_,
        v_e_543_,
        v_alsoCasesOn_boxed_545_,
    );
    return v_res_546_;
}
pub unsafe fn l_Lean_Meta_MatcherApp_altNumParams(
    mut v_matcherApp_547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toMatcherInfo_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut LeanObject = core::ptr::null_mut();
    v_toMatcherInfo_548_ = lean_ctor_get(v_matcherApp_547_, 0);
    lean_inc_ref(v_toMatcherInfo_548_);
    lean_dec_ref(v_matcherApp_547_);
    v___x_549_ = l_Lean_Meta_Match_MatcherInfo_altNumParams(v_toMatcherInfo_548_);
    return v___x_549_;
}
pub unsafe fn l_Lean_Meta_MatcherApp_toExpr(
    mut v_matcherApp_550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_matcherName_551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_matcherLevels_552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_motive_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discrs_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_remaining_557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    v_matcherName_551_ = lean_ctor_get(v_matcherApp_550_, 1);
    lean_inc(v_matcherName_551_);
    v_matcherLevels_552_ = lean_ctor_get(v_matcherApp_550_, 2);
    lean_inc_ref(v_matcherLevels_552_);
    v_params_553_ = lean_ctor_get(v_matcherApp_550_, 3);
    lean_inc_ref(v_params_553_);
    v_motive_554_ = lean_ctor_get(v_matcherApp_550_, 4);
    lean_inc_ref(v_motive_554_);
    v_discrs_555_ = lean_ctor_get(v_matcherApp_550_, 5);
    lean_inc_ref(v_discrs_555_);
    v_alts_556_ = lean_ctor_get(v_matcherApp_550_, 6);
    lean_inc_ref(v_alts_556_);
    v_remaining_557_ = lean_ctor_get(v_matcherApp_550_, 7);
    lean_inc_ref(v_remaining_557_);
    lean_dec_ref(v_matcherApp_550_);
    v___x_558_ = lean_array_to_list(v_matcherLevels_552_);
    v___x_559_ = l_Lean_mkConst(v_matcherName_551_, v___x_558_);
    v_result_560_ = l_Lean_mkAppN(v___x_559_, v_params_553_);
    lean_dec_ref(v_params_553_);
    v_result_561_ = l_Lean_Expr_app___override(v_result_560_, v_motive_554_);
    v_result_562_ = l_Lean_mkAppN(v_result_561_, v_discrs_555_);
    lean_dec_ref(v_discrs_555_);
    v_result_563_ = l_Lean_mkAppN(v_result_562_, v_alts_556_);
    lean_dec_ref(v_alts_556_);
    v___x_564_ = l_Lean_mkAppN(v_result_563_, v_remaining_557_);
    lean_dec_ref(v_remaining_557_);
    return v___x_564_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Match_MatcherApp_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Match_MatcherApp_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Match_MatcherApp_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Match_MatcherInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_MatcherApp_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Match_MatcherApp_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Match_MatcherApp_Basic(builtin);
}

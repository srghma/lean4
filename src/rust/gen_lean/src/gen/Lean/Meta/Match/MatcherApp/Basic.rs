// Lean compiler output
// Module: Lean.Meta.Match.MatcherApp.Basic
// Imports: Lean.Meta.Match.MatcherInfo
use crate::ffi::{
    lean_array_get, lean_array_get_size, lean_array_mk, lean_array_size, lean_array_to_list,
    lean_mk_array, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
};
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
pub static l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__0_value:
    leanh::LeanStringObject<33> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__1_value:
    leanh::LeanStringObject<27> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__2_value:
    leanh::LeanStringObject<21> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__1_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__0(
    mut v_inst_283_: *mut leanh::LeanObject,
    mut v_____r_284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_285_ = leanh::lean_ctor_get(v_inst_283_, 0);
    leanh::lean_inc_ref(v_toApplicative_285_);
    leanh::lean_dec_ref(v_inst_283_);
    v_toPure_286_ = leanh::lean_ctor_get(v_toApplicative_285_, 1);
    leanh::lean_inc(v_toPure_286_);
    leanh::lean_dec_ref(v_toApplicative_285_);
    v___x_287_ = leanh::lean_box(0);
    v___x_288_ = leanh::lean_apply_2(v_toPure_286_, leanh::lean_box(0), v___x_287_);
    return v___x_288_;
}
pub unsafe fn _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_292_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__2;
    v___x_293_ = leanh::lean_unsigned_to_nat(53);
    v___x_294_ = leanh::lean_unsigned_to_nat(62);
    v___x_295_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__1;
    v___x_296_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__0;
    v___x_297_ =
        l_mkPanicMessageWithDecl(v___x_296_, v___x_295_, v___x_294_, v___x_293_, v___x_292_);
    return v___x_297_;
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1(
    mut v_toApplicative_298_: *mut leanh::LeanObject,
    mut v_inst_299_: *mut leanh::LeanObject,
    mut v_____x_300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____x_300_) == 6 {
        let mut v_val_301_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_302_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_numFields_303_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_304_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_305_: u8 = 0;
        let mut v___x_306_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_299_);
        v_val_301_ = leanh::lean_ctor_get(v_____x_300_, 0);
        v_toPure_302_ = leanh::lean_ctor_get(v_toApplicative_298_, 1);
        leanh::lean_inc(v_toPure_302_);
        leanh::lean_dec_ref(v_toApplicative_298_);
        v_numFields_303_ = leanh::lean_ctor_get(v_val_301_, 4);
        v___x_304_ = leanh::lean_unsigned_to_nat(0);
        v___x_305_ = 0;
        leanh::lean_inc(v_numFields_303_);
        v___x_306_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
        leanh::lean_ctor_set(v___x_306_, 0, v_numFields_303_);
        leanh::lean_ctor_set(v___x_306_, 1, v___x_304_);
        leanh::lean_ctor_set_uint8(
            v___x_306_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            v___x_305_,
        );
        v___x_307_ =
            leanh::lean_apply_2(v_toPure_302_, leanh::lean_box(0), v___x_306_);
        return v___x_307_;
    } else {
        let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_310_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_311_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toApplicative_298_);
        v___x_308_ = l_Lean_Meta_Match_instInhabitedAltParamInfo_default;
        v___x_309_ = l_instInhabitedOfMonad___redArg(v_inst_299_, v___x_308_);
        v___x_310_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__3),
            core::ptr::addr_of_mut!(
                l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__3_once
            ),
            _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___closed__3,
        );
        v___x_311_ = l_panic___redArg(v___x_309_, v___x_310_);
        leanh::lean_dec(v___x_309_);
        return v___x_311_;
    }
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___boxed(
    mut v_toApplicative_312_: *mut leanh::LeanObject,
    mut v_inst_313_: *mut leanh::LeanObject,
    mut v_____x_314_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_315_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1(
        v_toApplicative_312_,
        v_inst_313_,
        v_____x_314_,
    );
    leanh::lean_dec_ref(v_____x_314_);
    return v_res_315_;
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__2(
    mut v_inst_316_: *mut leanh::LeanObject,
    mut v_inst_317_: *mut leanh::LeanObject,
    mut v_inst_318_: *mut leanh::LeanObject,
    mut v_toBind_319_: *mut leanh::LeanObject,
    mut v___f_320_: *mut leanh::LeanObject,
    mut v_ctor_321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_322_ = l_Lean_getConstInfo___redArg(v_inst_316_, v_inst_317_, v_inst_318_, v_ctor_321_);
    v___x_323_ = leanh::lean_apply_4(
        v_toBind_319_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_322_,
        v___f_320_,
    );
    return v___x_323_;
}
pub unsafe fn _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_324_ = leanh::lean_box(0);
    v___x_325_ = leanh::lean_unsigned_to_nat(16);
    v___x_326_ = lean_mk_array(v___x_325_, v___x_324_);
    return v___x_326_;
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3(
    mut v_toApplicative_327_: *mut leanh::LeanObject,
    mut v_params_328_: *mut leanh::LeanObject,
    mut v_discrs_329_: *mut leanh::LeanObject,
    mut v___x_330_: *mut leanh::LeanObject,
    mut v___y_331_: *mut leanh::LeanObject,
    mut v_discrInfos_332_: *mut leanh::LeanObject,
    mut v_us_333_: *mut leanh::LeanObject,
    mut v_alts_334_: *mut leanh::LeanObject,
    mut v___x_335_: *mut leanh::LeanObject,
    mut v_declName_336_: *mut leanh::LeanObject,
    mut v_motive_337_: *mut leanh::LeanObject,
    mut v_altInfos_338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toPure_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toPure_339_ = leanh::lean_ctor_get(v_toApplicative_327_, 1);
    leanh::lean_inc(v_toPure_339_);
    leanh::lean_dec_ref(v_toApplicative_327_);
    v_start_340_ = leanh::lean_ctor_get(v_params_328_, 1);
    v_stop_341_ = leanh::lean_ctor_get(v_params_328_, 2);
    v_start_342_ = leanh::lean_ctor_get(v_discrs_329_, 1);
    v_stop_343_ = leanh::lean_ctor_get(v_discrs_329_, 2);
    v___x_344_ = lean_nat_sub(v_stop_341_, v_start_340_);
    v___x_345_ = lean_nat_sub(v_stop_343_, v_start_342_);
    v___x_346_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0_once),
        _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3___closed__0,
    );
    v___x_347_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_347_, 0, v___x_330_);
    leanh::lean_ctor_set(v___x_347_, 1, v___x_346_);
    v___x_348_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_348_, 0, v___x_344_);
    leanh::lean_ctor_set(v___x_348_, 1, v___x_345_);
    leanh::lean_ctor_set(v___x_348_, 2, v_altInfos_338_);
    leanh::lean_ctor_set(v___x_348_, 3, v___y_331_);
    leanh::lean_ctor_set(v___x_348_, 4, v_discrInfos_332_);
    leanh::lean_ctor_set(v___x_348_, 5, v___x_347_);
    v___x_349_ = lean_array_mk(v_us_333_);
    v___x_350_ = l_Subarray_copy___redArg(v_params_328_);
    v___x_351_ = l_Subarray_copy___redArg(v_discrs_329_);
    v___x_352_ = l_Subarray_copy___redArg(v_alts_334_);
    v___x_353_ = l_Subarray_copy___redArg(v___x_335_);
    v___x_354_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
    leanh::lean_ctor_set(v___x_354_, 0, v___x_348_);
    leanh::lean_ctor_set(v___x_354_, 1, v_declName_336_);
    leanh::lean_ctor_set(v___x_354_, 2, v___x_349_);
    leanh::lean_ctor_set(v___x_354_, 3, v___x_350_);
    leanh::lean_ctor_set(v___x_354_, 4, v_motive_337_);
    leanh::lean_ctor_set(v___x_354_, 5, v___x_351_);
    leanh::lean_ctor_set(v___x_354_, 6, v___x_352_);
    leanh::lean_ctor_set(v___x_354_, 7, v___x_353_);
    v___x_355_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_355_, 0, v___x_354_);
    v___x_356_ = leanh::lean_apply_2(v_toPure_339_, leanh::lean_box(0), v___x_355_);
    return v___x_356_;
}
pub unsafe fn _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_357_ = leanh::lean_box(0);
    v_dummy_358_ = l_Lean_Expr_sort___override(v___x_357_);
    return v_dummy_358_;
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4(
    mut v_e_361_: *mut leanh::LeanObject,
    mut v_toApplicative_362_: *mut leanh::LeanObject,
    mut v_us_363_: *mut leanh::LeanObject,
    mut v_declName_364_: *mut leanh::LeanObject,
    mut v_inst_365_: *mut leanh::LeanObject,
    mut v___f_366_: *mut leanh::LeanObject,
    mut v_toBind_367_: *mut leanh::LeanObject,
    mut v_____x_368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_386_: u8 = 0;
    let mut v_toPure_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_motive_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_discrs_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_discrInfos_397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_404_: usize = 0;
    let mut v___x_405_: usize = 0;
    let mut v___x_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_415_: u8 = 0;
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: u8 = 0;
    let mut v_toPure_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____x_368_) == 5 {
                    v_val_369_ = leanh::lean_ctor_get(v_____x_368_, 0);
                    leanh::lean_inc_ref(v_val_369_);
                    leanh::lean_dec_ref_known(v_____x_368_, 1);
                    v_toConstantVal_370_ = leanh::lean_ctor_get(v_val_369_, 0);
                    leanh::lean_inc_ref(v_toConstantVal_370_);
                    v_numParams_371_ = leanh::lean_ctor_get(v_val_369_, 1);
                    leanh::lean_inc(v_numParams_371_);
                    v_numIndices_372_ = leanh::lean_ctor_get(v_val_369_, 2);
                    leanh::lean_inc(v_numIndices_372_);
                    v_ctors_373_ = leanh::lean_ctor_get(v_val_369_, 4);
                    leanh::lean_inc(v_ctors_373_);
                    v_nargs_374_ = l_Lean_Expr_getAppNumArgs(v_e_361_);
                    v_dummy_375_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0_once
                        ),
                        _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0,
                    );
                    leanh::lean_inc(v_nargs_374_);
                    v___x_376_ = lean_mk_array(v_nargs_374_, v_dummy_375_);
                    v___x_377_ = leanh::lean_unsigned_to_nat(1);
                    v___x_378_ = lean_nat_sub(v_nargs_374_, v___x_377_);
                    leanh::lean_dec(v_nargs_374_);
                    v_args_379_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_e_361_, v___x_376_, v___x_378_,
                    );
                    v___x_380_ = lean_nat_add(v_numParams_371_, v___x_377_);
                    v___x_381_ = lean_nat_add(v___x_380_, v_numIndices_372_);
                    v___x_382_ = lean_nat_add(v___x_381_, v___x_377_);
                    leanh::lean_dec(v___x_381_);
                    v___x_383_ = l_Lean_InductiveVal_numCtors(v_val_369_);
                    leanh::lean_dec_ref(v_val_369_);
                    v___x_384_ = lean_nat_add(v___x_382_, v___x_383_);
                    leanh::lean_dec(v___x_383_);
                    v___x_385_ = lean_array_get_size(v_args_379_);
                    v___x_386_ = lean_nat_dec_le(v___x_384_, v___x_385_);
                    if v___x_386_ == 0 {
                        leanh::lean_dec(v___x_384_);
                        leanh::lean_dec(v___x_382_);
                        leanh::lean_dec(v___x_380_);
                        leanh::lean_dec_ref(v_args_379_);
                        leanh::lean_dec(v_ctors_373_);
                        leanh::lean_dec(v_numIndices_372_);
                        leanh::lean_dec(v_numParams_371_);
                        leanh::lean_dec_ref(v_toConstantVal_370_);
                        leanh::lean_dec(v_toBind_367_);
                        leanh::lean_dec(v___f_366_);
                        leanh::lean_dec_ref(v_inst_365_);
                        leanh::lean_dec(v_declName_364_);
                        leanh::lean_dec(v_us_363_);
                        v_toPure_387_ = leanh::lean_ctor_get(v_toApplicative_362_, 1);
                        leanh::lean_inc(v_toPure_387_);
                        leanh::lean_dec_ref(v_toApplicative_362_);
                        v___x_388_ = leanh::lean_box(0);
                        v___x_389_ = leanh::lean_apply_2(
                            v_toPure_387_,
                            leanh::lean_box(0),
                            v___x_388_,
                        );
                        return v___x_389_;
                    } else {
                        v___x_390_ = leanh::lean_unsigned_to_nat(0);
                        leanh::lean_inc(v_numParams_371_);
                        leanh::lean_inc_ref_n(v_args_379_, 3);
                        v_params_391_ =
                            l_Array_toSubarray___redArg(v_args_379_, v___x_390_, v_numParams_371_);
                        v___x_392_ = l_Lean_instInhabitedExpr;
                        v_motive_393_ = lean_array_get(v___x_392_, v_args_379_, v_numParams_371_);
                        leanh::lean_dec(v_numParams_371_);
                        leanh::lean_inc(v___x_382_);
                        v_discrs_394_ =
                            l_Array_toSubarray___redArg(v_args_379_, v___x_380_, v___x_382_);
                        v___x_395_ = lean_nat_add(v_numIndices_372_, v___x_377_);
                        leanh::lean_dec(v_numIndices_372_);
                        v___x_396_ = leanh::lean_box(0);
                        v_discrInfos_397_ = lean_mk_array(v___x_395_, v___x_396_);
                        leanh::lean_inc(v___x_384_);
                        v_alts_398_ =
                            l_Array_toSubarray___redArg(v_args_379_, v___x_382_, v___x_384_);
                        v___x_417_ = lean_nat_dec_le(v___x_384_, v___x_390_);
                        if v___x_417_ == 0 {
                            v_lower_409_ = v___x_384_;
                            v_upper_410_ = v___x_385_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_384_);
                            v_lower_409_ = v___x_390_;
                            v_upper_410_ = v___x_385_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_____x_368_);
                    leanh::lean_dec(v_toBind_367_);
                    leanh::lean_dec(v___f_366_);
                    leanh::lean_dec_ref(v_inst_365_);
                    leanh::lean_dec(v_declName_364_);
                    leanh::lean_dec(v_us_363_);
                    leanh::lean_dec_ref(v_e_361_);
                    v_toPure_418_ = leanh::lean_ctor_get(v_toApplicative_362_, 1);
                    leanh::lean_inc(v_toPure_418_);
                    leanh::lean_dec_ref(v_toApplicative_362_);
                    v___x_419_ = leanh::lean_box(0);
                    v___x_420_ = leanh::lean_apply_2(
                        v_toPure_418_,
                        leanh::lean_box(0),
                        v___x_419_,
                    );
                    return v___x_420_;
                }
            }
            1 => {
                v___f_402_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__3 as *mut core::ffi::c_void,
                    12,
                    11,
                );
                leanh::lean_closure_set(v___f_402_, 0, v_toApplicative_362_);
                leanh::lean_closure_set(v___f_402_, 1, v_params_391_);
                leanh::lean_closure_set(v___f_402_, 2, v_discrs_394_);
                leanh::lean_closure_set(v___f_402_, 3, v___x_390_);
                leanh::lean_closure_set(v___f_402_, 4, v___y_401_);
                leanh::lean_closure_set(v___f_402_, 5, v_discrInfos_397_);
                leanh::lean_closure_set(v___f_402_, 6, v_us_363_);
                leanh::lean_closure_set(v___f_402_, 7, v_alts_398_);
                leanh::lean_closure_set(v___f_402_, 8, v___y_400_);
                leanh::lean_closure_set(v___f_402_, 9, v_declName_364_);
                leanh::lean_closure_set(v___f_402_, 10, v_motive_393_);
                v___x_403_ = lean_array_mk(v_ctors_373_);
                v_sz_404_ = lean_array_size(v___x_403_);
                v___x_405_ = 0usize;
                v___x_406_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v_inst_365_,
                    v___f_366_,
                    v_sz_404_,
                    v___x_405_,
                    v___x_403_,
                );
                v___x_407_ = leanh::lean_apply_4(
                    v_toBind_367_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_406_,
                    v___f_402_,
                );
                return v___x_407_;
            }
            2 => {
                v_levelParams_411_ = leanh::lean_ctor_get(v_toConstantVal_370_, 1);
                leanh::lean_inc(v_levelParams_411_);
                leanh::lean_dec_ref(v_toConstantVal_370_);
                v___x_412_ = l_Array_toSubarray___redArg(v_args_379_, v_lower_409_, v_upper_410_);
                v___x_413_ = l_List_lengthTR___redArg(v_levelParams_411_);
                leanh::lean_dec(v_levelParams_411_);
                v___x_414_ = l_List_lengthTR___redArg(v_us_363_);
                v___x_415_ = lean_nat_dec_eq(v___x_413_, v___x_414_);
                leanh::lean_dec(v___x_414_);
                leanh::lean_dec(v___x_413_);
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
    mut v___f_421_: *mut leanh::LeanObject,
    mut v_alsoCasesOn_422_: u8,
    mut v_declName_423_: *mut leanh::LeanObject,
    mut v_inst_424_: *mut leanh::LeanObject,
    mut v_inst_425_: *mut leanh::LeanObject,
    mut v_inst_426_: *mut leanh::LeanObject,
    mut v_toBind_427_: *mut leanh::LeanObject,
    mut v___f_428_: *mut leanh::LeanObject,
    mut v_____do__lift_429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: u8 = 0;
    let mut v_indName_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_alsoCasesOn_422_ == 0 {
                    leanh::lean_dec_ref(v_____do__lift_429_);
                    leanh::lean_dec(v___f_428_);
                    leanh::lean_dec(v_toBind_427_);
                    leanh::lean_dec_ref(v_inst_426_);
                    leanh::lean_dec_ref(v_inst_425_);
                    leanh::lean_dec_ref(v_inst_424_);
                    leanh::lean_dec(v_declName_423_);
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_declName_423_);
                    v___x_433_ = l_Lean_isCasesOnRecursor(v_____do__lift_429_, v_declName_423_);
                    if v___x_433_ == 0 {
                        leanh::lean_dec(v___f_428_);
                        leanh::lean_dec(v_toBind_427_);
                        leanh::lean_dec_ref(v_inst_426_);
                        leanh::lean_dec_ref(v_inst_425_);
                        leanh::lean_dec_ref(v_inst_424_);
                        leanh::lean_dec(v_declName_423_);
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___f_421_);
                        v_indName_434_ = l_Lean_Name_getPrefix(v_declName_423_);
                        leanh::lean_dec(v_declName_423_);
                        v___x_435_ = l_Lean_getConstInfo___redArg(
                            v_inst_424_,
                            v_inst_425_,
                            v_inst_426_,
                            v_indName_434_,
                        );
                        v___x_436_ = leanh::lean_apply_4(
                            v_toBind_427_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_435_,
                            v___f_428_,
                        );
                        return v___x_436_;
                    }
                }
            }
            1 => {
                v___x_431_ = leanh::lean_box(0);
                v___x_432_ = leanh::lean_apply_1(v___f_421_, v___x_431_);
                return v___x_432_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5___boxed(
    mut v___f_437_: *mut leanh::LeanObject,
    mut v_alsoCasesOn_438_: *mut leanh::LeanObject,
    mut v_declName_439_: *mut leanh::LeanObject,
    mut v_inst_440_: *mut leanh::LeanObject,
    mut v_inst_441_: *mut leanh::LeanObject,
    mut v_inst_442_: *mut leanh::LeanObject,
    mut v_toBind_443_: *mut leanh::LeanObject,
    mut v___f_444_: *mut leanh::LeanObject,
    mut v_____do__lift_445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_alsoCasesOn_boxed_446_: u8 = 0;
    let mut v_res_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_alsoCasesOn_boxed_446_ = (leanh::lean_unbox(v_alsoCasesOn_438_) as u8);
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
    mut v_e_448_: *mut leanh::LeanObject,
    mut v_toApplicative_449_: *mut leanh::LeanObject,
    mut v_us_450_: *mut leanh::LeanObject,
    mut v_declName_451_: *mut leanh::LeanObject,
    mut v_inst_452_: *mut leanh::LeanObject,
    mut v_toBind_453_: *mut leanh::LeanObject,
    mut v___f_454_: *mut leanh::LeanObject,
    mut v_____do__lift_455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_459_: u8 = 0;
    let mut v_dummy_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: u8 = 0;
    let mut v_toPure_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numDiscrs_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_496_: u8 = 0;
    let mut v_getEnv_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_455_) == 1 {
                    leanh::lean_dec(v___f_454_);
                    leanh::lean_dec(v_toBind_453_);
                    leanh::lean_dec_ref(v_inst_452_);
                    v_val_456_ = leanh::lean_ctor_get(v_____do__lift_455_, 0);
                    v_isSharedCheck_496_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_455_)) as u8;
                    if v_isSharedCheck_496_ == 0 {
                        v___x_458_ = v_____do__lift_455_;
                        v_isShared_459_ = v_isSharedCheck_496_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_456_);
                        leanh::lean_dec(v_____do__lift_455_);
                        v___x_458_ = leanh::lean_box(0);
                        v_isShared_459_ = v_isSharedCheck_496_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_____do__lift_455_);
                    leanh::lean_dec(v_declName_451_);
                    leanh::lean_dec(v_us_450_);
                    leanh::lean_dec_ref(v_toApplicative_449_);
                    leanh::lean_dec_ref(v_e_448_);
                    v_getEnv_497_ = leanh::lean_ctor_get(v_inst_452_, 0);
                    leanh::lean_inc(v_getEnv_497_);
                    leanh::lean_dec_ref(v_inst_452_);
                    v___x_498_ = leanh::lean_apply_4(
                        v_toBind_453_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v_getEnv_497_,
                        v___f_454_,
                    );
                    return v___x_498_;
                }
            }
            1 => {
                v_dummy_460_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0_once
                    ),
                    _init_l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4___closed__0,
                );
                v_nargs_461_ = l_Lean_Expr_getAppNumArgs(v_e_448_);
                leanh::lean_inc(v_nargs_461_);
                v___x_462_ = lean_mk_array(v_nargs_461_, v_dummy_460_);
                v___x_463_ = leanh::lean_unsigned_to_nat(1);
                v___x_464_ = lean_nat_sub(v_nargs_461_, v___x_463_);
                leanh::lean_dec(v_nargs_461_);
                v_args_465_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                    v_e_448_, v___x_462_, v___x_464_,
                );
                v___x_466_ = lean_array_get_size(v_args_465_);
                v___x_467_ = l_Lean_Meta_Match_MatcherInfo_arity(v_val_456_);
                v___x_468_ = lean_nat_dec_lt(v___x_466_, v___x_467_);
                leanh::lean_dec(v___x_467_);
                if v___x_468_ == 0 {
                    v_toPure_469_ = leanh::lean_ctor_get(v_toApplicative_449_, 1);
                    leanh::lean_inc(v_toPure_469_);
                    leanh::lean_dec_ref(v_toApplicative_449_);
                    v_numParams_470_ = leanh::lean_ctor_get(v_val_456_, 0);
                    v_numDiscrs_471_ = leanh::lean_ctor_get(v_val_456_, 1);
                    v___x_472_ = lean_array_mk(v_us_450_);
                    v___x_473_ = leanh::lean_unsigned_to_nat(0);
                    leanh::lean_inc(v_numParams_470_);
                    v___x_474_ =
                        l_Array_extract___redArg(v_args_465_, v___x_473_, v_numParams_470_);
                    v___x_475_ = l_Lean_instInhabitedExpr;
                    v___x_476_ = l_Lean_Meta_Match_MatcherInfo_getMotivePos(v_val_456_);
                    v___x_477_ = lean_array_get(v___x_475_, v_args_465_, v___x_476_);
                    leanh::lean_dec(v___x_476_);
                    v___x_478_ = lean_nat_add(v_numParams_470_, v___x_463_);
                    v___x_479_ = lean_nat_add(v___x_478_, v_numDiscrs_471_);
                    leanh::lean_inc(v___x_479_);
                    leanh::lean_inc_ref_n(v_args_465_, 2);
                    v___x_480_ = l_Array_toSubarray___redArg(v_args_465_, v___x_478_, v___x_479_);
                    v___x_481_ = l_Subarray_copy___redArg(v___x_480_);
                    v___x_482_ = l_Lean_Meta_Match_MatcherInfo_numAlts(v_val_456_);
                    v___x_483_ = lean_nat_add(v___x_479_, v___x_482_);
                    leanh::lean_dec(v___x_482_);
                    leanh::lean_inc(v___x_483_);
                    v___x_484_ = l_Array_toSubarray___redArg(v_args_465_, v___x_479_, v___x_483_);
                    v___x_485_ = l_Subarray_copy___redArg(v___x_484_);
                    v___x_486_ = l_Array_toSubarray___redArg(v_args_465_, v___x_483_, v___x_466_);
                    v___x_487_ = l_Subarray_copy___redArg(v___x_486_);
                    v___x_488_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    leanh::lean_ctor_set(v___x_488_, 0, v_val_456_);
                    leanh::lean_ctor_set(v___x_488_, 1, v_declName_451_);
                    leanh::lean_ctor_set(v___x_488_, 2, v___x_472_);
                    leanh::lean_ctor_set(v___x_488_, 3, v___x_474_);
                    leanh::lean_ctor_set(v___x_488_, 4, v___x_477_);
                    leanh::lean_ctor_set(v___x_488_, 5, v___x_481_);
                    leanh::lean_ctor_set(v___x_488_, 6, v___x_485_);
                    leanh::lean_ctor_set(v___x_488_, 7, v___x_487_);
                    if v_isShared_459_ == 0 {
                        leanh::lean_ctor_set(v___x_458_, 0, v___x_488_);
                        v___x_490_ = v___x_458_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_492_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_488_);
                        v___x_490_ = v_reuseFailAlloc_492_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_args_465_);
                    leanh::lean_del_object(v___x_458_);
                    leanh::lean_dec(v_val_456_);
                    leanh::lean_dec(v_declName_451_);
                    leanh::lean_dec(v_us_450_);
                    v_toPure_493_ = leanh::lean_ctor_get(v_toApplicative_449_, 1);
                    leanh::lean_inc(v_toPure_493_);
                    leanh::lean_dec_ref(v_toApplicative_449_);
                    v___x_494_ = leanh::lean_box(0);
                    v___x_495_ = leanh::lean_apply_2(
                        v_toPure_493_,
                        leanh::lean_box(0),
                        v___x_494_,
                    );
                    return v___x_495_;
                }
            }
            2 => {
                v___x_491_ = leanh::lean_apply_2(
                    v_toPure_469_,
                    leanh::lean_box(0),
                    v___x_490_,
                );
                return v___x_491_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___redArg(
    mut v_inst_499_: *mut leanh::LeanObject,
    mut v_inst_500_: *mut leanh::LeanObject,
    mut v_inst_501_: *mut leanh::LeanObject,
    mut v_e_502_: *mut leanh::LeanObject,
    mut v_alsoCasesOn_503_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_504_: u8 = 0;
    v___x_504_ = l_Lean_Expr_isApp(v_e_502_);
    if v___x_504_ == 0 {
        let mut v_toApplicative_505_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_506_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_507_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_508_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_e_502_);
        leanh::lean_dec_ref(v_inst_501_);
        leanh::lean_dec_ref(v_inst_500_);
        v_toApplicative_505_ = leanh::lean_ctor_get(v_inst_499_, 0);
        leanh::lean_inc_ref(v_toApplicative_505_);
        leanh::lean_dec_ref(v_inst_499_);
        v_toPure_506_ = leanh::lean_ctor_get(v_toApplicative_505_, 1);
        leanh::lean_inc(v_toPure_506_);
        leanh::lean_dec_ref(v_toApplicative_505_);
        v___x_507_ = leanh::lean_box(0);
        v___x_508_ =
            leanh::lean_apply_2(v_toPure_506_, leanh::lean_box(0), v___x_507_);
        return v___x_508_;
    } else {
        let mut v___f_509_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_510_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc_ref(v_inst_499_);
        v___f_509_ = leanh::lean_alloc_closure(
            l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__0 as *mut core::ffi::c_void,
            2,
            1,
        );
        leanh::lean_closure_set(v___f_509_, 0, v_inst_499_);
        v___x_510_ = l_Lean_Expr_getAppFn(v_e_502_);
        if leanh::lean_obj_tag(v___x_510_) == 4 {
            let mut v_declName_511_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_us_512_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toApplicative_513_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_toBind_514_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_515_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_516_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_517_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_519_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_520_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_521_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_522_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_declName_511_ = leanh::lean_ctor_get(v___x_510_, 0);
            leanh::lean_inc_n(v_declName_511_, 4);
            v_us_512_ = leanh::lean_ctor_get(v___x_510_, 1);
            leanh::lean_inc_n(v_us_512_, 2);
            leanh::lean_dec_ref_known(v___x_510_, 2);
            v_toApplicative_513_ = leanh::lean_ctor_get(v_inst_499_, 0);
            v_toBind_514_ = leanh::lean_ctor_get(v_inst_499_, 1);
            leanh::lean_inc_n(v_toBind_514_, 5);
            leanh::lean_inc_ref_n(v_inst_499_, 4);
            leanh::lean_inc_ref_n(v_toApplicative_513_, 3);
            v___f_515_ = leanh::lean_alloc_closure(
                l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
                3,
                2,
            );
            leanh::lean_closure_set(v___f_515_, 0, v_toApplicative_513_);
            leanh::lean_closure_set(v___f_515_, 1, v_inst_499_);
            leanh::lean_inc_ref(v_inst_501_);
            leanh::lean_inc_ref_n(v_inst_500_, 3);
            v___f_516_ = leanh::lean_alloc_closure(
                l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__2 as *mut core::ffi::c_void,
                6,
                5,
            );
            leanh::lean_closure_set(v___f_516_, 0, v_inst_499_);
            leanh::lean_closure_set(v___f_516_, 1, v_inst_500_);
            leanh::lean_closure_set(v___f_516_, 2, v_inst_501_);
            leanh::lean_closure_set(v___f_516_, 3, v_toBind_514_);
            leanh::lean_closure_set(v___f_516_, 4, v___f_515_);
            leanh::lean_inc_ref(v_e_502_);
            v___f_517_ = leanh::lean_alloc_closure(
                l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__4 as *mut core::ffi::c_void,
                8,
                7,
            );
            leanh::lean_closure_set(v___f_517_, 0, v_e_502_);
            leanh::lean_closure_set(v___f_517_, 1, v_toApplicative_513_);
            leanh::lean_closure_set(v___f_517_, 2, v_us_512_);
            leanh::lean_closure_set(v___f_517_, 3, v_declName_511_);
            leanh::lean_closure_set(v___f_517_, 4, v_inst_499_);
            leanh::lean_closure_set(v___f_517_, 5, v___f_516_);
            leanh::lean_closure_set(v___f_517_, 6, v_toBind_514_);
            v___x_518_ = leanh::lean_box((v_alsoCasesOn_503_) as usize);
            v___f_519_ = leanh::lean_alloc_closure(
                l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__5___boxed as *mut core::ffi::c_void,
                9,
                8,
            );
            leanh::lean_closure_set(v___f_519_, 0, v___f_509_);
            leanh::lean_closure_set(v___f_519_, 1, v___x_518_);
            leanh::lean_closure_set(v___f_519_, 2, v_declName_511_);
            leanh::lean_closure_set(v___f_519_, 3, v_inst_499_);
            leanh::lean_closure_set(v___f_519_, 4, v_inst_500_);
            leanh::lean_closure_set(v___f_519_, 5, v_inst_501_);
            leanh::lean_closure_set(v___f_519_, 6, v_toBind_514_);
            leanh::lean_closure_set(v___f_519_, 7, v___f_517_);
            v___f_520_ = leanh::lean_alloc_closure(
                l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__6 as *mut core::ffi::c_void,
                8,
                7,
            );
            leanh::lean_closure_set(v___f_520_, 0, v_e_502_);
            leanh::lean_closure_set(v___f_520_, 1, v_toApplicative_513_);
            leanh::lean_closure_set(v___f_520_, 2, v_us_512_);
            leanh::lean_closure_set(v___f_520_, 3, v_declName_511_);
            leanh::lean_closure_set(v___f_520_, 4, v_inst_500_);
            leanh::lean_closure_set(v___f_520_, 5, v_toBind_514_);
            leanh::lean_closure_set(v___f_520_, 6, v___f_519_);
            v___x_521_ =
                l_Lean_Meta_getMatcherInfo_x3f___redArg(v_inst_499_, v_inst_500_, v_declName_511_);
            v___x_522_ = leanh::lean_apply_4(
                v_toBind_514_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_521_,
                v___f_520_,
            );
            return v___x_522_;
        } else {
            let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v___x_510_);
            leanh::lean_dec_ref(v___f_509_);
            leanh::lean_dec_ref(v_e_502_);
            leanh::lean_dec_ref(v_inst_501_);
            leanh::lean_dec_ref(v_inst_500_);
            v___x_523_ = leanh::lean_box(0);
            v___x_524_ = l_Lean_Meta_matchMatcherApp_x3f___redArg___lam__0(v_inst_499_, v___x_523_);
            return v___x_524_;
        }
    }
}
pub unsafe fn l_Lean_Meta_matchMatcherApp_x3f___redArg___boxed(
    mut v_inst_525_: *mut leanh::LeanObject,
    mut v_inst_526_: *mut leanh::LeanObject,
    mut v_inst_527_: *mut leanh::LeanObject,
    mut v_e_528_: *mut leanh::LeanObject,
    mut v_alsoCasesOn_529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_alsoCasesOn_boxed_530_: u8 = 0;
    let mut v_res_531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_alsoCasesOn_boxed_530_ = (leanh::lean_unbox(v_alsoCasesOn_529_) as u8);
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
    mut v_m_532_: *mut leanh::LeanObject,
    mut v_inst_533_: *mut leanh::LeanObject,
    mut v_inst_534_: *mut leanh::LeanObject,
    mut v_inst_535_: *mut leanh::LeanObject,
    mut v_e_536_: *mut leanh::LeanObject,
    mut v_alsoCasesOn_537_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_m_539_: *mut leanh::LeanObject,
    mut v_inst_540_: *mut leanh::LeanObject,
    mut v_inst_541_: *mut leanh::LeanObject,
    mut v_inst_542_: *mut leanh::LeanObject,
    mut v_e_543_: *mut leanh::LeanObject,
    mut v_alsoCasesOn_544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_alsoCasesOn_boxed_545_: u8 = 0;
    let mut v_res_546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_alsoCasesOn_boxed_545_ = (leanh::lean_unbox(v_alsoCasesOn_544_) as u8);
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
    mut v_matcherApp_547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toMatcherInfo_548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_549_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toMatcherInfo_548_ = leanh::lean_ctor_get(v_matcherApp_547_, 0);
    leanh::lean_inc_ref(v_toMatcherInfo_548_);
    leanh::lean_dec_ref(v_matcherApp_547_);
    v___x_549_ = l_Lean_Meta_Match_MatcherInfo_altNumParams(v_toMatcherInfo_548_);
    return v___x_549_;
}
pub unsafe fn l_Lean_Meta_MatcherApp_toExpr(
    mut v_matcherApp_550_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_matcherName_551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_matcherLevels_552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_motive_554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_discrs_555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_remaining_557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_matcherName_551_ = leanh::lean_ctor_get(v_matcherApp_550_, 1);
    leanh::lean_inc(v_matcherName_551_);
    v_matcherLevels_552_ = leanh::lean_ctor_get(v_matcherApp_550_, 2);
    leanh::lean_inc_ref(v_matcherLevels_552_);
    v_params_553_ = leanh::lean_ctor_get(v_matcherApp_550_, 3);
    leanh::lean_inc_ref(v_params_553_);
    v_motive_554_ = leanh::lean_ctor_get(v_matcherApp_550_, 4);
    leanh::lean_inc_ref(v_motive_554_);
    v_discrs_555_ = leanh::lean_ctor_get(v_matcherApp_550_, 5);
    leanh::lean_inc_ref(v_discrs_555_);
    v_alts_556_ = leanh::lean_ctor_get(v_matcherApp_550_, 6);
    leanh::lean_inc_ref(v_alts_556_);
    v_remaining_557_ = leanh::lean_ctor_get(v_matcherApp_550_, 7);
    leanh::lean_inc_ref(v_remaining_557_);
    leanh::lean_dec_ref(v_matcherApp_550_);
    v___x_558_ = lean_array_to_list(v_matcherLevels_552_);
    v___x_559_ = l_Lean_mkConst(v_matcherName_551_, v___x_558_);
    v_result_560_ = l_Lean_mkAppN(v___x_559_, v_params_553_);
    leanh::lean_dec_ref(v_params_553_);
    v_result_561_ = l_Lean_Expr_app___override(v_result_560_, v_motive_554_);
    v_result_562_ = l_Lean_mkAppN(v_result_561_, v_discrs_555_);
    leanh::lean_dec_ref(v_discrs_555_);
    v_result_563_ = l_Lean_mkAppN(v_result_562_, v_alts_556_);
    leanh::lean_dec_ref(v_alts_556_);
    v___x_564_ = l_Lean_mkAppN(v_result_563_, v_remaining_557_);
    leanh::lean_dec_ref(v_remaining_557_);
    return v___x_564_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Match_MatcherApp_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Match_MatcherInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Match_MatcherApp_Basic(
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
pub unsafe fn initialize_Lean_Meta_Match_MatcherApp_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Match_MatcherInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Match_MatcherApp_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Match_MatcherApp_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Match_MatcherApp_Basic(builtin);
}
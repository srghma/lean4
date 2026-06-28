// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.SearchM
// Imports: Lean.Meta.Tactic.Grind.Arith.Linear.LinearM
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_num___override};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Expr::{l_Lean_Expr_const___override, l_Lean_FVarIdSet_insert};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::LinearM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM,
    l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Types::{
    l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default,
    l_Lean_Meta_Grind_Arith_Linear_linearExt,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg;
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_nat_add, lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__0_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__0_value
        ) as *mut LeanObject,
        17542774118954891045 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__2()
-> *mut LeanObject {
    let mut v___x_281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut LeanObject = core::ptr::null_mut();
    v___x_281_ = lean_box(0);
    v___x_282_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__1;
    v___x_283_ = l_Lean_Expr_const___override(v___x_282_, v___x_281_);
    return v___x_283_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__3()
-> *mut LeanObject {
    let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut LeanObject = core::ptr::null_mut();
    v___x_284_ = lean_box(0);
    v___x_285_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__2,
    );
    v___x_286_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_286_, 0, v___x_285_);
    lean_ctor_set(v___x_286_, 1, v___x_285_);
    lean_ctor_set(v___x_286_, 2, v___x_284_);
    lean_ctor_set(v___x_286_, 3, v___x_284_);
    return v___x_286_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__4()
-> *mut LeanObject {
    let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_289_: *mut LeanObject = core::ptr::null_mut();
    v___x_287_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__3,
    );
    v___x_288_ = lean_box(0);
    v___x_289_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_289_, 0, v___x_288_);
    lean_ctor_set(v___x_289_, 1, v___x_287_);
    return v___x_289_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__5()
-> *mut LeanObject {
    let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut LeanObject = core::ptr::null_mut();
    v___x_290_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
    v___x_291_ = lean_box(0);
    v___x_292_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__4_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__4,
    );
    v___x_293_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_293_, 0, v___x_292_);
    lean_ctor_set(v___x_293_, 1, v___x_291_);
    lean_ctor_set(v___x_293_, 2, v___x_290_);
    return v___x_293_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default() -> *mut LeanObject {
    let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
    v___x_294_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__5_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default___closed__5,
    );
    return v___x_294_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase() -> *mut LeanObject {
    let mut v___x_295_: *mut LeanObject = core::ptr::null_mut();
    v___x_295_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default;
    return v___x_295_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_mkCase___lam__0(
    mut v_a_296_: *mut LeanObject,
    mut v_s_297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_structs_298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToStructIdEntries_301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_forbiddenNatModules_302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natStructs_303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natTypeIdOf_304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNatStructId_305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_307_: u8 = 0;
    let mut v___x_309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_310_: u8 = 0;
    let mut v_v_311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringId_x3f_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intModuleInst_316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leInst_x3f_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltInst_x3f_318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lawfulOrderLTInst_x3f_319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isPreorderInst_x3f_320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_orderedAddInst_x3f_321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isLinearInst_x3f_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_noNatDivInst_x3f_323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ringInst_x3f_324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_x3f_325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_orderedRingInst_x3f_326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charInst_x3f_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ofNatZero_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_x3f_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leFn_x3f_332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltFn_x3f_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zsmulFn_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nsmulFn_336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zsmulFn_x3f_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nsmulFn_x3f_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_homomulFn_x3f_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subFn_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_negFn_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowers_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uppers_345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignment_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_conflict_x3f_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimStack_351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_occurs_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ignored_353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_356_: u8 = 0;
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_366_: u8 = 0;
    let mut v_isSharedCheck_367_: u8 = 0;
    let mut v_unused_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_375_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_298_ = lean_ctor_get(v_s_297_, 0);
                v_typeIdOf_299_ = lean_ctor_get(v_s_297_, 1);
                v_exprToStructId_300_ = lean_ctor_get(v_s_297_, 2);
                v_exprToStructIdEntries_301_ = lean_ctor_get(v_s_297_, 3);
                v_forbiddenNatModules_302_ = lean_ctor_get(v_s_297_, 4);
                v_natStructs_303_ = lean_ctor_get(v_s_297_, 5);
                v_natTypeIdOf_304_ = lean_ctor_get(v_s_297_, 6);
                v_exprToNatStructId_305_ = lean_ctor_get(v_s_297_, 7);
                v___x_306_ = lean_array_get_size(v_structs_298_);
                v___x_307_ = lean_nat_dec_lt(v_a_296_, v___x_306_);
                if v___x_307_ == 0 {
                    return v_s_297_;
                } else {
                    lean_inc_ref(v_exprToNatStructId_305_);
                    lean_inc_ref(v_natTypeIdOf_304_);
                    lean_inc_ref(v_natStructs_303_);
                    lean_inc_ref(v_forbiddenNatModules_302_);
                    lean_inc_ref(v_exprToStructIdEntries_301_);
                    lean_inc_ref(v_exprToStructId_300_);
                    lean_inc_ref(v_typeIdOf_299_);
                    lean_inc_ref(v_structs_298_);
                    v_isSharedCheck_367_ = (!lean_is_exclusive(v_s_297_)) as u8;
                    if v_isSharedCheck_367_ == 0 {
                        v_unused_368_ = lean_ctor_get(v_s_297_, 7);
                        lean_dec(v_unused_368_);
                        v_unused_369_ = lean_ctor_get(v_s_297_, 6);
                        lean_dec(v_unused_369_);
                        v_unused_370_ = lean_ctor_get(v_s_297_, 5);
                        lean_dec(v_unused_370_);
                        v_unused_371_ = lean_ctor_get(v_s_297_, 4);
                        lean_dec(v_unused_371_);
                        v_unused_372_ = lean_ctor_get(v_s_297_, 3);
                        lean_dec(v_unused_372_);
                        v_unused_373_ = lean_ctor_get(v_s_297_, 2);
                        lean_dec(v_unused_373_);
                        v_unused_374_ = lean_ctor_get(v_s_297_, 1);
                        lean_dec(v_unused_374_);
                        v_unused_375_ = lean_ctor_get(v_s_297_, 0);
                        lean_dec(v_unused_375_);
                        v___x_309_ = v_s_297_;
                        v_isShared_310_ = v_isSharedCheck_367_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_s_297_);
                        v___x_309_ = lean_box(0);
                        v_isShared_310_ = v_isSharedCheck_367_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_311_ = lean_array_fget(v_structs_298_, v_a_296_);
                v_id_312_ = lean_ctor_get(v_v_311_, 0);
                v_ringId_x3f_313_ = lean_ctor_get(v_v_311_, 1);
                v_type_314_ = lean_ctor_get(v_v_311_, 2);
                v_u_315_ = lean_ctor_get(v_v_311_, 3);
                v_intModuleInst_316_ = lean_ctor_get(v_v_311_, 4);
                v_leInst_x3f_317_ = lean_ctor_get(v_v_311_, 5);
                v_ltInst_x3f_318_ = lean_ctor_get(v_v_311_, 6);
                v_lawfulOrderLTInst_x3f_319_ = lean_ctor_get(v_v_311_, 7);
                v_isPreorderInst_x3f_320_ = lean_ctor_get(v_v_311_, 8);
                v_orderedAddInst_x3f_321_ = lean_ctor_get(v_v_311_, 9);
                v_isLinearInst_x3f_322_ = lean_ctor_get(v_v_311_, 10);
                v_noNatDivInst_x3f_323_ = lean_ctor_get(v_v_311_, 11);
                v_ringInst_x3f_324_ = lean_ctor_get(v_v_311_, 12);
                v_commRingInst_x3f_325_ = lean_ctor_get(v_v_311_, 13);
                v_orderedRingInst_x3f_326_ = lean_ctor_get(v_v_311_, 14);
                v_fieldInst_x3f_327_ = lean_ctor_get(v_v_311_, 15);
                v_charInst_x3f_328_ = lean_ctor_get(v_v_311_, 16);
                v_zero_329_ = lean_ctor_get(v_v_311_, 17);
                v_ofNatZero_330_ = lean_ctor_get(v_v_311_, 18);
                v_one_x3f_331_ = lean_ctor_get(v_v_311_, 19);
                v_leFn_x3f_332_ = lean_ctor_get(v_v_311_, 20);
                v_ltFn_x3f_333_ = lean_ctor_get(v_v_311_, 21);
                v_addFn_334_ = lean_ctor_get(v_v_311_, 22);
                v_zsmulFn_335_ = lean_ctor_get(v_v_311_, 23);
                v_nsmulFn_336_ = lean_ctor_get(v_v_311_, 24);
                v_zsmulFn_x3f_337_ = lean_ctor_get(v_v_311_, 25);
                v_nsmulFn_x3f_338_ = lean_ctor_get(v_v_311_, 26);
                v_homomulFn_x3f_339_ = lean_ctor_get(v_v_311_, 27);
                v_subFn_340_ = lean_ctor_get(v_v_311_, 28);
                v_negFn_341_ = lean_ctor_get(v_v_311_, 29);
                v_vars_342_ = lean_ctor_get(v_v_311_, 30);
                v_varMap_343_ = lean_ctor_get(v_v_311_, 31);
                v_lowers_344_ = lean_ctor_get(v_v_311_, 32);
                v_uppers_345_ = lean_ctor_get(v_v_311_, 33);
                v_diseqs_346_ = lean_ctor_get(v_v_311_, 34);
                v_assignment_347_ = lean_ctor_get(v_v_311_, 35);
                v_conflict_x3f_348_ = lean_ctor_get(v_v_311_, 36);
                v_diseqSplits_349_ = lean_ctor_get(v_v_311_, 37);
                v_elimEqs_350_ = lean_ctor_get(v_v_311_, 38);
                v_elimStack_351_ = lean_ctor_get(v_v_311_, 39);
                v_occurs_352_ = lean_ctor_get(v_v_311_, 40);
                v_ignored_353_ = lean_ctor_get(v_v_311_, 41);
                v_isSharedCheck_366_ = (!lean_is_exclusive(v_v_311_)) as u8;
                if v_isSharedCheck_366_ == 0 {
                    v___x_355_ = v_v_311_;
                    v_isShared_356_ = v_isSharedCheck_366_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_ignored_353_);
                    lean_inc(v_occurs_352_);
                    lean_inc(v_elimStack_351_);
                    lean_inc(v_elimEqs_350_);
                    lean_inc(v_diseqSplits_349_);
                    lean_inc(v_conflict_x3f_348_);
                    lean_inc(v_assignment_347_);
                    lean_inc(v_diseqs_346_);
                    lean_inc(v_uppers_345_);
                    lean_inc(v_lowers_344_);
                    lean_inc(v_varMap_343_);
                    lean_inc(v_vars_342_);
                    lean_inc(v_negFn_341_);
                    lean_inc(v_subFn_340_);
                    lean_inc(v_homomulFn_x3f_339_);
                    lean_inc(v_nsmulFn_x3f_338_);
                    lean_inc(v_zsmulFn_x3f_337_);
                    lean_inc(v_nsmulFn_336_);
                    lean_inc(v_zsmulFn_335_);
                    lean_inc(v_addFn_334_);
                    lean_inc(v_ltFn_x3f_333_);
                    lean_inc(v_leFn_x3f_332_);
                    lean_inc(v_one_x3f_331_);
                    lean_inc(v_ofNatZero_330_);
                    lean_inc(v_zero_329_);
                    lean_inc(v_charInst_x3f_328_);
                    lean_inc(v_fieldInst_x3f_327_);
                    lean_inc(v_orderedRingInst_x3f_326_);
                    lean_inc(v_commRingInst_x3f_325_);
                    lean_inc(v_ringInst_x3f_324_);
                    lean_inc(v_noNatDivInst_x3f_323_);
                    lean_inc(v_isLinearInst_x3f_322_);
                    lean_inc(v_orderedAddInst_x3f_321_);
                    lean_inc(v_isPreorderInst_x3f_320_);
                    lean_inc(v_lawfulOrderLTInst_x3f_319_);
                    lean_inc(v_ltInst_x3f_318_);
                    lean_inc(v_leInst_x3f_317_);
                    lean_inc(v_intModuleInst_316_);
                    lean_inc(v_u_315_);
                    lean_inc(v_type_314_);
                    lean_inc(v_ringId_x3f_313_);
                    lean_inc(v_id_312_);
                    lean_dec(v_v_311_);
                    v___x_355_ = lean_box(0);
                    v_isShared_356_ = v_isSharedCheck_366_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_357_ = lean_box(0);
                v_xs_x27_358_ = lean_array_fset(v_structs_298_, v_a_296_, v___x_357_);
                if v_isShared_356_ == 0 {
                    v___x_360_ = v___x_355_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 42, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_365_, 0, v_id_312_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 1, v_ringId_x3f_313_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 2, v_type_314_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 3, v_u_315_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 4, v_intModuleInst_316_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 5, v_leInst_x3f_317_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 6, v_ltInst_x3f_318_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 7, v_lawfulOrderLTInst_x3f_319_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 8, v_isPreorderInst_x3f_320_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 9, v_orderedAddInst_x3f_321_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 10, v_isLinearInst_x3f_322_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 11, v_noNatDivInst_x3f_323_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 12, v_ringInst_x3f_324_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 13, v_commRingInst_x3f_325_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 14, v_orderedRingInst_x3f_326_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 15, v_fieldInst_x3f_327_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 16, v_charInst_x3f_328_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 17, v_zero_329_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 18, v_ofNatZero_330_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 19, v_one_x3f_331_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 20, v_leFn_x3f_332_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 21, v_ltFn_x3f_333_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 22, v_addFn_334_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 23, v_zsmulFn_335_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 24, v_nsmulFn_336_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 25, v_zsmulFn_x3f_337_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 26, v_nsmulFn_x3f_338_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 27, v_homomulFn_x3f_339_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 28, v_subFn_340_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 29, v_negFn_341_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 30, v_vars_342_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 31, v_varMap_343_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 32, v_lowers_344_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 33, v_uppers_345_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 34, v_diseqs_346_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 35, v_assignment_347_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 36, v_conflict_x3f_348_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 37, v_diseqSplits_349_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 38, v_elimEqs_350_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 39, v_elimStack_351_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 40, v_occurs_352_);
                    lean_ctor_set(v_reuseFailAlloc_365_, 41, v_ignored_353_);
                    v___x_360_ = v_reuseFailAlloc_365_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v___x_360_,
                    (core::mem::size_of::<*mut LeanObject>() * 42) as u32,
                    v___x_307_,
                );
                v___x_361_ = lean_array_fset(v_xs_x27_358_, v_a_296_, v___x_360_);
                if v_isShared_310_ == 0 {
                    lean_ctor_set(v___x_309_, 0, v___x_361_);
                    v___x_363_ = v___x_309_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
                    lean_ctor_set(v_reuseFailAlloc_364_, 1, v_typeIdOf_299_);
                    lean_ctor_set(v_reuseFailAlloc_364_, 2, v_exprToStructId_300_);
                    lean_ctor_set(v_reuseFailAlloc_364_, 3, v_exprToStructIdEntries_301_);
                    lean_ctor_set(v_reuseFailAlloc_364_, 4, v_forbiddenNatModules_302_);
                    lean_ctor_set(v_reuseFailAlloc_364_, 5, v_natStructs_303_);
                    lean_ctor_set(v_reuseFailAlloc_364_, 6, v_natTypeIdOf_304_);
                    lean_ctor_set(v_reuseFailAlloc_364_, 7, v_exprToNatStructId_305_);
                    v___x_363_ = v_reuseFailAlloc_364_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_363_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_mkCase___lam__0___boxed(
    mut v_a_376_: *mut LeanObject,
    mut v_s_377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_378_: *mut LeanObject = core::ptr::null_mut();
    v_res_378_ = l_Lean_Meta_Grind_Arith_Linear_mkCase___lam__0(v_a_376_, v_s_377_);
    lean_dec(v_a_376_);
    return v_res_378_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___redArg(
    mut v___y_379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_387_: u8 = 0;
    let mut v___x_388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_399_: u8 = 0;
    let mut v_r_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_411_: u8 = 0;
    let mut v_unused_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_413_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_381_ = lean_st_ref_get(v___y_379_);
                v_ngen_382_ = lean_ctor_get(v___x_381_, 2);
                lean_inc_ref(v_ngen_382_);
                lean_dec(v___x_381_);
                v_namePrefix_383_ = lean_ctor_get(v_ngen_382_, 0);
                v_idx_384_ = lean_ctor_get(v_ngen_382_, 1);
                v_isSharedCheck_413_ = (!lean_is_exclusive(v_ngen_382_)) as u8;
                if v_isSharedCheck_413_ == 0 {
                    v___x_386_ = v_ngen_382_;
                    v_isShared_387_ = v_isSharedCheck_413_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_idx_384_);
                    lean_inc(v_namePrefix_383_);
                    lean_dec(v_ngen_382_);
                    v___x_386_ = lean_box(0);
                    v_isShared_387_ = v_isSharedCheck_413_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_388_ = lean_st_ref_take(v___y_379_);
                v_env_389_ = lean_ctor_get(v___x_388_, 0);
                v_nextMacroScope_390_ = lean_ctor_get(v___x_388_, 1);
                v_auxDeclNGen_391_ = lean_ctor_get(v___x_388_, 3);
                v_traceState_392_ = lean_ctor_get(v___x_388_, 4);
                v_cache_393_ = lean_ctor_get(v___x_388_, 5);
                v_messages_394_ = lean_ctor_get(v___x_388_, 6);
                v_infoState_395_ = lean_ctor_get(v___x_388_, 7);
                v_snapshotTasks_396_ = lean_ctor_get(v___x_388_, 8);
                v_isSharedCheck_411_ = (!lean_is_exclusive(v___x_388_)) as u8;
                if v_isSharedCheck_411_ == 0 {
                    v_unused_412_ = lean_ctor_get(v___x_388_, 2);
                    lean_dec(v_unused_412_);
                    v___x_398_ = v___x_388_;
                    v_isShared_399_ = v_isSharedCheck_411_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_396_);
                    lean_inc(v_infoState_395_);
                    lean_inc(v_messages_394_);
                    lean_inc(v_cache_393_);
                    lean_inc(v_traceState_392_);
                    lean_inc(v_auxDeclNGen_391_);
                    lean_inc(v_nextMacroScope_390_);
                    lean_inc(v_env_389_);
                    lean_dec(v___x_388_);
                    v___x_398_ = lean_box(0);
                    v_isShared_399_ = v_isSharedCheck_411_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_idx_384_);
                lean_inc(v_namePrefix_383_);
                v_r_400_ = l_Lean_Name_num___override(v_namePrefix_383_, v_idx_384_);
                v___x_401_ = lean_unsigned_to_nat(1);
                v___x_402_ = lean_nat_add(v_idx_384_, v___x_401_);
                lean_dec(v_idx_384_);
                if v_isShared_387_ == 0 {
                    lean_ctor_set(v___x_386_, 1, v___x_402_);
                    v___x_404_ = v___x_386_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_410_, 0, v_namePrefix_383_);
                    lean_ctor_set(v_reuseFailAlloc_410_, 1, v___x_402_);
                    v___x_404_ = v_reuseFailAlloc_410_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_399_ == 0 {
                    lean_ctor_set(v___x_398_, 2, v___x_404_);
                    v___x_406_ = v___x_398_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_409_, 0, v_env_389_);
                    lean_ctor_set(v_reuseFailAlloc_409_, 1, v_nextMacroScope_390_);
                    lean_ctor_set(v_reuseFailAlloc_409_, 2, v___x_404_);
                    lean_ctor_set(v_reuseFailAlloc_409_, 3, v_auxDeclNGen_391_);
                    lean_ctor_set(v_reuseFailAlloc_409_, 4, v_traceState_392_);
                    lean_ctor_set(v_reuseFailAlloc_409_, 5, v_cache_393_);
                    lean_ctor_set(v_reuseFailAlloc_409_, 6, v_messages_394_);
                    lean_ctor_set(v_reuseFailAlloc_409_, 7, v_infoState_395_);
                    lean_ctor_set(v_reuseFailAlloc_409_, 8, v_snapshotTasks_396_);
                    v___x_406_ = v_reuseFailAlloc_409_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_407_ = lean_st_ref_set(v___y_379_, v___x_406_);
                v___x_408_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_408_, 0, v_r_400_);
                return v___x_408_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___redArg___boxed(
    mut v___y_414_: *mut LeanObject,
    mut v___y_415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_416_: *mut LeanObject = core::ptr::null_mut();
    v_res_416_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___redArg(v___y_414_);
    lean_dec(v___y_414_);
    return v_res_416_;
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0(
    mut v___y_417_: *mut LeanObject,
    mut v___y_418_: *mut LeanObject,
    mut v___y_419_: *mut LeanObject,
    mut v___y_420_: *mut LeanObject,
    mut v___y_421_: *mut LeanObject,
    mut v___y_422_: *mut LeanObject,
    mut v___y_423_: *mut LeanObject,
    mut v___y_424_: *mut LeanObject,
    mut v___y_425_: *mut LeanObject,
    mut v___y_426_: *mut LeanObject,
    mut v___y_427_: *mut LeanObject,
    mut v___y_428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_434_: u8 = 0;
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_438_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_430_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___redArg(v___y_428_);
                v_a_431_ = lean_ctor_get(v___x_430_, 0);
                v_isSharedCheck_438_ = (!lean_is_exclusive(v___x_430_)) as u8;
                if v_isSharedCheck_438_ == 0 {
                    v___x_433_ = v___x_430_;
                    v_isShared_434_ = v_isSharedCheck_438_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_431_);
                    lean_dec(v___x_430_);
                    v___x_433_ = lean_box(0);
                    v_isShared_434_ = v_isSharedCheck_438_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_434_ == 0 {
                    v___x_436_ = v___x_433_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_437_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_437_, 0, v_a_431_);
                    v___x_436_ = v_reuseFailAlloc_437_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_436_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0___boxed(
    mut v___y_439_: *mut LeanObject,
    mut v___y_440_: *mut LeanObject,
    mut v___y_441_: *mut LeanObject,
    mut v___y_442_: *mut LeanObject,
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
    let mut v_res_452_: *mut LeanObject = core::ptr::null_mut();
    v_res_452_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0(
        v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_,
        v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_,
    );
    lean_dec(v___y_450_);
    lean_dec_ref(v___y_449_);
    lean_dec(v___y_448_);
    lean_dec_ref(v___y_447_);
    lean_dec(v___y_446_);
    lean_dec_ref(v___y_445_);
    lean_dec(v___y_444_);
    lean_dec_ref(v___y_443_);
    lean_dec(v___y_442_);
    lean_dec(v___y_441_);
    lean_dec(v___y_440_);
    lean_dec(v___y_439_);
    return v_res_452_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_mkCase(
    mut v_c_453_: *mut LeanObject,
    mut v_a_454_: *mut LeanObject,
    mut v_a_455_: *mut LeanObject,
    mut v_a_456_: *mut LeanObject,
    mut v_a_457_: *mut LeanObject,
    mut v_a_458_: *mut LeanObject,
    mut v_a_459_: *mut LeanObject,
    mut v_a_460_: *mut LeanObject,
    mut v_a_461_: *mut LeanObject,
    mut v_a_462_: *mut LeanObject,
    mut v_a_463_: *mut LeanObject,
    mut v_a_464_: *mut LeanObject,
    mut v_a_465_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cases_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decVars_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_476_: u8 = 0;
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_488_: u8 = 0;
    let mut v___x_490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_492_: u8 = 0;
    let mut v_unused_493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_497_: u8 = 0;
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_501_: u8 = 0;
    let mut v_reuseFailAlloc_502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_503_: u8 = 0;
    let mut v_a_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_507_: u8 = 0;
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_511_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_467_ =
                    l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0(
                        v_a_454_, v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_,
                        v_a_461_, v_a_462_, v_a_463_, v_a_464_, v_a_465_,
                    );
                if lean_obj_tag(v___x_467_) == 0 {
                    v_a_468_ = lean_ctor_get(v___x_467_, 0);
                    lean_inc(v_a_468_);
                    lean_dec_ref_known(v___x_467_, 1);
                    v___x_469_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                        v_a_455_, v_a_456_, v_a_457_, v_a_458_, v_a_459_, v_a_460_, v_a_461_,
                        v_a_462_, v_a_463_, v_a_464_, v_a_465_,
                    );
                    if lean_obj_tag(v___x_469_) == 0 {
                        v_a_470_ = lean_ctor_get(v___x_469_, 0);
                        lean_inc(v_a_470_);
                        lean_dec_ref_known(v___x_469_, 1);
                        v___x_471_ = lean_st_ref_take(v_a_454_);
                        v_cases_472_ = lean_ctor_get(v___x_471_, 0);
                        v_decVars_473_ = lean_ctor_get(v___x_471_, 1);
                        v_isSharedCheck_503_ = (!lean_is_exclusive(v___x_471_)) as u8;
                        if v_isSharedCheck_503_ == 0 {
                            v___x_475_ = v___x_471_;
                            v_isShared_476_ = v_isSharedCheck_503_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_decVars_473_);
                            lean_inc(v_cases_472_);
                            lean_dec(v___x_471_);
                            v___x_475_ = lean_box(0);
                            v_isShared_476_ = v_isSharedCheck_503_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_468_);
                        lean_dec_ref(v_c_453_);
                        v_a_504_ = lean_ctor_get(v___x_469_, 0);
                        v_isSharedCheck_511_ = (!lean_is_exclusive(v___x_469_)) as u8;
                        if v_isSharedCheck_511_ == 0 {
                            v___x_506_ = v___x_469_;
                            v_isShared_507_ = v_isSharedCheck_511_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_504_);
                            lean_dec(v___x_469_);
                            v___x_506_ = lean_box(0);
                            v_isShared_507_ = v_isSharedCheck_511_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_c_453_);
                    return v___x_467_;
                }
            }
            1 => {
                lean_inc_n(v_a_468_, 2);
                v___x_477_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_477_, 0, v_c_453_);
                lean_ctor_set(v___x_477_, 1, v_a_468_);
                lean_ctor_set(v___x_477_, 2, v_a_470_);
                v___x_478_ = l_Lean_PersistentArray_push___redArg(v_cases_472_, v___x_477_);
                v___x_479_ = l_Lean_FVarIdSet_insert(v_decVars_473_, v_a_468_);
                if v_isShared_476_ == 0 {
                    lean_ctor_set(v___x_475_, 1, v___x_479_);
                    lean_ctor_set(v___x_475_, 0, v___x_478_);
                    v___x_481_ = v___x_475_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_502_, 0, v___x_478_);
                    lean_ctor_set(v_reuseFailAlloc_502_, 1, v___x_479_);
                    v___x_481_ = v_reuseFailAlloc_502_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_482_ = lean_st_ref_set(v_a_454_, v___x_481_);
                lean_inc(v_a_455_);
                v___f_483_ = lean_alloc_closure(
                    l_Lean_Meta_Grind_Arith_Linear_mkCase___lam__0___boxed
                        as *mut core::ffi::c_void,
                    2,
                    1,
                );
                lean_closure_set(v___f_483_, 0, v_a_455_);
                v___x_484_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
                v___x_485_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_484_, v___f_483_, v_a_456_);
                if lean_obj_tag(v___x_485_) == 0 {
                    v_isSharedCheck_492_ = (!lean_is_exclusive(v___x_485_)) as u8;
                    if v_isSharedCheck_492_ == 0 {
                        v_unused_493_ = lean_ctor_get(v___x_485_, 0);
                        lean_dec(v_unused_493_);
                        v___x_487_ = v___x_485_;
                        v_isShared_488_ = v_isSharedCheck_492_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_485_);
                        v___x_487_ = lean_box(0);
                        v_isShared_488_ = v_isSharedCheck_492_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_468_);
                    v_a_494_ = lean_ctor_get(v___x_485_, 0);
                    v_isSharedCheck_501_ = (!lean_is_exclusive(v___x_485_)) as u8;
                    if v_isSharedCheck_501_ == 0 {
                        v___x_496_ = v___x_485_;
                        v_isShared_497_ = v_isSharedCheck_501_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_494_);
                        lean_dec(v___x_485_);
                        v___x_496_ = lean_box(0);
                        v_isShared_497_ = v_isSharedCheck_501_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_488_ == 0 {
                    lean_ctor_set(v___x_487_, 0, v_a_468_);
                    v___x_490_ = v___x_487_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_491_, 0, v_a_468_);
                    v___x_490_ = v_reuseFailAlloc_491_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_490_;
            }
            5 => {
                if v_isShared_497_ == 0 {
                    v___x_499_ = v___x_496_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_500_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_500_, 0, v_a_494_);
                    v___x_499_ = v_reuseFailAlloc_500_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_499_;
            }
            7 => {
                if v_isShared_507_ == 0 {
                    v___x_509_ = v___x_506_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_510_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_510_, 0, v_a_504_);
                    v___x_509_ = v_reuseFailAlloc_510_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_509_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_mkCase___boxed(
    mut v_c_512_: *mut LeanObject,
    mut v_a_513_: *mut LeanObject,
    mut v_a_514_: *mut LeanObject,
    mut v_a_515_: *mut LeanObject,
    mut v_a_516_: *mut LeanObject,
    mut v_a_517_: *mut LeanObject,
    mut v_a_518_: *mut LeanObject,
    mut v_a_519_: *mut LeanObject,
    mut v_a_520_: *mut LeanObject,
    mut v_a_521_: *mut LeanObject,
    mut v_a_522_: *mut LeanObject,
    mut v_a_523_: *mut LeanObject,
    mut v_a_524_: *mut LeanObject,
    mut v_a_525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_526_: *mut LeanObject = core::ptr::null_mut();
    v_res_526_ = l_Lean_Meta_Grind_Arith_Linear_mkCase(
        v_c_512_, v_a_513_, v_a_514_, v_a_515_, v_a_516_, v_a_517_, v_a_518_, v_a_519_, v_a_520_,
        v_a_521_, v_a_522_, v_a_523_, v_a_524_,
    );
    lean_dec(v_a_524_);
    lean_dec_ref(v_a_523_);
    lean_dec(v_a_522_);
    lean_dec_ref(v_a_521_);
    lean_dec(v_a_520_);
    lean_dec_ref(v_a_519_);
    lean_dec(v_a_518_);
    lean_dec_ref(v_a_517_);
    lean_dec(v_a_516_);
    lean_dec(v_a_515_);
    lean_dec(v_a_514_);
    lean_dec(v_a_513_);
    return v_res_526_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0(
    mut v___y_527_: *mut LeanObject,
    mut v___y_528_: *mut LeanObject,
    mut v___y_529_: *mut LeanObject,
    mut v___y_530_: *mut LeanObject,
    mut v___y_531_: *mut LeanObject,
    mut v___y_532_: *mut LeanObject,
    mut v___y_533_: *mut LeanObject,
    mut v___y_534_: *mut LeanObject,
    mut v___y_535_: *mut LeanObject,
    mut v___y_536_: *mut LeanObject,
    mut v___y_537_: *mut LeanObject,
    mut v___y_538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_540_: *mut LeanObject = core::ptr::null_mut();
    v___x_540_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___redArg(v___y_538_);
    return v___x_540_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0___boxed(
    mut v___y_541_: *mut LeanObject,
    mut v___y_542_: *mut LeanObject,
    mut v___y_543_: *mut LeanObject,
    mut v___y_544_: *mut LeanObject,
    mut v___y_545_: *mut LeanObject,
    mut v___y_546_: *mut LeanObject,
    mut v___y_547_: *mut LeanObject,
    mut v___y_548_: *mut LeanObject,
    mut v___y_549_: *mut LeanObject,
    mut v___y_550_: *mut LeanObject,
    mut v___y_551_: *mut LeanObject,
    mut v___y_552_: *mut LeanObject,
    mut v___y_553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_554_: *mut LeanObject = core::ptr::null_mut();
    v_res_554_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Linear_mkCase_spec__0_spec__0(v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
    lean_dec(v___y_552_);
    lean_dec_ref(v___y_551_);
    lean_dec(v___y_550_);
    lean_dec_ref(v___y_549_);
    lean_dec(v___y_548_);
    lean_dec_ref(v___y_547_);
    lean_dec(v___y_546_);
    lean_dec_ref(v___y_545_);
    lean_dec(v___y_544_);
    lean_dec(v___y_543_);
    lean_dec(v___y_542_);
    lean_dec(v___y_541_);
    return v_res_554_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default =
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase_default);
    l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase =
        _init_l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_Linear_instInhabitedCase);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_SearchM(builtin);
}

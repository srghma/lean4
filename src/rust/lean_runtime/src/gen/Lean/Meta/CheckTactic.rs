// Lean compiler output
// Module: Lean.Meta.CheckTactic
// Imports: Lean.Meta.Basic
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr4, l_Lean_replaceRef};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_const___override, l_Lean_Expr_sort___override, l_Lean_mkAppB, l_Lean_mkAppN,
    l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_Meta_isExprDefEq, l_Lean_Meta_mkFreshExprMVar,
    l_Lean_Meta_mkFreshLevelMVar, runtime_initialize_Lean_Meta_Basic,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [77, 101, 116, 97, 0],
    };
static mut l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [67, 104, 101, 99, 107, 84, 97, 99, 116, 105, 99, 0],
    };
static mut l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            67, 104, 101, 99, 107, 71, 111, 97, 108, 84, 121, 112, 101, 0,
        ],
    };
static mut l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3_value)
        as *mut LeanObject;
static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__0_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1_value)
                as *mut LeanObject,
            15449383196166861506 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_2: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2_value)
                as *mut LeanObject,
            13088578035309973495 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3_value)
                as *mut LeanObject,
            11417940687150260387 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [71, 111, 97, 108, 0],
    };
static mut l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2_value: LeanStringObject<23> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            10, 105, 115, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 111, 32, 109, 97,
            116, 99, 104, 32, 0,
        ],
    };
static mut l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_CheckTactic_mkCheckGoalType(
    mut v_val_272_: *mut LeanObject,
    mut v_type_273_: *mut LeanObject,
    mut v_a_274_: *mut LeanObject,
    mut v_a_275_: *mut LeanObject,
    mut v_a_276_: *mut LeanObject,
    mut v_a_277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_283_: u8 = 0;
    let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_292_: u8 = 0;
    let mut v_a_293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_296_: u8 = 0;
    let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_300_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_279_ = l_Lean_Meta_mkFreshLevelMVar(v_a_274_, v_a_275_, v_a_276_, v_a_277_);
                if lean_obj_tag(v___x_279_) == 0 {
                    v_a_280_ = lean_ctor_get(v___x_279_, 0);
                    v_isSharedCheck_292_ = (!lean_is_exclusive(v___x_279_)) as u8;
                    if v_isSharedCheck_292_ == 0 {
                        v___x_282_ = v___x_279_;
                        v_isShared_283_ = v_isSharedCheck_292_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_280_);
                        lean_dec(v___x_279_);
                        v___x_282_ = lean_box(0);
                        v_isShared_283_ = v_isSharedCheck_292_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_type_273_);
                    lean_dec_ref(v_val_272_);
                    v_a_293_ = lean_ctor_get(v___x_279_, 0);
                    v_isSharedCheck_300_ = (!lean_is_exclusive(v___x_279_)) as u8;
                    if v_isSharedCheck_300_ == 0 {
                        v___x_295_ = v___x_279_;
                        v_isShared_296_ = v_isSharedCheck_300_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_293_);
                        lean_dec(v___x_279_);
                        v___x_295_ = lean_box(0);
                        v_isShared_296_ = v_isSharedCheck_300_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_284_ = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4;
                v___x_285_ = lean_box(0);
                v___x_286_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_286_, 0, v_a_280_);
                lean_ctor_set(v___x_286_, 1, v___x_285_);
                v___x_287_ = l_Lean_mkConst(v___x_284_, v___x_286_);
                v___x_288_ = l_Lean_mkAppB(v___x_287_, v_type_273_, v_val_272_);
                if v_isShared_283_ == 0 {
                    lean_ctor_set(v___x_282_, 0, v___x_288_);
                    v___x_290_ = v___x_282_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_291_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_288_);
                    v___x_290_ = v_reuseFailAlloc_291_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_290_;
            }
            3 => {
                if v_isShared_296_ == 0 {
                    v___x_298_ = v___x_295_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_293_);
                    v___x_298_ = v_reuseFailAlloc_299_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_298_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_CheckTactic_mkCheckGoalType___boxed(
    mut v_val_301_: *mut LeanObject,
    mut v_type_302_: *mut LeanObject,
    mut v_a_303_: *mut LeanObject,
    mut v_a_304_: *mut LeanObject,
    mut v_a_305_: *mut LeanObject,
    mut v_a_306_: *mut LeanObject,
    mut v_a_307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_308_: *mut LeanObject = core::ptr::null_mut();
    v_res_308_ = l_Lean_Meta_CheckTactic_mkCheckGoalType(
        v_val_301_,
        v_type_302_,
        v_a_303_,
        v_a_304_,
        v_a_305_,
        v_a_306_,
    );
    lean_dec(v_a_306_);
    lean_dec_ref(v_a_305_);
    lean_dec(v_a_304_);
    lean_dec_ref(v_a_303_);
    return v_res_308_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1(
    mut v_msgData_309_: *mut LeanObject,
    mut v___y_310_: *mut LeanObject,
    mut v___y_311_: *mut LeanObject,
    mut v___y_312_: *mut LeanObject,
    mut v___y_313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    v___x_315_ = lean_st_ref_get(v___y_313_);
    v_env_316_ = lean_ctor_get(v___x_315_, 0);
    lean_inc_ref(v_env_316_);
    lean_dec(v___x_315_);
    v___x_317_ = lean_st_ref_get(v___y_311_);
    v_mctx_318_ = lean_ctor_get(v___x_317_, 0);
    lean_inc_ref(v_mctx_318_);
    lean_dec(v___x_317_);
    v_lctx_319_ = lean_ctor_get(v___y_310_, 2);
    v_options_320_ = lean_ctor_get(v___y_312_, 2);
    lean_inc_ref(v_options_320_);
    lean_inc_ref(v_lctx_319_);
    v___x_321_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_321_, 0, v_env_316_);
    lean_ctor_set(v___x_321_, 1, v_mctx_318_);
    lean_ctor_set(v___x_321_, 2, v_lctx_319_);
    lean_ctor_set(v___x_321_, 3, v_options_320_);
    v___x_322_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_322_, 0, v___x_321_);
    lean_ctor_set(v___x_322_, 1, v_msgData_309_);
    v___x_323_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_323_, 0, v___x_322_);
    return v___x_323_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_324_: *mut LeanObject,
    mut v___y_325_: *mut LeanObject,
    mut v___y_326_: *mut LeanObject,
    mut v___y_327_: *mut LeanObject,
    mut v___y_328_: *mut LeanObject,
    mut v___y_329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_330_: *mut LeanObject = core::ptr::null_mut();
    v_res_330_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1(v_msgData_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
    lean_dec(v___y_328_);
    lean_dec_ref(v___y_327_);
    lean_dec(v___y_326_);
    lean_dec_ref(v___y_325_);
    return v_res_330_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(
    mut v_msg_331_: *mut LeanObject,
    mut v___y_332_: *mut LeanObject,
    mut v___y_333_: *mut LeanObject,
    mut v___y_334_: *mut LeanObject,
    mut v___y_335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_342_: u8 = 0;
    let mut v___x_343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_347_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_337_ = lean_ctor_get(v___y_334_, 5);
                v___x_338_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1(v_msg_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
                v_a_339_ = lean_ctor_get(v___x_338_, 0);
                v_isSharedCheck_347_ = (!lean_is_exclusive(v___x_338_)) as u8;
                if v_isSharedCheck_347_ == 0 {
                    v___x_341_ = v___x_338_;
                    v_isShared_342_ = v_isSharedCheck_347_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_339_);
                    lean_dec(v___x_338_);
                    v___x_341_ = lean_box(0);
                    v_isShared_342_ = v_isSharedCheck_347_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_337_);
                v___x_343_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_343_, 0, v_ref_337_);
                lean_ctor_set(v___x_343_, 1, v_a_339_);
                if v_isShared_342_ == 0 {
                    lean_ctor_set_tag(v___x_341_, 1);
                    lean_ctor_set(v___x_341_, 0, v___x_343_);
                    v___x_345_ = v___x_341_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_346_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
                    v___x_345_ = v_reuseFailAlloc_346_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_345_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg___boxed(
    mut v_msg_348_: *mut LeanObject,
    mut v___y_349_: *mut LeanObject,
    mut v___y_350_: *mut LeanObject,
    mut v___y_351_: *mut LeanObject,
    mut v___y_352_: *mut LeanObject,
    mut v___y_353_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_354_: *mut LeanObject = core::ptr::null_mut();
    v_res_354_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(v_msg_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
    lean_dec(v___y_352_);
    lean_dec_ref(v___y_351_);
    lean_dec(v___y_350_);
    lean_dec_ref(v___y_349_);
    return v_res_354_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(
    mut v_ref_355_: *mut LeanObject,
    mut v_msg_356_: *mut LeanObject,
    mut v___y_357_: *mut LeanObject,
    mut v___y_358_: *mut LeanObject,
    mut v___y_359_: *mut LeanObject,
    mut v___y_360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_374_: u8 = 0;
    let mut v_cancelTk_x3f_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_376_: u8 = 0;
    let mut v_inheritedTraceOptions_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_362_ = lean_ctor_get(v___y_359_, 0);
    v_fileMap_363_ = lean_ctor_get(v___y_359_, 1);
    v_options_364_ = lean_ctor_get(v___y_359_, 2);
    v_currRecDepth_365_ = lean_ctor_get(v___y_359_, 3);
    v_maxRecDepth_366_ = lean_ctor_get(v___y_359_, 4);
    v_ref_367_ = lean_ctor_get(v___y_359_, 5);
    v_currNamespace_368_ = lean_ctor_get(v___y_359_, 6);
    v_openDecls_369_ = lean_ctor_get(v___y_359_, 7);
    v_initHeartbeats_370_ = lean_ctor_get(v___y_359_, 8);
    v_maxHeartbeats_371_ = lean_ctor_get(v___y_359_, 9);
    v_quotContext_372_ = lean_ctor_get(v___y_359_, 10);
    v_currMacroScope_373_ = lean_ctor_get(v___y_359_, 11);
    v_diag_374_ = lean_ctor_get_uint8(
        v___y_359_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_375_ = lean_ctor_get(v___y_359_, 12);
    v_suppressElabErrors_376_ = lean_ctor_get_uint8(
        v___y_359_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_377_ = lean_ctor_get(v___y_359_, 13);
    v_ref_378_ = l_Lean_replaceRef(v_ref_355_, v_ref_367_);
    lean_inc_ref(v_inheritedTraceOptions_377_);
    lean_inc(v_cancelTk_x3f_375_);
    lean_inc(v_currMacroScope_373_);
    lean_inc(v_quotContext_372_);
    lean_inc(v_maxHeartbeats_371_);
    lean_inc(v_initHeartbeats_370_);
    lean_inc(v_openDecls_369_);
    lean_inc(v_currNamespace_368_);
    lean_inc(v_maxRecDepth_366_);
    lean_inc(v_currRecDepth_365_);
    lean_inc_ref(v_options_364_);
    lean_inc_ref(v_fileMap_363_);
    lean_inc_ref(v_fileName_362_);
    v___x_379_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_379_, 0, v_fileName_362_);
    lean_ctor_set(v___x_379_, 1, v_fileMap_363_);
    lean_ctor_set(v___x_379_, 2, v_options_364_);
    lean_ctor_set(v___x_379_, 3, v_currRecDepth_365_);
    lean_ctor_set(v___x_379_, 4, v_maxRecDepth_366_);
    lean_ctor_set(v___x_379_, 5, v_ref_378_);
    lean_ctor_set(v___x_379_, 6, v_currNamespace_368_);
    lean_ctor_set(v___x_379_, 7, v_openDecls_369_);
    lean_ctor_set(v___x_379_, 8, v_initHeartbeats_370_);
    lean_ctor_set(v___x_379_, 9, v_maxHeartbeats_371_);
    lean_ctor_set(v___x_379_, 10, v_quotContext_372_);
    lean_ctor_set(v___x_379_, 11, v_currMacroScope_373_);
    lean_ctor_set(v___x_379_, 12, v_cancelTk_x3f_375_);
    lean_ctor_set(v___x_379_, 13, v_inheritedTraceOptions_377_);
    lean_ctor_set_uint8(
        v___x_379_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_374_,
    );
    lean_ctor_set_uint8(
        v___x_379_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_376_,
    );
    v___x_380_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(v_msg_356_, v___y_357_, v___y_358_, v___x_379_, v___y_360_);
    lean_dec_ref_known(v___x_379_, 14);
    return v___x_380_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg___boxed(
    mut v_ref_381_: *mut LeanObject,
    mut v_msg_382_: *mut LeanObject,
    mut v___y_383_: *mut LeanObject,
    mut v___y_384_: *mut LeanObject,
    mut v___y_385_: *mut LeanObject,
    mut v___y_386_: *mut LeanObject,
    mut v___y_387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_388_: *mut LeanObject = core::ptr::null_mut();
    v_res_388_ =
        l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(
            v_ref_381_, v_msg_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_,
        );
    lean_dec(v___y_386_);
    lean_dec_ref(v___y_385_);
    lean_dec(v___y_384_);
    lean_dec_ref(v___y_383_);
    lean_dec(v_ref_381_);
    return v_res_388_;
}
pub unsafe fn _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1() -> *mut LeanObject {
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
    v___x_390_ = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0;
    v___x_391_ = l_Lean_stringToMessageData(v___x_390_);
    return v___x_391_;
}
pub unsafe fn _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3() -> *mut LeanObject {
    let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut LeanObject = core::ptr::null_mut();
    v___x_393_ = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2;
    v___x_394_ = l_Lean_stringToMessageData(v___x_393_);
    return v___x_394_;
}
pub unsafe fn l_Lean_Meta_CheckTactic_matchCheckGoalType(
    mut v_stx_395_: *mut LeanObject,
    mut v_goalType_396_: *mut LeanObject,
    mut v_a_397_: *mut LeanObject,
    mut v_a_398_: *mut LeanObject,
    mut v_a_399_: *mut LeanObject,
    mut v_a_400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_406_: u8 = 0;
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_415_: u8 = 0;
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_433_: u8 = 0;
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_445_: u8 = 0;
    let mut v___x_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_449_: u8 = 0;
    let mut v_a_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_453_: u8 = 0;
    let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_457_: u8 = 0;
    let mut v_isSharedCheck_458_: u8 = 0;
    let mut v_a_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_462_: u8 = 0;
    let mut v___x_464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_466_: u8 = 0;
    let mut v_a_467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_470_: u8 = 0;
    let mut v___x_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_474_: u8 = 0;
    let mut v_a_475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_478_: u8 = 0;
    let mut v___x_480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_482_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_402_ = l_Lean_Meta_mkFreshLevelMVar(v_a_397_, v_a_398_, v_a_399_, v_a_400_);
                if lean_obj_tag(v___x_402_) == 0 {
                    v_a_403_ = lean_ctor_get(v___x_402_, 0);
                    lean_inc_n(v_a_403_, 2);
                    lean_dec_ref_known(v___x_402_, 1);
                    v___x_404_ = l_Lean_Expr_sort___override(v_a_403_);
                    v___x_405_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_405_, 0, v___x_404_);
                    v___x_406_ = 0;
                    v___x_407_ = lean_box(0);
                    v___x_408_ = l_Lean_Meta_mkFreshExprMVar(
                        v___x_405_, v___x_406_, v___x_407_, v_a_397_, v_a_398_, v_a_399_, v_a_400_,
                    );
                    if lean_obj_tag(v___x_408_) == 0 {
                        v_a_409_ = lean_ctor_get(v___x_408_, 0);
                        lean_inc_n(v_a_409_, 2);
                        lean_dec_ref_known(v___x_408_, 1);
                        v___x_410_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_410_, 0, v_a_409_);
                        v___x_411_ = l_Lean_Meta_mkFreshExprMVar(
                            v___x_410_, v___x_406_, v___x_407_, v_a_397_, v_a_398_, v_a_399_,
                            v_a_400_,
                        );
                        if lean_obj_tag(v___x_411_) == 0 {
                            v_a_412_ = lean_ctor_get(v___x_411_, 0);
                            v_isSharedCheck_458_ = (!lean_is_exclusive(v___x_411_)) as u8;
                            if v_isSharedCheck_458_ == 0 {
                                v___x_414_ = v___x_411_;
                                v_isShared_415_ = v_isSharedCheck_458_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_412_);
                                lean_dec(v___x_411_);
                                v___x_414_ = lean_box(0);
                                v_isShared_415_ = v_isSharedCheck_458_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_409_);
                            lean_dec(v_a_403_);
                            lean_dec_ref(v_goalType_396_);
                            v_a_459_ = lean_ctor_get(v___x_411_, 0);
                            v_isSharedCheck_466_ = (!lean_is_exclusive(v___x_411_)) as u8;
                            if v_isSharedCheck_466_ == 0 {
                                v___x_461_ = v___x_411_;
                                v_isShared_462_ = v_isSharedCheck_466_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_459_);
                                lean_dec(v___x_411_);
                                v___x_461_ = lean_box(0);
                                v_isShared_462_ = v_isSharedCheck_466_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_403_);
                        lean_dec_ref(v_goalType_396_);
                        v_a_467_ = lean_ctor_get(v___x_408_, 0);
                        v_isSharedCheck_474_ = (!lean_is_exclusive(v___x_408_)) as u8;
                        if v_isSharedCheck_474_ == 0 {
                            v___x_469_ = v___x_408_;
                            v_isShared_470_ = v_isSharedCheck_474_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_467_);
                            lean_dec(v___x_408_);
                            v___x_469_ = lean_box(0);
                            v_isShared_470_ = v_isSharedCheck_474_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_goalType_396_);
                    v_a_475_ = lean_ctor_get(v___x_402_, 0);
                    v_isSharedCheck_482_ = (!lean_is_exclusive(v___x_402_)) as u8;
                    if v_isSharedCheck_482_ == 0 {
                        v___x_477_ = v___x_402_;
                        v_isShared_478_ = v_isSharedCheck_482_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_475_);
                        lean_dec(v___x_402_);
                        v___x_477_ = lean_box(0);
                        v_isShared_478_ = v_isSharedCheck_482_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v___x_422_ = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4;
                v___x_423_ = lean_box(0);
                lean_inc(v_a_403_);
                v___x_424_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_424_, 0, v_a_403_);
                lean_ctor_set(v___x_424_, 1, v___x_423_);
                v___x_425_ = l_Lean_Expr_const___override(v___x_422_, v___x_424_);
                v___x_426_ = lean_unsigned_to_nat(2);
                v___x_427_ = lean_mk_empty_array_with_capacity(v___x_426_);
                lean_inc(v_a_409_);
                v___x_428_ = lean_array_push(v___x_427_, v_a_409_);
                lean_inc(v_a_412_);
                v___x_429_ = lean_array_push(v___x_428_, v_a_412_);
                v___x_430_ = l_Lean_mkAppN(v___x_425_, v___x_429_);
                lean_dec_ref(v___x_429_);
                lean_inc_ref(v___x_430_);
                lean_inc_ref(v_goalType_396_);
                v___x_431_ = l_Lean_Meta_isExprDefEq(
                    v_goalType_396_,
                    v___x_430_,
                    v_a_397_,
                    v_a_398_,
                    v_a_399_,
                    v_a_400_,
                );
                if lean_obj_tag(v___x_431_) == 0 {
                    v_a_432_ = lean_ctor_get(v___x_431_, 0);
                    lean_inc(v_a_432_);
                    lean_dec_ref_known(v___x_431_, 1);
                    v___x_433_ = (lean_unbox(v_a_432_) as u8);
                    lean_dec(v_a_432_);
                    if v___x_433_ == 0 {
                        lean_del_object(v___x_414_);
                        lean_dec(v_a_412_);
                        lean_dec(v_a_409_);
                        lean_dec(v_a_403_);
                        v___x_434_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1_once
                            ),
                            _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1,
                        );
                        v___x_435_ = l_Lean_indentExpr(v_goalType_396_);
                        v___x_436_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_436_, 0, v___x_434_);
                        lean_ctor_set(v___x_436_, 1, v___x_435_);
                        v___x_437_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3_once
                            ),
                            _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3,
                        );
                        v___x_438_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_438_, 0, v___x_436_);
                        lean_ctor_set(v___x_438_, 1, v___x_437_);
                        v___x_439_ = l_Lean_indentExpr(v___x_430_);
                        v___x_440_ = lean_alloc_ctor(7, 2, (0) as u32);
                        lean_ctor_set(v___x_440_, 0, v___x_438_);
                        lean_ctor_set(v___x_440_, 1, v___x_439_);
                        v___x_441_ = l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(v_stx_395_, v___x_440_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
                        v_a_442_ = lean_ctor_get(v___x_441_, 0);
                        v_isSharedCheck_449_ = (!lean_is_exclusive(v___x_441_)) as u8;
                        if v_isSharedCheck_449_ == 0 {
                            v___x_444_ = v___x_441_;
                            v_isShared_445_ = v_isSharedCheck_449_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_442_);
                            lean_dec(v___x_441_);
                            v___x_444_ = lean_box(0);
                            v_isShared_445_ = v_isSharedCheck_449_;
                            state = 4;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_430_);
                        lean_dec_ref(v_goalType_396_);
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_430_);
                    lean_del_object(v___x_414_);
                    lean_dec(v_a_412_);
                    lean_dec(v_a_409_);
                    lean_dec(v_a_403_);
                    lean_dec_ref(v_goalType_396_);
                    v_a_450_ = lean_ctor_get(v___x_431_, 0);
                    v_isSharedCheck_457_ = (!lean_is_exclusive(v___x_431_)) as u8;
                    if v_isSharedCheck_457_ == 0 {
                        v___x_452_ = v___x_431_;
                        v_isShared_453_ = v_isSharedCheck_457_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_450_);
                        lean_dec(v___x_431_);
                        v___x_452_ = lean_box(0);
                        v_isShared_453_ = v_isSharedCheck_457_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_417_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_417_, 0, v_a_409_);
                lean_ctor_set(v___x_417_, 1, v_a_403_);
                v___x_418_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_418_, 0, v_a_412_);
                lean_ctor_set(v___x_418_, 1, v___x_417_);
                if v_isShared_415_ == 0 {
                    lean_ctor_set(v___x_414_, 0, v___x_418_);
                    v___x_420_ = v___x_414_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_421_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
                    v___x_420_ = v_reuseFailAlloc_421_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_420_;
            }
            4 => {
                if v_isShared_445_ == 0 {
                    v___x_447_ = v___x_444_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_448_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
                    v___x_447_ = v_reuseFailAlloc_448_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_447_;
            }
            6 => {
                if v_isShared_453_ == 0 {
                    v___x_455_ = v___x_452_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_456_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
                    v___x_455_ = v_reuseFailAlloc_456_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_455_;
            }
            8 => {
                if v_isShared_462_ == 0 {
                    v___x_464_ = v___x_461_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_465_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
                    v___x_464_ = v_reuseFailAlloc_465_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_464_;
            }
            10 => {
                if v_isShared_470_ == 0 {
                    v___x_472_ = v___x_469_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
                    v___x_472_ = v_reuseFailAlloc_473_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_472_;
            }
            12 => {
                if v_isShared_478_ == 0 {
                    v___x_480_ = v___x_477_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
                    v___x_480_ = v_reuseFailAlloc_481_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_480_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_CheckTactic_matchCheckGoalType___boxed(
    mut v_stx_483_: *mut LeanObject,
    mut v_goalType_484_: *mut LeanObject,
    mut v_a_485_: *mut LeanObject,
    mut v_a_486_: *mut LeanObject,
    mut v_a_487_: *mut LeanObject,
    mut v_a_488_: *mut LeanObject,
    mut v_a_489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_490_: *mut LeanObject = core::ptr::null_mut();
    v_res_490_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(
        v_stx_483_,
        v_goalType_484_,
        v_a_485_,
        v_a_486_,
        v_a_487_,
        v_a_488_,
    );
    lean_dec(v_a_488_);
    lean_dec_ref(v_a_487_);
    lean_dec(v_a_486_);
    lean_dec_ref(v_a_485_);
    lean_dec(v_stx_483_);
    return v_res_490_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0(
    mut v_00_u03b1_491_: *mut LeanObject,
    mut v_ref_492_: *mut LeanObject,
    mut v_msg_493_: *mut LeanObject,
    mut v___y_494_: *mut LeanObject,
    mut v___y_495_: *mut LeanObject,
    mut v___y_496_: *mut LeanObject,
    mut v___y_497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    v___x_499_ =
        l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(
            v_ref_492_, v_msg_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_,
        );
    return v___x_499_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___boxed(
    mut v_00_u03b1_500_: *mut LeanObject,
    mut v_ref_501_: *mut LeanObject,
    mut v_msg_502_: *mut LeanObject,
    mut v___y_503_: *mut LeanObject,
    mut v___y_504_: *mut LeanObject,
    mut v___y_505_: *mut LeanObject,
    mut v___y_506_: *mut LeanObject,
    mut v___y_507_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_508_: *mut LeanObject = core::ptr::null_mut();
    v_res_508_ = l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0(
        v_00_u03b1_500_,
        v_ref_501_,
        v_msg_502_,
        v___y_503_,
        v___y_504_,
        v___y_505_,
        v___y_506_,
    );
    lean_dec(v___y_506_);
    lean_dec_ref(v___y_505_);
    lean_dec(v___y_504_);
    lean_dec_ref(v___y_503_);
    lean_dec(v_ref_501_);
    return v_res_508_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0(
    mut v_00_u03b1_509_: *mut LeanObject,
    mut v_msg_510_: *mut LeanObject,
    mut v___y_511_: *mut LeanObject,
    mut v___y_512_: *mut LeanObject,
    mut v___y_513_: *mut LeanObject,
    mut v___y_514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    v___x_516_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(v_msg_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
    return v___x_516_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___boxed(
    mut v_00_u03b1_517_: *mut LeanObject,
    mut v_msg_518_: *mut LeanObject,
    mut v___y_519_: *mut LeanObject,
    mut v___y_520_: *mut LeanObject,
    mut v___y_521_: *mut LeanObject,
    mut v___y_522_: *mut LeanObject,
    mut v___y_523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_524_: *mut LeanObject = core::ptr::null_mut();
    v_res_524_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0(v_00_u03b1_517_, v_msg_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
    lean_dec(v___y_522_);
    lean_dec_ref(v___y_521_);
    lean_dec(v___y_520_);
    lean_dec_ref(v___y_519_);
    return v_res_524_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_CheckTactic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_CheckTactic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_CheckTactic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CheckTactic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_CheckTactic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_CheckTactic(builtin);
}

// Lean compiler output
// Module: Lean.Meta.CheckTactic
// Imports: Lean.Meta.Basic
use crate::ffi::{lean_array_push, lean_mk_empty_array_with_capacity, lean_st_ref_get};
use crate::r#gen::Init::Prelude::l_Lean_replaceRef;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_const___override, l_Lean_Expr_sort___override, l_Lean_mkAppB, l_Lean_mkAppN,
    l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_Meta_isExprDefEq, l_Lean_Meta_mkFreshExprMVar,
    l_Lean_Meta_mkFreshLevelMVar, runtime_initialize_Lean_Meta_Basic,
};
pub static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1_value)
            as *mut leanh::LeanObject,
        15449383196166861506 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_2:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2_value)
            as *mut leanh::LeanObject,
        13088578035309973495 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value: leanh::LeanCtorObject<
    3,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3_value)
            as *mut leanh::LeanObject,
        11417940687150260387 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2_value:
    leanh::LeanStringObject<23> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        10, 105, 115, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 111, 32, 109, 97, 116,
        99, 104, 32, 0,
    ],
};
static mut l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_CheckTactic_mkCheckGoalType(
    mut v_val_272_: *mut leanh::LeanObject,
    mut v_type_273_: *mut leanh::LeanObject,
    mut v_a_274_: *mut leanh::LeanObject,
    mut v_a_275_: *mut leanh::LeanObject,
    mut v_a_276_: *mut leanh::LeanObject,
    mut v_a_277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_283_: u8 = 0;
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_292_: u8 = 0;
    let mut v_a_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_296_: u8 = 0;
    let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_300_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_279_ = l_Lean_Meta_mkFreshLevelMVar(v_a_274_, v_a_275_, v_a_276_, v_a_277_);
                if leanh::lean_obj_tag(v___x_279_) == 0 {
                    v_a_280_ = leanh::lean_ctor_get(v___x_279_, 0);
                    v_isSharedCheck_292_ = (!leanh::lean_is_exclusive(v___x_279_)) as u8;
                    if v_isSharedCheck_292_ == 0 {
                        v___x_282_ = v___x_279_;
                        v_isShared_283_ = v_isSharedCheck_292_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_280_);
                        leanh::lean_dec(v___x_279_);
                        v___x_282_ = leanh::lean_box(0);
                        v_isShared_283_ = v_isSharedCheck_292_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_type_273_);
                    leanh::lean_dec_ref(v_val_272_);
                    v_a_293_ = leanh::lean_ctor_get(v___x_279_, 0);
                    v_isSharedCheck_300_ = (!leanh::lean_is_exclusive(v___x_279_)) as u8;
                    if v_isSharedCheck_300_ == 0 {
                        v___x_295_ = v___x_279_;
                        v_isShared_296_ = v_isSharedCheck_300_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_293_);
                        leanh::lean_dec(v___x_279_);
                        v___x_295_ = leanh::lean_box(0);
                        v_isShared_296_ = v_isSharedCheck_300_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_284_ = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4;
                v___x_285_ = leanh::lean_box(0);
                v___x_286_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_286_, 0, v_a_280_);
                leanh::lean_ctor_set(v___x_286_, 1, v___x_285_);
                v___x_287_ = l_Lean_mkConst(v___x_284_, v___x_286_);
                v___x_288_ = l_Lean_mkAppB(v___x_287_, v_type_273_, v_val_272_);
                if v_isShared_283_ == 0 {
                    leanh::lean_ctor_set(v___x_282_, 0, v___x_288_);
                    v___x_290_ = v___x_282_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_291_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_288_);
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
                    v_reuseFailAlloc_299_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_293_);
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
    mut v_val_301_: *mut leanh::LeanObject,
    mut v_type_302_: *mut leanh::LeanObject,
    mut v_a_303_: *mut leanh::LeanObject,
    mut v_a_304_: *mut leanh::LeanObject,
    mut v_a_305_: *mut leanh::LeanObject,
    mut v_a_306_: *mut leanh::LeanObject,
    mut v_a_307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_308_ = l_Lean_Meta_CheckTactic_mkCheckGoalType(
        v_val_301_,
        v_type_302_,
        v_a_303_,
        v_a_304_,
        v_a_305_,
        v_a_306_,
    );
    leanh::lean_dec(v_a_306_);
    leanh::lean_dec_ref(v_a_305_);
    leanh::lean_dec(v_a_304_);
    leanh::lean_dec_ref(v_a_303_);
    return v_res_308_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1(
    mut v_msgData_309_: *mut leanh::LeanObject,
    mut v___y_310_: *mut leanh::LeanObject,
    mut v___y_311_: *mut leanh::LeanObject,
    mut v___y_312_: *mut leanh::LeanObject,
    mut v___y_313_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_315_ = lean_st_ref_get(v___y_313_);
    v_env_316_ = leanh::lean_ctor_get(v___x_315_, 0);
    leanh::lean_inc_ref(v_env_316_);
    leanh::lean_dec(v___x_315_);
    v___x_317_ = lean_st_ref_get(v___y_311_);
    v_mctx_318_ = leanh::lean_ctor_get(v___x_317_, 0);
    leanh::lean_inc_ref(v_mctx_318_);
    leanh::lean_dec(v___x_317_);
    v_lctx_319_ = leanh::lean_ctor_get(v___y_310_, 2);
    v_options_320_ = leanh::lean_ctor_get(v___y_312_, 2);
    leanh::lean_inc_ref(v_options_320_);
    leanh::lean_inc_ref(v_lctx_319_);
    v___x_321_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_321_, 0, v_env_316_);
    leanh::lean_ctor_set(v___x_321_, 1, v_mctx_318_);
    leanh::lean_ctor_set(v___x_321_, 2, v_lctx_319_);
    leanh::lean_ctor_set(v___x_321_, 3, v_options_320_);
    v___x_322_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_322_, 0, v___x_321_);
    leanh::lean_ctor_set(v___x_322_, 1, v_msgData_309_);
    v___x_323_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_323_, 0, v___x_322_);
    return v___x_323_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_324_: *mut leanh::LeanObject,
    mut v___y_325_: *mut leanh::LeanObject,
    mut v___y_326_: *mut leanh::LeanObject,
    mut v___y_327_: *mut leanh::LeanObject,
    mut v___y_328_: *mut leanh::LeanObject,
    mut v___y_329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_330_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1(v_msgData_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
    leanh::lean_dec(v___y_328_);
    leanh::lean_dec_ref(v___y_327_);
    leanh::lean_dec(v___y_326_);
    leanh::lean_dec_ref(v___y_325_);
    return v_res_330_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(
    mut v_msg_331_: *mut leanh::LeanObject,
    mut v___y_332_: *mut leanh::LeanObject,
    mut v___y_333_: *mut leanh::LeanObject,
    mut v___y_334_: *mut leanh::LeanObject,
    mut v___y_335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_342_: u8 = 0;
    let mut v___x_343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_347_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_337_ = leanh::lean_ctor_get(v___y_334_, 5);
                v___x_338_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1(v_msg_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
                v_a_339_ = leanh::lean_ctor_get(v___x_338_, 0);
                v_isSharedCheck_347_ = (!leanh::lean_is_exclusive(v___x_338_)) as u8;
                if v_isSharedCheck_347_ == 0 {
                    v___x_341_ = v___x_338_;
                    v_isShared_342_ = v_isSharedCheck_347_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_339_);
                    leanh::lean_dec(v___x_338_);
                    v___x_341_ = leanh::lean_box(0);
                    v_isShared_342_ = v_isSharedCheck_347_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_337_);
                v___x_343_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_343_, 0, v_ref_337_);
                leanh::lean_ctor_set(v___x_343_, 1, v_a_339_);
                if v_isShared_342_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_341_, 1);
                    leanh::lean_ctor_set(v___x_341_, 0, v___x_343_);
                    v___x_345_ = v___x_341_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_346_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
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
    mut v_msg_348_: *mut leanh::LeanObject,
    mut v___y_349_: *mut leanh::LeanObject,
    mut v___y_350_: *mut leanh::LeanObject,
    mut v___y_351_: *mut leanh::LeanObject,
    mut v___y_352_: *mut leanh::LeanObject,
    mut v___y_353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_354_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(v_msg_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
    leanh::lean_dec(v___y_352_);
    leanh::lean_dec_ref(v___y_351_);
    leanh::lean_dec(v___y_350_);
    leanh::lean_dec_ref(v___y_349_);
    return v_res_354_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(
    mut v_ref_355_: *mut leanh::LeanObject,
    mut v_msg_356_: *mut leanh::LeanObject,
    mut v___y_357_: *mut leanh::LeanObject,
    mut v___y_358_: *mut leanh::LeanObject,
    mut v___y_359_: *mut leanh::LeanObject,
    mut v___y_360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_374_: u8 = 0;
    let mut v_cancelTk_x3f_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_376_: u8 = 0;
    let mut v_inheritedTraceOptions_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_362_ = leanh::lean_ctor_get(v___y_359_, 0);
    v_fileMap_363_ = leanh::lean_ctor_get(v___y_359_, 1);
    v_options_364_ = leanh::lean_ctor_get(v___y_359_, 2);
    v_currRecDepth_365_ = leanh::lean_ctor_get(v___y_359_, 3);
    v_maxRecDepth_366_ = leanh::lean_ctor_get(v___y_359_, 4);
    v_ref_367_ = leanh::lean_ctor_get(v___y_359_, 5);
    v_currNamespace_368_ = leanh::lean_ctor_get(v___y_359_, 6);
    v_openDecls_369_ = leanh::lean_ctor_get(v___y_359_, 7);
    v_initHeartbeats_370_ = leanh::lean_ctor_get(v___y_359_, 8);
    v_maxHeartbeats_371_ = leanh::lean_ctor_get(v___y_359_, 9);
    v_quotContext_372_ = leanh::lean_ctor_get(v___y_359_, 10);
    v_currMacroScope_373_ = leanh::lean_ctor_get(v___y_359_, 11);
    v_diag_374_ = leanh::lean_ctor_get_uint8(
        v___y_359_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_375_ = leanh::lean_ctor_get(v___y_359_, 12);
    v_suppressElabErrors_376_ = leanh::lean_ctor_get_uint8(
        v___y_359_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_377_ = leanh::lean_ctor_get(v___y_359_, 13);
    v_ref_378_ = l_Lean_replaceRef(v_ref_355_, v_ref_367_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_377_);
    leanh::lean_inc(v_cancelTk_x3f_375_);
    leanh::lean_inc(v_currMacroScope_373_);
    leanh::lean_inc(v_quotContext_372_);
    leanh::lean_inc(v_maxHeartbeats_371_);
    leanh::lean_inc(v_initHeartbeats_370_);
    leanh::lean_inc(v_openDecls_369_);
    leanh::lean_inc(v_currNamespace_368_);
    leanh::lean_inc(v_maxRecDepth_366_);
    leanh::lean_inc(v_currRecDepth_365_);
    leanh::lean_inc_ref(v_options_364_);
    leanh::lean_inc_ref(v_fileMap_363_);
    leanh::lean_inc_ref(v_fileName_362_);
    v___x_379_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_379_, 0, v_fileName_362_);
    leanh::lean_ctor_set(v___x_379_, 1, v_fileMap_363_);
    leanh::lean_ctor_set(v___x_379_, 2, v_options_364_);
    leanh::lean_ctor_set(v___x_379_, 3, v_currRecDepth_365_);
    leanh::lean_ctor_set(v___x_379_, 4, v_maxRecDepth_366_);
    leanh::lean_ctor_set(v___x_379_, 5, v_ref_378_);
    leanh::lean_ctor_set(v___x_379_, 6, v_currNamespace_368_);
    leanh::lean_ctor_set(v___x_379_, 7, v_openDecls_369_);
    leanh::lean_ctor_set(v___x_379_, 8, v_initHeartbeats_370_);
    leanh::lean_ctor_set(v___x_379_, 9, v_maxHeartbeats_371_);
    leanh::lean_ctor_set(v___x_379_, 10, v_quotContext_372_);
    leanh::lean_ctor_set(v___x_379_, 11, v_currMacroScope_373_);
    leanh::lean_ctor_set(v___x_379_, 12, v_cancelTk_x3f_375_);
    leanh::lean_ctor_set(v___x_379_, 13, v_inheritedTraceOptions_377_);
    leanh::lean_ctor_set_uint8(
        v___x_379_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_374_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_379_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_376_,
    );
    v___x_380_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(v_msg_356_, v___y_357_, v___y_358_, v___x_379_, v___y_360_);
    leanh::lean_dec_ref_known(v___x_379_, 14);
    return v___x_380_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg___boxed(
    mut v_ref_381_: *mut leanh::LeanObject,
    mut v_msg_382_: *mut leanh::LeanObject,
    mut v___y_383_: *mut leanh::LeanObject,
    mut v___y_384_: *mut leanh::LeanObject,
    mut v___y_385_: *mut leanh::LeanObject,
    mut v___y_386_: *mut leanh::LeanObject,
    mut v___y_387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_388_ =
        l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(
            v_ref_381_, v_msg_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_,
        );
    leanh::lean_dec(v___y_386_);
    leanh::lean_dec_ref(v___y_385_);
    leanh::lean_dec(v___y_384_);
    leanh::lean_dec_ref(v___y_383_);
    leanh::lean_dec(v_ref_381_);
    return v_res_388_;
}
pub unsafe fn _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_390_ = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0;
    v___x_391_ = l_Lean_stringToMessageData(v___x_390_);
    return v___x_391_;
}
pub unsafe fn _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_393_ = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2;
    v___x_394_ = l_Lean_stringToMessageData(v___x_393_);
    return v___x_394_;
}
pub unsafe fn l_Lean_Meta_CheckTactic_matchCheckGoalType(
    mut v_stx_395_: *mut leanh::LeanObject,
    mut v_goalType_396_: *mut leanh::LeanObject,
    mut v_a_397_: *mut leanh::LeanObject,
    mut v_a_398_: *mut leanh::LeanObject,
    mut v_a_399_: *mut leanh::LeanObject,
    mut v_a_400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: u8 = 0;
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_415_: u8 = 0;
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: u8 = 0;
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_445_: u8 = 0;
    let mut v___x_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_449_: u8 = 0;
    let mut v_a_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_453_: u8 = 0;
    let mut v___x_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_457_: u8 = 0;
    let mut v_isSharedCheck_458_: u8 = 0;
    let mut v_a_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_462_: u8 = 0;
    let mut v___x_464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_466_: u8 = 0;
    let mut v_a_467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_470_: u8 = 0;
    let mut v___x_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_474_: u8 = 0;
    let mut v_a_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_478_: u8 = 0;
    let mut v___x_480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_482_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_402_ = l_Lean_Meta_mkFreshLevelMVar(v_a_397_, v_a_398_, v_a_399_, v_a_400_);
                if leanh::lean_obj_tag(v___x_402_) == 0 {
                    v_a_403_ = leanh::lean_ctor_get(v___x_402_, 0);
                    leanh::lean_inc_n(v_a_403_, 2);
                    leanh::lean_dec_ref_known(v___x_402_, 1);
                    v___x_404_ = l_Lean_Expr_sort___override(v_a_403_);
                    v___x_405_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_405_, 0, v___x_404_);
                    v___x_406_ = 0;
                    v___x_407_ = leanh::lean_box(0);
                    v___x_408_ = l_Lean_Meta_mkFreshExprMVar(
                        v___x_405_, v___x_406_, v___x_407_, v_a_397_, v_a_398_, v_a_399_, v_a_400_,
                    );
                    if leanh::lean_obj_tag(v___x_408_) == 0 {
                        v_a_409_ = leanh::lean_ctor_get(v___x_408_, 0);
                        leanh::lean_inc_n(v_a_409_, 2);
                        leanh::lean_dec_ref_known(v___x_408_, 1);
                        v___x_410_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_410_, 0, v_a_409_);
                        v___x_411_ = l_Lean_Meta_mkFreshExprMVar(
                            v___x_410_, v___x_406_, v___x_407_, v_a_397_, v_a_398_, v_a_399_,
                            v_a_400_,
                        );
                        if leanh::lean_obj_tag(v___x_411_) == 0 {
                            v_a_412_ = leanh::lean_ctor_get(v___x_411_, 0);
                            v_isSharedCheck_458_ =
                                (!leanh::lean_is_exclusive(v___x_411_)) as u8;
                            if v_isSharedCheck_458_ == 0 {
                                v___x_414_ = v___x_411_;
                                v_isShared_415_ = v_isSharedCheck_458_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_412_);
                                leanh::lean_dec(v___x_411_);
                                v___x_414_ = leanh::lean_box(0);
                                v_isShared_415_ = v_isSharedCheck_458_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_409_);
                            leanh::lean_dec(v_a_403_);
                            leanh::lean_dec_ref(v_goalType_396_);
                            v_a_459_ = leanh::lean_ctor_get(v___x_411_, 0);
                            v_isSharedCheck_466_ =
                                (!leanh::lean_is_exclusive(v___x_411_)) as u8;
                            if v_isSharedCheck_466_ == 0 {
                                v___x_461_ = v___x_411_;
                                v_isShared_462_ = v_isSharedCheck_466_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_459_);
                                leanh::lean_dec(v___x_411_);
                                v___x_461_ = leanh::lean_box(0);
                                v_isShared_462_ = v_isSharedCheck_466_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_403_);
                        leanh::lean_dec_ref(v_goalType_396_);
                        v_a_467_ = leanh::lean_ctor_get(v___x_408_, 0);
                        v_isSharedCheck_474_ = (!leanh::lean_is_exclusive(v___x_408_)) as u8;
                        if v_isSharedCheck_474_ == 0 {
                            v___x_469_ = v___x_408_;
                            v_isShared_470_ = v_isSharedCheck_474_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_467_);
                            leanh::lean_dec(v___x_408_);
                            v___x_469_ = leanh::lean_box(0);
                            v_isShared_470_ = v_isSharedCheck_474_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_goalType_396_);
                    v_a_475_ = leanh::lean_ctor_get(v___x_402_, 0);
                    v_isSharedCheck_482_ = (!leanh::lean_is_exclusive(v___x_402_)) as u8;
                    if v_isSharedCheck_482_ == 0 {
                        v___x_477_ = v___x_402_;
                        v_isShared_478_ = v_isSharedCheck_482_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_475_);
                        leanh::lean_dec(v___x_402_);
                        v___x_477_ = leanh::lean_box(0);
                        v_isShared_478_ = v_isSharedCheck_482_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v___x_422_ = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4;
                v___x_423_ = leanh::lean_box(0);
                leanh::lean_inc(v_a_403_);
                v___x_424_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_424_, 0, v_a_403_);
                leanh::lean_ctor_set(v___x_424_, 1, v___x_423_);
                v___x_425_ = l_Lean_Expr_const___override(v___x_422_, v___x_424_);
                v___x_426_ = leanh::lean_unsigned_to_nat(2);
                v___x_427_ = lean_mk_empty_array_with_capacity(v___x_426_);
                leanh::lean_inc(v_a_409_);
                v___x_428_ = lean_array_push(v___x_427_, v_a_409_);
                leanh::lean_inc(v_a_412_);
                v___x_429_ = lean_array_push(v___x_428_, v_a_412_);
                v___x_430_ = l_Lean_mkAppN(v___x_425_, v___x_429_);
                leanh::lean_dec_ref(v___x_429_);
                leanh::lean_inc_ref(v___x_430_);
                leanh::lean_inc_ref(v_goalType_396_);
                v___x_431_ = l_Lean_Meta_isExprDefEq(
                    v_goalType_396_,
                    v___x_430_,
                    v_a_397_,
                    v_a_398_,
                    v_a_399_,
                    v_a_400_,
                );
                if leanh::lean_obj_tag(v___x_431_) == 0 {
                    v_a_432_ = leanh::lean_ctor_get(v___x_431_, 0);
                    leanh::lean_inc(v_a_432_);
                    leanh::lean_dec_ref_known(v___x_431_, 1);
                    v___x_433_ = (leanh::lean_unbox(v_a_432_) as u8);
                    leanh::lean_dec(v_a_432_);
                    if v___x_433_ == 0 {
                        leanh::lean_del_object(v___x_414_);
                        leanh::lean_dec(v_a_412_);
                        leanh::lean_dec(v_a_409_);
                        leanh::lean_dec(v_a_403_);
                        v___x_434_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1_once
                            ),
                            _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1,
                        );
                        v___x_435_ = l_Lean_indentExpr(v_goalType_396_);
                        v___x_436_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_436_, 0, v___x_434_);
                        leanh::lean_ctor_set(v___x_436_, 1, v___x_435_);
                        v___x_437_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3_once
                            ),
                            _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3,
                        );
                        v___x_438_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_438_, 0, v___x_436_);
                        leanh::lean_ctor_set(v___x_438_, 1, v___x_437_);
                        v___x_439_ = l_Lean_indentExpr(v___x_430_);
                        v___x_440_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_440_, 0, v___x_438_);
                        leanh::lean_ctor_set(v___x_440_, 1, v___x_439_);
                        v___x_441_ = l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(v_stx_395_, v___x_440_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
                        v_a_442_ = leanh::lean_ctor_get(v___x_441_, 0);
                        v_isSharedCheck_449_ = (!leanh::lean_is_exclusive(v___x_441_)) as u8;
                        if v_isSharedCheck_449_ == 0 {
                            v___x_444_ = v___x_441_;
                            v_isShared_445_ = v_isSharedCheck_449_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_442_);
                            leanh::lean_dec(v___x_441_);
                            v___x_444_ = leanh::lean_box(0);
                            v_isShared_445_ = v_isSharedCheck_449_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_430_);
                        leanh::lean_dec_ref(v_goalType_396_);
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_430_);
                    leanh::lean_del_object(v___x_414_);
                    leanh::lean_dec(v_a_412_);
                    leanh::lean_dec(v_a_409_);
                    leanh::lean_dec(v_a_403_);
                    leanh::lean_dec_ref(v_goalType_396_);
                    v_a_450_ = leanh::lean_ctor_get(v___x_431_, 0);
                    v_isSharedCheck_457_ = (!leanh::lean_is_exclusive(v___x_431_)) as u8;
                    if v_isSharedCheck_457_ == 0 {
                        v___x_452_ = v___x_431_;
                        v_isShared_453_ = v_isSharedCheck_457_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_450_);
                        leanh::lean_dec(v___x_431_);
                        v___x_452_ = leanh::lean_box(0);
                        v_isShared_453_ = v_isSharedCheck_457_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_417_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_417_, 0, v_a_409_);
                leanh::lean_ctor_set(v___x_417_, 1, v_a_403_);
                v___x_418_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_418_, 0, v_a_412_);
                leanh::lean_ctor_set(v___x_418_, 1, v___x_417_);
                if v_isShared_415_ == 0 {
                    leanh::lean_ctor_set(v___x_414_, 0, v___x_418_);
                    v___x_420_ = v___x_414_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_421_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
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
                    v_reuseFailAlloc_448_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
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
                    v_reuseFailAlloc_456_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
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
                    v_reuseFailAlloc_465_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
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
                    v_reuseFailAlloc_473_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
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
                    v_reuseFailAlloc_481_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
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
    mut v_stx_483_: *mut leanh::LeanObject,
    mut v_goalType_484_: *mut leanh::LeanObject,
    mut v_a_485_: *mut leanh::LeanObject,
    mut v_a_486_: *mut leanh::LeanObject,
    mut v_a_487_: *mut leanh::LeanObject,
    mut v_a_488_: *mut leanh::LeanObject,
    mut v_a_489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_490_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(
        v_stx_483_,
        v_goalType_484_,
        v_a_485_,
        v_a_486_,
        v_a_487_,
        v_a_488_,
    );
    leanh::lean_dec(v_a_488_);
    leanh::lean_dec_ref(v_a_487_);
    leanh::lean_dec(v_a_486_);
    leanh::lean_dec_ref(v_a_485_);
    leanh::lean_dec(v_stx_483_);
    return v_res_490_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0(
    mut v_00_u03b1_491_: *mut leanh::LeanObject,
    mut v_ref_492_: *mut leanh::LeanObject,
    mut v_msg_493_: *mut leanh::LeanObject,
    mut v___y_494_: *mut leanh::LeanObject,
    mut v___y_495_: *mut leanh::LeanObject,
    mut v___y_496_: *mut leanh::LeanObject,
    mut v___y_497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_499_ =
        l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(
            v_ref_492_, v_msg_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_,
        );
    return v___x_499_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___boxed(
    mut v_00_u03b1_500_: *mut leanh::LeanObject,
    mut v_ref_501_: *mut leanh::LeanObject,
    mut v_msg_502_: *mut leanh::LeanObject,
    mut v___y_503_: *mut leanh::LeanObject,
    mut v___y_504_: *mut leanh::LeanObject,
    mut v___y_505_: *mut leanh::LeanObject,
    mut v___y_506_: *mut leanh::LeanObject,
    mut v___y_507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_508_ = l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0(
        v_00_u03b1_500_,
        v_ref_501_,
        v_msg_502_,
        v___y_503_,
        v___y_504_,
        v___y_505_,
        v___y_506_,
    );
    leanh::lean_dec(v___y_506_);
    leanh::lean_dec_ref(v___y_505_);
    leanh::lean_dec(v___y_504_);
    leanh::lean_dec_ref(v___y_503_);
    leanh::lean_dec(v_ref_501_);
    return v_res_508_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0(
    mut v_00_u03b1_509_: *mut leanh::LeanObject,
    mut v_msg_510_: *mut leanh::LeanObject,
    mut v___y_511_: *mut leanh::LeanObject,
    mut v___y_512_: *mut leanh::LeanObject,
    mut v___y_513_: *mut leanh::LeanObject,
    mut v___y_514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_516_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(v_msg_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
    return v___x_516_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___boxed(
    mut v_00_u03b1_517_: *mut leanh::LeanObject,
    mut v_msg_518_: *mut leanh::LeanObject,
    mut v___y_519_: *mut leanh::LeanObject,
    mut v___y_520_: *mut leanh::LeanObject,
    mut v___y_521_: *mut leanh::LeanObject,
    mut v___y_522_: *mut leanh::LeanObject,
    mut v___y_523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_524_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0(v_00_u03b1_517_, v_msg_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
    leanh::lean_dec(v___y_522_);
    leanh::lean_dec_ref(v___y_521_);
    leanh::lean_dec(v___y_520_);
    leanh::lean_dec_ref(v___y_519_);
    return v_res_524_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_CheckTactic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_CheckTactic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_CheckTactic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CheckTactic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_CheckTactic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_CheckTactic(builtin);
}
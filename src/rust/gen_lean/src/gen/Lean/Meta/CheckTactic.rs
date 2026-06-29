// Lean compiler output
// Module: Lean.Meta.CheckTactic
// Imports: Lean.Meta.Basic
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
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
pub static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3_value:
    crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_0:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__0_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_1:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__1_value)
            as *mut crate::leanh::LeanObject,
        15449383196166861506 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_2:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__2_value)
            as *mut crate::leanh::LeanObject,
        13088578035309973495 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value: crate::leanh::LeanCtorObject<
    3,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value_aux_2)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__3_value)
            as *mut crate::leanh::LeanObject,
        11417940687150260387 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2_value:
    crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_CheckTactic_mkCheckGoalType(
    mut v_val_272_: *mut crate::leanh::LeanObject,
    mut v_type_273_: *mut crate::leanh::LeanObject,
    mut v_a_274_: *mut crate::leanh::LeanObject,
    mut v_a_275_: *mut crate::leanh::LeanObject,
    mut v_a_276_: *mut crate::leanh::LeanObject,
    mut v_a_277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_283_: u8 = 0;
    let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_292_: u8 = 0;
    let mut v_a_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_296_: u8 = 0;
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_300_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_279_ = l_Lean_Meta_mkFreshLevelMVar(v_a_274_, v_a_275_, v_a_276_, v_a_277_);
                if crate::leanh::lean_obj_tag(v___x_279_) == 0 {
                    v_a_280_ = crate::leanh::lean_ctor_get(v___x_279_, 0);
                    v_isSharedCheck_292_ = (!crate::leanh::lean_is_exclusive(v___x_279_)) as u8;
                    if v_isSharedCheck_292_ == 0 {
                        v___x_282_ = v___x_279_;
                        v_isShared_283_ = v_isSharedCheck_292_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_280_);
                        crate::leanh::lean_dec(v___x_279_);
                        v___x_282_ = crate::leanh::lean_box(0);
                        v_isShared_283_ = v_isSharedCheck_292_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_273_);
                    crate::leanh::lean_dec_ref(v_val_272_);
                    v_a_293_ = crate::leanh::lean_ctor_get(v___x_279_, 0);
                    v_isSharedCheck_300_ = (!crate::leanh::lean_is_exclusive(v___x_279_)) as u8;
                    if v_isSharedCheck_300_ == 0 {
                        v___x_295_ = v___x_279_;
                        v_isShared_296_ = v_isSharedCheck_300_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_293_);
                        crate::leanh::lean_dec(v___x_279_);
                        v___x_295_ = crate::leanh::lean_box(0);
                        v_isShared_296_ = v_isSharedCheck_300_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_284_ = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4;
                v___x_285_ = crate::leanh::lean_box(0);
                v___x_286_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_286_, 0, v_a_280_);
                crate::leanh::lean_ctor_set(v___x_286_, 1, v___x_285_);
                v___x_287_ = l_Lean_mkConst(v___x_284_, v___x_286_);
                v___x_288_ = l_Lean_mkAppB(v___x_287_, v_type_273_, v_val_272_);
                if v_isShared_283_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_282_, 0, v___x_288_);
                    v___x_290_ = v___x_282_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_291_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_288_);
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
                    v_reuseFailAlloc_299_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_293_);
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
    mut v_val_301_: *mut crate::leanh::LeanObject,
    mut v_type_302_: *mut crate::leanh::LeanObject,
    mut v_a_303_: *mut crate::leanh::LeanObject,
    mut v_a_304_: *mut crate::leanh::LeanObject,
    mut v_a_305_: *mut crate::leanh::LeanObject,
    mut v_a_306_: *mut crate::leanh::LeanObject,
    mut v_a_307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_308_ = l_Lean_Meta_CheckTactic_mkCheckGoalType(
        v_val_301_,
        v_type_302_,
        v_a_303_,
        v_a_304_,
        v_a_305_,
        v_a_306_,
    );
    crate::leanh::lean_dec(v_a_306_);
    crate::leanh::lean_dec_ref(v_a_305_);
    crate::leanh::lean_dec(v_a_304_);
    crate::leanh::lean_dec_ref(v_a_303_);
    return v_res_308_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1(
    mut v_msgData_309_: *mut crate::leanh::LeanObject,
    mut v___y_310_: *mut crate::leanh::LeanObject,
    mut v___y_311_: *mut crate::leanh::LeanObject,
    mut v___y_312_: *mut crate::leanh::LeanObject,
    mut v___y_313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_315_ = lean_st_ref_get(v___y_313_);
    v_env_316_ = crate::leanh::lean_ctor_get(v___x_315_, 0);
    crate::leanh::lean_inc_ref(v_env_316_);
    crate::leanh::lean_dec(v___x_315_);
    v___x_317_ = lean_st_ref_get(v___y_311_);
    v_mctx_318_ = crate::leanh::lean_ctor_get(v___x_317_, 0);
    crate::leanh::lean_inc_ref(v_mctx_318_);
    crate::leanh::lean_dec(v___x_317_);
    v_lctx_319_ = crate::leanh::lean_ctor_get(v___y_310_, 2);
    v_options_320_ = crate::leanh::lean_ctor_get(v___y_312_, 2);
    crate::leanh::lean_inc_ref(v_options_320_);
    crate::leanh::lean_inc_ref(v_lctx_319_);
    v___x_321_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_321_, 0, v_env_316_);
    crate::leanh::lean_ctor_set(v___x_321_, 1, v_mctx_318_);
    crate::leanh::lean_ctor_set(v___x_321_, 2, v_lctx_319_);
    crate::leanh::lean_ctor_set(v___x_321_, 3, v_options_320_);
    v___x_322_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_322_, 0, v___x_321_);
    crate::leanh::lean_ctor_set(v___x_322_, 1, v_msgData_309_);
    v___x_323_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_323_, 0, v___x_322_);
    return v___x_323_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1___boxed(
    mut v_msgData_324_: *mut crate::leanh::LeanObject,
    mut v___y_325_: *mut crate::leanh::LeanObject,
    mut v___y_326_: *mut crate::leanh::LeanObject,
    mut v___y_327_: *mut crate::leanh::LeanObject,
    mut v___y_328_: *mut crate::leanh::LeanObject,
    mut v___y_329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_330_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1(v_msgData_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
    crate::leanh::lean_dec(v___y_328_);
    crate::leanh::lean_dec_ref(v___y_327_);
    crate::leanh::lean_dec(v___y_326_);
    crate::leanh::lean_dec_ref(v___y_325_);
    return v_res_330_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(
    mut v_msg_331_: *mut crate::leanh::LeanObject,
    mut v___y_332_: *mut crate::leanh::LeanObject,
    mut v___y_333_: *mut crate::leanh::LeanObject,
    mut v___y_334_: *mut crate::leanh::LeanObject,
    mut v___y_335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_342_: u8 = 0;
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_347_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_337_ = crate::leanh::lean_ctor_get(v___y_334_, 5);
                v___x_338_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0_spec__1(v_msg_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_);
                v_a_339_ = crate::leanh::lean_ctor_get(v___x_338_, 0);
                v_isSharedCheck_347_ = (!crate::leanh::lean_is_exclusive(v___x_338_)) as u8;
                if v_isSharedCheck_347_ == 0 {
                    v___x_341_ = v___x_338_;
                    v_isShared_342_ = v_isSharedCheck_347_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_339_);
                    crate::leanh::lean_dec(v___x_338_);
                    v___x_341_ = crate::leanh::lean_box(0);
                    v_isShared_342_ = v_isSharedCheck_347_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_337_);
                v___x_343_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_343_, 0, v_ref_337_);
                crate::leanh::lean_ctor_set(v___x_343_, 1, v_a_339_);
                if v_isShared_342_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_341_, 1);
                    crate::leanh::lean_ctor_set(v___x_341_, 0, v___x_343_);
                    v___x_345_ = v___x_341_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_346_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_343_);
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
    mut v_msg_348_: *mut crate::leanh::LeanObject,
    mut v___y_349_: *mut crate::leanh::LeanObject,
    mut v___y_350_: *mut crate::leanh::LeanObject,
    mut v___y_351_: *mut crate::leanh::LeanObject,
    mut v___y_352_: *mut crate::leanh::LeanObject,
    mut v___y_353_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_354_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(v_msg_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
    crate::leanh::lean_dec(v___y_352_);
    crate::leanh::lean_dec_ref(v___y_351_);
    crate::leanh::lean_dec(v___y_350_);
    crate::leanh::lean_dec_ref(v___y_349_);
    return v_res_354_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(
    mut v_ref_355_: *mut crate::leanh::LeanObject,
    mut v_msg_356_: *mut crate::leanh::LeanObject,
    mut v___y_357_: *mut crate::leanh::LeanObject,
    mut v___y_358_: *mut crate::leanh::LeanObject,
    mut v___y_359_: *mut crate::leanh::LeanObject,
    mut v___y_360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_374_: u8 = 0;
    let mut v_cancelTk_x3f_375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_376_: u8 = 0;
    let mut v_inheritedTraceOptions_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_362_ = crate::leanh::lean_ctor_get(v___y_359_, 0);
    v_fileMap_363_ = crate::leanh::lean_ctor_get(v___y_359_, 1);
    v_options_364_ = crate::leanh::lean_ctor_get(v___y_359_, 2);
    v_currRecDepth_365_ = crate::leanh::lean_ctor_get(v___y_359_, 3);
    v_maxRecDepth_366_ = crate::leanh::lean_ctor_get(v___y_359_, 4);
    v_ref_367_ = crate::leanh::lean_ctor_get(v___y_359_, 5);
    v_currNamespace_368_ = crate::leanh::lean_ctor_get(v___y_359_, 6);
    v_openDecls_369_ = crate::leanh::lean_ctor_get(v___y_359_, 7);
    v_initHeartbeats_370_ = crate::leanh::lean_ctor_get(v___y_359_, 8);
    v_maxHeartbeats_371_ = crate::leanh::lean_ctor_get(v___y_359_, 9);
    v_quotContext_372_ = crate::leanh::lean_ctor_get(v___y_359_, 10);
    v_currMacroScope_373_ = crate::leanh::lean_ctor_get(v___y_359_, 11);
    v_diag_374_ = crate::leanh::lean_ctor_get_uint8(
        v___y_359_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_375_ = crate::leanh::lean_ctor_get(v___y_359_, 12);
    v_suppressElabErrors_376_ = crate::leanh::lean_ctor_get_uint8(
        v___y_359_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_377_ = crate::leanh::lean_ctor_get(v___y_359_, 13);
    v_ref_378_ = l_Lean_replaceRef(v_ref_355_, v_ref_367_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_377_);
    crate::leanh::lean_inc(v_cancelTk_x3f_375_);
    crate::leanh::lean_inc(v_currMacroScope_373_);
    crate::leanh::lean_inc(v_quotContext_372_);
    crate::leanh::lean_inc(v_maxHeartbeats_371_);
    crate::leanh::lean_inc(v_initHeartbeats_370_);
    crate::leanh::lean_inc(v_openDecls_369_);
    crate::leanh::lean_inc(v_currNamespace_368_);
    crate::leanh::lean_inc(v_maxRecDepth_366_);
    crate::leanh::lean_inc(v_currRecDepth_365_);
    crate::leanh::lean_inc_ref(v_options_364_);
    crate::leanh::lean_inc_ref(v_fileMap_363_);
    crate::leanh::lean_inc_ref(v_fileName_362_);
    v___x_379_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_379_, 0, v_fileName_362_);
    crate::leanh::lean_ctor_set(v___x_379_, 1, v_fileMap_363_);
    crate::leanh::lean_ctor_set(v___x_379_, 2, v_options_364_);
    crate::leanh::lean_ctor_set(v___x_379_, 3, v_currRecDepth_365_);
    crate::leanh::lean_ctor_set(v___x_379_, 4, v_maxRecDepth_366_);
    crate::leanh::lean_ctor_set(v___x_379_, 5, v_ref_378_);
    crate::leanh::lean_ctor_set(v___x_379_, 6, v_currNamespace_368_);
    crate::leanh::lean_ctor_set(v___x_379_, 7, v_openDecls_369_);
    crate::leanh::lean_ctor_set(v___x_379_, 8, v_initHeartbeats_370_);
    crate::leanh::lean_ctor_set(v___x_379_, 9, v_maxHeartbeats_371_);
    crate::leanh::lean_ctor_set(v___x_379_, 10, v_quotContext_372_);
    crate::leanh::lean_ctor_set(v___x_379_, 11, v_currMacroScope_373_);
    crate::leanh::lean_ctor_set(v___x_379_, 12, v_cancelTk_x3f_375_);
    crate::leanh::lean_ctor_set(v___x_379_, 13, v_inheritedTraceOptions_377_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_379_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_374_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_379_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_376_,
    );
    v___x_380_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(v_msg_356_, v___y_357_, v___y_358_, v___x_379_, v___y_360_);
    crate::leanh::lean_dec_ref_known(v___x_379_, 14);
    return v___x_380_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg___boxed(
    mut v_ref_381_: *mut crate::leanh::LeanObject,
    mut v_msg_382_: *mut crate::leanh::LeanObject,
    mut v___y_383_: *mut crate::leanh::LeanObject,
    mut v___y_384_: *mut crate::leanh::LeanObject,
    mut v___y_385_: *mut crate::leanh::LeanObject,
    mut v___y_386_: *mut crate::leanh::LeanObject,
    mut v___y_387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_388_ =
        l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(
            v_ref_381_, v_msg_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_,
        );
    crate::leanh::lean_dec(v___y_386_);
    crate::leanh::lean_dec_ref(v___y_385_);
    crate::leanh::lean_dec(v___y_384_);
    crate::leanh::lean_dec_ref(v___y_383_);
    crate::leanh::lean_dec(v_ref_381_);
    return v_res_388_;
}
pub unsafe fn _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_390_ = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__0;
    v___x_391_ = l_Lean_stringToMessageData(v___x_390_);
    return v___x_391_;
}
pub unsafe fn _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_393_ = l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__2;
    v___x_394_ = l_Lean_stringToMessageData(v___x_393_);
    return v___x_394_;
}
pub unsafe fn l_Lean_Meta_CheckTactic_matchCheckGoalType(
    mut v_stx_395_: *mut crate::leanh::LeanObject,
    mut v_goalType_396_: *mut crate::leanh::LeanObject,
    mut v_a_397_: *mut crate::leanh::LeanObject,
    mut v_a_398_: *mut crate::leanh::LeanObject,
    mut v_a_399_: *mut crate::leanh::LeanObject,
    mut v_a_400_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_406_: u8 = 0;
    let mut v___x_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_415_: u8 = 0;
    let mut v___x_417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: u8 = 0;
    let mut v___x_434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_445_: u8 = 0;
    let mut v___x_447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_449_: u8 = 0;
    let mut v_a_450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_453_: u8 = 0;
    let mut v___x_455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_457_: u8 = 0;
    let mut v_isSharedCheck_458_: u8 = 0;
    let mut v_a_459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_462_: u8 = 0;
    let mut v___x_464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_466_: u8 = 0;
    let mut v_a_467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_470_: u8 = 0;
    let mut v___x_472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_474_: u8 = 0;
    let mut v_a_475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_478_: u8 = 0;
    let mut v___x_480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_482_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_402_ = l_Lean_Meta_mkFreshLevelMVar(v_a_397_, v_a_398_, v_a_399_, v_a_400_);
                if crate::leanh::lean_obj_tag(v___x_402_) == 0 {
                    v_a_403_ = crate::leanh::lean_ctor_get(v___x_402_, 0);
                    crate::leanh::lean_inc_n(v_a_403_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_402_, 1);
                    v___x_404_ = l_Lean_Expr_sort___override(v_a_403_);
                    v___x_405_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_405_, 0, v___x_404_);
                    v___x_406_ = 0;
                    v___x_407_ = crate::leanh::lean_box(0);
                    v___x_408_ = l_Lean_Meta_mkFreshExprMVar(
                        v___x_405_, v___x_406_, v___x_407_, v_a_397_, v_a_398_, v_a_399_, v_a_400_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_408_) == 0 {
                        v_a_409_ = crate::leanh::lean_ctor_get(v___x_408_, 0);
                        crate::leanh::lean_inc_n(v_a_409_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_408_, 1);
                        v___x_410_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_410_, 0, v_a_409_);
                        v___x_411_ = l_Lean_Meta_mkFreshExprMVar(
                            v___x_410_, v___x_406_, v___x_407_, v_a_397_, v_a_398_, v_a_399_,
                            v_a_400_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_411_) == 0 {
                            v_a_412_ = crate::leanh::lean_ctor_get(v___x_411_, 0);
                            v_isSharedCheck_458_ =
                                (!crate::leanh::lean_is_exclusive(v___x_411_)) as u8;
                            if v_isSharedCheck_458_ == 0 {
                                v___x_414_ = v___x_411_;
                                v_isShared_415_ = v_isSharedCheck_458_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_412_);
                                crate::leanh::lean_dec(v___x_411_);
                                v___x_414_ = crate::leanh::lean_box(0);
                                v_isShared_415_ = v_isSharedCheck_458_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_409_);
                            crate::leanh::lean_dec(v_a_403_);
                            crate::leanh::lean_dec_ref(v_goalType_396_);
                            v_a_459_ = crate::leanh::lean_ctor_get(v___x_411_, 0);
                            v_isSharedCheck_466_ =
                                (!crate::leanh::lean_is_exclusive(v___x_411_)) as u8;
                            if v_isSharedCheck_466_ == 0 {
                                v___x_461_ = v___x_411_;
                                v_isShared_462_ = v_isSharedCheck_466_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_459_);
                                crate::leanh::lean_dec(v___x_411_);
                                v___x_461_ = crate::leanh::lean_box(0);
                                v_isShared_462_ = v_isSharedCheck_466_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_403_);
                        crate::leanh::lean_dec_ref(v_goalType_396_);
                        v_a_467_ = crate::leanh::lean_ctor_get(v___x_408_, 0);
                        v_isSharedCheck_474_ = (!crate::leanh::lean_is_exclusive(v___x_408_)) as u8;
                        if v_isSharedCheck_474_ == 0 {
                            v___x_469_ = v___x_408_;
                            v_isShared_470_ = v_isSharedCheck_474_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_467_);
                            crate::leanh::lean_dec(v___x_408_);
                            v___x_469_ = crate::leanh::lean_box(0);
                            v_isShared_470_ = v_isSharedCheck_474_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_goalType_396_);
                    v_a_475_ = crate::leanh::lean_ctor_get(v___x_402_, 0);
                    v_isSharedCheck_482_ = (!crate::leanh::lean_is_exclusive(v___x_402_)) as u8;
                    if v_isSharedCheck_482_ == 0 {
                        v___x_477_ = v___x_402_;
                        v_isShared_478_ = v_isSharedCheck_482_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_475_);
                        crate::leanh::lean_dec(v___x_402_);
                        v___x_477_ = crate::leanh::lean_box(0);
                        v_isShared_478_ = v_isSharedCheck_482_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                v___x_422_ = l_Lean_Meta_CheckTactic_mkCheckGoalType___closed__4;
                v___x_423_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_a_403_);
                v___x_424_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_424_, 0, v_a_403_);
                crate::leanh::lean_ctor_set(v___x_424_, 1, v___x_423_);
                v___x_425_ = l_Lean_Expr_const___override(v___x_422_, v___x_424_);
                v___x_426_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_427_ = lean_mk_empty_array_with_capacity(v___x_426_);
                crate::leanh::lean_inc(v_a_409_);
                v___x_428_ = lean_array_push(v___x_427_, v_a_409_);
                crate::leanh::lean_inc(v_a_412_);
                v___x_429_ = lean_array_push(v___x_428_, v_a_412_);
                v___x_430_ = l_Lean_mkAppN(v___x_425_, v___x_429_);
                crate::leanh::lean_dec_ref(v___x_429_);
                crate::leanh::lean_inc_ref(v___x_430_);
                crate::leanh::lean_inc_ref(v_goalType_396_);
                v___x_431_ = l_Lean_Meta_isExprDefEq(
                    v_goalType_396_,
                    v___x_430_,
                    v_a_397_,
                    v_a_398_,
                    v_a_399_,
                    v_a_400_,
                );
                if crate::leanh::lean_obj_tag(v___x_431_) == 0 {
                    v_a_432_ = crate::leanh::lean_ctor_get(v___x_431_, 0);
                    crate::leanh::lean_inc(v_a_432_);
                    crate::leanh::lean_dec_ref_known(v___x_431_, 1);
                    v___x_433_ = (crate::leanh::lean_unbox(v_a_432_) as u8);
                    crate::leanh::lean_dec(v_a_432_);
                    if v___x_433_ == 0 {
                        crate::leanh::lean_del_object(v___x_414_);
                        crate::leanh::lean_dec(v_a_412_);
                        crate::leanh::lean_dec(v_a_409_);
                        crate::leanh::lean_dec(v_a_403_);
                        v___x_434_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1_once
                            ),
                            _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__1,
                        );
                        v___x_435_ = l_Lean_indentExpr(v_goalType_396_);
                        v___x_436_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_436_, 0, v___x_434_);
                        crate::leanh::lean_ctor_set(v___x_436_, 1, v___x_435_);
                        v___x_437_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3_once
                            ),
                            _init_l_Lean_Meta_CheckTactic_matchCheckGoalType___closed__3,
                        );
                        v___x_438_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_438_, 0, v___x_436_);
                        crate::leanh::lean_ctor_set(v___x_438_, 1, v___x_437_);
                        v___x_439_ = l_Lean_indentExpr(v___x_430_);
                        v___x_440_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_440_, 0, v___x_438_);
                        crate::leanh::lean_ctor_set(v___x_440_, 1, v___x_439_);
                        v___x_441_ = l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(v_stx_395_, v___x_440_, v_a_397_, v_a_398_, v_a_399_, v_a_400_);
                        v_a_442_ = crate::leanh::lean_ctor_get(v___x_441_, 0);
                        v_isSharedCheck_449_ = (!crate::leanh::lean_is_exclusive(v___x_441_)) as u8;
                        if v_isSharedCheck_449_ == 0 {
                            v___x_444_ = v___x_441_;
                            v_isShared_445_ = v_isSharedCheck_449_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_442_);
                            crate::leanh::lean_dec(v___x_441_);
                            v___x_444_ = crate::leanh::lean_box(0);
                            v_isShared_445_ = v_isSharedCheck_449_;
                            state = 4;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_430_);
                        crate::leanh::lean_dec_ref(v_goalType_396_);
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_430_);
                    crate::leanh::lean_del_object(v___x_414_);
                    crate::leanh::lean_dec(v_a_412_);
                    crate::leanh::lean_dec(v_a_409_);
                    crate::leanh::lean_dec(v_a_403_);
                    crate::leanh::lean_dec_ref(v_goalType_396_);
                    v_a_450_ = crate::leanh::lean_ctor_get(v___x_431_, 0);
                    v_isSharedCheck_457_ = (!crate::leanh::lean_is_exclusive(v___x_431_)) as u8;
                    if v_isSharedCheck_457_ == 0 {
                        v___x_452_ = v___x_431_;
                        v_isShared_453_ = v_isSharedCheck_457_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_450_);
                        crate::leanh::lean_dec(v___x_431_);
                        v___x_452_ = crate::leanh::lean_box(0);
                        v_isShared_453_ = v_isSharedCheck_457_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v___x_417_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_417_, 0, v_a_409_);
                crate::leanh::lean_ctor_set(v___x_417_, 1, v_a_403_);
                v___x_418_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_418_, 0, v_a_412_);
                crate::leanh::lean_ctor_set(v___x_418_, 1, v___x_417_);
                if v_isShared_415_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_414_, 0, v___x_418_);
                    v___x_420_ = v___x_414_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_421_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_421_, 0, v___x_418_);
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
                    v_reuseFailAlloc_448_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_448_, 0, v_a_442_);
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
                    v_reuseFailAlloc_456_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_456_, 0, v_a_450_);
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
                    v_reuseFailAlloc_465_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_465_, 0, v_a_459_);
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
                    v_reuseFailAlloc_473_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
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
                    v_reuseFailAlloc_481_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
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
    mut v_stx_483_: *mut crate::leanh::LeanObject,
    mut v_goalType_484_: *mut crate::leanh::LeanObject,
    mut v_a_485_: *mut crate::leanh::LeanObject,
    mut v_a_486_: *mut crate::leanh::LeanObject,
    mut v_a_487_: *mut crate::leanh::LeanObject,
    mut v_a_488_: *mut crate::leanh::LeanObject,
    mut v_a_489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_490_ = l_Lean_Meta_CheckTactic_matchCheckGoalType(
        v_stx_483_,
        v_goalType_484_,
        v_a_485_,
        v_a_486_,
        v_a_487_,
        v_a_488_,
    );
    crate::leanh::lean_dec(v_a_488_);
    crate::leanh::lean_dec_ref(v_a_487_);
    crate::leanh::lean_dec(v_a_486_);
    crate::leanh::lean_dec_ref(v_a_485_);
    crate::leanh::lean_dec(v_stx_483_);
    return v_res_490_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0(
    mut v_00_u03b1_491_: *mut crate::leanh::LeanObject,
    mut v_ref_492_: *mut crate::leanh::LeanObject,
    mut v_msg_493_: *mut crate::leanh::LeanObject,
    mut v___y_494_: *mut crate::leanh::LeanObject,
    mut v___y_495_: *mut crate::leanh::LeanObject,
    mut v___y_496_: *mut crate::leanh::LeanObject,
    mut v___y_497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_499_ =
        l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___redArg(
            v_ref_492_, v_msg_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_,
        );
    return v___x_499_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0___boxed(
    mut v_00_u03b1_500_: *mut crate::leanh::LeanObject,
    mut v_ref_501_: *mut crate::leanh::LeanObject,
    mut v_msg_502_: *mut crate::leanh::LeanObject,
    mut v___y_503_: *mut crate::leanh::LeanObject,
    mut v___y_504_: *mut crate::leanh::LeanObject,
    mut v___y_505_: *mut crate::leanh::LeanObject,
    mut v___y_506_: *mut crate::leanh::LeanObject,
    mut v___y_507_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_508_ = l_Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0(
        v_00_u03b1_500_,
        v_ref_501_,
        v_msg_502_,
        v___y_503_,
        v___y_504_,
        v___y_505_,
        v___y_506_,
    );
    crate::leanh::lean_dec(v___y_506_);
    crate::leanh::lean_dec_ref(v___y_505_);
    crate::leanh::lean_dec(v___y_504_);
    crate::leanh::lean_dec_ref(v___y_503_);
    crate::leanh::lean_dec(v_ref_501_);
    return v_res_508_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0(
    mut v_00_u03b1_509_: *mut crate::leanh::LeanObject,
    mut v_msg_510_: *mut crate::leanh::LeanObject,
    mut v___y_511_: *mut crate::leanh::LeanObject,
    mut v___y_512_: *mut crate::leanh::LeanObject,
    mut v___y_513_: *mut crate::leanh::LeanObject,
    mut v___y_514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_516_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___redArg(v_msg_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_);
    return v___x_516_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0___boxed(
    mut v_00_u03b1_517_: *mut crate::leanh::LeanObject,
    mut v_msg_518_: *mut crate::leanh::LeanObject,
    mut v___y_519_: *mut crate::leanh::LeanObject,
    mut v___y_520_: *mut crate::leanh::LeanObject,
    mut v___y_521_: *mut crate::leanh::LeanObject,
    mut v___y_522_: *mut crate::leanh::LeanObject,
    mut v___y_523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_524_ = l_Lean_throwError___at___00Lean_throwErrorAt___at___00Lean_Meta_CheckTactic_matchCheckGoalType_spec__0_spec__0(v_00_u03b1_517_, v_msg_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
    crate::leanh::lean_dec(v___y_522_);
    crate::leanh::lean_dec_ref(v___y_521_);
    crate::leanh::lean_dec(v___y_520_);
    crate::leanh::lean_dec_ref(v___y_519_);
    return v_res_524_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_CheckTactic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_CheckTactic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_CheckTactic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CheckTactic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_CheckTactic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_CheckTactic(builtin);
}

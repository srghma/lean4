// Lean compiler output
// Module: Lean.Meta.Sym.InferType
// Imports: Lean.Meta.Sym.SymM
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{l_Lean_mkAppB, l_Lean_mkConst};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    initialize_Lean_Meta_Sym_SymM, l_Lean_Meta_Sym_shareCommonInc___redArg,
    runtime_initialize_Lean_Meta_Sym_SymM,
};
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_nat_add, lean_nat_dec_lt,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::ffi::lean_infer_type;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_mkEqRefl___redArg___closed__0_value: crate::leanh::LeanStringObject<3> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [69, 113, 0],
    };
static mut l_Lean_Meta_Sym_mkEqRefl___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_mkEqRefl___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Sym_mkEqRefl___redArg___closed__1_value: crate::leanh::LeanStringObject<5> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [114, 101, 102, 108, 0],
    };
static mut l_Lean_Meta_Sym_mkEqRefl___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_mkEqRefl___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Sym_mkEqRefl___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Sym_mkEqRefl___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16122875713692181903 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Sym_mkEqRefl___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Sym_mkEqRefl___redArg___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Sym_mkEqRefl___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
            13480818501600609864 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Sym_mkEqRefl___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_mkEqRefl___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache(
    mut v_e_559_: *mut crate::leanh::LeanObject,
    mut v_a_560_: *mut crate::leanh::LeanObject,
    mut v_a_561_: *mut crate::leanh::LeanObject,
    mut v_a_562_: *mut crate::leanh::LeanObject,
    mut v_a_563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keyedConfig_565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_566_: u8 = 0;
    let mut v_zetaDeltaSet_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_573_: u8 = 0;
    let mut v_inTypeClassResolution_574_: u8 = 0;
    let mut v___x_575_: u8 = 0;
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keyedConfig_565_ = crate::leanh::lean_ctor_get(v_a_560_, 0);
    v_trackZetaDelta_566_ = crate::leanh::lean_ctor_get_uint8(
        v_a_560_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
    );
    v_zetaDeltaSet_567_ = crate::leanh::lean_ctor_get(v_a_560_, 1);
    v_lctx_568_ = crate::leanh::lean_ctor_get(v_a_560_, 2);
    v_localInstances_569_ = crate::leanh::lean_ctor_get(v_a_560_, 3);
    v_defEqCtx_x3f_570_ = crate::leanh::lean_ctor_get(v_a_560_, 4);
    v_synthPendingDepth_571_ = crate::leanh::lean_ctor_get(v_a_560_, 5);
    v_canUnfold_x3f_572_ = crate::leanh::lean_ctor_get(v_a_560_, 6);
    v_univApprox_573_ = crate::leanh::lean_ctor_get_uint8(
        v_a_560_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
    );
    v_inTypeClassResolution_574_ = crate::leanh::lean_ctor_get_uint8(
        v_a_560_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
    );
    v___x_575_ = 0;
    crate::leanh::lean_inc(v_canUnfold_x3f_572_);
    crate::leanh::lean_inc(v_synthPendingDepth_571_);
    crate::leanh::lean_inc(v_defEqCtx_x3f_570_);
    crate::leanh::lean_inc_ref(v_localInstances_569_);
    crate::leanh::lean_inc_ref(v_lctx_568_);
    crate::leanh::lean_inc(v_zetaDeltaSet_567_);
    crate::leanh::lean_inc_ref(v_keyedConfig_565_);
    v___x_576_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
    crate::leanh::lean_ctor_set(v___x_576_, 0, v_keyedConfig_565_);
    crate::leanh::lean_ctor_set(v___x_576_, 1, v_zetaDeltaSet_567_);
    crate::leanh::lean_ctor_set(v___x_576_, 2, v_lctx_568_);
    crate::leanh::lean_ctor_set(v___x_576_, 3, v_localInstances_569_);
    crate::leanh::lean_ctor_set(v___x_576_, 4, v_defEqCtx_x3f_570_);
    crate::leanh::lean_ctor_set(v___x_576_, 5, v_synthPendingDepth_571_);
    crate::leanh::lean_ctor_set(v___x_576_, 6, v_canUnfold_x3f_572_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_576_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
        v_trackZetaDelta_566_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_576_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
        v_univApprox_573_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_576_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
        v_inTypeClassResolution_574_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_576_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
        v___x_575_,
    );
    crate::leanh::lean_inc(v_a_563_);
    crate::leanh::lean_inc_ref(v_a_562_);
    crate::leanh::lean_inc(v_a_561_);
    v___x_577_ = lean_infer_type(v_e_559_, v___x_576_, v_a_561_, v_a_562_, v_a_563_);
    return v___x_577_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache___boxed(
    mut v_e_578_: *mut crate::leanh::LeanObject,
    mut v_a_579_: *mut crate::leanh::LeanObject,
    mut v_a_580_: *mut crate::leanh::LeanObject,
    mut v_a_581_: *mut crate::leanh::LeanObject,
    mut v_a_582_: *mut crate::leanh::LeanObject,
    mut v_a_583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_584_ = l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache(
        v_e_578_, v_a_579_, v_a_580_, v_a_581_, v_a_582_,
    );
    crate::leanh::lean_dec(v_a_582_);
    crate::leanh::lean_dec_ref(v_a_581_);
    crate::leanh::lean_dec(v_a_580_);
    crate::leanh::lean_dec_ref(v_a_579_);
    return v_res_584_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache(
    mut v_type_585_: *mut crate::leanh::LeanObject,
    mut v_a_586_: *mut crate::leanh::LeanObject,
    mut v_a_587_: *mut crate::leanh::LeanObject,
    mut v_a_588_: *mut crate::leanh::LeanObject,
    mut v_a_589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_keyedConfig_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_592_: u8 = 0;
    let mut v_zetaDeltaSet_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_599_: u8 = 0;
    let mut v_inTypeClassResolution_600_: u8 = 0;
    let mut v___x_601_: u8 = 0;
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_keyedConfig_591_ = crate::leanh::lean_ctor_get(v_a_586_, 0);
    v_trackZetaDelta_592_ = crate::leanh::lean_ctor_get_uint8(
        v_a_586_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
    );
    v_zetaDeltaSet_593_ = crate::leanh::lean_ctor_get(v_a_586_, 1);
    v_lctx_594_ = crate::leanh::lean_ctor_get(v_a_586_, 2);
    v_localInstances_595_ = crate::leanh::lean_ctor_get(v_a_586_, 3);
    v_defEqCtx_x3f_596_ = crate::leanh::lean_ctor_get(v_a_586_, 4);
    v_synthPendingDepth_597_ = crate::leanh::lean_ctor_get(v_a_586_, 5);
    v_canUnfold_x3f_598_ = crate::leanh::lean_ctor_get(v_a_586_, 6);
    v_univApprox_599_ = crate::leanh::lean_ctor_get_uint8(
        v_a_586_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
    );
    v_inTypeClassResolution_600_ = crate::leanh::lean_ctor_get_uint8(
        v_a_586_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
    );
    v___x_601_ = 0;
    crate::leanh::lean_inc(v_canUnfold_x3f_598_);
    crate::leanh::lean_inc(v_synthPendingDepth_597_);
    crate::leanh::lean_inc(v_defEqCtx_x3f_596_);
    crate::leanh::lean_inc_ref(v_localInstances_595_);
    crate::leanh::lean_inc_ref(v_lctx_594_);
    crate::leanh::lean_inc(v_zetaDeltaSet_593_);
    crate::leanh::lean_inc_ref(v_keyedConfig_591_);
    v___x_602_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
    crate::leanh::lean_ctor_set(v___x_602_, 0, v_keyedConfig_591_);
    crate::leanh::lean_ctor_set(v___x_602_, 1, v_zetaDeltaSet_593_);
    crate::leanh::lean_ctor_set(v___x_602_, 2, v_lctx_594_);
    crate::leanh::lean_ctor_set(v___x_602_, 3, v_localInstances_595_);
    crate::leanh::lean_ctor_set(v___x_602_, 4, v_defEqCtx_x3f_596_);
    crate::leanh::lean_ctor_set(v___x_602_, 5, v_synthPendingDepth_597_);
    crate::leanh::lean_ctor_set(v___x_602_, 6, v_canUnfold_x3f_598_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_602_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
        v_trackZetaDelta_592_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_602_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
        v_univApprox_599_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_602_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
        v_inTypeClassResolution_600_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_602_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
        v___x_601_,
    );
    v___x_603_ = l_Lean_Meta_getLevel(v_type_585_, v___x_602_, v_a_587_, v_a_588_, v_a_589_);
    crate::leanh::lean_dec_ref_known(v___x_602_, 7);
    return v___x_603_;
}
pub unsafe fn l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache___boxed(
    mut v_type_604_: *mut crate::leanh::LeanObject,
    mut v_a_605_: *mut crate::leanh::LeanObject,
    mut v_a_606_: *mut crate::leanh::LeanObject,
    mut v_a_607_: *mut crate::leanh::LeanObject,
    mut v_a_608_: *mut crate::leanh::LeanObject,
    mut v_a_609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_610_ = l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache(
        v_type_604_,
        v_a_605_,
        v_a_606_,
        v_a_607_,
        v_a_608_,
    );
    crate::leanh::lean_dec(v_a_608_);
    crate::leanh::lean_dec_ref(v_a_607_);
    crate::leanh::lean_dec(v_a_606_);
    crate::leanh::lean_dec_ref(v_a_605_);
    return v_res_610_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(
    mut v_keys_611_: *mut crate::leanh::LeanObject,
    mut v_vals_612_: *mut crate::leanh::LeanObject,
    mut v_i_613_: *mut crate::leanh::LeanObject,
    mut v_k_614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: u8 = 0;
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: u8 = 0;
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_615_ = lean_array_get_size(v_keys_611_);
                v___x_616_ = lean_nat_dec_lt(v_i_613_, v___x_615_);
                if v___x_616_ == 0 {
                    crate::leanh::lean_dec(v_i_613_);
                    v___x_617_ = crate::leanh::lean_box(0);
                    return v___x_617_;
                } else {
                    v_k_x27_618_ = lean_array_fget_borrowed(v_keys_611_, v_i_613_);
                    v___x_619_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_614_,
                            v_k_x27_618_,
                        );
                    if v___x_619_ == 0 {
                        v___x_620_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_621_ = lean_nat_add(v_i_613_, v___x_620_);
                        crate::leanh::lean_dec(v_i_613_);
                        v_i_613_ = v___x_621_;
                        state = 0;
                        continue;
                    } else {
                        v___x_623_ = lean_array_fget_borrowed(v_vals_612_, v_i_613_);
                        crate::leanh::lean_dec(v_i_613_);
                        crate::leanh::lean_inc(v___x_623_);
                        v___x_624_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_624_, 0, v___x_623_);
                        return v___x_624_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_625_: *mut crate::leanh::LeanObject,
    mut v_vals_626_: *mut crate::leanh::LeanObject,
    mut v_i_627_: *mut crate::leanh::LeanObject,
    mut v_k_628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_629_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(v_keys_625_, v_vals_626_, v_i_627_, v_k_628_);
    crate::leanh::lean_dec_ref(v_k_628_);
    crate::leanh::lean_dec_ref(v_vals_626_);
    crate::leanh::lean_dec_ref(v_keys_625_);
    return v_res_629_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_630_: usize = 0;
    let mut v___x_631_: usize = 0;
    let mut v___x_632_: usize = 0;
    v___x_630_ = 5usize;
    v___x_631_ = 1usize;
    v___x_632_ = lean_usize_shift_left(v___x_631_, v___x_630_);
    return v___x_632_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_633_: usize = 0;
    let mut v___x_634_: usize = 0;
    let mut v___x_635_: usize = 0;
    v___x_633_ = 1usize;
    v___x_634_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__0);
    v___x_635_ = lean_usize_sub(v___x_634_, v___x_633_);
    return v___x_635_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(
    mut v_x_636_: *mut crate::leanh::LeanObject,
    mut v_x_637_: usize,
    mut v_x_638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: usize = 0;
    let mut v___x_642_: usize = 0;
    let mut v___x_643_: usize = 0;
    let mut v_j_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: u8 = 0;
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: usize = 0;
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_636_) == 0 {
                    v_es_639_ = crate::leanh::lean_ctor_get(v_x_636_, 0);
                    v___x_640_ = crate::leanh::lean_box(2);
                    v___x_641_ = 5usize;
                    v___x_642_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1);
                    v___x_643_ = lean_usize_land(v_x_637_, v___x_642_);
                    v_j_644_ = lean_usize_to_nat(v___x_643_);
                    v___x_645_ = lean_array_get_borrowed(v___x_640_, v_es_639_, v_j_644_);
                    crate::leanh::lean_dec(v_j_644_);
                    match crate::leanh::lean_obj_tag(v___x_645_) {
                        0 => {
                            v_key_646_ = crate::leanh::lean_ctor_get(v___x_645_, 0);
                            v_val_647_ = crate::leanh::lean_ctor_get(v___x_645_, 1);
                            v___x_648_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_638_, v_key_646_);
                            if v___x_648_ == 0 {
                                v___x_649_ = crate::leanh::lean_box(0);
                                return v___x_649_;
                            } else {
                                crate::leanh::lean_inc(v_val_647_);
                                v___x_650_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_650_, 0, v_val_647_);
                                return v___x_650_;
                            }
                        }
                        1 => {
                            v_node_651_ = crate::leanh::lean_ctor_get(v___x_645_, 0);
                            v___x_652_ = lean_usize_shift_right(v_x_637_, v___x_641_);
                            v_x_636_ = v_node_651_;
                            v_x_637_ = v___x_652_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_654_ = crate::leanh::lean_box(0);
                            return v___x_654_;
                        }
                    }
                } else {
                    v_ks_655_ = crate::leanh::lean_ctor_get(v_x_636_, 0);
                    v_vs_656_ = crate::leanh::lean_ctor_get(v_x_636_, 1);
                    v___x_657_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_658_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(v_ks_655_, v_vs_656_, v___x_657_, v_x_638_);
                    return v___x_658_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___boxed(
    mut v_x_659_: *mut crate::leanh::LeanObject,
    mut v_x_660_: *mut crate::leanh::LeanObject,
    mut v_x_661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2882__boxed_662_: usize = 0;
    let mut v_res_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2882__boxed_662_ = crate::leanh::lean_unbox_usize(v_x_660_);
    crate::leanh::lean_dec(v_x_660_);
    v_res_663_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(v_x_659_, v_x_2882__boxed_662_, v_x_661_);
    crate::leanh::lean_dec_ref(v_x_661_);
    crate::leanh::lean_dec_ref(v_x_659_);
    return v_res_663_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(
    mut v_x_664_: *mut crate::leanh::LeanObject,
    mut v_x_665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_666_: u64 = 0;
    let mut v___x_667_: usize = 0;
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_666_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_665_);
    v___x_667_ = lean_uint64_to_usize(v___x_666_);
    v___x_668_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(v_x_664_, v___x_667_, v_x_665_);
    return v___x_668_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg___boxed(
    mut v_x_669_: *mut crate::leanh::LeanObject,
    mut v_x_670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_671_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(
            v_x_669_, v_x_670_,
        );
    crate::leanh::lean_dec_ref(v_x_670_);
    crate::leanh::lean_dec_ref(v_x_669_);
    return v_res_671_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5___redArg(
    mut v_x_672_: *mut crate::leanh::LeanObject,
    mut v_x_673_: *mut crate::leanh::LeanObject,
    mut v_x_674_: *mut crate::leanh::LeanObject,
    mut v_x_675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_680_: u8 = 0;
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: u8 = 0;
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: u8 = 0;
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_701_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_676_ = crate::leanh::lean_ctor_get(v_x_672_, 0);
                v_vs_677_ = crate::leanh::lean_ctor_get(v_x_672_, 1);
                v_isSharedCheck_701_ = (!crate::leanh::lean_is_exclusive(v_x_672_)) as u8;
                if v_isSharedCheck_701_ == 0 {
                    v___x_679_ = v_x_672_;
                    v_isShared_680_ = v_isSharedCheck_701_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_677_);
                    crate::leanh::lean_inc(v_ks_676_);
                    crate::leanh::lean_dec(v_x_672_);
                    v___x_679_ = crate::leanh::lean_box(0);
                    v_isShared_680_ = v_isSharedCheck_701_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_681_ = lean_array_get_size(v_ks_676_);
                v___x_682_ = lean_nat_dec_lt(v_x_673_, v___x_681_);
                if v___x_682_ == 0 {
                    crate::leanh::lean_dec(v_x_673_);
                    v___x_683_ = lean_array_push(v_ks_676_, v_x_674_);
                    v___x_684_ = lean_array_push(v_vs_677_, v_x_675_);
                    if v_isShared_680_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_679_, 1, v___x_684_);
                        crate::leanh::lean_ctor_set(v___x_679_, 0, v___x_683_);
                        v___x_686_ = v___x_679_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_687_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_687_, 0, v___x_683_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_687_, 1, v___x_684_);
                        v___x_686_ = v_reuseFailAlloc_687_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_688_ = lean_array_fget_borrowed(v_ks_676_, v_x_673_);
                    v___x_689_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_674_,
                            v_k_x27_688_,
                        );
                    if v___x_689_ == 0 {
                        if v_isShared_680_ == 0 {
                            v___x_691_ = v___x_679_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_695_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_695_, 0, v_ks_676_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_695_, 1, v_vs_677_);
                            v___x_691_ = v_reuseFailAlloc_695_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_696_ = lean_array_fset(v_ks_676_, v_x_673_, v_x_674_);
                        v___x_697_ = lean_array_fset(v_vs_677_, v_x_673_, v_x_675_);
                        crate::leanh::lean_dec(v_x_673_);
                        if v_isShared_680_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_679_, 1, v___x_697_);
                            crate::leanh::lean_ctor_set(v___x_679_, 0, v___x_696_);
                            v___x_699_ = v___x_679_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_700_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_696_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_700_, 1, v___x_697_);
                            v___x_699_ = v_reuseFailAlloc_700_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_686_;
            }
            3 => {
                v___x_692_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_693_ = lean_nat_add(v_x_673_, v___x_692_);
                crate::leanh::lean_dec(v_x_673_);
                v_x_672_ = v___x_691_;
                v_x_673_ = v___x_693_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_699_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4___redArg(
    mut v_n_702_: *mut crate::leanh::LeanObject,
    mut v_k_703_: *mut crate::leanh::LeanObject,
    mut v_v_704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_705_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_706_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5___redArg(v_n_702_, v___x_705_, v_k_703_, v_v_704_);
    return v___x_706_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_707_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_707_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(
    mut v_x_708_: *mut crate::leanh::LeanObject,
    mut v_x_709_: usize,
    mut v_x_710_: usize,
    mut v_x_711_: *mut crate::leanh::LeanObject,
    mut v_x_712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_714_: usize = 0;
    let mut v___x_715_: usize = 0;
    let mut v___x_716_: usize = 0;
    let mut v___x_717_: usize = 0;
    let mut v_j_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_720_: u8 = 0;
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_723_: u8 = 0;
    let mut v_v_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_737_: u8 = 0;
    let mut v___x_738_: u8 = 0;
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_744_: u8 = 0;
    let mut v_node_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_748_: u8 = 0;
    let mut v___x_749_: usize = 0;
    let mut v___x_750_: usize = 0;
    let mut v___x_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_755_: u8 = 0;
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_757_: u8 = 0;
    let mut v_unused_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_763_: u8 = 0;
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_768_: u8 = 0;
    let mut v_ks_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: usize = 0;
    let mut v___x_775_: u8 = 0;
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_778_: u8 = 0;
    let mut v_reuseFailAlloc_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_780_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_708_) == 0 {
                    v_es_713_ = crate::leanh::lean_ctor_get(v_x_708_, 0);
                    v___x_714_ = 5usize;
                    v___x_715_ = 1usize;
                    v___x_716_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg___closed__1);
                    v___x_717_ = lean_usize_land(v_x_709_, v___x_716_);
                    v_j_718_ = lean_usize_to_nat(v___x_717_);
                    v___x_719_ = lean_array_get_size(v_es_713_);
                    v___x_720_ = lean_nat_dec_lt(v_j_718_, v___x_719_);
                    if v___x_720_ == 0 {
                        crate::leanh::lean_dec(v_j_718_);
                        crate::leanh::lean_dec(v_x_712_);
                        crate::leanh::lean_dec_ref(v_x_711_);
                        return v_x_708_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_713_);
                        v_isSharedCheck_757_ = (!crate::leanh::lean_is_exclusive(v_x_708_)) as u8;
                        if v_isSharedCheck_757_ == 0 {
                            v_unused_758_ = crate::leanh::lean_ctor_get(v_x_708_, 0);
                            crate::leanh::lean_dec(v_unused_758_);
                            v___x_722_ = v_x_708_;
                            v_isShared_723_ = v_isSharedCheck_757_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_708_);
                            v___x_722_ = crate::leanh::lean_box(0);
                            v_isShared_723_ = v_isSharedCheck_757_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_759_ = crate::leanh::lean_ctor_get(v_x_708_, 0);
                    v_vs_760_ = crate::leanh::lean_ctor_get(v_x_708_, 1);
                    v_isSharedCheck_780_ = (!crate::leanh::lean_is_exclusive(v_x_708_)) as u8;
                    if v_isSharedCheck_780_ == 0 {
                        v___x_762_ = v_x_708_;
                        v_isShared_763_ = v_isSharedCheck_780_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_760_);
                        crate::leanh::lean_inc(v_ks_759_);
                        crate::leanh::lean_dec(v_x_708_);
                        v___x_762_ = crate::leanh::lean_box(0);
                        v_isShared_763_ = v_isSharedCheck_780_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_724_ = lean_array_fget(v_es_713_, v_j_718_);
                v___x_725_ = crate::leanh::lean_box(0);
                v_xs_x27_726_ = lean_array_fset(v_es_713_, v_j_718_, v___x_725_);
                match crate::leanh::lean_obj_tag(v_v_724_) {
                    0 => {
                        v_key_733_ = crate::leanh::lean_ctor_get(v_v_724_, 0);
                        v_val_734_ = crate::leanh::lean_ctor_get(v_v_724_, 1);
                        v_isSharedCheck_744_ = (!crate::leanh::lean_is_exclusive(v_v_724_)) as u8;
                        if v_isSharedCheck_744_ == 0 {
                            v___x_736_ = v_v_724_;
                            v_isShared_737_ = v_isSharedCheck_744_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_734_);
                            crate::leanh::lean_inc(v_key_733_);
                            crate::leanh::lean_dec(v_v_724_);
                            v___x_736_ = crate::leanh::lean_box(0);
                            v_isShared_737_ = v_isSharedCheck_744_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_745_ = crate::leanh::lean_ctor_get(v_v_724_, 0);
                        v_isSharedCheck_755_ = (!crate::leanh::lean_is_exclusive(v_v_724_)) as u8;
                        if v_isSharedCheck_755_ == 0 {
                            v___x_747_ = v_v_724_;
                            v_isShared_748_ = v_isSharedCheck_755_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_745_);
                            crate::leanh::lean_dec(v_v_724_);
                            v___x_747_ = crate::leanh::lean_box(0);
                            v_isShared_748_ = v_isSharedCheck_755_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_756_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_756_, 0, v_x_711_);
                        crate::leanh::lean_ctor_set(v___x_756_, 1, v_x_712_);
                        v___y_728_ = v___x_756_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_729_ = lean_array_fset(v_xs_x27_726_, v_j_718_, v___y_728_);
                crate::leanh::lean_dec(v_j_718_);
                if v_isShared_723_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_722_, 0, v___x_729_);
                    v___x_731_ = v___x_722_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_732_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_732_, 0, v___x_729_);
                    v___x_731_ = v_reuseFailAlloc_732_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_731_;
            }
            4 => {
                v___x_738_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_711_, v_key_733_,
                    );
                if v___x_738_ == 0 {
                    crate::leanh::lean_del_object(v___x_736_);
                    v___x_739_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_733_, v_val_734_, v_x_711_, v_x_712_,
                    );
                    v___x_740_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_740_, 0, v___x_739_);
                    v___y_728_ = v___x_740_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_734_);
                    crate::leanh::lean_dec(v_key_733_);
                    if v_isShared_737_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_736_, 1, v_x_712_);
                        crate::leanh::lean_ctor_set(v___x_736_, 0, v_x_711_);
                        v___x_742_ = v___x_736_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_743_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_743_, 0, v_x_711_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_743_, 1, v_x_712_);
                        v___x_742_ = v_reuseFailAlloc_743_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_728_ = v___x_742_;
                state = 2;
                continue;
            }
            6 => {
                v___x_749_ = lean_usize_shift_right(v_x_709_, v___x_714_);
                v___x_750_ = lean_usize_add(v_x_710_, v___x_715_);
                v___x_751_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_node_745_, v___x_749_, v___x_750_, v_x_711_, v_x_712_);
                if v_isShared_748_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_747_, 0, v___x_751_);
                    v___x_753_ = v___x_747_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_754_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_754_, 0, v___x_751_);
                    v___x_753_ = v_reuseFailAlloc_754_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_728_ = v___x_753_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_763_ == 0 {
                    v___x_765_ = v___x_762_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_779_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_779_, 0, v_ks_759_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_779_, 1, v_vs_760_);
                    v___x_765_ = v_reuseFailAlloc_779_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_766_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4___redArg(v___x_765_, v_x_711_, v_x_712_);
                v___x_774_ = 7usize;
                v___x_775_ = lean_usize_dec_le(v___x_774_, v_x_710_);
                if v___x_775_ == 0 {
                    v___x_776_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_766_);
                    v___x_777_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_778_ = lean_nat_dec_lt(v___x_776_, v___x_777_);
                    crate::leanh::lean_dec(v___x_776_);
                    v___y_768_ = v___x_778_;
                    state = 10;
                    continue;
                } else {
                    v___y_768_ = v___x_775_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_768_ == 0 {
                    v_ks_769_ = crate::leanh::lean_ctor_get(v_newNode_766_, 0);
                    crate::leanh::lean_inc_ref(v_ks_769_);
                    v_vs_770_ = crate::leanh::lean_ctor_get(v_newNode_766_, 1);
                    crate::leanh::lean_inc_ref(v_vs_770_);
                    crate::leanh::lean_dec_ref(v_newNode_766_);
                    v___x_771_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_772_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___closed__0);
                    v___x_773_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(v_x_710_, v_ks_769_, v_vs_770_, v___x_771_, v___x_772_);
                    crate::leanh::lean_dec_ref(v_vs_770_);
                    crate::leanh::lean_dec_ref(v_ks_769_);
                    return v___x_773_;
                } else {
                    return v_newNode_766_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(
    mut v_depth_781_: usize,
    mut v_keys_782_: *mut crate::leanh::LeanObject,
    mut v_vals_783_: *mut crate::leanh::LeanObject,
    mut v_i_784_: *mut crate::leanh::LeanObject,
    mut v_entries_785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: u8 = 0;
    let mut v_k_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: u64 = 0;
    let mut v_h_791_: usize = 0;
    let mut v___x_792_: usize = 0;
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: usize = 0;
    let mut v___x_795_: usize = 0;
    let mut v___x_796_: usize = 0;
    let mut v_h_797_: usize = 0;
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_786_ = lean_array_get_size(v_keys_782_);
                v___x_787_ = lean_nat_dec_lt(v_i_784_, v___x_786_);
                if v___x_787_ == 0 {
                    crate::leanh::lean_dec(v_i_784_);
                    return v_entries_785_;
                } else {
                    v_k_788_ = lean_array_fget_borrowed(v_keys_782_, v_i_784_);
                    v_v_789_ = lean_array_fget_borrowed(v_vals_783_, v_i_784_);
                    v___x_790_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_788_);
                    v_h_791_ = lean_uint64_to_usize(v___x_790_);
                    v___x_792_ = 5usize;
                    v___x_793_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_794_ = 1usize;
                    v___x_795_ = lean_usize_sub(v_depth_781_, v___x_794_);
                    v___x_796_ = lean_usize_mul(v___x_792_, v___x_795_);
                    v_h_797_ = lean_usize_shift_right(v_h_791_, v___x_796_);
                    v___x_798_ = lean_nat_add(v_i_784_, v___x_793_);
                    crate::leanh::lean_dec(v_i_784_);
                    crate::leanh::lean_inc(v_v_789_);
                    crate::leanh::lean_inc(v_k_788_);
                    v___x_799_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_entries_785_, v_h_797_, v_depth_781_, v_k_788_, v_v_789_);
                    v_i_784_ = v___x_798_;
                    v_entries_785_ = v___x_799_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_depth_801_: *mut crate::leanh::LeanObject,
    mut v_keys_802_: *mut crate::leanh::LeanObject,
    mut v_vals_803_: *mut crate::leanh::LeanObject,
    mut v_i_804_: *mut crate::leanh::LeanObject,
    mut v_entries_805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_806_: usize = 0;
    let mut v_res_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_806_ = crate::leanh::lean_unbox_usize(v_depth_801_);
    crate::leanh::lean_dec(v_depth_801_);
    v_res_807_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(v_depth_boxed_806_, v_keys_802_, v_vals_803_, v_i_804_, v_entries_805_);
    crate::leanh::lean_dec_ref(v_vals_803_);
    crate::leanh::lean_dec_ref(v_keys_802_);
    return v_res_807_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg___boxed(
    mut v_x_808_: *mut crate::leanh::LeanObject,
    mut v_x_809_: *mut crate::leanh::LeanObject,
    mut v_x_810_: *mut crate::leanh::LeanObject,
    mut v_x_811_: *mut crate::leanh::LeanObject,
    mut v_x_812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_3029__boxed_813_: usize = 0;
    let mut v_x_3030__boxed_814_: usize = 0;
    let mut v_res_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_3029__boxed_813_ = crate::leanh::lean_unbox_usize(v_x_809_);
    crate::leanh::lean_dec(v_x_809_);
    v_x_3030__boxed_814_ = crate::leanh::lean_unbox_usize(v_x_810_);
    crate::leanh::lean_dec(v_x_810_);
    v_res_815_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_x_808_, v_x_3029__boxed_813_, v_x_3030__boxed_814_, v_x_811_, v_x_812_);
    return v_res_815_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(
    mut v_x_816_: *mut crate::leanh::LeanObject,
    mut v_x_817_: *mut crate::leanh::LeanObject,
    mut v_x_818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_819_: u64 = 0;
    let mut v___x_820_: usize = 0;
    let mut v___x_821_: usize = 0;
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_819_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_817_);
    v___x_820_ = lean_uint64_to_usize(v___x_819_);
    v___x_821_ = 1usize;
    v___x_822_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_x_816_, v___x_820_, v___x_821_, v_x_817_, v_x_818_);
    return v___x_822_;
}
pub unsafe fn l_Lean_Meta_Sym_inferType___redArg(
    mut v_e_823_: *mut crate::leanh::LeanObject,
    mut v_a_824_: *mut crate::leanh::LeanObject,
    mut v_a_825_: *mut crate::leanh::LeanObject,
    mut v_a_826_: *mut crate::leanh::LeanObject,
    mut v_a_827_: *mut crate::leanh::LeanObject,
    mut v_a_828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_836_: u8 = 0;
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_840_: u8 = 0;
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_847_: u8 = 0;
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_859_: u8 = 0;
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_862_: u8 = 0;
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_871_: u8 = 0;
    let mut v_isSharedCheck_872_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_830_ = lean_st_ref_get(v_a_824_);
                v_inferType_831_ = crate::leanh::lean_ctor_get(v___x_830_, 3);
                crate::leanh::lean_inc_ref(v_inferType_831_);
                crate::leanh::lean_dec(v___x_830_);
                v___x_832_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_inferType_831_, v_e_823_);
                crate::leanh::lean_dec_ref(v_inferType_831_);
                if crate::leanh::lean_obj_tag(v___x_832_) == 1 {
                    crate::leanh::lean_dec_ref(v_e_823_);
                    v_val_833_ = crate::leanh::lean_ctor_get(v___x_832_, 0);
                    v_isSharedCheck_840_ = (!crate::leanh::lean_is_exclusive(v___x_832_)) as u8;
                    if v_isSharedCheck_840_ == 0 {
                        v___x_835_ = v___x_832_;
                        v_isShared_836_ = v_isSharedCheck_840_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_833_);
                        crate::leanh::lean_dec(v___x_832_);
                        v___x_835_ = crate::leanh::lean_box(0);
                        v_isShared_836_ = v_isSharedCheck_840_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_832_);
                    crate::leanh::lean_inc_ref(v_e_823_);
                    v___x_841_ =
                        l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_inferTypeWithoutCache(
                            v_e_823_, v_a_825_, v_a_826_, v_a_827_, v_a_828_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_841_) == 0 {
                        v_a_842_ = crate::leanh::lean_ctor_get(v___x_841_, 0);
                        crate::leanh::lean_inc(v_a_842_);
                        crate::leanh::lean_dec_ref_known(v___x_841_, 1);
                        v___x_843_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_842_, v_a_824_);
                        if crate::leanh::lean_obj_tag(v___x_843_) == 0 {
                            v_a_844_ = crate::leanh::lean_ctor_get(v___x_843_, 0);
                            v_isSharedCheck_872_ =
                                (!crate::leanh::lean_is_exclusive(v___x_843_)) as u8;
                            if v_isSharedCheck_872_ == 0 {
                                v___x_846_ = v___x_843_;
                                v_isShared_847_ = v_isSharedCheck_872_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_844_);
                                crate::leanh::lean_dec(v___x_843_);
                                v___x_846_ = crate::leanh::lean_box(0);
                                v_isShared_847_ = v_isSharedCheck_872_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_823_);
                            return v___x_843_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_823_);
                        return v___x_841_;
                    }
                }
            }
            1 => {
                if v_isShared_836_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_835_, 0);
                    v___x_838_ = v___x_835_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_839_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_839_, 0, v_val_833_);
                    v___x_838_ = v_reuseFailAlloc_839_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_838_;
            }
            3 => {
                v___x_848_ = lean_st_ref_take(v_a_824_);
                v_share_849_ = crate::leanh::lean_ctor_get(v___x_848_, 0);
                v_maxFVar_850_ = crate::leanh::lean_ctor_get(v___x_848_, 1);
                v_proofInstInfo_851_ = crate::leanh::lean_ctor_get(v___x_848_, 2);
                v_inferType_852_ = crate::leanh::lean_ctor_get(v___x_848_, 3);
                v_getLevel_853_ = crate::leanh::lean_ctor_get(v___x_848_, 4);
                v_congrInfo_854_ = crate::leanh::lean_ctor_get(v___x_848_, 5);
                v_defEqI_855_ = crate::leanh::lean_ctor_get(v___x_848_, 6);
                v_extensions_856_ = crate::leanh::lean_ctor_get(v___x_848_, 7);
                v_issues_857_ = crate::leanh::lean_ctor_get(v___x_848_, 8);
                v_canon_858_ = crate::leanh::lean_ctor_get(v___x_848_, 9);
                v_debug_859_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_848_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_871_ = (!crate::leanh::lean_is_exclusive(v___x_848_)) as u8;
                if v_isSharedCheck_871_ == 0 {
                    v___x_861_ = v___x_848_;
                    v_isShared_862_ = v_isSharedCheck_871_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_858_);
                    crate::leanh::lean_inc(v_issues_857_);
                    crate::leanh::lean_inc(v_extensions_856_);
                    crate::leanh::lean_inc(v_defEqI_855_);
                    crate::leanh::lean_inc(v_congrInfo_854_);
                    crate::leanh::lean_inc(v_getLevel_853_);
                    crate::leanh::lean_inc(v_inferType_852_);
                    crate::leanh::lean_inc(v_proofInstInfo_851_);
                    crate::leanh::lean_inc(v_maxFVar_850_);
                    crate::leanh::lean_inc(v_share_849_);
                    crate::leanh::lean_dec(v___x_848_);
                    v___x_861_ = crate::leanh::lean_box(0);
                    v_isShared_862_ = v_isSharedCheck_871_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc(v_a_844_);
                v___x_863_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(v_inferType_852_, v_e_823_, v_a_844_);
                if v_isShared_862_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_861_, 3, v___x_863_);
                    v___x_865_ = v___x_861_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_870_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_870_, 0, v_share_849_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_870_, 1, v_maxFVar_850_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_870_, 2, v_proofInstInfo_851_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_870_, 3, v___x_863_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_870_, 4, v_getLevel_853_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_870_, 5, v_congrInfo_854_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_870_, 6, v_defEqI_855_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_870_, 7, v_extensions_856_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_870_, 8, v_issues_857_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_870_, 9, v_canon_858_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_870_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_859_,
                    );
                    v___x_865_ = v_reuseFailAlloc_870_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_866_ = lean_st_ref_set(v_a_824_, v___x_865_);
                if v_isShared_847_ == 0 {
                    v___x_868_ = v___x_846_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_869_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_869_, 0, v_a_844_);
                    v___x_868_ = v_reuseFailAlloc_869_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_868_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_inferType___redArg___boxed(
    mut v_e_873_: *mut crate::leanh::LeanObject,
    mut v_a_874_: *mut crate::leanh::LeanObject,
    mut v_a_875_: *mut crate::leanh::LeanObject,
    mut v_a_876_: *mut crate::leanh::LeanObject,
    mut v_a_877_: *mut crate::leanh::LeanObject,
    mut v_a_878_: *mut crate::leanh::LeanObject,
    mut v_a_879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_880_ = l_Lean_Meta_Sym_inferType___redArg(
        v_e_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_,
    );
    crate::leanh::lean_dec(v_a_878_);
    crate::leanh::lean_dec_ref(v_a_877_);
    crate::leanh::lean_dec(v_a_876_);
    crate::leanh::lean_dec_ref(v_a_875_);
    crate::leanh::lean_dec(v_a_874_);
    return v_res_880_;
}
pub unsafe fn l_Lean_Meta_Sym_inferType(
    mut v_e_881_: *mut crate::leanh::LeanObject,
    mut v_a_882_: *mut crate::leanh::LeanObject,
    mut v_a_883_: *mut crate::leanh::LeanObject,
    mut v_a_884_: *mut crate::leanh::LeanObject,
    mut v_a_885_: *mut crate::leanh::LeanObject,
    mut v_a_886_: *mut crate::leanh::LeanObject,
    mut v_a_887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_889_ = l_Lean_Meta_Sym_inferType___redArg(
        v_e_881_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_,
    );
    return v___x_889_;
}
pub unsafe fn l_Lean_Meta_Sym_inferType___boxed(
    mut v_e_890_: *mut crate::leanh::LeanObject,
    mut v_a_891_: *mut crate::leanh::LeanObject,
    mut v_a_892_: *mut crate::leanh::LeanObject,
    mut v_a_893_: *mut crate::leanh::LeanObject,
    mut v_a_894_: *mut crate::leanh::LeanObject,
    mut v_a_895_: *mut crate::leanh::LeanObject,
    mut v_a_896_: *mut crate::leanh::LeanObject,
    mut v_a_897_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_898_ = l_Lean_Meta_Sym_inferType(
        v_e_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_,
    );
    crate::leanh::lean_dec(v_a_896_);
    crate::leanh::lean_dec_ref(v_a_895_);
    crate::leanh::lean_dec(v_a_894_);
    crate::leanh::lean_dec_ref(v_a_893_);
    crate::leanh::lean_dec(v_a_892_);
    crate::leanh::lean_dec_ref(v_a_891_);
    return v_res_898_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0(
    mut v_00_u03b2_899_: *mut crate::leanh::LeanObject,
    mut v_x_900_: *mut crate::leanh::LeanObject,
    mut v_x_901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_902_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(
            v_x_900_, v_x_901_,
        );
    return v___x_902_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___boxed(
    mut v_00_u03b2_903_: *mut crate::leanh::LeanObject,
    mut v_x_904_: *mut crate::leanh::LeanObject,
    mut v_x_905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_906_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0(
        v_00_u03b2_903_,
        v_x_904_,
        v_x_905_,
    );
    crate::leanh::lean_dec_ref(v_x_905_);
    crate::leanh::lean_dec_ref(v_x_904_);
    return v_res_906_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1(
    mut v_00_u03b2_907_: *mut crate::leanh::LeanObject,
    mut v_x_908_: *mut crate::leanh::LeanObject,
    mut v_x_909_: *mut crate::leanh::LeanObject,
    mut v_x_910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_911_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(
        v_x_908_, v_x_909_, v_x_910_,
    );
    return v___x_911_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0(
    mut v_00_u03b2_912_: *mut crate::leanh::LeanObject,
    mut v_x_913_: *mut crate::leanh::LeanObject,
    mut v_x_914_: usize,
    mut v_x_915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_916_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___redArg(v_x_913_, v_x_914_, v_x_915_);
    return v___x_916_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0___boxed(
    mut v_00_u03b2_917_: *mut crate::leanh::LeanObject,
    mut v_x_918_: *mut crate::leanh::LeanObject,
    mut v_x_919_: *mut crate::leanh::LeanObject,
    mut v_x_920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_3287__boxed_921_: usize = 0;
    let mut v_res_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_3287__boxed_921_ = crate::leanh::lean_unbox_usize(v_x_919_);
    crate::leanh::lean_dec(v_x_919_);
    v_res_922_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0(v_00_u03b2_917_, v_x_918_, v_x_3287__boxed_921_, v_x_920_);
    crate::leanh::lean_dec_ref(v_x_920_);
    crate::leanh::lean_dec_ref(v_x_918_);
    return v_res_922_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2(
    mut v_00_u03b2_923_: *mut crate::leanh::LeanObject,
    mut v_x_924_: *mut crate::leanh::LeanObject,
    mut v_x_925_: usize,
    mut v_x_926_: usize,
    mut v_x_927_: *mut crate::leanh::LeanObject,
    mut v_x_928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_929_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___redArg(v_x_924_, v_x_925_, v_x_926_, v_x_927_, v_x_928_);
    return v___x_929_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2___boxed(
    mut v_00_u03b2_930_: *mut crate::leanh::LeanObject,
    mut v_x_931_: *mut crate::leanh::LeanObject,
    mut v_x_932_: *mut crate::leanh::LeanObject,
    mut v_x_933_: *mut crate::leanh::LeanObject,
    mut v_x_934_: *mut crate::leanh::LeanObject,
    mut v_x_935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_3298__boxed_936_: usize = 0;
    let mut v_x_3299__boxed_937_: usize = 0;
    let mut v_res_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_3298__boxed_936_ = crate::leanh::lean_unbox_usize(v_x_932_);
    crate::leanh::lean_dec(v_x_932_);
    v_x_3299__boxed_937_ = crate::leanh::lean_unbox_usize(v_x_933_);
    crate::leanh::lean_dec(v_x_933_);
    v_res_938_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2(v_00_u03b2_930_, v_x_931_, v_x_3298__boxed_936_, v_x_3299__boxed_937_, v_x_934_, v_x_935_);
    return v_res_938_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1(
    mut v_00_u03b2_939_: *mut crate::leanh::LeanObject,
    mut v_keys_940_: *mut crate::leanh::LeanObject,
    mut v_vals_941_: *mut crate::leanh::LeanObject,
    mut v_heq_942_: *mut crate::leanh::LeanObject,
    mut v_i_943_: *mut crate::leanh::LeanObject,
    mut v_k_944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_945_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___redArg(v_keys_940_, v_vals_941_, v_i_943_, v_k_944_);
    return v___x_945_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_946_: *mut crate::leanh::LeanObject,
    mut v_keys_947_: *mut crate::leanh::LeanObject,
    mut v_vals_948_: *mut crate::leanh::LeanObject,
    mut v_heq_949_: *mut crate::leanh::LeanObject,
    mut v_i_950_: *mut crate::leanh::LeanObject,
    mut v_k_951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_952_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0_spec__0_spec__1(v_00_u03b2_946_, v_keys_947_, v_vals_948_, v_heq_949_, v_i_950_, v_k_951_);
    crate::leanh::lean_dec_ref(v_k_951_);
    crate::leanh::lean_dec_ref(v_vals_948_);
    crate::leanh::lean_dec_ref(v_keys_947_);
    return v_res_952_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4(
    mut v_00_u03b2_953_: *mut crate::leanh::LeanObject,
    mut v_n_954_: *mut crate::leanh::LeanObject,
    mut v_k_955_: *mut crate::leanh::LeanObject,
    mut v_v_956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_957_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4___redArg(v_n_954_, v_k_955_, v_v_956_);
    return v___x_957_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5(
    mut v_00_u03b2_958_: *mut crate::leanh::LeanObject,
    mut v_depth_959_: usize,
    mut v_keys_960_: *mut crate::leanh::LeanObject,
    mut v_vals_961_: *mut crate::leanh::LeanObject,
    mut v_heq_962_: *mut crate::leanh::LeanObject,
    mut v_i_963_: *mut crate::leanh::LeanObject,
    mut v_entries_964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_965_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___redArg(v_depth_959_, v_keys_960_, v_vals_961_, v_i_963_, v_entries_964_);
    return v___x_965_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_966_: *mut crate::leanh::LeanObject,
    mut v_depth_967_: *mut crate::leanh::LeanObject,
    mut v_keys_968_: *mut crate::leanh::LeanObject,
    mut v_vals_969_: *mut crate::leanh::LeanObject,
    mut v_heq_970_: *mut crate::leanh::LeanObject,
    mut v_i_971_: *mut crate::leanh::LeanObject,
    mut v_entries_972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_973_: usize = 0;
    let mut v_res_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_973_ = crate::leanh::lean_unbox_usize(v_depth_967_);
    crate::leanh::lean_dec(v_depth_967_);
    v_res_974_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__5(v_00_u03b2_966_, v_depth_boxed_973_, v_keys_968_, v_vals_969_, v_heq_970_, v_i_971_, v_entries_972_);
    crate::leanh::lean_dec_ref(v_vals_969_);
    crate::leanh::lean_dec_ref(v_keys_968_);
    return v_res_974_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5(
    mut v_00_u03b2_975_: *mut crate::leanh::LeanObject,
    mut v_x_976_: *mut crate::leanh::LeanObject,
    mut v_x_977_: *mut crate::leanh::LeanObject,
    mut v_x_978_: *mut crate::leanh::LeanObject,
    mut v_x_979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_980_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1_spec__2_spec__4_spec__5___redArg(v_x_976_, v_x_977_, v_x_978_, v_x_979_);
    return v___x_980_;
}
pub unsafe fn l_Lean_Meta_Sym_getLevel___redArg(
    mut v_type_981_: *mut crate::leanh::LeanObject,
    mut v_a_982_: *mut crate::leanh::LeanObject,
    mut v_a_983_: *mut crate::leanh::LeanObject,
    mut v_a_984_: *mut crate::leanh::LeanObject,
    mut v_a_985_: *mut crate::leanh::LeanObject,
    mut v_a_986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_994_: u8 = 0;
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_998_: u8 = 0;
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1003_: u8 = 0;
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_share_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxFVar_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proofInstInfo_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inferType_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_getLevel_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_congrInfo_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqI_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_extensions_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_issues_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canon_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_debug_1015_: u8 = 0;
    let mut v___x_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1018_: u8 = 0;
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1027_: u8 = 0;
    let mut v_isSharedCheck_1028_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_988_ = lean_st_ref_get(v_a_982_);
                v_getLevel_989_ = crate::leanh::lean_ctor_get(v___x_988_, 4);
                crate::leanh::lean_inc_ref(v_getLevel_989_);
                crate::leanh::lean_dec(v___x_988_);
                v___x_990_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Sym_inferType_spec__0___redArg(v_getLevel_989_, v_type_981_);
                crate::leanh::lean_dec_ref(v_getLevel_989_);
                if crate::leanh::lean_obj_tag(v___x_990_) == 1 {
                    crate::leanh::lean_dec_ref(v_type_981_);
                    v_val_991_ = crate::leanh::lean_ctor_get(v___x_990_, 0);
                    v_isSharedCheck_998_ = (!crate::leanh::lean_is_exclusive(v___x_990_)) as u8;
                    if v_isSharedCheck_998_ == 0 {
                        v___x_993_ = v___x_990_;
                        v_isShared_994_ = v_isSharedCheck_998_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_991_);
                        crate::leanh::lean_dec(v___x_990_);
                        v___x_993_ = crate::leanh::lean_box(0);
                        v_isShared_994_ = v_isSharedCheck_998_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_990_);
                    crate::leanh::lean_inc_ref(v_type_981_);
                    v___x_999_ =
                        l___private_Lean_Meta_Sym_InferType_0__Lean_Meta_Sym_getLevelWithoutCache(
                            v_type_981_,
                            v_a_983_,
                            v_a_984_,
                            v_a_985_,
                            v_a_986_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_999_) == 0 {
                        v_a_1000_ = crate::leanh::lean_ctor_get(v___x_999_, 0);
                        v_isSharedCheck_1028_ =
                            (!crate::leanh::lean_is_exclusive(v___x_999_)) as u8;
                        if v_isSharedCheck_1028_ == 0 {
                            v___x_1002_ = v___x_999_;
                            v_isShared_1003_ = v_isSharedCheck_1028_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1000_);
                            crate::leanh::lean_dec(v___x_999_);
                            v___x_1002_ = crate::leanh::lean_box(0);
                            v_isShared_1003_ = v_isSharedCheck_1028_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_type_981_);
                        return v___x_999_;
                    }
                }
            }
            1 => {
                if v_isShared_994_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_993_, 0);
                    v___x_996_ = v___x_993_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_997_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_997_, 0, v_val_991_);
                    v___x_996_ = v_reuseFailAlloc_997_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_996_;
            }
            3 => {
                v___x_1004_ = lean_st_ref_take(v_a_982_);
                v_share_1005_ = crate::leanh::lean_ctor_get(v___x_1004_, 0);
                v_maxFVar_1006_ = crate::leanh::lean_ctor_get(v___x_1004_, 1);
                v_proofInstInfo_1007_ = crate::leanh::lean_ctor_get(v___x_1004_, 2);
                v_inferType_1008_ = crate::leanh::lean_ctor_get(v___x_1004_, 3);
                v_getLevel_1009_ = crate::leanh::lean_ctor_get(v___x_1004_, 4);
                v_congrInfo_1010_ = crate::leanh::lean_ctor_get(v___x_1004_, 5);
                v_defEqI_1011_ = crate::leanh::lean_ctor_get(v___x_1004_, 6);
                v_extensions_1012_ = crate::leanh::lean_ctor_get(v___x_1004_, 7);
                v_issues_1013_ = crate::leanh::lean_ctor_get(v___x_1004_, 8);
                v_canon_1014_ = crate::leanh::lean_ctor_get(v___x_1004_, 9);
                v_debug_1015_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_1004_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                );
                v_isSharedCheck_1027_ = (!crate::leanh::lean_is_exclusive(v___x_1004_)) as u8;
                if v_isSharedCheck_1027_ == 0 {
                    v___x_1017_ = v___x_1004_;
                    v_isShared_1018_ = v_isSharedCheck_1027_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_canon_1014_);
                    crate::leanh::lean_inc(v_issues_1013_);
                    crate::leanh::lean_inc(v_extensions_1012_);
                    crate::leanh::lean_inc(v_defEqI_1011_);
                    crate::leanh::lean_inc(v_congrInfo_1010_);
                    crate::leanh::lean_inc(v_getLevel_1009_);
                    crate::leanh::lean_inc(v_inferType_1008_);
                    crate::leanh::lean_inc(v_proofInstInfo_1007_);
                    crate::leanh::lean_inc(v_maxFVar_1006_);
                    crate::leanh::lean_inc(v_share_1005_);
                    crate::leanh::lean_dec(v___x_1004_);
                    v___x_1017_ = crate::leanh::lean_box(0);
                    v_isShared_1018_ = v_isSharedCheck_1027_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc(v_a_1000_);
                v___x_1019_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Sym_inferType_spec__1___redArg(v_getLevel_1009_, v_type_981_, v_a_1000_);
                if v_isShared_1018_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1017_, 4, v___x_1019_);
                    v___x_1021_ = v___x_1017_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1026_ = crate::leanh::lean_alloc_ctor(0, 10, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1026_, 0, v_share_1005_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1026_, 1, v_maxFVar_1006_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1026_, 2, v_proofInstInfo_1007_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1026_, 3, v_inferType_1008_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1026_, 4, v___x_1019_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1026_, 5, v_congrInfo_1010_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1026_, 6, v_defEqI_1011_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1026_, 7, v_extensions_1012_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1026_, 8, v_issues_1013_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1026_, 9, v_canon_1014_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1026_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 10) as u32,
                        v_debug_1015_,
                    );
                    v___x_1021_ = v_reuseFailAlloc_1026_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1022_ = lean_st_ref_set(v_a_982_, v___x_1021_);
                if v_isShared_1003_ == 0 {
                    v___x_1024_ = v___x_1002_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1025_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1025_, 0, v_a_1000_);
                    v___x_1024_ = v_reuseFailAlloc_1025_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1024_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_getLevel___redArg___boxed(
    mut v_type_1029_: *mut crate::leanh::LeanObject,
    mut v_a_1030_: *mut crate::leanh::LeanObject,
    mut v_a_1031_: *mut crate::leanh::LeanObject,
    mut v_a_1032_: *mut crate::leanh::LeanObject,
    mut v_a_1033_: *mut crate::leanh::LeanObject,
    mut v_a_1034_: *mut crate::leanh::LeanObject,
    mut v_a_1035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1036_ = l_Lean_Meta_Sym_getLevel___redArg(
        v_type_1029_,
        v_a_1030_,
        v_a_1031_,
        v_a_1032_,
        v_a_1033_,
        v_a_1034_,
    );
    crate::leanh::lean_dec(v_a_1034_);
    crate::leanh::lean_dec_ref(v_a_1033_);
    crate::leanh::lean_dec(v_a_1032_);
    crate::leanh::lean_dec_ref(v_a_1031_);
    crate::leanh::lean_dec(v_a_1030_);
    return v_res_1036_;
}
pub unsafe fn l_Lean_Meta_Sym_getLevel(
    mut v_type_1037_: *mut crate::leanh::LeanObject,
    mut v_a_1038_: *mut crate::leanh::LeanObject,
    mut v_a_1039_: *mut crate::leanh::LeanObject,
    mut v_a_1040_: *mut crate::leanh::LeanObject,
    mut v_a_1041_: *mut crate::leanh::LeanObject,
    mut v_a_1042_: *mut crate::leanh::LeanObject,
    mut v_a_1043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1045_ = l_Lean_Meta_Sym_getLevel___redArg(
        v_type_1037_,
        v_a_1039_,
        v_a_1040_,
        v_a_1041_,
        v_a_1042_,
        v_a_1043_,
    );
    return v___x_1045_;
}
pub unsafe fn l_Lean_Meta_Sym_getLevel___boxed(
    mut v_type_1046_: *mut crate::leanh::LeanObject,
    mut v_a_1047_: *mut crate::leanh::LeanObject,
    mut v_a_1048_: *mut crate::leanh::LeanObject,
    mut v_a_1049_: *mut crate::leanh::LeanObject,
    mut v_a_1050_: *mut crate::leanh::LeanObject,
    mut v_a_1051_: *mut crate::leanh::LeanObject,
    mut v_a_1052_: *mut crate::leanh::LeanObject,
    mut v_a_1053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1054_ = l_Lean_Meta_Sym_getLevel(
        v_type_1046_,
        v_a_1047_,
        v_a_1048_,
        v_a_1049_,
        v_a_1050_,
        v_a_1051_,
        v_a_1052_,
    );
    crate::leanh::lean_dec(v_a_1052_);
    crate::leanh::lean_dec_ref(v_a_1051_);
    crate::leanh::lean_dec(v_a_1050_);
    crate::leanh::lean_dec_ref(v_a_1049_);
    crate::leanh::lean_dec(v_a_1048_);
    crate::leanh::lean_dec_ref(v_a_1047_);
    return v_res_1054_;
}
pub unsafe fn l_Lean_Meta_Sym_mkEqRefl___redArg(
    mut v_e_1060_: *mut crate::leanh::LeanObject,
    mut v_a_1061_: *mut crate::leanh::LeanObject,
    mut v_a_1062_: *mut crate::leanh::LeanObject,
    mut v_a_1063_: *mut crate::leanh::LeanObject,
    mut v_a_1064_: *mut crate::leanh::LeanObject,
    mut v_a_1065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1073_: u8 = 0;
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1082_: u8 = 0;
    let mut v_a_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1086_: u8 = 0;
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1090_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_e_1060_);
                v___x_1067_ = l_Lean_Meta_Sym_inferType___redArg(
                    v_e_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_,
                );
                if crate::leanh::lean_obj_tag(v___x_1067_) == 0 {
                    v_a_1068_ = crate::leanh::lean_ctor_get(v___x_1067_, 0);
                    crate::leanh::lean_inc_n(v_a_1068_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1067_, 1);
                    v___x_1069_ = l_Lean_Meta_Sym_getLevel___redArg(
                        v_a_1068_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1069_) == 0 {
                        v_a_1070_ = crate::leanh::lean_ctor_get(v___x_1069_, 0);
                        v_isSharedCheck_1082_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1069_)) as u8;
                        if v_isSharedCheck_1082_ == 0 {
                            v___x_1072_ = v___x_1069_;
                            v_isShared_1073_ = v_isSharedCheck_1082_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1070_);
                            crate::leanh::lean_dec(v___x_1069_);
                            v___x_1072_ = crate::leanh::lean_box(0);
                            v_isShared_1073_ = v_isSharedCheck_1082_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1068_);
                        crate::leanh::lean_dec_ref(v_e_1060_);
                        v_a_1083_ = crate::leanh::lean_ctor_get(v___x_1069_, 0);
                        v_isSharedCheck_1090_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1069_)) as u8;
                        if v_isSharedCheck_1090_ == 0 {
                            v___x_1085_ = v___x_1069_;
                            v_isShared_1086_ = v_isSharedCheck_1090_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1083_);
                            crate::leanh::lean_dec(v___x_1069_);
                            v___x_1085_ = crate::leanh::lean_box(0);
                            v_isShared_1086_ = v_isSharedCheck_1090_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1060_);
                    return v___x_1067_;
                }
            }
            1 => {
                v___x_1074_ = l_Lean_Meta_Sym_mkEqRefl___redArg___closed__2;
                v___x_1075_ = crate::leanh::lean_box(0);
                v___x_1076_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1076_, 0, v_a_1070_);
                crate::leanh::lean_ctor_set(v___x_1076_, 1, v___x_1075_);
                v___x_1077_ = l_Lean_mkConst(v___x_1074_, v___x_1076_);
                v___x_1078_ = l_Lean_mkAppB(v___x_1077_, v_a_1068_, v_e_1060_);
                if v_isShared_1073_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1072_, 0, v___x_1078_);
                    v___x_1080_ = v___x_1072_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1081_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
                    v___x_1080_ = v_reuseFailAlloc_1081_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1080_;
            }
            3 => {
                if v_isShared_1086_ == 0 {
                    v___x_1088_ = v___x_1085_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1089_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1089_, 0, v_a_1083_);
                    v___x_1088_ = v_reuseFailAlloc_1089_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1088_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_mkEqRefl___redArg___boxed(
    mut v_e_1091_: *mut crate::leanh::LeanObject,
    mut v_a_1092_: *mut crate::leanh::LeanObject,
    mut v_a_1093_: *mut crate::leanh::LeanObject,
    mut v_a_1094_: *mut crate::leanh::LeanObject,
    mut v_a_1095_: *mut crate::leanh::LeanObject,
    mut v_a_1096_: *mut crate::leanh::LeanObject,
    mut v_a_1097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1098_ = l_Lean_Meta_Sym_mkEqRefl___redArg(
        v_e_1091_, v_a_1092_, v_a_1093_, v_a_1094_, v_a_1095_, v_a_1096_,
    );
    crate::leanh::lean_dec(v_a_1096_);
    crate::leanh::lean_dec_ref(v_a_1095_);
    crate::leanh::lean_dec(v_a_1094_);
    crate::leanh::lean_dec_ref(v_a_1093_);
    crate::leanh::lean_dec(v_a_1092_);
    return v_res_1098_;
}
pub unsafe fn l_Lean_Meta_Sym_mkEqRefl(
    mut v_e_1099_: *mut crate::leanh::LeanObject,
    mut v_a_1100_: *mut crate::leanh::LeanObject,
    mut v_a_1101_: *mut crate::leanh::LeanObject,
    mut v_a_1102_: *mut crate::leanh::LeanObject,
    mut v_a_1103_: *mut crate::leanh::LeanObject,
    mut v_a_1104_: *mut crate::leanh::LeanObject,
    mut v_a_1105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1107_ = l_Lean_Meta_Sym_mkEqRefl___redArg(
        v_e_1099_, v_a_1101_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_,
    );
    return v___x_1107_;
}
pub unsafe fn l_Lean_Meta_Sym_mkEqRefl___boxed(
    mut v_e_1108_: *mut crate::leanh::LeanObject,
    mut v_a_1109_: *mut crate::leanh::LeanObject,
    mut v_a_1110_: *mut crate::leanh::LeanObject,
    mut v_a_1111_: *mut crate::leanh::LeanObject,
    mut v_a_1112_: *mut crate::leanh::LeanObject,
    mut v_a_1113_: *mut crate::leanh::LeanObject,
    mut v_a_1114_: *mut crate::leanh::LeanObject,
    mut v_a_1115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1116_ = l_Lean_Meta_Sym_mkEqRefl(
        v_e_1108_, v_a_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_,
    );
    crate::leanh::lean_dec(v_a_1114_);
    crate::leanh::lean_dec_ref(v_a_1113_);
    crate::leanh::lean_dec(v_a_1112_);
    crate::leanh::lean_dec_ref(v_a_1111_);
    crate::leanh::lean_dec(v_a_1110_);
    crate::leanh::lean_dec_ref(v_a_1109_);
    return v_res_1116_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_InferType(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_SymM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_InferType(
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
pub unsafe fn initialize_Lean_Meta_Sym_InferType(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_SymM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_InferType(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_InferType(builtin);
}

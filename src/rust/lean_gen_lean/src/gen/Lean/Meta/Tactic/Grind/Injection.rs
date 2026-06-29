// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Injection
// Imports: Lean.Meta.Basic Lean.Meta.Tactic.Clear Lean.Meta.AppBuilder Lean.Meta.CtorRecognizer
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_headBeta, l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_Expr_mvarId_x21,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_mkFVar,
};
use crate::r#gen::Lean::LocalContext::l_Lean_LocalDecl_type;
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkNoConfusion,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l_Lean_FVarId_getDecl___redArg, l_Lean_Meta_whnfD, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::CtorRecognizer::{
    initialize_Lean_Meta_CtorRecognizer, l_Lean_Meta_isConstructorAppCore_x3f___redArg,
    runtime_initialize_Lean_Meta_CtorRecognizer,
};
use crate::r#gen::Lean::Meta::Tactic::Clear::{
    initialize_Lean_Meta_Tactic_Clear, l_Lean_MVarId_tryClear,
    runtime_initialize_Lean_Meta_Tactic_Clear,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getTag, l_Lean_MVarId_getType, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_name_eq,
    lean_nat_add, lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_set, lean_st_ref_take};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16122875713692181903 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1___redArg(
    mut v_mvarId_526_: *mut crate::leanh::LeanObject,
    mut v_x_527_: *mut crate::leanh::LeanObject,
    mut v___y_528_: *mut crate::leanh::LeanObject,
    mut v___y_529_: *mut crate::leanh::LeanObject,
    mut v___y_530_: *mut crate::leanh::LeanObject,
    mut v___y_531_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_537_: u8 = 0;
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_541_: u8 = 0;
    let mut v_a_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_545_: u8 = 0;
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_549_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_533_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_526_,
                    v_x_527_,
                    v___y_528_,
                    v___y_529_,
                    v___y_530_,
                    v___y_531_,
                );
                if crate::leanh::lean_obj_tag(v___x_533_) == 0 {
                    v_a_534_ = crate::leanh::lean_ctor_get(v___x_533_, 0);
                    v_isSharedCheck_541_ = (!crate::leanh::lean_is_exclusive(v___x_533_)) as u8;
                    if v_isSharedCheck_541_ == 0 {
                        v___x_536_ = v___x_533_;
                        v_isShared_537_ = v_isSharedCheck_541_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_534_);
                        crate::leanh::lean_dec(v___x_533_);
                        v___x_536_ = crate::leanh::lean_box(0);
                        v_isShared_537_ = v_isSharedCheck_541_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_542_ = crate::leanh::lean_ctor_get(v___x_533_, 0);
                    v_isSharedCheck_549_ = (!crate::leanh::lean_is_exclusive(v___x_533_)) as u8;
                    if v_isSharedCheck_549_ == 0 {
                        v___x_544_ = v___x_533_;
                        v_isShared_545_ = v_isSharedCheck_549_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_542_);
                        crate::leanh::lean_dec(v___x_533_);
                        v___x_544_ = crate::leanh::lean_box(0);
                        v_isShared_545_ = v_isSharedCheck_549_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_537_ == 0 {
                    v___x_539_ = v___x_536_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_540_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
                    v___x_539_ = v_reuseFailAlloc_540_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_539_;
            }
            3 => {
                if v_isShared_545_ == 0 {
                    v___x_547_ = v___x_544_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_548_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
                    v___x_547_ = v_reuseFailAlloc_548_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_547_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1___redArg___boxed(
    mut v_mvarId_550_: *mut crate::leanh::LeanObject,
    mut v_x_551_: *mut crate::leanh::LeanObject,
    mut v___y_552_: *mut crate::leanh::LeanObject,
    mut v___y_553_: *mut crate::leanh::LeanObject,
    mut v___y_554_: *mut crate::leanh::LeanObject,
    mut v___y_555_: *mut crate::leanh::LeanObject,
    mut v___y_556_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_557_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1___redArg(
        v_mvarId_550_,
        v_x_551_,
        v___y_552_,
        v___y_553_,
        v___y_554_,
        v___y_555_,
    );
    crate::leanh::lean_dec(v___y_555_);
    crate::leanh::lean_dec_ref(v___y_554_);
    crate::leanh::lean_dec(v___y_553_);
    crate::leanh::lean_dec_ref(v___y_552_);
    return v_res_557_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1(
    mut v_00_u03b1_558_: *mut crate::leanh::LeanObject,
    mut v_mvarId_559_: *mut crate::leanh::LeanObject,
    mut v_x_560_: *mut crate::leanh::LeanObject,
    mut v___y_561_: *mut crate::leanh::LeanObject,
    mut v___y_562_: *mut crate::leanh::LeanObject,
    mut v___y_563_: *mut crate::leanh::LeanObject,
    mut v___y_564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_566_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1___redArg(
        v_mvarId_559_,
        v_x_560_,
        v___y_561_,
        v___y_562_,
        v___y_563_,
        v___y_564_,
    );
    return v___x_566_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1___boxed(
    mut v_00_u03b1_567_: *mut crate::leanh::LeanObject,
    mut v_mvarId_568_: *mut crate::leanh::LeanObject,
    mut v_x_569_: *mut crate::leanh::LeanObject,
    mut v___y_570_: *mut crate::leanh::LeanObject,
    mut v___y_571_: *mut crate::leanh::LeanObject,
    mut v___y_572_: *mut crate::leanh::LeanObject,
    mut v___y_573_: *mut crate::leanh::LeanObject,
    mut v___y_574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_575_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1(
        v_00_u03b1_567_,
        v_mvarId_568_,
        v_x_569_,
        v___y_570_,
        v___y_571_,
        v___y_572_,
        v___y_573_,
    );
    crate::leanh::lean_dec(v___y_573_);
    crate::leanh::lean_dec_ref(v___y_572_);
    crate::leanh::lean_dec(v___y_571_);
    crate::leanh::lean_dec_ref(v___y_570_);
    return v_res_575_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(
    mut v_x_576_: *mut crate::leanh::LeanObject,
    mut v_x_577_: *mut crate::leanh::LeanObject,
    mut v_x_578_: *mut crate::leanh::LeanObject,
    mut v_x_579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_584_: u8 = 0;
    let mut v___x_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_586_: u8 = 0;
    let mut v___x_587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: u8 = 0;
    let mut v___x_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_580_ = crate::leanh::lean_ctor_get(v_x_576_, 0);
                v_vs_581_ = crate::leanh::lean_ctor_get(v_x_576_, 1);
                v_isSharedCheck_605_ = (!crate::leanh::lean_is_exclusive(v_x_576_)) as u8;
                if v_isSharedCheck_605_ == 0 {
                    v___x_583_ = v_x_576_;
                    v_isShared_584_ = v_isSharedCheck_605_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_581_);
                    crate::leanh::lean_inc(v_ks_580_);
                    crate::leanh::lean_dec(v_x_576_);
                    v___x_583_ = crate::leanh::lean_box(0);
                    v_isShared_584_ = v_isSharedCheck_605_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_585_ = lean_array_get_size(v_ks_580_);
                v___x_586_ = lean_nat_dec_lt(v_x_577_, v___x_585_);
                if v___x_586_ == 0 {
                    crate::leanh::lean_dec(v_x_577_);
                    v___x_587_ = lean_array_push(v_ks_580_, v_x_578_);
                    v___x_588_ = lean_array_push(v_vs_581_, v_x_579_);
                    if v_isShared_584_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_583_, 1, v___x_588_);
                        crate::leanh::lean_ctor_set(v___x_583_, 0, v___x_587_);
                        v___x_590_ = v___x_583_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_591_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_587_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_591_, 1, v___x_588_);
                        v___x_590_ = v_reuseFailAlloc_591_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_592_ = lean_array_fget_borrowed(v_ks_580_, v_x_577_);
                    v___x_593_ = l_Lean_instBEqMVarId_beq(v_x_578_, v_k_x27_592_);
                    if v___x_593_ == 0 {
                        if v_isShared_584_ == 0 {
                            v___x_595_ = v___x_583_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_599_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_599_, 0, v_ks_580_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_599_, 1, v_vs_581_);
                            v___x_595_ = v_reuseFailAlloc_599_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_600_ = lean_array_fset(v_ks_580_, v_x_577_, v_x_578_);
                        v___x_601_ = lean_array_fset(v_vs_581_, v_x_577_, v_x_579_);
                        crate::leanh::lean_dec(v_x_577_);
                        if v_isShared_584_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_583_, 1, v___x_601_);
                            crate::leanh::lean_ctor_set(v___x_583_, 0, v___x_600_);
                            v___x_603_ = v___x_583_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_604_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_600_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_604_, 1, v___x_601_);
                            v___x_603_ = v_reuseFailAlloc_604_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_590_;
            }
            3 => {
                v___x_596_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_597_ = lean_nat_add(v_x_577_, v___x_596_);
                crate::leanh::lean_dec(v_x_577_);
                v_x_576_ = v___x_595_;
                v_x_577_ = v___x_597_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_603_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_n_606_: *mut crate::leanh::LeanObject,
    mut v_k_607_: *mut crate::leanh::LeanObject,
    mut v_v_608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_609_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_610_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_606_, v___x_609_, v_k_607_, v_v_608_);
    return v___x_610_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_611_: usize = 0;
    let mut v___x_612_: usize = 0;
    let mut v___x_613_: usize = 0;
    v___x_611_ = 5usize;
    v___x_612_ = 1usize;
    v___x_613_ = lean_usize_shift_left(v___x_612_, v___x_611_);
    return v___x_613_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_614_: usize = 0;
    let mut v___x_615_: usize = 0;
    let mut v___x_616_: usize = 0;
    v___x_614_ = 1usize;
    v___x_615_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__0);
    v___x_616_ = lean_usize_sub(v___x_615_, v___x_614_);
    return v___x_616_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_617_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_617_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg(
    mut v_x_618_: *mut crate::leanh::LeanObject,
    mut v_x_619_: usize,
    mut v_x_620_: usize,
    mut v_x_621_: *mut crate::leanh::LeanObject,
    mut v_x_622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_624_: usize = 0;
    let mut v___x_625_: usize = 0;
    let mut v___x_626_: usize = 0;
    let mut v___x_627_: usize = 0;
    let mut v_j_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: u8 = 0;
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_633_: u8 = 0;
    let mut v_v_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_647_: u8 = 0;
    let mut v___x_648_: u8 = 0;
    let mut v___x_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_654_: u8 = 0;
    let mut v_node_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_658_: u8 = 0;
    let mut v___x_659_: usize = 0;
    let mut v___x_660_: usize = 0;
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_665_: u8 = 0;
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_667_: u8 = 0;
    let mut v_unused_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_673_: u8 = 0;
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_678_: u8 = 0;
    let mut v_ks_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_684_: usize = 0;
    let mut v___x_685_: u8 = 0;
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: u8 = 0;
    let mut v_reuseFailAlloc_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_690_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_618_) == 0 {
                    v_es_623_ = crate::leanh::lean_ctor_get(v_x_618_, 0);
                    v___x_624_ = 5usize;
                    v___x_625_ = 1usize;
                    v___x_626_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_627_ = lean_usize_land(v_x_619_, v___x_626_);
                    v_j_628_ = lean_usize_to_nat(v___x_627_);
                    v___x_629_ = lean_array_get_size(v_es_623_);
                    v___x_630_ = lean_nat_dec_lt(v_j_628_, v___x_629_);
                    if v___x_630_ == 0 {
                        crate::leanh::lean_dec(v_j_628_);
                        crate::leanh::lean_dec(v_x_622_);
                        crate::leanh::lean_dec(v_x_621_);
                        return v_x_618_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_623_);
                        v_isSharedCheck_667_ = (!crate::leanh::lean_is_exclusive(v_x_618_)) as u8;
                        if v_isSharedCheck_667_ == 0 {
                            v_unused_668_ = crate::leanh::lean_ctor_get(v_x_618_, 0);
                            crate::leanh::lean_dec(v_unused_668_);
                            v___x_632_ = v_x_618_;
                            v_isShared_633_ = v_isSharedCheck_667_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_618_);
                            v___x_632_ = crate::leanh::lean_box(0);
                            v_isShared_633_ = v_isSharedCheck_667_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_669_ = crate::leanh::lean_ctor_get(v_x_618_, 0);
                    v_vs_670_ = crate::leanh::lean_ctor_get(v_x_618_, 1);
                    v_isSharedCheck_690_ = (!crate::leanh::lean_is_exclusive(v_x_618_)) as u8;
                    if v_isSharedCheck_690_ == 0 {
                        v___x_672_ = v_x_618_;
                        v_isShared_673_ = v_isSharedCheck_690_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_670_);
                        crate::leanh::lean_inc(v_ks_669_);
                        crate::leanh::lean_dec(v_x_618_);
                        v___x_672_ = crate::leanh::lean_box(0);
                        v_isShared_673_ = v_isSharedCheck_690_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_634_ = lean_array_fget(v_es_623_, v_j_628_);
                v___x_635_ = crate::leanh::lean_box(0);
                v_xs_x27_636_ = lean_array_fset(v_es_623_, v_j_628_, v___x_635_);
                match crate::leanh::lean_obj_tag(v_v_634_) {
                    0 => {
                        v_key_643_ = crate::leanh::lean_ctor_get(v_v_634_, 0);
                        v_val_644_ = crate::leanh::lean_ctor_get(v_v_634_, 1);
                        v_isSharedCheck_654_ = (!crate::leanh::lean_is_exclusive(v_v_634_)) as u8;
                        if v_isSharedCheck_654_ == 0 {
                            v___x_646_ = v_v_634_;
                            v_isShared_647_ = v_isSharedCheck_654_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_644_);
                            crate::leanh::lean_inc(v_key_643_);
                            crate::leanh::lean_dec(v_v_634_);
                            v___x_646_ = crate::leanh::lean_box(0);
                            v_isShared_647_ = v_isSharedCheck_654_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_655_ = crate::leanh::lean_ctor_get(v_v_634_, 0);
                        v_isSharedCheck_665_ = (!crate::leanh::lean_is_exclusive(v_v_634_)) as u8;
                        if v_isSharedCheck_665_ == 0 {
                            v___x_657_ = v_v_634_;
                            v_isShared_658_ = v_isSharedCheck_665_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_655_);
                            crate::leanh::lean_dec(v_v_634_);
                            v___x_657_ = crate::leanh::lean_box(0);
                            v_isShared_658_ = v_isSharedCheck_665_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_666_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_666_, 0, v_x_621_);
                        crate::leanh::lean_ctor_set(v___x_666_, 1, v_x_622_);
                        v___y_638_ = v___x_666_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_639_ = lean_array_fset(v_xs_x27_636_, v_j_628_, v___y_638_);
                crate::leanh::lean_dec(v_j_628_);
                if v_isShared_633_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_632_, 0, v___x_639_);
                    v___x_641_ = v___x_632_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_642_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
                    v___x_641_ = v_reuseFailAlloc_642_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_641_;
            }
            4 => {
                v___x_648_ = l_Lean_instBEqMVarId_beq(v_x_621_, v_key_643_);
                if v___x_648_ == 0 {
                    crate::leanh::lean_del_object(v___x_646_);
                    v___x_649_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_643_, v_val_644_, v_x_621_, v_x_622_,
                    );
                    v___x_650_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_650_, 0, v___x_649_);
                    v___y_638_ = v___x_650_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_644_);
                    crate::leanh::lean_dec(v_key_643_);
                    if v_isShared_647_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_646_, 1, v_x_622_);
                        crate::leanh::lean_ctor_set(v___x_646_, 0, v_x_621_);
                        v___x_652_ = v___x_646_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_653_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_653_, 0, v_x_621_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_653_, 1, v_x_622_);
                        v___x_652_ = v_reuseFailAlloc_653_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_638_ = v___x_652_;
                state = 2;
                continue;
            }
            6 => {
                v___x_659_ = lean_usize_shift_right(v_x_619_, v___x_624_);
                v___x_660_ = lean_usize_add(v_x_620_, v___x_625_);
                v___x_661_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg(v_node_655_, v___x_659_, v___x_660_, v_x_621_, v_x_622_);
                if v_isShared_658_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_657_, 0, v___x_661_);
                    v___x_663_ = v___x_657_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_664_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
                    v___x_663_ = v_reuseFailAlloc_664_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_638_ = v___x_663_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_673_ == 0 {
                    v___x_675_ = v___x_672_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_689_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_689_, 0, v_ks_669_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_689_, 1, v_vs_670_);
                    v___x_675_ = v_reuseFailAlloc_689_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_676_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3___redArg(v___x_675_, v_x_621_, v_x_622_);
                v___x_684_ = 7usize;
                v___x_685_ = lean_usize_dec_le(v___x_684_, v_x_620_);
                if v___x_685_ == 0 {
                    v___x_686_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_676_);
                    v___x_687_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_688_ = lean_nat_dec_lt(v___x_686_, v___x_687_);
                    crate::leanh::lean_dec(v___x_686_);
                    v___y_678_ = v___x_688_;
                    state = 10;
                    continue;
                } else {
                    v___y_678_ = v___x_685_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_678_ == 0 {
                    v_ks_679_ = crate::leanh::lean_ctor_get(v_newNode_676_, 0);
                    crate::leanh::lean_inc_ref(v_ks_679_);
                    v_vs_680_ = crate::leanh::lean_ctor_get(v_newNode_676_, 1);
                    crate::leanh::lean_inc_ref(v_vs_680_);
                    crate::leanh::lean_dec_ref(v_newNode_676_);
                    v___x_681_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_682_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__2);
                    v___x_683_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_x_620_, v_ks_679_, v_vs_680_, v___x_681_, v___x_682_);
                    crate::leanh::lean_dec_ref(v_vs_680_);
                    crate::leanh::lean_dec_ref(v_ks_679_);
                    return v___x_683_;
                } else {
                    return v_newNode_676_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_depth_691_: usize,
    mut v_keys_692_: *mut crate::leanh::LeanObject,
    mut v_vals_693_: *mut crate::leanh::LeanObject,
    mut v_i_694_: *mut crate::leanh::LeanObject,
    mut v_entries_695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: u8 = 0;
    let mut v_k_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: u64 = 0;
    let mut v_h_701_: usize = 0;
    let mut v___x_702_: usize = 0;
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: usize = 0;
    let mut v___x_705_: usize = 0;
    let mut v___x_706_: usize = 0;
    let mut v_h_707_: usize = 0;
    let mut v___x_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_696_ = lean_array_get_size(v_keys_692_);
                v___x_697_ = lean_nat_dec_lt(v_i_694_, v___x_696_);
                if v___x_697_ == 0 {
                    crate::leanh::lean_dec(v_i_694_);
                    return v_entries_695_;
                } else {
                    v_k_698_ = lean_array_fget_borrowed(v_keys_692_, v_i_694_);
                    v_v_699_ = lean_array_fget_borrowed(v_vals_693_, v_i_694_);
                    v___x_700_ = l_Lean_instHashableMVarId_hash(v_k_698_);
                    v_h_701_ = lean_uint64_to_usize(v___x_700_);
                    v___x_702_ = 5usize;
                    v___x_703_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_704_ = 1usize;
                    v___x_705_ = lean_usize_sub(v_depth_691_, v___x_704_);
                    v___x_706_ = lean_usize_mul(v___x_702_, v___x_705_);
                    v_h_707_ = lean_usize_shift_right(v_h_701_, v___x_706_);
                    v___x_708_ = lean_nat_add(v_i_694_, v___x_703_);
                    crate::leanh::lean_dec(v_i_694_);
                    crate::leanh::lean_inc(v_v_699_);
                    crate::leanh::lean_inc(v_k_698_);
                    v___x_709_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg(v_entries_695_, v_h_707_, v_depth_691_, v_k_698_, v_v_699_);
                    v_i_694_ = v___x_708_;
                    v_entries_695_ = v___x_709_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_depth_711_: *mut crate::leanh::LeanObject,
    mut v_keys_712_: *mut crate::leanh::LeanObject,
    mut v_vals_713_: *mut crate::leanh::LeanObject,
    mut v_i_714_: *mut crate::leanh::LeanObject,
    mut v_entries_715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_716_: usize = 0;
    let mut v_res_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_716_ = crate::leanh::lean_unbox_usize(v_depth_711_);
    crate::leanh::lean_dec(v_depth_711_);
    v_res_717_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_716_, v_keys_712_, v_vals_713_, v_i_714_, v_entries_715_);
    crate::leanh::lean_dec_ref(v_vals_713_);
    crate::leanh::lean_dec_ref(v_keys_712_);
    return v_res_717_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_718_: *mut crate::leanh::LeanObject,
    mut v_x_719_: *mut crate::leanh::LeanObject,
    mut v_x_720_: *mut crate::leanh::LeanObject,
    mut v_x_721_: *mut crate::leanh::LeanObject,
    mut v_x_722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4803__boxed_723_: usize = 0;
    let mut v_x_4804__boxed_724_: usize = 0;
    let mut v_res_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4803__boxed_723_ = crate::leanh::lean_unbox_usize(v_x_719_);
    crate::leanh::lean_dec(v_x_719_);
    v_x_4804__boxed_724_ = crate::leanh::lean_unbox_usize(v_x_720_);
    crate::leanh::lean_dec(v_x_720_);
    v_res_725_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg(v_x_718_, v_x_4803__boxed_723_, v_x_4804__boxed_724_, v_x_721_, v_x_722_);
    return v_res_725_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0___redArg(
    mut v_x_726_: *mut crate::leanh::LeanObject,
    mut v_x_727_: *mut crate::leanh::LeanObject,
    mut v_x_728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_729_: u64 = 0;
    let mut v___x_730_: usize = 0;
    let mut v___x_731_: usize = 0;
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_729_ = l_Lean_instHashableMVarId_hash(v_x_727_);
    v___x_730_ = lean_uint64_to_usize(v___x_729_);
    v___x_731_ = 1usize;
    v___x_732_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg(v_x_726_, v___x_730_, v___x_731_, v_x_727_, v_x_728_);
    return v___x_732_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0___redArg(
    mut v_mvarId_733_: *mut crate::leanh::LeanObject,
    mut v_val_734_: *mut crate::leanh::LeanObject,
    mut v___y_735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_745_: u8 = 0;
    let mut v_depth_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_758_: u8 = 0;
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_769_: u8 = 0;
    let mut v_isSharedCheck_770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_737_ = lean_st_ref_take(v___y_735_);
                v_mctx_738_ = crate::leanh::lean_ctor_get(v___x_737_, 0);
                v_cache_739_ = crate::leanh::lean_ctor_get(v___x_737_, 1);
                v_zetaDeltaFVarIds_740_ = crate::leanh::lean_ctor_get(v___x_737_, 2);
                v_postponed_741_ = crate::leanh::lean_ctor_get(v___x_737_, 3);
                v_diag_742_ = crate::leanh::lean_ctor_get(v___x_737_, 4);
                v_isSharedCheck_770_ = (!crate::leanh::lean_is_exclusive(v___x_737_)) as u8;
                if v_isSharedCheck_770_ == 0 {
                    v___x_744_ = v___x_737_;
                    v_isShared_745_ = v_isSharedCheck_770_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_742_);
                    crate::leanh::lean_inc(v_postponed_741_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_740_);
                    crate::leanh::lean_inc(v_cache_739_);
                    crate::leanh::lean_inc(v_mctx_738_);
                    crate::leanh::lean_dec(v___x_737_);
                    v___x_744_ = crate::leanh::lean_box(0);
                    v_isShared_745_ = v_isSharedCheck_770_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_746_ = crate::leanh::lean_ctor_get(v_mctx_738_, 0);
                v_levelAssignDepth_747_ = crate::leanh::lean_ctor_get(v_mctx_738_, 1);
                v_lmvarCounter_748_ = crate::leanh::lean_ctor_get(v_mctx_738_, 2);
                v_mvarCounter_749_ = crate::leanh::lean_ctor_get(v_mctx_738_, 3);
                v_lDecls_750_ = crate::leanh::lean_ctor_get(v_mctx_738_, 4);
                v_decls_751_ = crate::leanh::lean_ctor_get(v_mctx_738_, 5);
                v_userNames_752_ = crate::leanh::lean_ctor_get(v_mctx_738_, 6);
                v_lAssignment_753_ = crate::leanh::lean_ctor_get(v_mctx_738_, 7);
                v_eAssignment_754_ = crate::leanh::lean_ctor_get(v_mctx_738_, 8);
                v_dAssignment_755_ = crate::leanh::lean_ctor_get(v_mctx_738_, 9);
                v_isSharedCheck_769_ = (!crate::leanh::lean_is_exclusive(v_mctx_738_)) as u8;
                if v_isSharedCheck_769_ == 0 {
                    v___x_757_ = v_mctx_738_;
                    v_isShared_758_ = v_isSharedCheck_769_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_755_);
                    crate::leanh::lean_inc(v_eAssignment_754_);
                    crate::leanh::lean_inc(v_lAssignment_753_);
                    crate::leanh::lean_inc(v_userNames_752_);
                    crate::leanh::lean_inc(v_decls_751_);
                    crate::leanh::lean_inc(v_lDecls_750_);
                    crate::leanh::lean_inc(v_mvarCounter_749_);
                    crate::leanh::lean_inc(v_lmvarCounter_748_);
                    crate::leanh::lean_inc(v_levelAssignDepth_747_);
                    crate::leanh::lean_inc(v_depth_746_);
                    crate::leanh::lean_dec(v_mctx_738_);
                    v___x_757_ = crate::leanh::lean_box(0);
                    v_isShared_758_ = v_isSharedCheck_769_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_759_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0___redArg(v_eAssignment_754_, v_mvarId_733_, v_val_734_);
                if v_isShared_758_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_757_, 8, v___x_759_);
                    v___x_761_ = v___x_757_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_768_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_768_, 0, v_depth_746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_768_, 1, v_levelAssignDepth_747_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_768_, 2, v_lmvarCounter_748_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_768_, 3, v_mvarCounter_749_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_768_, 4, v_lDecls_750_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_768_, 5, v_decls_751_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_768_, 6, v_userNames_752_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_768_, 7, v_lAssignment_753_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_768_, 8, v___x_759_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_768_, 9, v_dAssignment_755_);
                    v___x_761_ = v_reuseFailAlloc_768_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_745_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_744_, 0, v___x_761_);
                    v___x_763_ = v___x_744_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_767_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_761_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_767_, 1, v_cache_739_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_767_, 2, v_zetaDeltaFVarIds_740_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_767_, 3, v_postponed_741_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_767_, 4, v_diag_742_);
                    v___x_763_ = v_reuseFailAlloc_767_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_764_ = lean_st_ref_set(v___y_735_, v___x_763_);
                v___x_765_ = crate::leanh::lean_box(0);
                v___x_766_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_766_, 0, v___x_765_);
                return v___x_766_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0___redArg___boxed(
    mut v_mvarId_771_: *mut crate::leanh::LeanObject,
    mut v_val_772_: *mut crate::leanh::LeanObject,
    mut v___y_773_: *mut crate::leanh::LeanObject,
    mut v___y_774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_775_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0___redArg(
        v_mvarId_771_,
        v_val_772_,
        v___y_773_,
    );
    crate::leanh::lean_dec(v___y_773_);
    return v_res_775_;
}
pub unsafe fn l_Lean_Meta_Grind_injection_x3f___lam__0(
    mut v_fvarId_779_: *mut crate::leanh::LeanObject,
    mut v_mvarId_780_: *mut crate::leanh::LeanObject,
    mut v___y_781_: *mut crate::leanh::LeanObject,
    mut v___y_782_: *mut crate::leanh::LeanObject,
    mut v___y_783_: *mut crate::leanh::LeanObject,
    mut v___y_784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_790_: u8 = 0;
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: u8 = 0;
    let mut v_arg_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_801_: u8 = 0;
    let mut v_arg_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: u8 = 0;
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: u8 = 0;
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_812_: u8 = 0;
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_817_: u8 = 0;
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_830_: u8 = 0;
    let mut v_binderType_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_841_: u8 = 0;
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_847_: u8 = 0;
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_854_: u8 = 0;
    let mut v_a_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_858_: u8 = 0;
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_862_: u8 = 0;
    let mut v_isSharedCheck_863_: u8 = 0;
    let mut v_unused_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_868_: u8 = 0;
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_872_: u8 = 0;
    let mut v_a_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_876_: u8 = 0;
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_880_: u8 = 0;
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_885_: u8 = 0;
    let mut v_a_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_889_: u8 = 0;
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_893_: u8 = 0;
    let mut v_a_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_897_: u8 = 0;
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_901_: u8 = 0;
    let mut v_a_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_905_: u8 = 0;
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_909_: u8 = 0;
    let mut v_a_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_913_: u8 = 0;
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_917_: u8 = 0;
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_929_: u8 = 0;
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_934_: u8 = 0;
    let mut v_a_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_938_: u8 = 0;
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_942_: u8 = 0;
    let mut v_isSharedCheck_943_: u8 = 0;
    let mut v_a_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_947_: u8 = 0;
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_951_: u8 = 0;
    let mut v_isSharedCheck_952_: u8 = 0;
    let mut v_a_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_956_: u8 = 0;
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_960_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_fvarId_779_);
                v___x_786_ = l_Lean_FVarId_getDecl___redArg(
                    v_fvarId_779_,
                    v___y_781_,
                    v___y_783_,
                    v___y_784_,
                );
                if crate::leanh::lean_obj_tag(v___x_786_) == 0 {
                    v_a_787_ = crate::leanh::lean_ctor_get(v___x_786_, 0);
                    v_isSharedCheck_952_ = (!crate::leanh::lean_is_exclusive(v___x_786_)) as u8;
                    if v_isSharedCheck_952_ == 0 {
                        v___x_789_ = v___x_786_;
                        v_isShared_790_ = v_isSharedCheck_952_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_787_);
                        crate::leanh::lean_dec(v___x_786_);
                        v___x_789_ = crate::leanh::lean_box(0);
                        v_isShared_790_ = v_isSharedCheck_952_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_784_);
                    crate::leanh::lean_dec_ref(v___y_783_);
                    crate::leanh::lean_dec(v___y_782_);
                    crate::leanh::lean_dec_ref(v___y_781_);
                    crate::leanh::lean_dec(v_mvarId_780_);
                    crate::leanh::lean_dec(v_fvarId_779_);
                    v_a_953_ = crate::leanh::lean_ctor_get(v___x_786_, 0);
                    v_isSharedCheck_960_ = (!crate::leanh::lean_is_exclusive(v___x_786_)) as u8;
                    if v_isSharedCheck_960_ == 0 {
                        v___x_955_ = v___x_786_;
                        v_isShared_956_ = v_isSharedCheck_960_;
                        state = 34;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_953_);
                        crate::leanh::lean_dec(v___x_786_);
                        v___x_955_ = crate::leanh::lean_box(0);
                        v_isShared_956_ = v_isSharedCheck_960_;
                        state = 34;
                        continue;
                    }
                }
            }
            1 => {
                v___x_796_ = l_Lean_LocalDecl_type(v_a_787_);
                crate::leanh::lean_dec(v_a_787_);
                v___x_797_ = l_Lean_Expr_cleanupAnnotations(v___x_796_);
                v___x_798_ = l_Lean_Expr_isApp(v___x_797_);
                if v___x_798_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_797_);
                    crate::leanh::lean_dec(v___y_784_);
                    crate::leanh::lean_dec_ref(v___y_783_);
                    crate::leanh::lean_dec(v___y_782_);
                    crate::leanh::lean_dec_ref(v___y_781_);
                    crate::leanh::lean_dec(v_mvarId_780_);
                    crate::leanh::lean_dec(v_fvarId_779_);
                    state = 2;
                    continue;
                } else {
                    v_arg_799_ = crate::leanh::lean_ctor_get(v___x_797_, 1);
                    crate::leanh::lean_inc_ref(v_arg_799_);
                    v___x_800_ = l_Lean_Expr_appFnCleanup___redArg(v___x_797_);
                    v___x_801_ = l_Lean_Expr_isApp(v___x_800_);
                    if v___x_801_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_800_);
                        crate::leanh::lean_dec_ref(v_arg_799_);
                        crate::leanh::lean_dec(v___y_784_);
                        crate::leanh::lean_dec_ref(v___y_783_);
                        crate::leanh::lean_dec(v___y_782_);
                        crate::leanh::lean_dec_ref(v___y_781_);
                        crate::leanh::lean_dec(v_mvarId_780_);
                        crate::leanh::lean_dec(v_fvarId_779_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_802_ = crate::leanh::lean_ctor_get(v___x_800_, 1);
                        crate::leanh::lean_inc_ref(v_arg_802_);
                        v___x_803_ = l_Lean_Expr_appFnCleanup___redArg(v___x_800_);
                        v___x_804_ = l_Lean_Expr_isApp(v___x_803_);
                        if v___x_804_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_803_);
                            crate::leanh::lean_dec_ref(v_arg_802_);
                            crate::leanh::lean_dec_ref(v_arg_799_);
                            crate::leanh::lean_dec(v___y_784_);
                            crate::leanh::lean_dec_ref(v___y_783_);
                            crate::leanh::lean_dec(v___y_782_);
                            crate::leanh::lean_dec_ref(v___y_781_);
                            crate::leanh::lean_dec(v_mvarId_780_);
                            crate::leanh::lean_dec(v_fvarId_779_);
                            state = 2;
                            continue;
                        } else {
                            v___x_805_ = l_Lean_Expr_appFnCleanup___redArg(v___x_803_);
                            v___x_806_ = l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1;
                            v___x_807_ = l_Lean_Expr_isConstOf(v___x_805_, v___x_806_);
                            crate::leanh::lean_dec_ref(v___x_805_);
                            if v___x_807_ == 0 {
                                crate::leanh::lean_dec_ref(v_arg_802_);
                                crate::leanh::lean_dec_ref(v_arg_799_);
                                crate::leanh::lean_dec(v___y_784_);
                                crate::leanh::lean_dec_ref(v___y_783_);
                                crate::leanh::lean_dec(v___y_782_);
                                crate::leanh::lean_dec_ref(v___y_781_);
                                crate::leanh::lean_dec(v_mvarId_780_);
                                crate::leanh::lean_dec(v_fvarId_779_);
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_789_);
                                v___x_808_ = l_Lean_Meta_isConstructorAppCore_x3f___redArg(
                                    v_arg_802_, v___y_784_,
                                );
                                crate::leanh::lean_dec_ref(v_arg_802_);
                                if crate::leanh::lean_obj_tag(v___x_808_) == 0 {
                                    v_a_809_ = crate::leanh::lean_ctor_get(v___x_808_, 0);
                                    v_isSharedCheck_943_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_808_)) as u8;
                                    if v_isSharedCheck_943_ == 0 {
                                        v___x_811_ = v___x_808_;
                                        v_isShared_812_ = v_isSharedCheck_943_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_809_);
                                        crate::leanh::lean_dec(v___x_808_);
                                        v___x_811_ = crate::leanh::lean_box(0);
                                        v_isShared_812_ = v_isSharedCheck_943_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_arg_799_);
                                    crate::leanh::lean_dec(v___y_784_);
                                    crate::leanh::lean_dec_ref(v___y_783_);
                                    crate::leanh::lean_dec(v___y_782_);
                                    crate::leanh::lean_dec_ref(v___y_781_);
                                    crate::leanh::lean_dec(v_mvarId_780_);
                                    crate::leanh::lean_dec(v_fvarId_779_);
                                    v_a_944_ = crate::leanh::lean_ctor_get(v___x_808_, 0);
                                    v_isSharedCheck_951_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_808_)) as u8;
                                    if v_isSharedCheck_951_ == 0 {
                                        v___x_946_ = v___x_808_;
                                        v_isShared_947_ = v_isSharedCheck_951_;
                                        state = 32;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_944_);
                                        crate::leanh::lean_dec(v___x_808_);
                                        v___x_946_ = crate::leanh::lean_box(0);
                                        v_isShared_947_ = v_isSharedCheck_951_;
                                        state = 32;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_792_ = crate::leanh::lean_box(0);
                if v_isShared_790_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_789_, 0, v___x_792_);
                    v___x_794_ = v___x_789_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_795_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
                    v___x_794_ = v_reuseFailAlloc_795_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_794_;
            }
            4 => {
                v___x_813_ = l_Lean_Meta_isConstructorAppCore_x3f___redArg(v_arg_799_, v___y_784_);
                crate::leanh::lean_dec_ref(v_arg_799_);
                if crate::leanh::lean_obj_tag(v___x_813_) == 0 {
                    v_a_814_ = crate::leanh::lean_ctor_get(v___x_813_, 0);
                    v_isSharedCheck_934_ = (!crate::leanh::lean_is_exclusive(v___x_813_)) as u8;
                    if v_isSharedCheck_934_ == 0 {
                        v___x_816_ = v___x_813_;
                        v_isShared_817_ = v_isSharedCheck_934_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_814_);
                        crate::leanh::lean_dec(v___x_813_);
                        v___x_816_ = crate::leanh::lean_box(0);
                        v_isShared_817_ = v_isSharedCheck_934_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_811_);
                    crate::leanh::lean_dec(v_a_809_);
                    crate::leanh::lean_dec(v___y_784_);
                    crate::leanh::lean_dec_ref(v___y_783_);
                    crate::leanh::lean_dec(v___y_782_);
                    crate::leanh::lean_dec_ref(v___y_781_);
                    crate::leanh::lean_dec(v_mvarId_780_);
                    crate::leanh::lean_dec(v_fvarId_779_);
                    v_a_935_ = crate::leanh::lean_ctor_get(v___x_813_, 0);
                    v_isSharedCheck_942_ = (!crate::leanh::lean_is_exclusive(v___x_813_)) as u8;
                    if v_isSharedCheck_942_ == 0 {
                        v___x_937_ = v___x_813_;
                        v_isShared_938_ = v_isSharedCheck_942_;
                        state = 30;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_935_);
                        crate::leanh::lean_dec(v___x_813_);
                        v___x_937_ = crate::leanh::lean_box(0);
                        v_isShared_938_ = v_isSharedCheck_942_;
                        state = 30;
                        continue;
                    }
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_809_) == 1 {
                    if crate::leanh::lean_obj_tag(v_a_814_) == 1 {
                        crate::leanh::lean_del_object(v___x_816_);
                        v_val_923_ = crate::leanh::lean_ctor_get(v_a_809_, 0);
                        crate::leanh::lean_inc(v_val_923_);
                        crate::leanh::lean_dec_ref_known(v_a_809_, 1);
                        v_toConstantVal_924_ = crate::leanh::lean_ctor_get(v_val_923_, 0);
                        crate::leanh::lean_inc_ref(v_toConstantVal_924_);
                        crate::leanh::lean_dec(v_val_923_);
                        v_val_925_ = crate::leanh::lean_ctor_get(v_a_814_, 0);
                        crate::leanh::lean_inc(v_val_925_);
                        crate::leanh::lean_dec_ref_known(v_a_814_, 1);
                        v_toConstantVal_926_ = crate::leanh::lean_ctor_get(v_val_925_, 0);
                        crate::leanh::lean_inc_ref(v_toConstantVal_926_);
                        crate::leanh::lean_dec(v_val_925_);
                        v_name_927_ = crate::leanh::lean_ctor_get(v_toConstantVal_924_, 0);
                        crate::leanh::lean_inc(v_name_927_);
                        crate::leanh::lean_dec_ref(v_toConstantVal_924_);
                        v_name_928_ = crate::leanh::lean_ctor_get(v_toConstantVal_926_, 0);
                        crate::leanh::lean_inc(v_name_928_);
                        crate::leanh::lean_dec_ref(v_toConstantVal_926_);
                        v___x_929_ = lean_name_eq(v_name_927_, v_name_928_);
                        crate::leanh::lean_dec(v_name_928_);
                        crate::leanh::lean_dec(v_name_927_);
                        if v___x_929_ == 0 {
                            if v___x_807_ == 0 {
                                crate::leanh::lean_del_object(v___x_811_);
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___y_784_);
                                crate::leanh::lean_dec_ref(v___y_783_);
                                crate::leanh::lean_dec(v___y_782_);
                                crate::leanh::lean_dec_ref(v___y_781_);
                                crate::leanh::lean_dec(v_mvarId_780_);
                                crate::leanh::lean_dec(v_fvarId_779_);
                                v___x_930_ = crate::leanh::lean_box(0);
                                if v_isShared_812_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_811_, 0, v___x_930_);
                                    v___x_932_ = v___x_811_;
                                    state = 29;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_933_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_933_,
                                        0,
                                        v___x_930_,
                                    );
                                    v___x_932_ = v_reuseFailAlloc_933_;
                                    state = 29;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_811_);
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_809_, 1);
                        crate::leanh::lean_dec(v_a_814_);
                        crate::leanh::lean_del_object(v___x_811_);
                        crate::leanh::lean_dec(v___y_784_);
                        crate::leanh::lean_dec_ref(v___y_783_);
                        crate::leanh::lean_dec(v___y_782_);
                        crate::leanh::lean_dec_ref(v___y_781_);
                        crate::leanh::lean_dec(v_mvarId_780_);
                        crate::leanh::lean_dec(v_fvarId_779_);
                        state = 27;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_814_);
                    crate::leanh::lean_del_object(v___x_811_);
                    crate::leanh::lean_dec(v_a_809_);
                    crate::leanh::lean_dec(v___y_784_);
                    crate::leanh::lean_dec_ref(v___y_783_);
                    crate::leanh::lean_dec(v___y_782_);
                    crate::leanh::lean_dec_ref(v___y_781_);
                    crate::leanh::lean_dec(v_mvarId_780_);
                    crate::leanh::lean_dec(v_fvarId_779_);
                    state = 27;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_inc(v_mvarId_780_);
                v___x_819_ = l_Lean_MVarId_getType(
                    v_mvarId_780_,
                    v___y_781_,
                    v___y_782_,
                    v___y_783_,
                    v___y_784_,
                );
                if crate::leanh::lean_obj_tag(v___x_819_) == 0 {
                    v_a_820_ = crate::leanh::lean_ctor_get(v___x_819_, 0);
                    crate::leanh::lean_inc(v_a_820_);
                    crate::leanh::lean_dec_ref_known(v___x_819_, 1);
                    crate::leanh::lean_inc(v_fvarId_779_);
                    v___x_821_ = l_Lean_mkFVar(v_fvarId_779_);
                    v___x_822_ = l_Lean_Meta_mkNoConfusion(
                        v_a_820_, v___x_821_, v___y_781_, v___y_782_, v___y_783_, v___y_784_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_822_) == 0 {
                        v_a_823_ = crate::leanh::lean_ctor_get(v___x_822_, 0);
                        crate::leanh::lean_inc_n(v_a_823_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_822_, 1);
                        crate::leanh::lean_inc(v___y_784_);
                        crate::leanh::lean_inc_ref(v___y_783_);
                        crate::leanh::lean_inc(v___y_782_);
                        crate::leanh::lean_inc_ref(v___y_781_);
                        v___x_824_ = lean_infer_type(
                            v_a_823_, v___y_781_, v___y_782_, v___y_783_, v___y_784_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_824_) == 0 {
                            v_a_825_ = crate::leanh::lean_ctor_get(v___x_824_, 0);
                            crate::leanh::lean_inc(v_a_825_);
                            crate::leanh::lean_dec_ref_known(v___x_824_, 1);
                            v___x_826_ = l_Lean_Meta_whnfD(
                                v_a_825_, v___y_781_, v___y_782_, v___y_783_, v___y_784_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_826_) == 0 {
                                v_a_827_ = crate::leanh::lean_ctor_get(v___x_826_, 0);
                                v_isSharedCheck_885_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_826_)) as u8;
                                if v_isSharedCheck_885_ == 0 {
                                    v___x_829_ = v___x_826_;
                                    v_isShared_830_ = v_isSharedCheck_885_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_827_);
                                    crate::leanh::lean_dec(v___x_826_);
                                    v___x_829_ = crate::leanh::lean_box(0);
                                    v_isShared_830_ = v_isSharedCheck_885_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_823_);
                                crate::leanh::lean_dec(v___y_784_);
                                crate::leanh::lean_dec_ref(v___y_783_);
                                crate::leanh::lean_dec(v___y_782_);
                                crate::leanh::lean_dec_ref(v___y_781_);
                                crate::leanh::lean_dec(v_mvarId_780_);
                                crate::leanh::lean_dec(v_fvarId_779_);
                                v_a_886_ = crate::leanh::lean_ctor_get(v___x_826_, 0);
                                v_isSharedCheck_893_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_826_)) as u8;
                                if v_isSharedCheck_893_ == 0 {
                                    v___x_888_ = v___x_826_;
                                    v_isShared_889_ = v_isSharedCheck_893_;
                                    state = 19;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_886_);
                                    crate::leanh::lean_dec(v___x_826_);
                                    v___x_888_ = crate::leanh::lean_box(0);
                                    v_isShared_889_ = v_isSharedCheck_893_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_823_);
                            crate::leanh::lean_dec(v___y_784_);
                            crate::leanh::lean_dec_ref(v___y_783_);
                            crate::leanh::lean_dec(v___y_782_);
                            crate::leanh::lean_dec_ref(v___y_781_);
                            crate::leanh::lean_dec(v_mvarId_780_);
                            crate::leanh::lean_dec(v_fvarId_779_);
                            v_a_894_ = crate::leanh::lean_ctor_get(v___x_824_, 0);
                            v_isSharedCheck_901_ =
                                (!crate::leanh::lean_is_exclusive(v___x_824_)) as u8;
                            if v_isSharedCheck_901_ == 0 {
                                v___x_896_ = v___x_824_;
                                v_isShared_897_ = v_isSharedCheck_901_;
                                state = 21;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_894_);
                                crate::leanh::lean_dec(v___x_824_);
                                v___x_896_ = crate::leanh::lean_box(0);
                                v_isShared_897_ = v_isSharedCheck_901_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_784_);
                        crate::leanh::lean_dec_ref(v___y_783_);
                        crate::leanh::lean_dec(v___y_782_);
                        crate::leanh::lean_dec_ref(v___y_781_);
                        crate::leanh::lean_dec(v_mvarId_780_);
                        crate::leanh::lean_dec(v_fvarId_779_);
                        v_a_902_ = crate::leanh::lean_ctor_get(v___x_822_, 0);
                        v_isSharedCheck_909_ = (!crate::leanh::lean_is_exclusive(v___x_822_)) as u8;
                        if v_isSharedCheck_909_ == 0 {
                            v___x_904_ = v___x_822_;
                            v_isShared_905_ = v_isSharedCheck_909_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_902_);
                            crate::leanh::lean_dec(v___x_822_);
                            v___x_904_ = crate::leanh::lean_box(0);
                            v_isShared_905_ = v_isSharedCheck_909_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_784_);
                    crate::leanh::lean_dec_ref(v___y_783_);
                    crate::leanh::lean_dec(v___y_782_);
                    crate::leanh::lean_dec_ref(v___y_781_);
                    crate::leanh::lean_dec(v_mvarId_780_);
                    crate::leanh::lean_dec(v_fvarId_779_);
                    v_a_910_ = crate::leanh::lean_ctor_get(v___x_819_, 0);
                    v_isSharedCheck_917_ = (!crate::leanh::lean_is_exclusive(v___x_819_)) as u8;
                    if v_isSharedCheck_917_ == 0 {
                        v___x_912_ = v___x_819_;
                        v_isShared_913_ = v_isSharedCheck_917_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_910_);
                        crate::leanh::lean_dec(v___x_819_);
                        v___x_912_ = crate::leanh::lean_box(0);
                        v_isShared_913_ = v_isSharedCheck_917_;
                        state = 25;
                        continue;
                    }
                }
            }
            7 => {
                if crate::leanh::lean_obj_tag(v_a_827_) == 7 {
                    crate::leanh::lean_del_object(v___x_829_);
                    v_binderType_831_ = crate::leanh::lean_ctor_get(v_a_827_, 1);
                    crate::leanh::lean_inc_ref(v_binderType_831_);
                    crate::leanh::lean_dec_ref_known(v_a_827_, 3);
                    crate::leanh::lean_inc(v_mvarId_780_);
                    v___x_832_ = l_Lean_MVarId_getTag(
                        v_mvarId_780_,
                        v___y_781_,
                        v___y_782_,
                        v___y_783_,
                        v___y_784_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_832_) == 0 {
                        v_a_833_ = crate::leanh::lean_ctor_get(v___x_832_, 0);
                        crate::leanh::lean_inc(v_a_833_);
                        crate::leanh::lean_dec_ref_known(v___x_832_, 1);
                        v___x_834_ = l_Lean_Expr_headBeta(v_binderType_831_);
                        v___x_835_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                            v___x_834_, v_a_833_, v___y_781_, v___y_782_, v___y_783_, v___y_784_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_835_) == 0 {
                            v_a_836_ = crate::leanh::lean_ctor_get(v___x_835_, 0);
                            crate::leanh::lean_inc_n(v_a_836_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_835_, 1);
                            v___x_837_ = l_Lean_Expr_app___override(v_a_823_, v_a_836_);
                            v___x_838_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0___redArg(v_mvarId_780_, v___x_837_, v___y_782_);
                            v_isSharedCheck_863_ =
                                (!crate::leanh::lean_is_exclusive(v___x_838_)) as u8;
                            if v_isSharedCheck_863_ == 0 {
                                v_unused_864_ = crate::leanh::lean_ctor_get(v___x_838_, 0);
                                crate::leanh::lean_dec(v_unused_864_);
                                v___x_840_ = v___x_838_;
                                v_isShared_841_ = v_isSharedCheck_863_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_838_);
                                v___x_840_ = crate::leanh::lean_box(0);
                                v_isShared_841_ = v_isSharedCheck_863_;
                                state = 8;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_823_);
                            crate::leanh::lean_dec(v___y_784_);
                            crate::leanh::lean_dec_ref(v___y_783_);
                            crate::leanh::lean_dec(v___y_782_);
                            crate::leanh::lean_dec_ref(v___y_781_);
                            crate::leanh::lean_dec(v_mvarId_780_);
                            crate::leanh::lean_dec(v_fvarId_779_);
                            v_a_865_ = crate::leanh::lean_ctor_get(v___x_835_, 0);
                            v_isSharedCheck_872_ =
                                (!crate::leanh::lean_is_exclusive(v___x_835_)) as u8;
                            if v_isSharedCheck_872_ == 0 {
                                v___x_867_ = v___x_835_;
                                v_isShared_868_ = v_isSharedCheck_872_;
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_865_);
                                crate::leanh::lean_dec(v___x_835_);
                                v___x_867_ = crate::leanh::lean_box(0);
                                v_isShared_868_ = v_isSharedCheck_872_;
                                state = 14;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_binderType_831_);
                        crate::leanh::lean_dec(v_a_823_);
                        crate::leanh::lean_dec(v___y_784_);
                        crate::leanh::lean_dec_ref(v___y_783_);
                        crate::leanh::lean_dec(v___y_782_);
                        crate::leanh::lean_dec_ref(v___y_781_);
                        crate::leanh::lean_dec(v_mvarId_780_);
                        crate::leanh::lean_dec(v_fvarId_779_);
                        v_a_873_ = crate::leanh::lean_ctor_get(v___x_832_, 0);
                        v_isSharedCheck_880_ = (!crate::leanh::lean_is_exclusive(v___x_832_)) as u8;
                        if v_isSharedCheck_880_ == 0 {
                            v___x_875_ = v___x_832_;
                            v_isShared_876_ = v_isSharedCheck_880_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_873_);
                            crate::leanh::lean_dec(v___x_832_);
                            v___x_875_ = crate::leanh::lean_box(0);
                            v_isShared_876_ = v_isSharedCheck_880_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_827_);
                    crate::leanh::lean_dec(v_a_823_);
                    crate::leanh::lean_dec(v___y_784_);
                    crate::leanh::lean_dec_ref(v___y_783_);
                    crate::leanh::lean_dec(v___y_782_);
                    crate::leanh::lean_dec_ref(v___y_781_);
                    crate::leanh::lean_dec(v_mvarId_780_);
                    crate::leanh::lean_dec(v_fvarId_779_);
                    v___x_881_ = crate::leanh::lean_box(0);
                    if v_isShared_830_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_829_, 0, v___x_881_);
                        v___x_883_ = v___x_829_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_884_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
                        v___x_883_ = v_reuseFailAlloc_884_;
                        state = 18;
                        continue;
                    }
                }
            }
            8 => {
                v___x_842_ = l_Lean_Expr_mvarId_x21(v_a_836_);
                crate::leanh::lean_dec(v_a_836_);
                v___x_843_ = l_Lean_MVarId_tryClear(
                    v___x_842_,
                    v_fvarId_779_,
                    v___y_781_,
                    v___y_782_,
                    v___y_783_,
                    v___y_784_,
                );
                crate::leanh::lean_dec(v___y_784_);
                crate::leanh::lean_dec_ref(v___y_783_);
                crate::leanh::lean_dec(v___y_782_);
                crate::leanh::lean_dec_ref(v___y_781_);
                if crate::leanh::lean_obj_tag(v___x_843_) == 0 {
                    v_a_844_ = crate::leanh::lean_ctor_get(v___x_843_, 0);
                    v_isSharedCheck_854_ = (!crate::leanh::lean_is_exclusive(v___x_843_)) as u8;
                    if v_isSharedCheck_854_ == 0 {
                        v___x_846_ = v___x_843_;
                        v_isShared_847_ = v_isSharedCheck_854_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_844_);
                        crate::leanh::lean_dec(v___x_843_);
                        v___x_846_ = crate::leanh::lean_box(0);
                        v_isShared_847_ = v_isSharedCheck_854_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_840_);
                    v_a_855_ = crate::leanh::lean_ctor_get(v___x_843_, 0);
                    v_isSharedCheck_862_ = (!crate::leanh::lean_is_exclusive(v___x_843_)) as u8;
                    if v_isSharedCheck_862_ == 0 {
                        v___x_857_ = v___x_843_;
                        v_isShared_858_ = v_isSharedCheck_862_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_855_);
                        crate::leanh::lean_dec(v___x_843_);
                        v___x_857_ = crate::leanh::lean_box(0);
                        v_isShared_858_ = v_isSharedCheck_862_;
                        state = 12;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_841_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_840_, 1);
                    crate::leanh::lean_ctor_set(v___x_840_, 0, v_a_844_);
                    v___x_849_ = v___x_840_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_853_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_844_);
                    v___x_849_ = v_reuseFailAlloc_853_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_847_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_846_, 0, v___x_849_);
                    v___x_851_ = v___x_846_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_852_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
                    v___x_851_ = v_reuseFailAlloc_852_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_851_;
            }
            12 => {
                if v_isShared_858_ == 0 {
                    v___x_860_ = v___x_857_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_861_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
                    v___x_860_ = v_reuseFailAlloc_861_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_860_;
            }
            14 => {
                if v_isShared_868_ == 0 {
                    v___x_870_ = v___x_867_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_871_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
                    v___x_870_ = v_reuseFailAlloc_871_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_870_;
            }
            16 => {
                if v_isShared_876_ == 0 {
                    v___x_878_ = v___x_875_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_879_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
                    v___x_878_ = v_reuseFailAlloc_879_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_878_;
            }
            18 => {
                return v___x_883_;
            }
            19 => {
                if v_isShared_889_ == 0 {
                    v___x_891_ = v___x_888_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_892_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
                    v___x_891_ = v_reuseFailAlloc_892_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_891_;
            }
            21 => {
                if v_isShared_897_ == 0 {
                    v___x_899_ = v___x_896_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_900_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
                    v___x_899_ = v_reuseFailAlloc_900_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_899_;
            }
            23 => {
                if v_isShared_905_ == 0 {
                    v___x_907_ = v___x_904_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_908_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
                    v___x_907_ = v_reuseFailAlloc_908_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_907_;
            }
            25 => {
                if v_isShared_913_ == 0 {
                    v___x_915_ = v___x_912_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_916_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
                    v___x_915_ = v_reuseFailAlloc_916_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_915_;
            }
            27 => {
                v___x_919_ = crate::leanh::lean_box(0);
                if v_isShared_817_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_816_, 0, v___x_919_);
                    v___x_921_ = v___x_816_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_922_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
                    v___x_921_ = v_reuseFailAlloc_922_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_921_;
            }
            29 => {
                return v___x_932_;
            }
            30 => {
                if v_isShared_938_ == 0 {
                    v___x_940_ = v___x_937_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_941_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
                    v___x_940_ = v_reuseFailAlloc_941_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_940_;
            }
            32 => {
                if v_isShared_947_ == 0 {
                    v___x_949_ = v___x_946_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_950_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
                    v___x_949_ = v_reuseFailAlloc_950_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_949_;
            }
            34 => {
                if v_isShared_956_ == 0 {
                    v___x_958_ = v___x_955_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_959_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
                    v___x_958_ = v_reuseFailAlloc_959_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_958_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_injection_x3f___lam__0___boxed(
    mut v_fvarId_961_: *mut crate::leanh::LeanObject,
    mut v_mvarId_962_: *mut crate::leanh::LeanObject,
    mut v___y_963_: *mut crate::leanh::LeanObject,
    mut v___y_964_: *mut crate::leanh::LeanObject,
    mut v___y_965_: *mut crate::leanh::LeanObject,
    mut v___y_966_: *mut crate::leanh::LeanObject,
    mut v___y_967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_968_ = l_Lean_Meta_Grind_injection_x3f___lam__0(
        v_fvarId_961_,
        v_mvarId_962_,
        v___y_963_,
        v___y_964_,
        v___y_965_,
        v___y_966_,
    );
    return v_res_968_;
}
pub unsafe fn l_Lean_Meta_Grind_injection_x3f(
    mut v_mvarId_969_: *mut crate::leanh::LeanObject,
    mut v_fvarId_970_: *mut crate::leanh::LeanObject,
    mut v_a_971_: *mut crate::leanh::LeanObject,
    mut v_a_972_: *mut crate::leanh::LeanObject,
    mut v_a_973_: *mut crate::leanh::LeanObject,
    mut v_a_974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_mvarId_969_);
    v___f_976_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_injection_x3f___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_976_, 0, v_fvarId_970_);
    crate::leanh::lean_closure_set(v___f_976_, 1, v_mvarId_969_);
    v___x_977_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1___redArg(
        v_mvarId_969_,
        v___f_976_,
        v_a_971_,
        v_a_972_,
        v_a_973_,
        v_a_974_,
    );
    return v___x_977_;
}
pub unsafe fn l_Lean_Meta_Grind_injection_x3f___boxed(
    mut v_mvarId_978_: *mut crate::leanh::LeanObject,
    mut v_fvarId_979_: *mut crate::leanh::LeanObject,
    mut v_a_980_: *mut crate::leanh::LeanObject,
    mut v_a_981_: *mut crate::leanh::LeanObject,
    mut v_a_982_: *mut crate::leanh::LeanObject,
    mut v_a_983_: *mut crate::leanh::LeanObject,
    mut v_a_984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_985_ = l_Lean_Meta_Grind_injection_x3f(
        v_mvarId_978_,
        v_fvarId_979_,
        v_a_980_,
        v_a_981_,
        v_a_982_,
        v_a_983_,
    );
    crate::leanh::lean_dec(v_a_983_);
    crate::leanh::lean_dec_ref(v_a_982_);
    crate::leanh::lean_dec(v_a_981_);
    crate::leanh::lean_dec_ref(v_a_980_);
    return v_res_985_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0(
    mut v_mvarId_986_: *mut crate::leanh::LeanObject,
    mut v_val_987_: *mut crate::leanh::LeanObject,
    mut v___y_988_: *mut crate::leanh::LeanObject,
    mut v___y_989_: *mut crate::leanh::LeanObject,
    mut v___y_990_: *mut crate::leanh::LeanObject,
    mut v___y_991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_993_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0___redArg(
        v_mvarId_986_,
        v_val_987_,
        v___y_989_,
    );
    return v___x_993_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0___boxed(
    mut v_mvarId_994_: *mut crate::leanh::LeanObject,
    mut v_val_995_: *mut crate::leanh::LeanObject,
    mut v___y_996_: *mut crate::leanh::LeanObject,
    mut v___y_997_: *mut crate::leanh::LeanObject,
    mut v___y_998_: *mut crate::leanh::LeanObject,
    mut v___y_999_: *mut crate::leanh::LeanObject,
    mut v___y_1000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1001_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0(
        v_mvarId_994_,
        v_val_995_,
        v___y_996_,
        v___y_997_,
        v___y_998_,
        v___y_999_,
    );
    crate::leanh::lean_dec(v___y_999_);
    crate::leanh::lean_dec_ref(v___y_998_);
    crate::leanh::lean_dec(v___y_997_);
    crate::leanh::lean_dec_ref(v___y_996_);
    return v_res_1001_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0(
    mut v_00_u03b2_1002_: *mut crate::leanh::LeanObject,
    mut v_x_1003_: *mut crate::leanh::LeanObject,
    mut v_x_1004_: *mut crate::leanh::LeanObject,
    mut v_x_1005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1006_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0___redArg(v_x_1003_, v_x_1004_, v_x_1005_);
    return v___x_1006_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2(
    mut v_00_u03b2_1007_: *mut crate::leanh::LeanObject,
    mut v_x_1008_: *mut crate::leanh::LeanObject,
    mut v_x_1009_: usize,
    mut v_x_1010_: usize,
    mut v_x_1011_: *mut crate::leanh::LeanObject,
    mut v_x_1012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1013_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg(v_x_1008_, v_x_1009_, v_x_1010_, v_x_1011_, v_x_1012_);
    return v___x_1013_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_1014_: *mut crate::leanh::LeanObject,
    mut v_x_1015_: *mut crate::leanh::LeanObject,
    mut v_x_1016_: *mut crate::leanh::LeanObject,
    mut v_x_1017_: *mut crate::leanh::LeanObject,
    mut v_x_1018_: *mut crate::leanh::LeanObject,
    mut v_x_1019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_5428__boxed_1020_: usize = 0;
    let mut v_x_5429__boxed_1021_: usize = 0;
    let mut v_res_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_5428__boxed_1020_ = crate::leanh::lean_unbox_usize(v_x_1016_);
    crate::leanh::lean_dec(v_x_1016_);
    v_x_5429__boxed_1021_ = crate::leanh::lean_unbox_usize(v_x_1017_);
    crate::leanh::lean_dec(v_x_1017_);
    v_res_1022_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2(v_00_u03b2_1014_, v_x_1015_, v_x_5428__boxed_1020_, v_x_5429__boxed_1021_, v_x_1018_, v_x_1019_);
    return v_res_1022_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b2_1023_: *mut crate::leanh::LeanObject,
    mut v_n_1024_: *mut crate::leanh::LeanObject,
    mut v_k_1025_: *mut crate::leanh::LeanObject,
    mut v_v_1026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1027_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3___redArg(v_n_1024_, v_k_1025_, v_v_1026_);
    return v___x_1027_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_1028_: *mut crate::leanh::LeanObject,
    mut v_depth_1029_: usize,
    mut v_keys_1030_: *mut crate::leanh::LeanObject,
    mut v_vals_1031_: *mut crate::leanh::LeanObject,
    mut v_heq_1032_: *mut crate::leanh::LeanObject,
    mut v_i_1033_: *mut crate::leanh::LeanObject,
    mut v_entries_1034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1035_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_1029_, v_keys_1030_, v_vals_1031_, v_i_1033_, v_entries_1034_);
    return v___x_1035_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b2_1036_: *mut crate::leanh::LeanObject,
    mut v_depth_1037_: *mut crate::leanh::LeanObject,
    mut v_keys_1038_: *mut crate::leanh::LeanObject,
    mut v_vals_1039_: *mut crate::leanh::LeanObject,
    mut v_heq_1040_: *mut crate::leanh::LeanObject,
    mut v_i_1041_: *mut crate::leanh::LeanObject,
    mut v_entries_1042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1043_: usize = 0;
    let mut v_res_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1043_ = crate::leanh::lean_unbox_usize(v_depth_1037_);
    crate::leanh::lean_dec(v_depth_1037_);
    v_res_1044_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_1036_, v_depth_boxed_1043_, v_keys_1038_, v_vals_1039_, v_heq_1040_, v_i_1041_, v_entries_1042_);
    crate::leanh::lean_dec_ref(v_vals_1039_);
    crate::leanh::lean_dec_ref(v_keys_1038_);
    return v_res_1044_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3_spec__4(
    mut v_00_u03b2_1045_: *mut crate::leanh::LeanObject,
    mut v_x_1046_: *mut crate::leanh::LeanObject,
    mut v_x_1047_: *mut crate::leanh::LeanObject,
    mut v_x_1048_: *mut crate::leanh::LeanObject,
    mut v_x_1049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1050_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_1046_, v_x_1047_, v_x_1048_, v_x_1049_);
    return v___x_1050_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Injection(
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
    res = runtime_initialize_Lean_Meta_Tactic_Clear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CtorRecognizer(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Injection(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Injection(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Lean_Meta_Tactic_Clear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_CtorRecognizer(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Injection(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Injection(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Injection(builtin);
}

// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Injection
// Imports: Lean.Meta.Basic Lean.Meta.Tactic.Clear Lean.Meta.AppBuilder Lean.Meta.CtorRecognizer
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_injection_x3f___lam__0___closed__0_value)
                as *mut LeanObject,
            16122875713692181903 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1___redArg(
    mut v_mvarId_526_: *mut LeanObject,
    mut v_x_527_: *mut LeanObject,
    mut v___y_528_: *mut LeanObject,
    mut v___y_529_: *mut LeanObject,
    mut v___y_530_: *mut LeanObject,
    mut v___y_531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_537_: u8 = 0;
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_541_: u8 = 0;
    let mut v_a_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_545_: u8 = 0;
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_549_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_533_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_526_,
                    v_x_527_,
                    v___y_528_,
                    v___y_529_,
                    v___y_530_,
                    v___y_531_,
                );
                if lean_obj_tag(v___x_533_) == 0 {
                    v_a_534_ = lean_ctor_get(v___x_533_, 0);
                    v_isSharedCheck_541_ = (!lean_is_exclusive(v___x_533_)) as u8;
                    if v_isSharedCheck_541_ == 0 {
                        v___x_536_ = v___x_533_;
                        v_isShared_537_ = v_isSharedCheck_541_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_534_);
                        lean_dec(v___x_533_);
                        v___x_536_ = lean_box(0);
                        v_isShared_537_ = v_isSharedCheck_541_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_542_ = lean_ctor_get(v___x_533_, 0);
                    v_isSharedCheck_549_ = (!lean_is_exclusive(v___x_533_)) as u8;
                    if v_isSharedCheck_549_ == 0 {
                        v___x_544_ = v___x_533_;
                        v_isShared_545_ = v_isSharedCheck_549_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_542_);
                        lean_dec(v___x_533_);
                        v___x_544_ = lean_box(0);
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
                    v_reuseFailAlloc_540_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_540_, 0, v_a_534_);
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
                    v_reuseFailAlloc_548_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_548_, 0, v_a_542_);
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
    mut v_mvarId_550_: *mut LeanObject,
    mut v_x_551_: *mut LeanObject,
    mut v___y_552_: *mut LeanObject,
    mut v___y_553_: *mut LeanObject,
    mut v___y_554_: *mut LeanObject,
    mut v___y_555_: *mut LeanObject,
    mut v___y_556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_557_: *mut LeanObject = core::ptr::null_mut();
    v_res_557_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1___redArg(
        v_mvarId_550_,
        v_x_551_,
        v___y_552_,
        v___y_553_,
        v___y_554_,
        v___y_555_,
    );
    lean_dec(v___y_555_);
    lean_dec_ref(v___y_554_);
    lean_dec(v___y_553_);
    lean_dec_ref(v___y_552_);
    return v_res_557_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1(
    mut v_00_u03b1_558_: *mut LeanObject,
    mut v_mvarId_559_: *mut LeanObject,
    mut v_x_560_: *mut LeanObject,
    mut v___y_561_: *mut LeanObject,
    mut v___y_562_: *mut LeanObject,
    mut v___y_563_: *mut LeanObject,
    mut v___y_564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_567_: *mut LeanObject,
    mut v_mvarId_568_: *mut LeanObject,
    mut v_x_569_: *mut LeanObject,
    mut v___y_570_: *mut LeanObject,
    mut v___y_571_: *mut LeanObject,
    mut v___y_572_: *mut LeanObject,
    mut v___y_573_: *mut LeanObject,
    mut v___y_574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_575_: *mut LeanObject = core::ptr::null_mut();
    v_res_575_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Grind_injection_x3f_spec__1(
        v_00_u03b1_567_,
        v_mvarId_568_,
        v_x_569_,
        v___y_570_,
        v___y_571_,
        v___y_572_,
        v___y_573_,
    );
    lean_dec(v___y_573_);
    lean_dec_ref(v___y_572_);
    lean_dec(v___y_571_);
    lean_dec_ref(v___y_570_);
    return v_res_575_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(
    mut v_x_576_: *mut LeanObject,
    mut v_x_577_: *mut LeanObject,
    mut v_x_578_: *mut LeanObject,
    mut v_x_579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_584_: u8 = 0;
    let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_586_: u8 = 0;
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: u8 = 0;
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_605_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_580_ = lean_ctor_get(v_x_576_, 0);
                v_vs_581_ = lean_ctor_get(v_x_576_, 1);
                v_isSharedCheck_605_ = (!lean_is_exclusive(v_x_576_)) as u8;
                if v_isSharedCheck_605_ == 0 {
                    v___x_583_ = v_x_576_;
                    v_isShared_584_ = v_isSharedCheck_605_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_581_);
                    lean_inc(v_ks_580_);
                    lean_dec(v_x_576_);
                    v___x_583_ = lean_box(0);
                    v_isShared_584_ = v_isSharedCheck_605_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_585_ = lean_array_get_size(v_ks_580_);
                v___x_586_ = lean_nat_dec_lt(v_x_577_, v___x_585_);
                if v___x_586_ == 0 {
                    lean_dec(v_x_577_);
                    v___x_587_ = lean_array_push(v_ks_580_, v_x_578_);
                    v___x_588_ = lean_array_push(v_vs_581_, v_x_579_);
                    if v_isShared_584_ == 0 {
                        lean_ctor_set(v___x_583_, 1, v___x_588_);
                        lean_ctor_set(v___x_583_, 0, v___x_587_);
                        v___x_590_ = v___x_583_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_591_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_591_, 0, v___x_587_);
                        lean_ctor_set(v_reuseFailAlloc_591_, 1, v___x_588_);
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
                            v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_599_, 0, v_ks_580_);
                            lean_ctor_set(v_reuseFailAlloc_599_, 1, v_vs_581_);
                            v___x_595_ = v_reuseFailAlloc_599_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_600_ = lean_array_fset(v_ks_580_, v_x_577_, v_x_578_);
                        v___x_601_ = lean_array_fset(v_vs_581_, v_x_577_, v_x_579_);
                        lean_dec(v_x_577_);
                        if v_isShared_584_ == 0 {
                            lean_ctor_set(v___x_583_, 1, v___x_601_);
                            lean_ctor_set(v___x_583_, 0, v___x_600_);
                            v___x_603_ = v___x_583_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_604_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_600_);
                            lean_ctor_set(v_reuseFailAlloc_604_, 1, v___x_601_);
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
                v___x_596_ = lean_unsigned_to_nat(1);
                v___x_597_ = lean_nat_add(v_x_577_, v___x_596_);
                lean_dec(v_x_577_);
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
    mut v_n_606_: *mut LeanObject,
    mut v_k_607_: *mut LeanObject,
    mut v_v_608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    v___x_609_ = lean_unsigned_to_nat(0);
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
    v___x_615_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__0);
    v___x_616_ = lean_usize_sub(v___x_615_, v___x_614_);
    return v___x_616_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    v___x_617_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_617_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg(
    mut v_x_618_: *mut LeanObject,
    mut v_x_619_: usize,
    mut v_x_620_: usize,
    mut v_x_621_: *mut LeanObject,
    mut v_x_622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_624_: usize = 0;
    let mut v___x_625_: usize = 0;
    let mut v___x_626_: usize = 0;
    let mut v___x_627_: usize = 0;
    let mut v_j_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: u8 = 0;
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_633_: u8 = 0;
    let mut v_v_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_647_: u8 = 0;
    let mut v___x_648_: u8 = 0;
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_654_: u8 = 0;
    let mut v_node_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_658_: u8 = 0;
    let mut v___x_659_: usize = 0;
    let mut v___x_660_: usize = 0;
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_665_: u8 = 0;
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_667_: u8 = 0;
    let mut v_unused_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_673_: u8 = 0;
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_678_: u8 = 0;
    let mut v_ks_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: usize = 0;
    let mut v___x_685_: u8 = 0;
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: u8 = 0;
    let mut v_reuseFailAlloc_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_690_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_618_) == 0 {
                    v_es_623_ = lean_ctor_get(v_x_618_, 0);
                    v___x_624_ = 5usize;
                    v___x_625_ = 1usize;
                    v___x_626_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_627_ = lean_usize_land(v_x_619_, v___x_626_);
                    v_j_628_ = lean_usize_to_nat(v___x_627_);
                    v___x_629_ = lean_array_get_size(v_es_623_);
                    v___x_630_ = lean_nat_dec_lt(v_j_628_, v___x_629_);
                    if v___x_630_ == 0 {
                        lean_dec(v_j_628_);
                        lean_dec(v_x_622_);
                        lean_dec(v_x_621_);
                        return v_x_618_;
                    } else {
                        lean_inc_ref(v_es_623_);
                        v_isSharedCheck_667_ = (!lean_is_exclusive(v_x_618_)) as u8;
                        if v_isSharedCheck_667_ == 0 {
                            v_unused_668_ = lean_ctor_get(v_x_618_, 0);
                            lean_dec(v_unused_668_);
                            v___x_632_ = v_x_618_;
                            v_isShared_633_ = v_isSharedCheck_667_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_618_);
                            v___x_632_ = lean_box(0);
                            v_isShared_633_ = v_isSharedCheck_667_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_669_ = lean_ctor_get(v_x_618_, 0);
                    v_vs_670_ = lean_ctor_get(v_x_618_, 1);
                    v_isSharedCheck_690_ = (!lean_is_exclusive(v_x_618_)) as u8;
                    if v_isSharedCheck_690_ == 0 {
                        v___x_672_ = v_x_618_;
                        v_isShared_673_ = v_isSharedCheck_690_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_670_);
                        lean_inc(v_ks_669_);
                        lean_dec(v_x_618_);
                        v___x_672_ = lean_box(0);
                        v_isShared_673_ = v_isSharedCheck_690_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_634_ = lean_array_fget(v_es_623_, v_j_628_);
                v___x_635_ = lean_box(0);
                v_xs_x27_636_ = lean_array_fset(v_es_623_, v_j_628_, v___x_635_);
                match lean_obj_tag(v_v_634_) {
                    0 => {
                        v_key_643_ = lean_ctor_get(v_v_634_, 0);
                        v_val_644_ = lean_ctor_get(v_v_634_, 1);
                        v_isSharedCheck_654_ = (!lean_is_exclusive(v_v_634_)) as u8;
                        if v_isSharedCheck_654_ == 0 {
                            v___x_646_ = v_v_634_;
                            v_isShared_647_ = v_isSharedCheck_654_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_644_);
                            lean_inc(v_key_643_);
                            lean_dec(v_v_634_);
                            v___x_646_ = lean_box(0);
                            v_isShared_647_ = v_isSharedCheck_654_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_655_ = lean_ctor_get(v_v_634_, 0);
                        v_isSharedCheck_665_ = (!lean_is_exclusive(v_v_634_)) as u8;
                        if v_isSharedCheck_665_ == 0 {
                            v___x_657_ = v_v_634_;
                            v_isShared_658_ = v_isSharedCheck_665_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_655_);
                            lean_dec(v_v_634_);
                            v___x_657_ = lean_box(0);
                            v_isShared_658_ = v_isSharedCheck_665_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_666_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_666_, 0, v_x_621_);
                        lean_ctor_set(v___x_666_, 1, v_x_622_);
                        v___y_638_ = v___x_666_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_639_ = lean_array_fset(v_xs_x27_636_, v_j_628_, v___y_638_);
                lean_dec(v_j_628_);
                if v_isShared_633_ == 0 {
                    lean_ctor_set(v___x_632_, 0, v___x_639_);
                    v___x_641_ = v___x_632_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_639_);
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
                    lean_del_object(v___x_646_);
                    v___x_649_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_643_, v_val_644_, v_x_621_, v_x_622_,
                    );
                    v___x_650_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_650_, 0, v___x_649_);
                    v___y_638_ = v___x_650_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_644_);
                    lean_dec(v_key_643_);
                    if v_isShared_647_ == 0 {
                        lean_ctor_set(v___x_646_, 1, v_x_622_);
                        lean_ctor_set(v___x_646_, 0, v_x_621_);
                        v___x_652_ = v___x_646_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_653_, 0, v_x_621_);
                        lean_ctor_set(v_reuseFailAlloc_653_, 1, v_x_622_);
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
                    lean_ctor_set(v___x_657_, 0, v___x_661_);
                    v___x_663_ = v___x_657_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
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
                    v_reuseFailAlloc_689_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_689_, 0, v_ks_669_);
                    lean_ctor_set(v_reuseFailAlloc_689_, 1, v_vs_670_);
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
                    v___x_687_ = lean_unsigned_to_nat(4);
                    v___x_688_ = lean_nat_dec_lt(v___x_686_, v___x_687_);
                    lean_dec(v___x_686_);
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
                    v_ks_679_ = lean_ctor_get(v_newNode_676_, 0);
                    lean_inc_ref(v_ks_679_);
                    v_vs_680_ = lean_ctor_get(v_newNode_676_, 1);
                    lean_inc_ref(v_vs_680_);
                    lean_dec_ref(v_newNode_676_);
                    v___x_681_ = lean_unsigned_to_nat(0);
                    v___x_682_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___closed__2);
                    v___x_683_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_x_620_, v_ks_679_, v_vs_680_, v___x_681_, v___x_682_);
                    lean_dec_ref(v_vs_680_);
                    lean_dec_ref(v_ks_679_);
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
    mut v_keys_692_: *mut LeanObject,
    mut v_vals_693_: *mut LeanObject,
    mut v_i_694_: *mut LeanObject,
    mut v_entries_695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: u8 = 0;
    let mut v_k_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: u64 = 0;
    let mut v_h_701_: usize = 0;
    let mut v___x_702_: usize = 0;
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: usize = 0;
    let mut v___x_705_: usize = 0;
    let mut v___x_706_: usize = 0;
    let mut v_h_707_: usize = 0;
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_696_ = lean_array_get_size(v_keys_692_);
                v___x_697_ = lean_nat_dec_lt(v_i_694_, v___x_696_);
                if v___x_697_ == 0 {
                    lean_dec(v_i_694_);
                    return v_entries_695_;
                } else {
                    v_k_698_ = lean_array_fget_borrowed(v_keys_692_, v_i_694_);
                    v_v_699_ = lean_array_fget_borrowed(v_vals_693_, v_i_694_);
                    v___x_700_ = l_Lean_instHashableMVarId_hash(v_k_698_);
                    v_h_701_ = lean_uint64_to_usize(v___x_700_);
                    v___x_702_ = 5usize;
                    v___x_703_ = lean_unsigned_to_nat(1);
                    v___x_704_ = 1usize;
                    v___x_705_ = lean_usize_sub(v_depth_691_, v___x_704_);
                    v___x_706_ = lean_usize_mul(v___x_702_, v___x_705_);
                    v_h_707_ = lean_usize_shift_right(v_h_701_, v___x_706_);
                    v___x_708_ = lean_nat_add(v_i_694_, v___x_703_);
                    lean_dec(v_i_694_);
                    lean_inc(v_v_699_);
                    lean_inc(v_k_698_);
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
    mut v_depth_711_: *mut LeanObject,
    mut v_keys_712_: *mut LeanObject,
    mut v_vals_713_: *mut LeanObject,
    mut v_i_714_: *mut LeanObject,
    mut v_entries_715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_716_: usize = 0;
    let mut v_res_717_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_716_ = lean_unbox_usize(v_depth_711_);
    lean_dec(v_depth_711_);
    v_res_717_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_716_, v_keys_712_, v_vals_713_, v_i_714_, v_entries_715_);
    lean_dec_ref(v_vals_713_);
    lean_dec_ref(v_keys_712_);
    return v_res_717_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_718_: *mut LeanObject,
    mut v_x_719_: *mut LeanObject,
    mut v_x_720_: *mut LeanObject,
    mut v_x_721_: *mut LeanObject,
    mut v_x_722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4803__boxed_723_: usize = 0;
    let mut v_x_4804__boxed_724_: usize = 0;
    let mut v_res_725_: *mut LeanObject = core::ptr::null_mut();
    v_x_4803__boxed_723_ = lean_unbox_usize(v_x_719_);
    lean_dec(v_x_719_);
    v_x_4804__boxed_724_ = lean_unbox_usize(v_x_720_);
    lean_dec(v_x_720_);
    v_res_725_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg(v_x_718_, v_x_4803__boxed_723_, v_x_4804__boxed_724_, v_x_721_, v_x_722_);
    return v_res_725_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0___redArg(
    mut v_x_726_: *mut LeanObject,
    mut v_x_727_: *mut LeanObject,
    mut v_x_728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_729_: u64 = 0;
    let mut v___x_730_: usize = 0;
    let mut v___x_731_: usize = 0;
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    v___x_729_ = l_Lean_instHashableMVarId_hash(v_x_727_);
    v___x_730_ = lean_uint64_to_usize(v___x_729_);
    v___x_731_ = 1usize;
    v___x_732_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg(v_x_726_, v___x_730_, v___x_731_, v_x_727_, v_x_728_);
    return v___x_732_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0___redArg(
    mut v_mvarId_733_: *mut LeanObject,
    mut v_val_734_: *mut LeanObject,
    mut v___y_735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_745_: u8 = 0;
    let mut v_depth_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_758_: u8 = 0;
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_769_: u8 = 0;
    let mut v_isSharedCheck_770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_737_ = lean_st_ref_take(v___y_735_);
                v_mctx_738_ = lean_ctor_get(v___x_737_, 0);
                v_cache_739_ = lean_ctor_get(v___x_737_, 1);
                v_zetaDeltaFVarIds_740_ = lean_ctor_get(v___x_737_, 2);
                v_postponed_741_ = lean_ctor_get(v___x_737_, 3);
                v_diag_742_ = lean_ctor_get(v___x_737_, 4);
                v_isSharedCheck_770_ = (!lean_is_exclusive(v___x_737_)) as u8;
                if v_isSharedCheck_770_ == 0 {
                    v___x_744_ = v___x_737_;
                    v_isShared_745_ = v_isSharedCheck_770_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_742_);
                    lean_inc(v_postponed_741_);
                    lean_inc(v_zetaDeltaFVarIds_740_);
                    lean_inc(v_cache_739_);
                    lean_inc(v_mctx_738_);
                    lean_dec(v___x_737_);
                    v___x_744_ = lean_box(0);
                    v_isShared_745_ = v_isSharedCheck_770_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_746_ = lean_ctor_get(v_mctx_738_, 0);
                v_levelAssignDepth_747_ = lean_ctor_get(v_mctx_738_, 1);
                v_lmvarCounter_748_ = lean_ctor_get(v_mctx_738_, 2);
                v_mvarCounter_749_ = lean_ctor_get(v_mctx_738_, 3);
                v_lDecls_750_ = lean_ctor_get(v_mctx_738_, 4);
                v_decls_751_ = lean_ctor_get(v_mctx_738_, 5);
                v_userNames_752_ = lean_ctor_get(v_mctx_738_, 6);
                v_lAssignment_753_ = lean_ctor_get(v_mctx_738_, 7);
                v_eAssignment_754_ = lean_ctor_get(v_mctx_738_, 8);
                v_dAssignment_755_ = lean_ctor_get(v_mctx_738_, 9);
                v_isSharedCheck_769_ = (!lean_is_exclusive(v_mctx_738_)) as u8;
                if v_isSharedCheck_769_ == 0 {
                    v___x_757_ = v_mctx_738_;
                    v_isShared_758_ = v_isSharedCheck_769_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_755_);
                    lean_inc(v_eAssignment_754_);
                    lean_inc(v_lAssignment_753_);
                    lean_inc(v_userNames_752_);
                    lean_inc(v_decls_751_);
                    lean_inc(v_lDecls_750_);
                    lean_inc(v_mvarCounter_749_);
                    lean_inc(v_lmvarCounter_748_);
                    lean_inc(v_levelAssignDepth_747_);
                    lean_inc(v_depth_746_);
                    lean_dec(v_mctx_738_);
                    v___x_757_ = lean_box(0);
                    v_isShared_758_ = v_isSharedCheck_769_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_759_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0___redArg(v_eAssignment_754_, v_mvarId_733_, v_val_734_);
                if v_isShared_758_ == 0 {
                    lean_ctor_set(v___x_757_, 8, v___x_759_);
                    v___x_761_ = v___x_757_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_768_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_768_, 0, v_depth_746_);
                    lean_ctor_set(v_reuseFailAlloc_768_, 1, v_levelAssignDepth_747_);
                    lean_ctor_set(v_reuseFailAlloc_768_, 2, v_lmvarCounter_748_);
                    lean_ctor_set(v_reuseFailAlloc_768_, 3, v_mvarCounter_749_);
                    lean_ctor_set(v_reuseFailAlloc_768_, 4, v_lDecls_750_);
                    lean_ctor_set(v_reuseFailAlloc_768_, 5, v_decls_751_);
                    lean_ctor_set(v_reuseFailAlloc_768_, 6, v_userNames_752_);
                    lean_ctor_set(v_reuseFailAlloc_768_, 7, v_lAssignment_753_);
                    lean_ctor_set(v_reuseFailAlloc_768_, 8, v___x_759_);
                    lean_ctor_set(v_reuseFailAlloc_768_, 9, v_dAssignment_755_);
                    v___x_761_ = v_reuseFailAlloc_768_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_745_ == 0 {
                    lean_ctor_set(v___x_744_, 0, v___x_761_);
                    v___x_763_ = v___x_744_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_767_, 0, v___x_761_);
                    lean_ctor_set(v_reuseFailAlloc_767_, 1, v_cache_739_);
                    lean_ctor_set(v_reuseFailAlloc_767_, 2, v_zetaDeltaFVarIds_740_);
                    lean_ctor_set(v_reuseFailAlloc_767_, 3, v_postponed_741_);
                    lean_ctor_set(v_reuseFailAlloc_767_, 4, v_diag_742_);
                    v___x_763_ = v_reuseFailAlloc_767_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_764_ = lean_st_ref_set(v___y_735_, v___x_763_);
                v___x_765_ = lean_box(0);
                v___x_766_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_766_, 0, v___x_765_);
                return v___x_766_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0___redArg___boxed(
    mut v_mvarId_771_: *mut LeanObject,
    mut v_val_772_: *mut LeanObject,
    mut v___y_773_: *mut LeanObject,
    mut v___y_774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_775_: *mut LeanObject = core::ptr::null_mut();
    v_res_775_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0___redArg(
        v_mvarId_771_,
        v_val_772_,
        v___y_773_,
    );
    lean_dec(v___y_773_);
    return v_res_775_;
}
pub unsafe fn l_Lean_Meta_Grind_injection_x3f___lam__0(
    mut v_fvarId_779_: *mut LeanObject,
    mut v_mvarId_780_: *mut LeanObject,
    mut v___y_781_: *mut LeanObject,
    mut v___y_782_: *mut LeanObject,
    mut v___y_783_: *mut LeanObject,
    mut v___y_784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_790_: u8 = 0;
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_798_: u8 = 0;
    let mut v_arg_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: u8 = 0;
    let mut v_arg_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_804_: u8 = 0;
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: u8 = 0;
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_812_: u8 = 0;
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_817_: u8 = 0;
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_830_: u8 = 0;
    let mut v_binderType_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_841_: u8 = 0;
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_847_: u8 = 0;
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_854_: u8 = 0;
    let mut v_a_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_858_: u8 = 0;
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_862_: u8 = 0;
    let mut v_isSharedCheck_863_: u8 = 0;
    let mut v_unused_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_868_: u8 = 0;
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_872_: u8 = 0;
    let mut v_a_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_876_: u8 = 0;
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_880_: u8 = 0;
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_885_: u8 = 0;
    let mut v_a_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_889_: u8 = 0;
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_893_: u8 = 0;
    let mut v_a_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_897_: u8 = 0;
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_901_: u8 = 0;
    let mut v_a_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_905_: u8 = 0;
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_909_: u8 = 0;
    let mut v_a_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_913_: u8 = 0;
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_917_: u8 = 0;
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_929_: u8 = 0;
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_934_: u8 = 0;
    let mut v_a_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_938_: u8 = 0;
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_942_: u8 = 0;
    let mut v_isSharedCheck_943_: u8 = 0;
    let mut v_a_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_947_: u8 = 0;
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_951_: u8 = 0;
    let mut v_isSharedCheck_952_: u8 = 0;
    let mut v_a_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_956_: u8 = 0;
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_960_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_fvarId_779_);
                v___x_786_ = l_Lean_FVarId_getDecl___redArg(
                    v_fvarId_779_,
                    v___y_781_,
                    v___y_783_,
                    v___y_784_,
                );
                if lean_obj_tag(v___x_786_) == 0 {
                    v_a_787_ = lean_ctor_get(v___x_786_, 0);
                    v_isSharedCheck_952_ = (!lean_is_exclusive(v___x_786_)) as u8;
                    if v_isSharedCheck_952_ == 0 {
                        v___x_789_ = v___x_786_;
                        v_isShared_790_ = v_isSharedCheck_952_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_787_);
                        lean_dec(v___x_786_);
                        v___x_789_ = lean_box(0);
                        v_isShared_790_ = v_isSharedCheck_952_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___y_784_);
                    lean_dec_ref(v___y_783_);
                    lean_dec(v___y_782_);
                    lean_dec_ref(v___y_781_);
                    lean_dec(v_mvarId_780_);
                    lean_dec(v_fvarId_779_);
                    v_a_953_ = lean_ctor_get(v___x_786_, 0);
                    v_isSharedCheck_960_ = (!lean_is_exclusive(v___x_786_)) as u8;
                    if v_isSharedCheck_960_ == 0 {
                        v___x_955_ = v___x_786_;
                        v_isShared_956_ = v_isSharedCheck_960_;
                        state = 34;
                        continue;
                    } else {
                        lean_inc(v_a_953_);
                        lean_dec(v___x_786_);
                        v___x_955_ = lean_box(0);
                        v_isShared_956_ = v_isSharedCheck_960_;
                        state = 34;
                        continue;
                    }
                }
            }
            1 => {
                v___x_796_ = l_Lean_LocalDecl_type(v_a_787_);
                lean_dec(v_a_787_);
                v___x_797_ = l_Lean_Expr_cleanupAnnotations(v___x_796_);
                v___x_798_ = l_Lean_Expr_isApp(v___x_797_);
                if v___x_798_ == 0 {
                    lean_dec_ref(v___x_797_);
                    lean_dec(v___y_784_);
                    lean_dec_ref(v___y_783_);
                    lean_dec(v___y_782_);
                    lean_dec_ref(v___y_781_);
                    lean_dec(v_mvarId_780_);
                    lean_dec(v_fvarId_779_);
                    state = 2;
                    continue;
                } else {
                    v_arg_799_ = lean_ctor_get(v___x_797_, 1);
                    lean_inc_ref(v_arg_799_);
                    v___x_800_ = l_Lean_Expr_appFnCleanup___redArg(v___x_797_);
                    v___x_801_ = l_Lean_Expr_isApp(v___x_800_);
                    if v___x_801_ == 0 {
                        lean_dec_ref(v___x_800_);
                        lean_dec_ref(v_arg_799_);
                        lean_dec(v___y_784_);
                        lean_dec_ref(v___y_783_);
                        lean_dec(v___y_782_);
                        lean_dec_ref(v___y_781_);
                        lean_dec(v_mvarId_780_);
                        lean_dec(v_fvarId_779_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_802_ = lean_ctor_get(v___x_800_, 1);
                        lean_inc_ref(v_arg_802_);
                        v___x_803_ = l_Lean_Expr_appFnCleanup___redArg(v___x_800_);
                        v___x_804_ = l_Lean_Expr_isApp(v___x_803_);
                        if v___x_804_ == 0 {
                            lean_dec_ref(v___x_803_);
                            lean_dec_ref(v_arg_802_);
                            lean_dec_ref(v_arg_799_);
                            lean_dec(v___y_784_);
                            lean_dec_ref(v___y_783_);
                            lean_dec(v___y_782_);
                            lean_dec_ref(v___y_781_);
                            lean_dec(v_mvarId_780_);
                            lean_dec(v_fvarId_779_);
                            state = 2;
                            continue;
                        } else {
                            v___x_805_ = l_Lean_Expr_appFnCleanup___redArg(v___x_803_);
                            v___x_806_ = l_Lean_Meta_Grind_injection_x3f___lam__0___closed__1;
                            v___x_807_ = l_Lean_Expr_isConstOf(v___x_805_, v___x_806_);
                            lean_dec_ref(v___x_805_);
                            if v___x_807_ == 0 {
                                lean_dec_ref(v_arg_802_);
                                lean_dec_ref(v_arg_799_);
                                lean_dec(v___y_784_);
                                lean_dec_ref(v___y_783_);
                                lean_dec(v___y_782_);
                                lean_dec_ref(v___y_781_);
                                lean_dec(v_mvarId_780_);
                                lean_dec(v_fvarId_779_);
                                state = 2;
                                continue;
                            } else {
                                lean_del_object(v___x_789_);
                                v___x_808_ = l_Lean_Meta_isConstructorAppCore_x3f___redArg(
                                    v_arg_802_, v___y_784_,
                                );
                                lean_dec_ref(v_arg_802_);
                                if lean_obj_tag(v___x_808_) == 0 {
                                    v_a_809_ = lean_ctor_get(v___x_808_, 0);
                                    v_isSharedCheck_943_ = (!lean_is_exclusive(v___x_808_)) as u8;
                                    if v_isSharedCheck_943_ == 0 {
                                        v___x_811_ = v___x_808_;
                                        v_isShared_812_ = v_isSharedCheck_943_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_809_);
                                        lean_dec(v___x_808_);
                                        v___x_811_ = lean_box(0);
                                        v_isShared_812_ = v_isSharedCheck_943_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_arg_799_);
                                    lean_dec(v___y_784_);
                                    lean_dec_ref(v___y_783_);
                                    lean_dec(v___y_782_);
                                    lean_dec_ref(v___y_781_);
                                    lean_dec(v_mvarId_780_);
                                    lean_dec(v_fvarId_779_);
                                    v_a_944_ = lean_ctor_get(v___x_808_, 0);
                                    v_isSharedCheck_951_ = (!lean_is_exclusive(v___x_808_)) as u8;
                                    if v_isSharedCheck_951_ == 0 {
                                        v___x_946_ = v___x_808_;
                                        v_isShared_947_ = v_isSharedCheck_951_;
                                        state = 32;
                                        continue;
                                    } else {
                                        lean_inc(v_a_944_);
                                        lean_dec(v___x_808_);
                                        v___x_946_ = lean_box(0);
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
                v___x_792_ = lean_box(0);
                if v_isShared_790_ == 0 {
                    lean_ctor_set(v___x_789_, 0, v___x_792_);
                    v___x_794_ = v___x_789_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_795_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_795_, 0, v___x_792_);
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
                lean_dec_ref(v_arg_799_);
                if lean_obj_tag(v___x_813_) == 0 {
                    v_a_814_ = lean_ctor_get(v___x_813_, 0);
                    v_isSharedCheck_934_ = (!lean_is_exclusive(v___x_813_)) as u8;
                    if v_isSharedCheck_934_ == 0 {
                        v___x_816_ = v___x_813_;
                        v_isShared_817_ = v_isSharedCheck_934_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_814_);
                        lean_dec(v___x_813_);
                        v___x_816_ = lean_box(0);
                        v_isShared_817_ = v_isSharedCheck_934_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_811_);
                    lean_dec(v_a_809_);
                    lean_dec(v___y_784_);
                    lean_dec_ref(v___y_783_);
                    lean_dec(v___y_782_);
                    lean_dec_ref(v___y_781_);
                    lean_dec(v_mvarId_780_);
                    lean_dec(v_fvarId_779_);
                    v_a_935_ = lean_ctor_get(v___x_813_, 0);
                    v_isSharedCheck_942_ = (!lean_is_exclusive(v___x_813_)) as u8;
                    if v_isSharedCheck_942_ == 0 {
                        v___x_937_ = v___x_813_;
                        v_isShared_938_ = v_isSharedCheck_942_;
                        state = 30;
                        continue;
                    } else {
                        lean_inc(v_a_935_);
                        lean_dec(v___x_813_);
                        v___x_937_ = lean_box(0);
                        v_isShared_938_ = v_isSharedCheck_942_;
                        state = 30;
                        continue;
                    }
                }
            }
            5 => {
                if lean_obj_tag(v_a_809_) == 1 {
                    if lean_obj_tag(v_a_814_) == 1 {
                        lean_del_object(v___x_816_);
                        v_val_923_ = lean_ctor_get(v_a_809_, 0);
                        lean_inc(v_val_923_);
                        lean_dec_ref_known(v_a_809_, 1);
                        v_toConstantVal_924_ = lean_ctor_get(v_val_923_, 0);
                        lean_inc_ref(v_toConstantVal_924_);
                        lean_dec(v_val_923_);
                        v_val_925_ = lean_ctor_get(v_a_814_, 0);
                        lean_inc(v_val_925_);
                        lean_dec_ref_known(v_a_814_, 1);
                        v_toConstantVal_926_ = lean_ctor_get(v_val_925_, 0);
                        lean_inc_ref(v_toConstantVal_926_);
                        lean_dec(v_val_925_);
                        v_name_927_ = lean_ctor_get(v_toConstantVal_924_, 0);
                        lean_inc(v_name_927_);
                        lean_dec_ref(v_toConstantVal_924_);
                        v_name_928_ = lean_ctor_get(v_toConstantVal_926_, 0);
                        lean_inc(v_name_928_);
                        lean_dec_ref(v_toConstantVal_926_);
                        v___x_929_ = lean_name_eq(v_name_927_, v_name_928_);
                        lean_dec(v_name_928_);
                        lean_dec(v_name_927_);
                        if v___x_929_ == 0 {
                            if v___x_807_ == 0 {
                                lean_del_object(v___x_811_);
                                state = 6;
                                continue;
                            } else {
                                lean_dec(v___y_784_);
                                lean_dec_ref(v___y_783_);
                                lean_dec(v___y_782_);
                                lean_dec_ref(v___y_781_);
                                lean_dec(v_mvarId_780_);
                                lean_dec(v_fvarId_779_);
                                v___x_930_ = lean_box(0);
                                if v_isShared_812_ == 0 {
                                    lean_ctor_set(v___x_811_, 0, v___x_930_);
                                    v___x_932_ = v___x_811_;
                                    state = 29;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_930_);
                                    v___x_932_ = v_reuseFailAlloc_933_;
                                    state = 29;
                                    continue;
                                }
                            }
                        } else {
                            lean_del_object(v___x_811_);
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_a_809_, 1);
                        lean_dec(v_a_814_);
                        lean_del_object(v___x_811_);
                        lean_dec(v___y_784_);
                        lean_dec_ref(v___y_783_);
                        lean_dec(v___y_782_);
                        lean_dec_ref(v___y_781_);
                        lean_dec(v_mvarId_780_);
                        lean_dec(v_fvarId_779_);
                        state = 27;
                        continue;
                    }
                } else {
                    lean_dec(v_a_814_);
                    lean_del_object(v___x_811_);
                    lean_dec(v_a_809_);
                    lean_dec(v___y_784_);
                    lean_dec_ref(v___y_783_);
                    lean_dec(v___y_782_);
                    lean_dec_ref(v___y_781_);
                    lean_dec(v_mvarId_780_);
                    lean_dec(v_fvarId_779_);
                    state = 27;
                    continue;
                }
            }
            6 => {
                lean_inc(v_mvarId_780_);
                v___x_819_ = l_Lean_MVarId_getType(
                    v_mvarId_780_,
                    v___y_781_,
                    v___y_782_,
                    v___y_783_,
                    v___y_784_,
                );
                if lean_obj_tag(v___x_819_) == 0 {
                    v_a_820_ = lean_ctor_get(v___x_819_, 0);
                    lean_inc(v_a_820_);
                    lean_dec_ref_known(v___x_819_, 1);
                    lean_inc(v_fvarId_779_);
                    v___x_821_ = l_Lean_mkFVar(v_fvarId_779_);
                    v___x_822_ = l_Lean_Meta_mkNoConfusion(
                        v_a_820_, v___x_821_, v___y_781_, v___y_782_, v___y_783_, v___y_784_,
                    );
                    if lean_obj_tag(v___x_822_) == 0 {
                        v_a_823_ = lean_ctor_get(v___x_822_, 0);
                        lean_inc_n(v_a_823_, 2);
                        lean_dec_ref_known(v___x_822_, 1);
                        lean_inc(v___y_784_);
                        lean_inc_ref(v___y_783_);
                        lean_inc(v___y_782_);
                        lean_inc_ref(v___y_781_);
                        v___x_824_ = lean_infer_type(
                            v_a_823_, v___y_781_, v___y_782_, v___y_783_, v___y_784_,
                        );
                        if lean_obj_tag(v___x_824_) == 0 {
                            v_a_825_ = lean_ctor_get(v___x_824_, 0);
                            lean_inc(v_a_825_);
                            lean_dec_ref_known(v___x_824_, 1);
                            v___x_826_ = l_Lean_Meta_whnfD(
                                v_a_825_, v___y_781_, v___y_782_, v___y_783_, v___y_784_,
                            );
                            if lean_obj_tag(v___x_826_) == 0 {
                                v_a_827_ = lean_ctor_get(v___x_826_, 0);
                                v_isSharedCheck_885_ = (!lean_is_exclusive(v___x_826_)) as u8;
                                if v_isSharedCheck_885_ == 0 {
                                    v___x_829_ = v___x_826_;
                                    v_isShared_830_ = v_isSharedCheck_885_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_827_);
                                    lean_dec(v___x_826_);
                                    v___x_829_ = lean_box(0);
                                    v_isShared_830_ = v_isSharedCheck_885_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_823_);
                                lean_dec(v___y_784_);
                                lean_dec_ref(v___y_783_);
                                lean_dec(v___y_782_);
                                lean_dec_ref(v___y_781_);
                                lean_dec(v_mvarId_780_);
                                lean_dec(v_fvarId_779_);
                                v_a_886_ = lean_ctor_get(v___x_826_, 0);
                                v_isSharedCheck_893_ = (!lean_is_exclusive(v___x_826_)) as u8;
                                if v_isSharedCheck_893_ == 0 {
                                    v___x_888_ = v___x_826_;
                                    v_isShared_889_ = v_isSharedCheck_893_;
                                    state = 19;
                                    continue;
                                } else {
                                    lean_inc(v_a_886_);
                                    lean_dec(v___x_826_);
                                    v___x_888_ = lean_box(0);
                                    v_isShared_889_ = v_isSharedCheck_893_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_823_);
                            lean_dec(v___y_784_);
                            lean_dec_ref(v___y_783_);
                            lean_dec(v___y_782_);
                            lean_dec_ref(v___y_781_);
                            lean_dec(v_mvarId_780_);
                            lean_dec(v_fvarId_779_);
                            v_a_894_ = lean_ctor_get(v___x_824_, 0);
                            v_isSharedCheck_901_ = (!lean_is_exclusive(v___x_824_)) as u8;
                            if v_isSharedCheck_901_ == 0 {
                                v___x_896_ = v___x_824_;
                                v_isShared_897_ = v_isSharedCheck_901_;
                                state = 21;
                                continue;
                            } else {
                                lean_inc(v_a_894_);
                                lean_dec(v___x_824_);
                                v___x_896_ = lean_box(0);
                                v_isShared_897_ = v_isSharedCheck_901_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___y_784_);
                        lean_dec_ref(v___y_783_);
                        lean_dec(v___y_782_);
                        lean_dec_ref(v___y_781_);
                        lean_dec(v_mvarId_780_);
                        lean_dec(v_fvarId_779_);
                        v_a_902_ = lean_ctor_get(v___x_822_, 0);
                        v_isSharedCheck_909_ = (!lean_is_exclusive(v___x_822_)) as u8;
                        if v_isSharedCheck_909_ == 0 {
                            v___x_904_ = v___x_822_;
                            v_isShared_905_ = v_isSharedCheck_909_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_902_);
                            lean_dec(v___x_822_);
                            v___x_904_ = lean_box(0);
                            v_isShared_905_ = v_isSharedCheck_909_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___y_784_);
                    lean_dec_ref(v___y_783_);
                    lean_dec(v___y_782_);
                    lean_dec_ref(v___y_781_);
                    lean_dec(v_mvarId_780_);
                    lean_dec(v_fvarId_779_);
                    v_a_910_ = lean_ctor_get(v___x_819_, 0);
                    v_isSharedCheck_917_ = (!lean_is_exclusive(v___x_819_)) as u8;
                    if v_isSharedCheck_917_ == 0 {
                        v___x_912_ = v___x_819_;
                        v_isShared_913_ = v_isSharedCheck_917_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_910_);
                        lean_dec(v___x_819_);
                        v___x_912_ = lean_box(0);
                        v_isShared_913_ = v_isSharedCheck_917_;
                        state = 25;
                        continue;
                    }
                }
            }
            7 => {
                if lean_obj_tag(v_a_827_) == 7 {
                    lean_del_object(v___x_829_);
                    v_binderType_831_ = lean_ctor_get(v_a_827_, 1);
                    lean_inc_ref(v_binderType_831_);
                    lean_dec_ref_known(v_a_827_, 3);
                    lean_inc(v_mvarId_780_);
                    v___x_832_ = l_Lean_MVarId_getTag(
                        v_mvarId_780_,
                        v___y_781_,
                        v___y_782_,
                        v___y_783_,
                        v___y_784_,
                    );
                    if lean_obj_tag(v___x_832_) == 0 {
                        v_a_833_ = lean_ctor_get(v___x_832_, 0);
                        lean_inc(v_a_833_);
                        lean_dec_ref_known(v___x_832_, 1);
                        v___x_834_ = l_Lean_Expr_headBeta(v_binderType_831_);
                        v___x_835_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                            v___x_834_, v_a_833_, v___y_781_, v___y_782_, v___y_783_, v___y_784_,
                        );
                        if lean_obj_tag(v___x_835_) == 0 {
                            v_a_836_ = lean_ctor_get(v___x_835_, 0);
                            lean_inc_n(v_a_836_, 2);
                            lean_dec_ref_known(v___x_835_, 1);
                            v___x_837_ = l_Lean_Expr_app___override(v_a_823_, v_a_836_);
                            v___x_838_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0___redArg(v_mvarId_780_, v___x_837_, v___y_782_);
                            v_isSharedCheck_863_ = (!lean_is_exclusive(v___x_838_)) as u8;
                            if v_isSharedCheck_863_ == 0 {
                                v_unused_864_ = lean_ctor_get(v___x_838_, 0);
                                lean_dec(v_unused_864_);
                                v___x_840_ = v___x_838_;
                                v_isShared_841_ = v_isSharedCheck_863_;
                                state = 8;
                                continue;
                            } else {
                                lean_dec(v___x_838_);
                                v___x_840_ = lean_box(0);
                                v_isShared_841_ = v_isSharedCheck_863_;
                                state = 8;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_823_);
                            lean_dec(v___y_784_);
                            lean_dec_ref(v___y_783_);
                            lean_dec(v___y_782_);
                            lean_dec_ref(v___y_781_);
                            lean_dec(v_mvarId_780_);
                            lean_dec(v_fvarId_779_);
                            v_a_865_ = lean_ctor_get(v___x_835_, 0);
                            v_isSharedCheck_872_ = (!lean_is_exclusive(v___x_835_)) as u8;
                            if v_isSharedCheck_872_ == 0 {
                                v___x_867_ = v___x_835_;
                                v_isShared_868_ = v_isSharedCheck_872_;
                                state = 14;
                                continue;
                            } else {
                                lean_inc(v_a_865_);
                                lean_dec(v___x_835_);
                                v___x_867_ = lean_box(0);
                                v_isShared_868_ = v_isSharedCheck_872_;
                                state = 14;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_binderType_831_);
                        lean_dec(v_a_823_);
                        lean_dec(v___y_784_);
                        lean_dec_ref(v___y_783_);
                        lean_dec(v___y_782_);
                        lean_dec_ref(v___y_781_);
                        lean_dec(v_mvarId_780_);
                        lean_dec(v_fvarId_779_);
                        v_a_873_ = lean_ctor_get(v___x_832_, 0);
                        v_isSharedCheck_880_ = (!lean_is_exclusive(v___x_832_)) as u8;
                        if v_isSharedCheck_880_ == 0 {
                            v___x_875_ = v___x_832_;
                            v_isShared_876_ = v_isSharedCheck_880_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_a_873_);
                            lean_dec(v___x_832_);
                            v___x_875_ = lean_box(0);
                            v_isShared_876_ = v_isSharedCheck_880_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_827_);
                    lean_dec(v_a_823_);
                    lean_dec(v___y_784_);
                    lean_dec_ref(v___y_783_);
                    lean_dec(v___y_782_);
                    lean_dec_ref(v___y_781_);
                    lean_dec(v_mvarId_780_);
                    lean_dec(v_fvarId_779_);
                    v___x_881_ = lean_box(0);
                    if v_isShared_830_ == 0 {
                        lean_ctor_set(v___x_829_, 0, v___x_881_);
                        v___x_883_ = v___x_829_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
                        v___x_883_ = v_reuseFailAlloc_884_;
                        state = 18;
                        continue;
                    }
                }
            }
            8 => {
                v___x_842_ = l_Lean_Expr_mvarId_x21(v_a_836_);
                lean_dec(v_a_836_);
                v___x_843_ = l_Lean_MVarId_tryClear(
                    v___x_842_,
                    v_fvarId_779_,
                    v___y_781_,
                    v___y_782_,
                    v___y_783_,
                    v___y_784_,
                );
                lean_dec(v___y_784_);
                lean_dec_ref(v___y_783_);
                lean_dec(v___y_782_);
                lean_dec_ref(v___y_781_);
                if lean_obj_tag(v___x_843_) == 0 {
                    v_a_844_ = lean_ctor_get(v___x_843_, 0);
                    v_isSharedCheck_854_ = (!lean_is_exclusive(v___x_843_)) as u8;
                    if v_isSharedCheck_854_ == 0 {
                        v___x_846_ = v___x_843_;
                        v_isShared_847_ = v_isSharedCheck_854_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_844_);
                        lean_dec(v___x_843_);
                        v___x_846_ = lean_box(0);
                        v_isShared_847_ = v_isSharedCheck_854_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_840_);
                    v_a_855_ = lean_ctor_get(v___x_843_, 0);
                    v_isSharedCheck_862_ = (!lean_is_exclusive(v___x_843_)) as u8;
                    if v_isSharedCheck_862_ == 0 {
                        v___x_857_ = v___x_843_;
                        v_isShared_858_ = v_isSharedCheck_862_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_855_);
                        lean_dec(v___x_843_);
                        v___x_857_ = lean_box(0);
                        v_isShared_858_ = v_isSharedCheck_862_;
                        state = 12;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_841_ == 0 {
                    lean_ctor_set_tag(v___x_840_, 1);
                    lean_ctor_set(v___x_840_, 0, v_a_844_);
                    v___x_849_ = v___x_840_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_844_);
                    v___x_849_ = v_reuseFailAlloc_853_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_847_ == 0 {
                    lean_ctor_set(v___x_846_, 0, v___x_849_);
                    v___x_851_ = v___x_846_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
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
                    v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
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
                    v_reuseFailAlloc_871_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_871_, 0, v_a_865_);
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
                    v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_879_, 0, v_a_873_);
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
                    v_reuseFailAlloc_892_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_892_, 0, v_a_886_);
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
                    v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
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
                    v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
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
                    v_reuseFailAlloc_916_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_916_, 0, v_a_910_);
                    v___x_915_ = v_reuseFailAlloc_916_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_915_;
            }
            27 => {
                v___x_919_ = lean_box(0);
                if v_isShared_817_ == 0 {
                    lean_ctor_set(v___x_816_, 0, v___x_919_);
                    v___x_921_ = v___x_816_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_922_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_922_, 0, v___x_919_);
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
                    v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
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
                    v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
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
                    v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
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
    mut v_fvarId_961_: *mut LeanObject,
    mut v_mvarId_962_: *mut LeanObject,
    mut v___y_963_: *mut LeanObject,
    mut v___y_964_: *mut LeanObject,
    mut v___y_965_: *mut LeanObject,
    mut v___y_966_: *mut LeanObject,
    mut v___y_967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_968_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_mvarId_969_: *mut LeanObject,
    mut v_fvarId_970_: *mut LeanObject,
    mut v_a_971_: *mut LeanObject,
    mut v_a_972_: *mut LeanObject,
    mut v_a_973_: *mut LeanObject,
    mut v_a_974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_mvarId_969_);
    v___f_976_ = lean_alloc_closure(
        l_Lean_Meta_Grind_injection_x3f___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___f_976_, 0, v_fvarId_970_);
    lean_closure_set(v___f_976_, 1, v_mvarId_969_);
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
    mut v_mvarId_978_: *mut LeanObject,
    mut v_fvarId_979_: *mut LeanObject,
    mut v_a_980_: *mut LeanObject,
    mut v_a_981_: *mut LeanObject,
    mut v_a_982_: *mut LeanObject,
    mut v_a_983_: *mut LeanObject,
    mut v_a_984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_985_: *mut LeanObject = core::ptr::null_mut();
    v_res_985_ = l_Lean_Meta_Grind_injection_x3f(
        v_mvarId_978_,
        v_fvarId_979_,
        v_a_980_,
        v_a_981_,
        v_a_982_,
        v_a_983_,
    );
    lean_dec(v_a_983_);
    lean_dec_ref(v_a_982_);
    lean_dec(v_a_981_);
    lean_dec_ref(v_a_980_);
    return v_res_985_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0(
    mut v_mvarId_986_: *mut LeanObject,
    mut v_val_987_: *mut LeanObject,
    mut v___y_988_: *mut LeanObject,
    mut v___y_989_: *mut LeanObject,
    mut v___y_990_: *mut LeanObject,
    mut v___y_991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    v___x_993_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0___redArg(
        v_mvarId_986_,
        v_val_987_,
        v___y_989_,
    );
    return v___x_993_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0___boxed(
    mut v_mvarId_994_: *mut LeanObject,
    mut v_val_995_: *mut LeanObject,
    mut v___y_996_: *mut LeanObject,
    mut v___y_997_: *mut LeanObject,
    mut v___y_998_: *mut LeanObject,
    mut v___y_999_: *mut LeanObject,
    mut v___y_1000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1001_: *mut LeanObject = core::ptr::null_mut();
    v_res_1001_ = l_Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0(
        v_mvarId_994_,
        v_val_995_,
        v___y_996_,
        v___y_997_,
        v___y_998_,
        v___y_999_,
    );
    lean_dec(v___y_999_);
    lean_dec_ref(v___y_998_);
    lean_dec(v___y_997_);
    lean_dec_ref(v___y_996_);
    return v_res_1001_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0(
    mut v_00_u03b2_1002_: *mut LeanObject,
    mut v_x_1003_: *mut LeanObject,
    mut v_x_1004_: *mut LeanObject,
    mut v_x_1005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    v___x_1006_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0___redArg(v_x_1003_, v_x_1004_, v_x_1005_);
    return v___x_1006_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2(
    mut v_00_u03b2_1007_: *mut LeanObject,
    mut v_x_1008_: *mut LeanObject,
    mut v_x_1009_: usize,
    mut v_x_1010_: usize,
    mut v_x_1011_: *mut LeanObject,
    mut v_x_1012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
    v___x_1013_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___redArg(v_x_1008_, v_x_1009_, v_x_1010_, v_x_1011_, v_x_1012_);
    return v___x_1013_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_1014_: *mut LeanObject,
    mut v_x_1015_: *mut LeanObject,
    mut v_x_1016_: *mut LeanObject,
    mut v_x_1017_: *mut LeanObject,
    mut v_x_1018_: *mut LeanObject,
    mut v_x_1019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_5428__boxed_1020_: usize = 0;
    let mut v_x_5429__boxed_1021_: usize = 0;
    let mut v_res_1022_: *mut LeanObject = core::ptr::null_mut();
    v_x_5428__boxed_1020_ = lean_unbox_usize(v_x_1016_);
    lean_dec(v_x_1016_);
    v_x_5429__boxed_1021_ = lean_unbox_usize(v_x_1017_);
    lean_dec(v_x_1017_);
    v_res_1022_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2(v_00_u03b2_1014_, v_x_1015_, v_x_5428__boxed_1020_, v_x_5429__boxed_1021_, v_x_1018_, v_x_1019_);
    return v_res_1022_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b2_1023_: *mut LeanObject,
    mut v_n_1024_: *mut LeanObject,
    mut v_k_1025_: *mut LeanObject,
    mut v_v_1026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    v___x_1027_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3___redArg(v_n_1024_, v_k_1025_, v_v_1026_);
    return v___x_1027_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_1028_: *mut LeanObject,
    mut v_depth_1029_: usize,
    mut v_keys_1030_: *mut LeanObject,
    mut v_vals_1031_: *mut LeanObject,
    mut v_heq_1032_: *mut LeanObject,
    mut v_i_1033_: *mut LeanObject,
    mut v_entries_1034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    v___x_1035_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_1029_, v_keys_1030_, v_vals_1031_, v_i_1033_, v_entries_1034_);
    return v___x_1035_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b2_1036_: *mut LeanObject,
    mut v_depth_1037_: *mut LeanObject,
    mut v_keys_1038_: *mut LeanObject,
    mut v_vals_1039_: *mut LeanObject,
    mut v_heq_1040_: *mut LeanObject,
    mut v_i_1041_: *mut LeanObject,
    mut v_entries_1042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1043_: usize = 0;
    let mut v_res_1044_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1043_ = lean_unbox_usize(v_depth_1037_);
    lean_dec(v_depth_1037_);
    v_res_1044_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_1036_, v_depth_boxed_1043_, v_keys_1038_, v_vals_1039_, v_heq_1040_, v_i_1041_, v_entries_1042_);
    lean_dec_ref(v_vals_1039_);
    lean_dec_ref(v_keys_1038_);
    return v_res_1044_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3_spec__4(
    mut v_00_u03b2_1045_: *mut LeanObject,
    mut v_x_1046_: *mut LeanObject,
    mut v_x_1047_: *mut LeanObject,
    mut v_x_1048_: *mut LeanObject,
    mut v_x_1049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
    v___x_1050_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Grind_injection_x3f_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_1046_, v_x_1047_, v_x_1048_, v_x_1049_);
    return v___x_1050_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Injection(builtin: u8) -> *mut LeanObject {
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
    res = runtime_initialize_Lean_Meta_Tactic_Clear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CtorRecognizer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Injection(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Injection(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Lean_Meta_Tactic_Clear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_CtorRecognizer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Injection(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Injection(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Injection(builtin);
}

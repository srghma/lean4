// Lean compiler output
// Module: Lean.Elab.Tactic.AsAuxLemma
// Imports: Lean.Elab.Tactic.Meta
use crate::r#gen::Init::Data::List::Basic::l_List_isEmpty___redArg;
use crate::r#gen::Init::Prelude::{l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_evalTactic___boxed, l_Lean_Elab_Tactic_getMainGoal___redArg,
    l_Lean_Elab_Tactic_run, l_Lean_Elab_Tactic_tacticElabAttribute,
    l_Lean_Elab_Tactic_withMainContext___redArg,
};
use crate::r#gen::Lean::Elab::Tactic::Meta::{
    initialize_Lean_Elab_Tactic_Meta, runtime_initialize_Lean_Elab_Tactic_Meta,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_hasMVar, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_mkMVar,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::Closure::l_Lean_Meta_mkAuxTheorem;
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_getType;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_nat_add,
    lean_nat_dec_lt,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_elabAsAuxLemma___lam__0___closed__0_value: crate::leanh::LeanStringObject<72> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 72,
        m_capacity: 72,
        m_length: 71,
        m_data: [
            67, 97, 110, 110, 111, 116, 32, 97, 98, 115, 116, 114, 97, 99, 116, 32, 116, 101, 114,
            109, 32, 105, 110, 116, 111, 32, 97, 117, 120, 105, 108, 105, 97, 114, 121, 32, 108,
            101, 109, 109, 97, 32, 98, 101, 99, 97, 117, 115, 101, 32, 116, 104, 101, 114, 101, 32,
            97, 114, 101, 32, 111, 112, 101, 110, 32, 103, 111, 97, 108, 115, 46, 0,
        ],
    };
static mut l_elabAsAuxLemma___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_elabAsAuxLemma___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_elabAsAuxLemma___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_elabAsAuxLemma___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_elabAsAuxLemma___closed__0_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_elabAsAuxLemma___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_elabAsAuxLemma___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_elabAsAuxLemma___closed__1_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [80, 97, 114, 115, 101, 114, 0],
    };
static mut l_elabAsAuxLemma___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_elabAsAuxLemma___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_elabAsAuxLemma___closed__2_value: crate::leanh::LeanStringObject<7> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [84, 97, 99, 116, 105, 99, 0],
    };
static mut l_elabAsAuxLemma___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_elabAsAuxLemma___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_elabAsAuxLemma___closed__3_value: crate::leanh::LeanStringObject<13> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [97, 115, 95, 97, 117, 120, 95, 108, 101, 109, 109, 97, 0],
    };
static mut l_elabAsAuxLemma___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_elabAsAuxLemma___closed__3_value) as *mut crate::leanh::LeanObject;
static l_elabAsAuxLemma___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_elabAsAuxLemma___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_elabAsAuxLemma___closed__4_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_elabAsAuxLemma___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_elabAsAuxLemma___closed__1_value)
                as *mut crate::leanh::LeanObject,
            8018486133748762727 as *mut crate::leanh::LeanObject,
        ],
    };
static l_elabAsAuxLemma___closed__4_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_elabAsAuxLemma___closed__4_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_elabAsAuxLemma___closed__2_value)
                as *mut crate::leanh::LeanObject,
            18344149449936419494 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_elabAsAuxLemma___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_elabAsAuxLemma___closed__4_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_elabAsAuxLemma___closed__3_value)
                as *mut crate::leanh::LeanObject,
            10642961203014691832 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_elabAsAuxLemma___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_elabAsAuxLemma___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_elabAsAuxLemma___closed__5_value: crate::leanh::LeanStringObject<28> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            73, 110, 118, 97, 108, 105, 100, 32, 97, 115, 95, 97, 117, 120, 95, 108, 101, 109, 109,
            97, 32, 115, 121, 110, 116, 97, 120, 0,
        ],
    };
static mut l_elabAsAuxLemma___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_elabAsAuxLemma___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_elabAsAuxLemma___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_elabAsAuxLemma___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 108, 97, 98, 65, 115, 65, 117, 120, 76, 101, 109, 109, 97, 0]};
static mut l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__0_value) as *mut crate::leanh::LeanObject,15561659288978570640 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg(
    mut v_e_534_: *mut crate::leanh::LeanObject,
    mut v___y_535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_537_: u8 = 0;
    let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_551_: u8 = 0;
    let mut v___x_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_557_: u8 = 0;
    let mut v_unused_558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_537_ = l_Lean_Expr_hasMVar(v_e_534_);
                if v___x_537_ == 0 {
                    v___x_538_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_538_, 0, v_e_534_);
                    return v___x_538_;
                } else {
                    v___x_539_ = lean_st_ref_get(v___y_535_);
                    v_mctx_540_ = crate::leanh::lean_ctor_get(v___x_539_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_540_);
                    crate::leanh::lean_dec(v___x_539_);
                    v___x_541_ = l_Lean_instantiateMVarsCore(v_mctx_540_, v_e_534_);
                    v_fst_542_ = crate::leanh::lean_ctor_get(v___x_541_, 0);
                    crate::leanh::lean_inc(v_fst_542_);
                    v_snd_543_ = crate::leanh::lean_ctor_get(v___x_541_, 1);
                    crate::leanh::lean_inc(v_snd_543_);
                    crate::leanh::lean_dec_ref(v___x_541_);
                    v___x_544_ = lean_st_ref_take(v___y_535_);
                    v_cache_545_ = crate::leanh::lean_ctor_get(v___x_544_, 1);
                    v_zetaDeltaFVarIds_546_ = crate::leanh::lean_ctor_get(v___x_544_, 2);
                    v_postponed_547_ = crate::leanh::lean_ctor_get(v___x_544_, 3);
                    v_diag_548_ = crate::leanh::lean_ctor_get(v___x_544_, 4);
                    v_isSharedCheck_557_ = (!crate::leanh::lean_is_exclusive(v___x_544_)) as u8;
                    if v_isSharedCheck_557_ == 0 {
                        v_unused_558_ = crate::leanh::lean_ctor_get(v___x_544_, 0);
                        crate::leanh::lean_dec(v_unused_558_);
                        v___x_550_ = v___x_544_;
                        v_isShared_551_ = v_isSharedCheck_557_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_548_);
                        crate::leanh::lean_inc(v_postponed_547_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_546_);
                        crate::leanh::lean_inc(v_cache_545_);
                        crate::leanh::lean_dec(v___x_544_);
                        v___x_550_ = crate::leanh::lean_box(0);
                        v_isShared_551_ = v_isSharedCheck_557_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_551_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_550_, 0, v_snd_543_);
                    v___x_553_ = v___x_550_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_556_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_556_, 0, v_snd_543_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_556_, 1, v_cache_545_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_556_, 2, v_zetaDeltaFVarIds_546_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_556_, 3, v_postponed_547_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_556_, 4, v_diag_548_);
                    v___x_553_ = v_reuseFailAlloc_556_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_554_ = lean_st_ref_set(v___y_535_, v___x_553_);
                v___x_555_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_555_, 0, v_fst_542_);
                return v___x_555_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg___boxed(
    mut v_e_559_: *mut crate::leanh::LeanObject,
    mut v___y_560_: *mut crate::leanh::LeanObject,
    mut v___y_561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_562_ =
        l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg(v_e_559_, v___y_560_);
    crate::leanh::lean_dec(v___y_560_);
    return v_res_562_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1(
    mut v_e_563_: *mut crate::leanh::LeanObject,
    mut v___y_564_: *mut crate::leanh::LeanObject,
    mut v___y_565_: *mut crate::leanh::LeanObject,
    mut v___y_566_: *mut crate::leanh::LeanObject,
    mut v___y_567_: *mut crate::leanh::LeanObject,
    mut v___y_568_: *mut crate::leanh::LeanObject,
    mut v___y_569_: *mut crate::leanh::LeanObject,
    mut v___y_570_: *mut crate::leanh::LeanObject,
    mut v___y_571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_573_ =
        l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg(v_e_563_, v___y_569_);
    return v___x_573_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___boxed(
    mut v_e_574_: *mut crate::leanh::LeanObject,
    mut v___y_575_: *mut crate::leanh::LeanObject,
    mut v___y_576_: *mut crate::leanh::LeanObject,
    mut v___y_577_: *mut crate::leanh::LeanObject,
    mut v___y_578_: *mut crate::leanh::LeanObject,
    mut v___y_579_: *mut crate::leanh::LeanObject,
    mut v___y_580_: *mut crate::leanh::LeanObject,
    mut v___y_581_: *mut crate::leanh::LeanObject,
    mut v___y_582_: *mut crate::leanh::LeanObject,
    mut v___y_583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_584_ = l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1(
        v_e_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_,
        v___y_581_, v___y_582_,
    );
    crate::leanh::lean_dec(v___y_582_);
    crate::leanh::lean_dec_ref(v___y_581_);
    crate::leanh::lean_dec(v___y_580_);
    crate::leanh::lean_dec_ref(v___y_579_);
    crate::leanh::lean_dec(v___y_578_);
    crate::leanh::lean_dec_ref(v___y_577_);
    crate::leanh::lean_dec(v___y_576_);
    crate::leanh::lean_dec_ref(v___y_575_);
    return v_res_584_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(
    mut v_x_585_: *mut crate::leanh::LeanObject,
    mut v_x_586_: *mut crate::leanh::LeanObject,
    mut v_x_587_: *mut crate::leanh::LeanObject,
    mut v_x_588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_593_: u8 = 0;
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: u8 = 0;
    let mut v___x_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: u8 = 0;
    let mut v___x_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_614_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_589_ = crate::leanh::lean_ctor_get(v_x_585_, 0);
                v_vs_590_ = crate::leanh::lean_ctor_get(v_x_585_, 1);
                v_isSharedCheck_614_ = (!crate::leanh::lean_is_exclusive(v_x_585_)) as u8;
                if v_isSharedCheck_614_ == 0 {
                    v___x_592_ = v_x_585_;
                    v_isShared_593_ = v_isSharedCheck_614_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_590_);
                    crate::leanh::lean_inc(v_ks_589_);
                    crate::leanh::lean_dec(v_x_585_);
                    v___x_592_ = crate::leanh::lean_box(0);
                    v_isShared_593_ = v_isSharedCheck_614_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_594_ = lean_array_get_size(v_ks_589_);
                v___x_595_ = lean_nat_dec_lt(v_x_586_, v___x_594_);
                if v___x_595_ == 0 {
                    crate::leanh::lean_dec(v_x_586_);
                    v___x_596_ = lean_array_push(v_ks_589_, v_x_587_);
                    v___x_597_ = lean_array_push(v_vs_590_, v_x_588_);
                    if v_isShared_593_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_592_, 1, v___x_597_);
                        crate::leanh::lean_ctor_set(v___x_592_, 0, v___x_596_);
                        v___x_599_ = v___x_592_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_600_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_596_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_600_, 1, v___x_597_);
                        v___x_599_ = v_reuseFailAlloc_600_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_601_ = lean_array_fget_borrowed(v_ks_589_, v_x_586_);
                    v___x_602_ = l_Lean_instBEqMVarId_beq(v_x_587_, v_k_x27_601_);
                    if v___x_602_ == 0 {
                        if v_isShared_593_ == 0 {
                            v___x_604_ = v___x_592_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_608_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_608_, 0, v_ks_589_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_608_, 1, v_vs_590_);
                            v___x_604_ = v_reuseFailAlloc_608_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_609_ = lean_array_fset(v_ks_589_, v_x_586_, v_x_587_);
                        v___x_610_ = lean_array_fset(v_vs_590_, v_x_586_, v_x_588_);
                        crate::leanh::lean_dec(v_x_586_);
                        if v_isShared_593_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_592_, 1, v___x_610_);
                            crate::leanh::lean_ctor_set(v___x_592_, 0, v___x_609_);
                            v___x_612_ = v___x_592_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_613_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_609_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_613_, 1, v___x_610_);
                            v___x_612_ = v_reuseFailAlloc_613_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_599_;
            }
            3 => {
                v___x_605_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_606_ = lean_nat_add(v_x_586_, v___x_605_);
                crate::leanh::lean_dec(v_x_586_);
                v_x_585_ = v___x_604_;
                v_x_586_ = v___x_606_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_612_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5___redArg(
    mut v_n_615_: *mut crate::leanh::LeanObject,
    mut v_k_616_: *mut crate::leanh::LeanObject,
    mut v_v_617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_618_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_619_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_n_615_, v___x_618_, v_k_616_, v_v_617_);
    return v___x_619_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_620_: usize = 0;
    let mut v___x_621_: usize = 0;
    let mut v___x_622_: usize = 0;
    v___x_620_ = 5usize;
    v___x_621_ = 1usize;
    v___x_622_ = lean_usize_shift_left(v___x_621_, v___x_620_);
    return v___x_622_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__1()
-> usize {
    let mut v___x_623_: usize = 0;
    let mut v___x_624_: usize = 0;
    let mut v___x_625_: usize = 0;
    v___x_623_ = 1usize;
    v___x_624_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_625_ = lean_usize_sub(v___x_624_, v___x_623_);
    return v___x_625_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_626_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_626_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(
    mut v_x_627_: *mut crate::leanh::LeanObject,
    mut v_x_628_: usize,
    mut v_x_629_: usize,
    mut v_x_630_: *mut crate::leanh::LeanObject,
    mut v_x_631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: usize = 0;
    let mut v___x_634_: usize = 0;
    let mut v___x_635_: usize = 0;
    let mut v___x_636_: usize = 0;
    let mut v_j_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: u8 = 0;
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_642_: u8 = 0;
    let mut v_v_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_656_: u8 = 0;
    let mut v___x_657_: u8 = 0;
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_663_: u8 = 0;
    let mut v_node_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_667_: u8 = 0;
    let mut v___x_668_: usize = 0;
    let mut v___x_669_: usize = 0;
    let mut v___x_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_674_: u8 = 0;
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_676_: u8 = 0;
    let mut v_unused_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_682_: u8 = 0;
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_687_: u8 = 0;
    let mut v_ks_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: usize = 0;
    let mut v___x_694_: u8 = 0;
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: u8 = 0;
    let mut v_reuseFailAlloc_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_699_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_627_) == 0 {
                    v_es_632_ = crate::leanh::lean_ctor_get(v_x_627_, 0);
                    v___x_633_ = 5usize;
                    v___x_634_ = 1usize;
                    v___x_635_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__1);
                    v___x_636_ = lean_usize_land(v_x_628_, v___x_635_);
                    v_j_637_ = lean_usize_to_nat(v___x_636_);
                    v___x_638_ = lean_array_get_size(v_es_632_);
                    v___x_639_ = lean_nat_dec_lt(v_j_637_, v___x_638_);
                    if v___x_639_ == 0 {
                        crate::leanh::lean_dec(v_j_637_);
                        crate::leanh::lean_dec(v_x_631_);
                        crate::leanh::lean_dec(v_x_630_);
                        return v_x_627_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_632_);
                        v_isSharedCheck_676_ = (!crate::leanh::lean_is_exclusive(v_x_627_)) as u8;
                        if v_isSharedCheck_676_ == 0 {
                            v_unused_677_ = crate::leanh::lean_ctor_get(v_x_627_, 0);
                            crate::leanh::lean_dec(v_unused_677_);
                            v___x_641_ = v_x_627_;
                            v_isShared_642_ = v_isSharedCheck_676_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_627_);
                            v___x_641_ = crate::leanh::lean_box(0);
                            v_isShared_642_ = v_isSharedCheck_676_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_678_ = crate::leanh::lean_ctor_get(v_x_627_, 0);
                    v_vs_679_ = crate::leanh::lean_ctor_get(v_x_627_, 1);
                    v_isSharedCheck_699_ = (!crate::leanh::lean_is_exclusive(v_x_627_)) as u8;
                    if v_isSharedCheck_699_ == 0 {
                        v___x_681_ = v_x_627_;
                        v_isShared_682_ = v_isSharedCheck_699_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_679_);
                        crate::leanh::lean_inc(v_ks_678_);
                        crate::leanh::lean_dec(v_x_627_);
                        v___x_681_ = crate::leanh::lean_box(0);
                        v_isShared_682_ = v_isSharedCheck_699_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_643_ = lean_array_fget(v_es_632_, v_j_637_);
                v___x_644_ = crate::leanh::lean_box(0);
                v_xs_x27_645_ = lean_array_fset(v_es_632_, v_j_637_, v___x_644_);
                match crate::leanh::lean_obj_tag(v_v_643_) {
                    0 => {
                        v_key_652_ = crate::leanh::lean_ctor_get(v_v_643_, 0);
                        v_val_653_ = crate::leanh::lean_ctor_get(v_v_643_, 1);
                        v_isSharedCheck_663_ = (!crate::leanh::lean_is_exclusive(v_v_643_)) as u8;
                        if v_isSharedCheck_663_ == 0 {
                            v___x_655_ = v_v_643_;
                            v_isShared_656_ = v_isSharedCheck_663_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_653_);
                            crate::leanh::lean_inc(v_key_652_);
                            crate::leanh::lean_dec(v_v_643_);
                            v___x_655_ = crate::leanh::lean_box(0);
                            v_isShared_656_ = v_isSharedCheck_663_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_664_ = crate::leanh::lean_ctor_get(v_v_643_, 0);
                        v_isSharedCheck_674_ = (!crate::leanh::lean_is_exclusive(v_v_643_)) as u8;
                        if v_isSharedCheck_674_ == 0 {
                            v___x_666_ = v_v_643_;
                            v_isShared_667_ = v_isSharedCheck_674_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_664_);
                            crate::leanh::lean_dec(v_v_643_);
                            v___x_666_ = crate::leanh::lean_box(0);
                            v_isShared_667_ = v_isSharedCheck_674_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_675_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_675_, 0, v_x_630_);
                        crate::leanh::lean_ctor_set(v___x_675_, 1, v_x_631_);
                        v___y_647_ = v___x_675_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_648_ = lean_array_fset(v_xs_x27_645_, v_j_637_, v___y_647_);
                crate::leanh::lean_dec(v_j_637_);
                if v_isShared_642_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_641_, 0, v___x_648_);
                    v___x_650_ = v___x_641_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_651_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_648_);
                    v___x_650_ = v_reuseFailAlloc_651_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_650_;
            }
            4 => {
                v___x_657_ = l_Lean_instBEqMVarId_beq(v_x_630_, v_key_652_);
                if v___x_657_ == 0 {
                    crate::leanh::lean_del_object(v___x_655_);
                    v___x_658_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_652_, v_val_653_, v_x_630_, v_x_631_,
                    );
                    v___x_659_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_659_, 0, v___x_658_);
                    v___y_647_ = v___x_659_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_653_);
                    crate::leanh::lean_dec(v_key_652_);
                    if v_isShared_656_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_655_, 1, v_x_631_);
                        crate::leanh::lean_ctor_set(v___x_655_, 0, v_x_630_);
                        v___x_661_ = v___x_655_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_662_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_662_, 0, v_x_630_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_662_, 1, v_x_631_);
                        v___x_661_ = v_reuseFailAlloc_662_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_647_ = v___x_661_;
                state = 2;
                continue;
            }
            6 => {
                v___x_668_ = lean_usize_shift_right(v_x_628_, v___x_633_);
                v___x_669_ = lean_usize_add(v_x_629_, v___x_634_);
                v___x_670_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_node_664_, v___x_668_, v___x_669_, v_x_630_, v_x_631_);
                if v_isShared_667_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_666_, 0, v___x_670_);
                    v___x_672_ = v___x_666_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_673_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
                    v___x_672_ = v_reuseFailAlloc_673_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_647_ = v___x_672_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_682_ == 0 {
                    v___x_684_ = v___x_681_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_698_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_698_, 0, v_ks_678_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_698_, 1, v_vs_679_);
                    v___x_684_ = v_reuseFailAlloc_698_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_685_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5___redArg(v___x_684_, v_x_630_, v_x_631_);
                v___x_693_ = 7usize;
                v___x_694_ = lean_usize_dec_le(v___x_693_, v_x_629_);
                if v___x_694_ == 0 {
                    v___x_695_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_685_);
                    v___x_696_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_697_ = lean_nat_dec_lt(v___x_695_, v___x_696_);
                    crate::leanh::lean_dec(v___x_695_);
                    v___y_687_ = v___x_697_;
                    state = 10;
                    continue;
                } else {
                    v___y_687_ = v___x_694_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_687_ == 0 {
                    v_ks_688_ = crate::leanh::lean_ctor_get(v_newNode_685_, 0);
                    crate::leanh::lean_inc_ref(v_ks_688_);
                    v_vs_689_ = crate::leanh::lean_ctor_get(v_newNode_685_, 1);
                    crate::leanh::lean_inc_ref(v_vs_689_);
                    crate::leanh::lean_dec_ref(v_newNode_685_);
                    v___x_690_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_691_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__2);
                    v___x_692_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(v_x_629_, v_ks_688_, v_vs_689_, v___x_690_, v___x_691_);
                    crate::leanh::lean_dec_ref(v_vs_689_);
                    crate::leanh::lean_dec_ref(v_ks_688_);
                    return v___x_692_;
                } else {
                    return v_newNode_685_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(
    mut v_depth_700_: usize,
    mut v_keys_701_: *mut crate::leanh::LeanObject,
    mut v_vals_702_: *mut crate::leanh::LeanObject,
    mut v_i_703_: *mut crate::leanh::LeanObject,
    mut v_entries_704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: u8 = 0;
    let mut v_k_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: u64 = 0;
    let mut v_h_710_: usize = 0;
    let mut v___x_711_: usize = 0;
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: usize = 0;
    let mut v___x_714_: usize = 0;
    let mut v___x_715_: usize = 0;
    let mut v_h_716_: usize = 0;
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_705_ = lean_array_get_size(v_keys_701_);
                v___x_706_ = lean_nat_dec_lt(v_i_703_, v___x_705_);
                if v___x_706_ == 0 {
                    crate::leanh::lean_dec(v_i_703_);
                    return v_entries_704_;
                } else {
                    v_k_707_ = lean_array_fget_borrowed(v_keys_701_, v_i_703_);
                    v_v_708_ = lean_array_fget_borrowed(v_vals_702_, v_i_703_);
                    v___x_709_ = l_Lean_instHashableMVarId_hash(v_k_707_);
                    v_h_710_ = lean_uint64_to_usize(v___x_709_);
                    v___x_711_ = 5usize;
                    v___x_712_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_713_ = 1usize;
                    v___x_714_ = lean_usize_sub(v_depth_700_, v___x_713_);
                    v___x_715_ = lean_usize_mul(v___x_711_, v___x_714_);
                    v_h_716_ = lean_usize_shift_right(v_h_710_, v___x_715_);
                    v___x_717_ = lean_nat_add(v_i_703_, v___x_712_);
                    crate::leanh::lean_dec(v_i_703_);
                    crate::leanh::lean_inc(v_v_708_);
                    crate::leanh::lean_inc(v_k_707_);
                    v___x_718_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_entries_704_, v_h_716_, v_depth_700_, v_k_707_, v_v_708_);
                    v_i_703_ = v___x_717_;
                    v_entries_704_ = v___x_718_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg___boxed(
    mut v_depth_720_: *mut crate::leanh::LeanObject,
    mut v_keys_721_: *mut crate::leanh::LeanObject,
    mut v_vals_722_: *mut crate::leanh::LeanObject,
    mut v_i_723_: *mut crate::leanh::LeanObject,
    mut v_entries_724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_725_: usize = 0;
    let mut v_res_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_725_ = crate::leanh::lean_unbox_usize(v_depth_720_);
    crate::leanh::lean_dec(v_depth_720_);
    v_res_726_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_boxed_725_, v_keys_721_, v_vals_722_, v_i_723_, v_entries_724_);
    crate::leanh::lean_dec_ref(v_vals_722_);
    crate::leanh::lean_dec_ref(v_keys_721_);
    return v_res_726_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_x_727_: *mut crate::leanh::LeanObject,
    mut v_x_728_: *mut crate::leanh::LeanObject,
    mut v_x_729_: *mut crate::leanh::LeanObject,
    mut v_x_730_: *mut crate::leanh::LeanObject,
    mut v_x_731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_4592__boxed_732_: usize = 0;
    let mut v_x_4593__boxed_733_: usize = 0;
    let mut v_res_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_4592__boxed_732_ = crate::leanh::lean_unbox_usize(v_x_728_);
    crate::leanh::lean_dec(v_x_728_);
    v_x_4593__boxed_733_ = crate::leanh::lean_unbox_usize(v_x_729_);
    crate::leanh::lean_dec(v_x_729_);
    v_res_734_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_x_727_, v_x_4592__boxed_732_, v_x_4593__boxed_733_, v_x_730_, v_x_731_);
    return v_res_734_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3___redArg(
    mut v_x_735_: *mut crate::leanh::LeanObject,
    mut v_x_736_: *mut crate::leanh::LeanObject,
    mut v_x_737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_738_: u64 = 0;
    let mut v___x_739_: usize = 0;
    let mut v___x_740_: usize = 0;
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_738_ = l_Lean_instHashableMVarId_hash(v_x_736_);
    v___x_739_ = lean_uint64_to_usize(v___x_738_);
    v___x_740_ = 1usize;
    v___x_741_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_x_735_, v___x_739_, v___x_740_, v_x_736_, v_x_737_);
    return v___x_741_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg(
    mut v_mvarId_742_: *mut crate::leanh::LeanObject,
    mut v_val_743_: *mut crate::leanh::LeanObject,
    mut v___y_744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_754_: u8 = 0;
    let mut v_depth_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_767_: u8 = 0;
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_778_: u8 = 0;
    let mut v_isSharedCheck_779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_746_ = lean_st_ref_take(v___y_744_);
                v_mctx_747_ = crate::leanh::lean_ctor_get(v___x_746_, 0);
                v_cache_748_ = crate::leanh::lean_ctor_get(v___x_746_, 1);
                v_zetaDeltaFVarIds_749_ = crate::leanh::lean_ctor_get(v___x_746_, 2);
                v_postponed_750_ = crate::leanh::lean_ctor_get(v___x_746_, 3);
                v_diag_751_ = crate::leanh::lean_ctor_get(v___x_746_, 4);
                v_isSharedCheck_779_ = (!crate::leanh::lean_is_exclusive(v___x_746_)) as u8;
                if v_isSharedCheck_779_ == 0 {
                    v___x_753_ = v___x_746_;
                    v_isShared_754_ = v_isSharedCheck_779_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_751_);
                    crate::leanh::lean_inc(v_postponed_750_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_749_);
                    crate::leanh::lean_inc(v_cache_748_);
                    crate::leanh::lean_inc(v_mctx_747_);
                    crate::leanh::lean_dec(v___x_746_);
                    v___x_753_ = crate::leanh::lean_box(0);
                    v_isShared_754_ = v_isSharedCheck_779_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_755_ = crate::leanh::lean_ctor_get(v_mctx_747_, 0);
                v_levelAssignDepth_756_ = crate::leanh::lean_ctor_get(v_mctx_747_, 1);
                v_lmvarCounter_757_ = crate::leanh::lean_ctor_get(v_mctx_747_, 2);
                v_mvarCounter_758_ = crate::leanh::lean_ctor_get(v_mctx_747_, 3);
                v_lDecls_759_ = crate::leanh::lean_ctor_get(v_mctx_747_, 4);
                v_decls_760_ = crate::leanh::lean_ctor_get(v_mctx_747_, 5);
                v_userNames_761_ = crate::leanh::lean_ctor_get(v_mctx_747_, 6);
                v_lAssignment_762_ = crate::leanh::lean_ctor_get(v_mctx_747_, 7);
                v_eAssignment_763_ = crate::leanh::lean_ctor_get(v_mctx_747_, 8);
                v_dAssignment_764_ = crate::leanh::lean_ctor_get(v_mctx_747_, 9);
                v_isSharedCheck_778_ = (!crate::leanh::lean_is_exclusive(v_mctx_747_)) as u8;
                if v_isSharedCheck_778_ == 0 {
                    v___x_766_ = v_mctx_747_;
                    v_isShared_767_ = v_isSharedCheck_778_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_764_);
                    crate::leanh::lean_inc(v_eAssignment_763_);
                    crate::leanh::lean_inc(v_lAssignment_762_);
                    crate::leanh::lean_inc(v_userNames_761_);
                    crate::leanh::lean_inc(v_decls_760_);
                    crate::leanh::lean_inc(v_lDecls_759_);
                    crate::leanh::lean_inc(v_mvarCounter_758_);
                    crate::leanh::lean_inc(v_lmvarCounter_757_);
                    crate::leanh::lean_inc(v_levelAssignDepth_756_);
                    crate::leanh::lean_inc(v_depth_755_);
                    crate::leanh::lean_dec(v_mctx_747_);
                    v___x_766_ = crate::leanh::lean_box(0);
                    v_isShared_767_ = v_isSharedCheck_778_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_768_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3___redArg(v_eAssignment_763_, v_mvarId_742_, v_val_743_);
                if v_isShared_767_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_766_, 8, v___x_768_);
                    v___x_770_ = v___x_766_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_777_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_777_, 0, v_depth_755_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_777_, 1, v_levelAssignDepth_756_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_777_, 2, v_lmvarCounter_757_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_777_, 3, v_mvarCounter_758_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_777_, 4, v_lDecls_759_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_777_, 5, v_decls_760_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_777_, 6, v_userNames_761_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_777_, 7, v_lAssignment_762_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_777_, 8, v___x_768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_777_, 9, v_dAssignment_764_);
                    v___x_770_ = v_reuseFailAlloc_777_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_754_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_753_, 0, v___x_770_);
                    v___x_772_ = v___x_753_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_776_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_770_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_776_, 1, v_cache_748_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_776_, 2, v_zetaDeltaFVarIds_749_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_776_, 3, v_postponed_750_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_776_, 4, v_diag_751_);
                    v___x_772_ = v_reuseFailAlloc_776_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_773_ = lean_st_ref_set(v___y_744_, v___x_772_);
                v___x_774_ = crate::leanh::lean_box(0);
                v___x_775_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_775_, 0, v___x_774_);
                return v___x_775_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg___boxed(
    mut v_mvarId_780_: *mut crate::leanh::LeanObject,
    mut v_val_781_: *mut crate::leanh::LeanObject,
    mut v___y_782_: *mut crate::leanh::LeanObject,
    mut v___y_783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_784_ = l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg(
        v_mvarId_780_,
        v_val_781_,
        v___y_782_,
    );
    crate::leanh::lean_dec(v___y_782_);
    return v_res_784_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabAsAuxLemma_spec__0_spec__0(
    mut v_msgData_785_: *mut crate::leanh::LeanObject,
    mut v___y_786_: *mut crate::leanh::LeanObject,
    mut v___y_787_: *mut crate::leanh::LeanObject,
    mut v___y_788_: *mut crate::leanh::LeanObject,
    mut v___y_789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_791_ = lean_st_ref_get(v___y_789_);
    v_env_792_ = crate::leanh::lean_ctor_get(v___x_791_, 0);
    crate::leanh::lean_inc_ref(v_env_792_);
    crate::leanh::lean_dec(v___x_791_);
    v___x_793_ = lean_st_ref_get(v___y_787_);
    v_mctx_794_ = crate::leanh::lean_ctor_get(v___x_793_, 0);
    crate::leanh::lean_inc_ref(v_mctx_794_);
    crate::leanh::lean_dec(v___x_793_);
    v_lctx_795_ = crate::leanh::lean_ctor_get(v___y_786_, 2);
    v_options_796_ = crate::leanh::lean_ctor_get(v___y_788_, 2);
    crate::leanh::lean_inc_ref(v_options_796_);
    crate::leanh::lean_inc_ref(v_lctx_795_);
    v___x_797_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_797_, 0, v_env_792_);
    crate::leanh::lean_ctor_set(v___x_797_, 1, v_mctx_794_);
    crate::leanh::lean_ctor_set(v___x_797_, 2, v_lctx_795_);
    crate::leanh::lean_ctor_set(v___x_797_, 3, v_options_796_);
    v___x_798_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_798_, 0, v___x_797_);
    crate::leanh::lean_ctor_set(v___x_798_, 1, v_msgData_785_);
    v___x_799_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_799_, 0, v___x_798_);
    return v___x_799_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabAsAuxLemma_spec__0_spec__0___boxed(
    mut v_msgData_800_: *mut crate::leanh::LeanObject,
    mut v___y_801_: *mut crate::leanh::LeanObject,
    mut v___y_802_: *mut crate::leanh::LeanObject,
    mut v___y_803_: *mut crate::leanh::LeanObject,
    mut v___y_804_: *mut crate::leanh::LeanObject,
    mut v___y_805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_806_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabAsAuxLemma_spec__0_spec__0(v_msgData_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
    crate::leanh::lean_dec(v___y_804_);
    crate::leanh::lean_dec_ref(v___y_803_);
    crate::leanh::lean_dec(v___y_802_);
    crate::leanh::lean_dec_ref(v___y_801_);
    return v_res_806_;
}
pub unsafe fn l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg(
    mut v_msg_807_: *mut crate::leanh::LeanObject,
    mut v___y_808_: *mut crate::leanh::LeanObject,
    mut v___y_809_: *mut crate::leanh::LeanObject,
    mut v___y_810_: *mut crate::leanh::LeanObject,
    mut v___y_811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_818_: u8 = 0;
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_823_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_813_ = crate::leanh::lean_ctor_get(v___y_810_, 5);
                v___x_814_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabAsAuxLemma_spec__0_spec__0(v_msg_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
                v_a_815_ = crate::leanh::lean_ctor_get(v___x_814_, 0);
                v_isSharedCheck_823_ = (!crate::leanh::lean_is_exclusive(v___x_814_)) as u8;
                if v_isSharedCheck_823_ == 0 {
                    v___x_817_ = v___x_814_;
                    v_isShared_818_ = v_isSharedCheck_823_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_815_);
                    crate::leanh::lean_dec(v___x_814_);
                    v___x_817_ = crate::leanh::lean_box(0);
                    v_isShared_818_ = v_isSharedCheck_823_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_813_);
                v___x_819_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_819_, 0, v_ref_813_);
                crate::leanh::lean_ctor_set(v___x_819_, 1, v_a_815_);
                if v_isShared_818_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_817_, 1);
                    crate::leanh::lean_ctor_set(v___x_817_, 0, v___x_819_);
                    v___x_821_ = v___x_817_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_822_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
                    v___x_821_ = v_reuseFailAlloc_822_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_821_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg___boxed(
    mut v_msg_824_: *mut crate::leanh::LeanObject,
    mut v___y_825_: *mut crate::leanh::LeanObject,
    mut v___y_826_: *mut crate::leanh::LeanObject,
    mut v___y_827_: *mut crate::leanh::LeanObject,
    mut v___y_828_: *mut crate::leanh::LeanObject,
    mut v___y_829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_830_ = l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg(
        v_msg_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_,
    );
    crate::leanh::lean_dec(v___y_828_);
    crate::leanh::lean_dec_ref(v___y_827_);
    crate::leanh::lean_dec(v___y_826_);
    crate::leanh::lean_dec_ref(v___y_825_);
    return v_res_830_;
}
pub unsafe fn _init_l_elabAsAuxLemma___lam__0___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_832_ = l_elabAsAuxLemma___lam__0___closed__0;
    v___x_833_ = l_Lean_stringToMessageData(v___x_832_);
    return v___x_833_;
}
pub unsafe fn l_elabAsAuxLemma___lam__0(
    mut v___x_834_: *mut crate::leanh::LeanObject,
    mut v___x_835_: u8,
    mut v___y_836_: *mut crate::leanh::LeanObject,
    mut v___y_837_: *mut crate::leanh::LeanObject,
    mut v___y_838_: *mut crate::leanh::LeanObject,
    mut v___y_839_: *mut crate::leanh::LeanObject,
    mut v___y_840_: *mut crate::leanh::LeanObject,
    mut v___y_841_: *mut crate::leanh::LeanObject,
    mut v___y_842_: *mut crate::leanh::LeanObject,
    mut v___y_843_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: u8 = 0;
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_869_: u8 = 0;
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_873_: u8 = 0;
    let mut v_a_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_877_: u8 = 0;
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_881_: u8 = 0;
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: u8 = 0;
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_891_: u8 = 0;
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_895_: u8 = 0;
    let mut v_a_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_899_: u8 = 0;
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_903_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_845_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_837_, v___y_840_, v___y_841_, v___y_842_, v___y_843_,
                );
                if crate::leanh::lean_obj_tag(v___x_845_) == 0 {
                    v_a_846_ = crate::leanh::lean_ctor_get(v___x_845_, 0);
                    crate::leanh::lean_inc_n(v_a_846_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_845_, 1);
                    v___x_882_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalTactic___boxed as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___x_882_, 0, v___x_834_);
                    v___x_883_ = l_Lean_Elab_Tactic_run(
                        v_a_846_, v___x_882_, v___y_838_, v___y_839_, v___y_840_, v___y_841_,
                        v___y_842_, v___y_843_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_883_) == 0 {
                        v_a_884_ = crate::leanh::lean_ctor_get(v___x_883_, 0);
                        crate::leanh::lean_inc(v_a_884_);
                        crate::leanh::lean_dec_ref_known(v___x_883_, 1);
                        v___x_885_ = l_List_isEmpty___redArg(v_a_884_);
                        crate::leanh::lean_dec(v_a_884_);
                        if v___x_885_ == 0 {
                            crate::leanh::lean_dec(v_a_846_);
                            v___x_886_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(l_elabAsAuxLemma___lam__0___closed__1),
                                core::ptr::addr_of_mut!(l_elabAsAuxLemma___lam__0___closed__1_once),
                                _init_l_elabAsAuxLemma___lam__0___closed__1,
                            );
                            v___x_887_ = l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg(
                                v___x_886_, v___y_840_, v___y_841_, v___y_842_, v___y_843_,
                            );
                            return v___x_887_;
                        } else {
                            v___y_848_ = v___y_836_;
                            v___y_849_ = v___y_837_;
                            v___y_850_ = v___y_838_;
                            v___y_851_ = v___y_839_;
                            v___y_852_ = v___y_840_;
                            v___y_853_ = v___y_841_;
                            v___y_854_ = v___y_842_;
                            v___y_855_ = v___y_843_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_846_);
                        v_a_888_ = crate::leanh::lean_ctor_get(v___x_883_, 0);
                        v_isSharedCheck_895_ = (!crate::leanh::lean_is_exclusive(v___x_883_)) as u8;
                        if v_isSharedCheck_895_ == 0 {
                            v___x_890_ = v___x_883_;
                            v_isShared_891_ = v_isSharedCheck_895_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_888_);
                            crate::leanh::lean_dec(v___x_883_);
                            v___x_890_ = crate::leanh::lean_box(0);
                            v_isShared_891_ = v_isSharedCheck_895_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_834_);
                    v_a_896_ = crate::leanh::lean_ctor_get(v___x_845_, 0);
                    v_isSharedCheck_903_ = (!crate::leanh::lean_is_exclusive(v___x_845_)) as u8;
                    if v_isSharedCheck_903_ == 0 {
                        v___x_898_ = v___x_845_;
                        v_isShared_899_ = v_isSharedCheck_903_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_896_);
                        crate::leanh::lean_dec(v___x_845_);
                        v___x_898_ = crate::leanh::lean_box(0);
                        v_isShared_899_ = v_isSharedCheck_903_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_n(v_a_846_, 2);
                v___x_856_ = l_Lean_mkMVar(v_a_846_);
                v___x_857_ = l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg(
                    v___x_856_, v___y_853_,
                );
                v_a_858_ = crate::leanh::lean_ctor_get(v___x_857_, 0);
                crate::leanh::lean_inc(v_a_858_);
                crate::leanh::lean_dec_ref(v___x_857_);
                v___x_859_ =
                    l_Lean_MVarId_getType(v_a_846_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
                if crate::leanh::lean_obj_tag(v___x_859_) == 0 {
                    v_a_860_ = crate::leanh::lean_ctor_get(v___x_859_, 0);
                    crate::leanh::lean_inc(v_a_860_);
                    crate::leanh::lean_dec_ref_known(v___x_859_, 1);
                    v___x_861_ = 0;
                    v___x_862_ = crate::leanh::lean_box(0);
                    v___x_863_ = l_Lean_Meta_mkAuxTheorem(
                        v_a_860_, v_a_858_, v___x_861_, v___x_862_, v___x_835_, v___y_852_,
                        v___y_853_, v___y_854_, v___y_855_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_863_) == 0 {
                        v_a_864_ = crate::leanh::lean_ctor_get(v___x_863_, 0);
                        crate::leanh::lean_inc(v_a_864_);
                        crate::leanh::lean_dec_ref_known(v___x_863_, 1);
                        v___x_865_ = l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg(
                            v_a_846_, v_a_864_, v___y_853_,
                        );
                        return v___x_865_;
                    } else {
                        crate::leanh::lean_dec(v_a_846_);
                        v_a_866_ = crate::leanh::lean_ctor_get(v___x_863_, 0);
                        v_isSharedCheck_873_ = (!crate::leanh::lean_is_exclusive(v___x_863_)) as u8;
                        if v_isSharedCheck_873_ == 0 {
                            v___x_868_ = v___x_863_;
                            v_isShared_869_ = v_isSharedCheck_873_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_866_);
                            crate::leanh::lean_dec(v___x_863_);
                            v___x_868_ = crate::leanh::lean_box(0);
                            v_isShared_869_ = v_isSharedCheck_873_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_858_);
                    crate::leanh::lean_dec(v_a_846_);
                    v_a_874_ = crate::leanh::lean_ctor_get(v___x_859_, 0);
                    v_isSharedCheck_881_ = (!crate::leanh::lean_is_exclusive(v___x_859_)) as u8;
                    if v_isSharedCheck_881_ == 0 {
                        v___x_876_ = v___x_859_;
                        v_isShared_877_ = v_isSharedCheck_881_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_874_);
                        crate::leanh::lean_dec(v___x_859_);
                        v___x_876_ = crate::leanh::lean_box(0);
                        v_isShared_877_ = v_isSharedCheck_881_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_869_ == 0 {
                    v___x_871_ = v___x_868_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_872_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
                    v___x_871_ = v_reuseFailAlloc_872_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_871_;
            }
            4 => {
                if v_isShared_877_ == 0 {
                    v___x_879_ = v___x_876_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_880_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
                    v___x_879_ = v_reuseFailAlloc_880_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_879_;
            }
            6 => {
                if v_isShared_891_ == 0 {
                    v___x_893_ = v___x_890_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_894_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
                    v___x_893_ = v_reuseFailAlloc_894_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_893_;
            }
            8 => {
                if v_isShared_899_ == 0 {
                    v___x_901_ = v___x_898_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_902_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
                    v___x_901_ = v_reuseFailAlloc_902_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_901_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_elabAsAuxLemma___lam__0___boxed(
    mut v___x_904_: *mut crate::leanh::LeanObject,
    mut v___x_905_: *mut crate::leanh::LeanObject,
    mut v___y_906_: *mut crate::leanh::LeanObject,
    mut v___y_907_: *mut crate::leanh::LeanObject,
    mut v___y_908_: *mut crate::leanh::LeanObject,
    mut v___y_909_: *mut crate::leanh::LeanObject,
    mut v___y_910_: *mut crate::leanh::LeanObject,
    mut v___y_911_: *mut crate::leanh::LeanObject,
    mut v___y_912_: *mut crate::leanh::LeanObject,
    mut v___y_913_: *mut crate::leanh::LeanObject,
    mut v___y_914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4879__boxed_915_: u8 = 0;
    let mut v_res_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4879__boxed_915_ = (crate::leanh::lean_unbox(v___x_905_) as u8);
    v_res_916_ = l_elabAsAuxLemma___lam__0(
        v___x_904_,
        v___x_4879__boxed_915_,
        v___y_906_,
        v___y_907_,
        v___y_908_,
        v___y_909_,
        v___y_910_,
        v___y_911_,
        v___y_912_,
        v___y_913_,
    );
    crate::leanh::lean_dec(v___y_913_);
    crate::leanh::lean_dec_ref(v___y_912_);
    crate::leanh::lean_dec(v___y_911_);
    crate::leanh::lean_dec_ref(v___y_910_);
    crate::leanh::lean_dec(v___y_909_);
    crate::leanh::lean_dec_ref(v___y_908_);
    crate::leanh::lean_dec(v___y_907_);
    crate::leanh::lean_dec_ref(v___y_906_);
    return v_res_916_;
}
pub unsafe fn _init_l_elabAsAuxLemma___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_927_ = l_elabAsAuxLemma___closed__5;
    v___x_928_ = l_Lean_stringToMessageData(v___x_927_);
    return v___x_928_;
}
pub unsafe fn l_elabAsAuxLemma(
    mut v_x_929_: *mut crate::leanh::LeanObject,
    mut v_a_930_: *mut crate::leanh::LeanObject,
    mut v_a_931_: *mut crate::leanh::LeanObject,
    mut v_a_932_: *mut crate::leanh::LeanObject,
    mut v_a_933_: *mut crate::leanh::LeanObject,
    mut v_a_934_: *mut crate::leanh::LeanObject,
    mut v_a_935_: *mut crate::leanh::LeanObject,
    mut v_a_936_: *mut crate::leanh::LeanObject,
    mut v_a_937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: u8 = 0;
    v___x_939_ = l_elabAsAuxLemma___closed__4;
    crate::leanh::lean_inc(v_x_929_);
    v___x_940_ = l_Lean_Syntax_isOfKind(v_x_929_, v___x_939_);
    if v___x_940_ == 0 {
        let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_929_);
        v___x_941_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_elabAsAuxLemma___closed__6),
            core::ptr::addr_of_mut!(l_elabAsAuxLemma___closed__6_once),
            _init_l_elabAsAuxLemma___closed__6,
        );
        v___x_942_ = l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg(
            v___x_941_, v_a_934_, v_a_935_, v_a_936_, v_a_937_,
        );
        return v___x_942_;
    } else {
        let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_943_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_944_ = l_Lean_Syntax_getArg(v_x_929_, v___x_943_);
        crate::leanh::lean_dec(v_x_929_);
        v___x_945_ = crate::leanh::lean_box((v___x_940_) as usize);
        v___f_946_ = crate::leanh::lean_alloc_closure(
            l_elabAsAuxLemma___lam__0___boxed as *mut core::ffi::c_void,
            11,
            2,
        );
        crate::leanh::lean_closure_set(v___f_946_, 0, v___x_944_);
        crate::leanh::lean_closure_set(v___f_946_, 1, v___x_945_);
        v___x_947_ = l_Lean_Elab_Tactic_withMainContext___redArg(
            v___f_946_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_,
            v_a_937_,
        );
        return v___x_947_;
    }
}
pub unsafe fn l_elabAsAuxLemma___boxed(
    mut v_x_948_: *mut crate::leanh::LeanObject,
    mut v_a_949_: *mut crate::leanh::LeanObject,
    mut v_a_950_: *mut crate::leanh::LeanObject,
    mut v_a_951_: *mut crate::leanh::LeanObject,
    mut v_a_952_: *mut crate::leanh::LeanObject,
    mut v_a_953_: *mut crate::leanh::LeanObject,
    mut v_a_954_: *mut crate::leanh::LeanObject,
    mut v_a_955_: *mut crate::leanh::LeanObject,
    mut v_a_956_: *mut crate::leanh::LeanObject,
    mut v_a_957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_958_ = l_elabAsAuxLemma(
        v_x_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_,
    );
    crate::leanh::lean_dec(v_a_956_);
    crate::leanh::lean_dec_ref(v_a_955_);
    crate::leanh::lean_dec(v_a_954_);
    crate::leanh::lean_dec_ref(v_a_953_);
    crate::leanh::lean_dec(v_a_952_);
    crate::leanh::lean_dec_ref(v_a_951_);
    crate::leanh::lean_dec(v_a_950_);
    crate::leanh::lean_dec_ref(v_a_949_);
    return v_res_958_;
}
pub unsafe fn l_Lean_throwError___at___00elabAsAuxLemma_spec__0(
    mut v_00_u03b1_959_: *mut crate::leanh::LeanObject,
    mut v_msg_960_: *mut crate::leanh::LeanObject,
    mut v___y_961_: *mut crate::leanh::LeanObject,
    mut v___y_962_: *mut crate::leanh::LeanObject,
    mut v___y_963_: *mut crate::leanh::LeanObject,
    mut v___y_964_: *mut crate::leanh::LeanObject,
    mut v___y_965_: *mut crate::leanh::LeanObject,
    mut v___y_966_: *mut crate::leanh::LeanObject,
    mut v___y_967_: *mut crate::leanh::LeanObject,
    mut v___y_968_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_970_ = l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg(
        v_msg_960_, v___y_965_, v___y_966_, v___y_967_, v___y_968_,
    );
    return v___x_970_;
}
pub unsafe fn l_Lean_throwError___at___00elabAsAuxLemma_spec__0___boxed(
    mut v_00_u03b1_971_: *mut crate::leanh::LeanObject,
    mut v_msg_972_: *mut crate::leanh::LeanObject,
    mut v___y_973_: *mut crate::leanh::LeanObject,
    mut v___y_974_: *mut crate::leanh::LeanObject,
    mut v___y_975_: *mut crate::leanh::LeanObject,
    mut v___y_976_: *mut crate::leanh::LeanObject,
    mut v___y_977_: *mut crate::leanh::LeanObject,
    mut v___y_978_: *mut crate::leanh::LeanObject,
    mut v___y_979_: *mut crate::leanh::LeanObject,
    mut v___y_980_: *mut crate::leanh::LeanObject,
    mut v___y_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_982_ = l_Lean_throwError___at___00elabAsAuxLemma_spec__0(
        v_00_u03b1_971_,
        v_msg_972_,
        v___y_973_,
        v___y_974_,
        v___y_975_,
        v___y_976_,
        v___y_977_,
        v___y_978_,
        v___y_979_,
        v___y_980_,
    );
    crate::leanh::lean_dec(v___y_980_);
    crate::leanh::lean_dec_ref(v___y_979_);
    crate::leanh::lean_dec(v___y_978_);
    crate::leanh::lean_dec_ref(v___y_977_);
    crate::leanh::lean_dec(v___y_976_);
    crate::leanh::lean_dec_ref(v___y_975_);
    crate::leanh::lean_dec(v___y_974_);
    crate::leanh::lean_dec_ref(v___y_973_);
    return v_res_982_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2(
    mut v_mvarId_983_: *mut crate::leanh::LeanObject,
    mut v_val_984_: *mut crate::leanh::LeanObject,
    mut v___y_985_: *mut crate::leanh::LeanObject,
    mut v___y_986_: *mut crate::leanh::LeanObject,
    mut v___y_987_: *mut crate::leanh::LeanObject,
    mut v___y_988_: *mut crate::leanh::LeanObject,
    mut v___y_989_: *mut crate::leanh::LeanObject,
    mut v___y_990_: *mut crate::leanh::LeanObject,
    mut v___y_991_: *mut crate::leanh::LeanObject,
    mut v___y_992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_994_ = l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg(
        v_mvarId_983_,
        v_val_984_,
        v___y_990_,
    );
    return v___x_994_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___boxed(
    mut v_mvarId_995_: *mut crate::leanh::LeanObject,
    mut v_val_996_: *mut crate::leanh::LeanObject,
    mut v___y_997_: *mut crate::leanh::LeanObject,
    mut v___y_998_: *mut crate::leanh::LeanObject,
    mut v___y_999_: *mut crate::leanh::LeanObject,
    mut v___y_1000_: *mut crate::leanh::LeanObject,
    mut v___y_1001_: *mut crate::leanh::LeanObject,
    mut v___y_1002_: *mut crate::leanh::LeanObject,
    mut v___y_1003_: *mut crate::leanh::LeanObject,
    mut v___y_1004_: *mut crate::leanh::LeanObject,
    mut v___y_1005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1006_ = l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2(
        v_mvarId_995_,
        v_val_996_,
        v___y_997_,
        v___y_998_,
        v___y_999_,
        v___y_1000_,
        v___y_1001_,
        v___y_1002_,
        v___y_1003_,
        v___y_1004_,
    );
    crate::leanh::lean_dec(v___y_1004_);
    crate::leanh::lean_dec_ref(v___y_1003_);
    crate::leanh::lean_dec(v___y_1002_);
    crate::leanh::lean_dec_ref(v___y_1001_);
    crate::leanh::lean_dec(v___y_1000_);
    crate::leanh::lean_dec_ref(v___y_999_);
    crate::leanh::lean_dec(v___y_998_);
    crate::leanh::lean_dec_ref(v___y_997_);
    return v_res_1006_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3(
    mut v_00_u03b2_1007_: *mut crate::leanh::LeanObject,
    mut v_x_1008_: *mut crate::leanh::LeanObject,
    mut v_x_1009_: *mut crate::leanh::LeanObject,
    mut v_x_1010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1011_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3___redArg(v_x_1008_, v_x_1009_, v_x_1010_);
    return v___x_1011_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4(
    mut v_00_u03b2_1012_: *mut crate::leanh::LeanObject,
    mut v_x_1013_: *mut crate::leanh::LeanObject,
    mut v_x_1014_: usize,
    mut v_x_1015_: usize,
    mut v_x_1016_: *mut crate::leanh::LeanObject,
    mut v_x_1017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1018_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_x_1013_, v_x_1014_, v_x_1015_, v_x_1016_, v_x_1017_);
    return v___x_1018_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___boxed(
    mut v_00_u03b2_1019_: *mut crate::leanh::LeanObject,
    mut v_x_1020_: *mut crate::leanh::LeanObject,
    mut v_x_1021_: *mut crate::leanh::LeanObject,
    mut v_x_1022_: *mut crate::leanh::LeanObject,
    mut v_x_1023_: *mut crate::leanh::LeanObject,
    mut v_x_1024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_5162__boxed_1025_: usize = 0;
    let mut v_x_5163__boxed_1026_: usize = 0;
    let mut v_res_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_5162__boxed_1025_ = crate::leanh::lean_unbox_usize(v_x_1021_);
    crate::leanh::lean_dec(v_x_1021_);
    v_x_5163__boxed_1026_ = crate::leanh::lean_unbox_usize(v_x_1022_);
    crate::leanh::lean_dec(v_x_1022_);
    v_res_1027_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4(v_00_u03b2_1019_, v_x_1020_, v_x_5162__boxed_1025_, v_x_5163__boxed_1026_, v_x_1023_, v_x_1024_);
    return v_res_1027_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5(
    mut v_00_u03b2_1028_: *mut crate::leanh::LeanObject,
    mut v_n_1029_: *mut crate::leanh::LeanObject,
    mut v_k_1030_: *mut crate::leanh::LeanObject,
    mut v_v_1031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1032_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5___redArg(v_n_1029_, v_k_1030_, v_v_1031_);
    return v___x_1032_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6(
    mut v_00_u03b2_1033_: *mut crate::leanh::LeanObject,
    mut v_depth_1034_: usize,
    mut v_keys_1035_: *mut crate::leanh::LeanObject,
    mut v_vals_1036_: *mut crate::leanh::LeanObject,
    mut v_heq_1037_: *mut crate::leanh::LeanObject,
    mut v_i_1038_: *mut crate::leanh::LeanObject,
    mut v_entries_1039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1040_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_1034_, v_keys_1035_, v_vals_1036_, v_i_1038_, v_entries_1039_);
    return v___x_1040_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___boxed(
    mut v_00_u03b2_1041_: *mut crate::leanh::LeanObject,
    mut v_depth_1042_: *mut crate::leanh::LeanObject,
    mut v_keys_1043_: *mut crate::leanh::LeanObject,
    mut v_vals_1044_: *mut crate::leanh::LeanObject,
    mut v_heq_1045_: *mut crate::leanh::LeanObject,
    mut v_i_1046_: *mut crate::leanh::LeanObject,
    mut v_entries_1047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1048_: usize = 0;
    let mut v_res_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1048_ = crate::leanh::lean_unbox_usize(v_depth_1042_);
    crate::leanh::lean_dec(v_depth_1042_);
    v_res_1049_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6(v_00_u03b2_1041_, v_depth_boxed_1048_, v_keys_1043_, v_vals_1044_, v_heq_1045_, v_i_1046_, v_entries_1047_);
    crate::leanh::lean_dec_ref(v_vals_1044_);
    crate::leanh::lean_dec_ref(v_keys_1043_);
    return v_res_1049_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6(
    mut v_00_u03b2_1050_: *mut crate::leanh::LeanObject,
    mut v_x_1051_: *mut crate::leanh::LeanObject,
    mut v_x_1052_: *mut crate::leanh::LeanObject,
    mut v_x_1053_: *mut crate::leanh::LeanObject,
    mut v_x_1054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1055_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_x_1051_, v_x_1052_, v_x_1053_, v_x_1054_);
    return v___x_1055_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1060_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1061_ = l_elabAsAuxLemma___closed__4;
    v___x_1062_ = l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__1;
    v___x_1063_ =
        crate::leanh::lean_alloc_closure(l_elabAsAuxLemma___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_1064_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1060_,
        v___x_1061_,
        v___x_1062_,
        v___x_1063_,
    );
    return v___x_1064_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___boxed(
    mut v_a_1065_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1066_ =
        l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1();
    return v_res_1066_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_AsAuxLemma(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res =
        l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_AsAuxLemma(
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
pub unsafe fn initialize_Lean_Elab_Tactic_AsAuxLemma(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Meta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_AsAuxLemma(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_AsAuxLemma(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_AsAuxLemma(builtin);
}

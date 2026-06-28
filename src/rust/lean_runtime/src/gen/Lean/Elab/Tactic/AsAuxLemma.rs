// Lean compiler output
// Module: Lean.Elab.Tactic.AsAuxLemma
// Imports: Lean.Elab.Tactic.Meta
use crate::r#gen::Init::Data::List::Basic::l_List_isEmpty___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr4, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
};
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
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_nat_add,
    lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_elabAsAuxLemma___lam__0___closed__0_value: LeanStringObject<72> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 72,
    m_capacity: 72,
    m_length: 71,
    m_data: [
        67, 97, 110, 110, 111, 116, 32, 97, 98, 115, 116, 114, 97, 99, 116, 32, 116, 101, 114, 109,
        32, 105, 110, 116, 111, 32, 97, 117, 120, 105, 108, 105, 97, 114, 121, 32, 108, 101, 109,
        109, 97, 32, 98, 101, 99, 97, 117, 115, 101, 32, 116, 104, 101, 114, 101, 32, 97, 114, 101,
        32, 111, 112, 101, 110, 32, 103, 111, 97, 108, 115, 46, 0,
    ],
};
static mut l_elabAsAuxLemma___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_elabAsAuxLemma___lam__0___closed__0_value) as *mut LeanObject;
static mut l_elabAsAuxLemma___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_elabAsAuxLemma___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_elabAsAuxLemma___closed__0_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_elabAsAuxLemma___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_elabAsAuxLemma___closed__0_value) as *mut LeanObject;
pub static l_elabAsAuxLemma___closed__1_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_elabAsAuxLemma___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_elabAsAuxLemma___closed__1_value) as *mut LeanObject;
pub static l_elabAsAuxLemma___closed__2_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_elabAsAuxLemma___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_elabAsAuxLemma___closed__2_value) as *mut LeanObject;
pub static l_elabAsAuxLemma___closed__3_value: LeanStringObject<13> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_elabAsAuxLemma___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_elabAsAuxLemma___closed__3_value) as *mut LeanObject;
static l_elabAsAuxLemma___closed__4_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_elabAsAuxLemma___closed__0_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_elabAsAuxLemma___closed__4_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_elabAsAuxLemma___closed__4_value_aux_0) as *mut LeanObject,
        core::ptr::addr_of!(l_elabAsAuxLemma___closed__1_value) as *mut LeanObject,
        8018486133748762727 as *mut LeanObject,
    ],
};
static l_elabAsAuxLemma___closed__4_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_elabAsAuxLemma___closed__4_value_aux_1) as *mut LeanObject,
        core::ptr::addr_of!(l_elabAsAuxLemma___closed__2_value) as *mut LeanObject,
        18344149449936419494 as *mut LeanObject,
    ],
};
pub static l_elabAsAuxLemma___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_elabAsAuxLemma___closed__4_value_aux_2) as *mut LeanObject,
        core::ptr::addr_of!(l_elabAsAuxLemma___closed__3_value) as *mut LeanObject,
        10642961203014691832 as *mut LeanObject,
    ],
};
static mut l_elabAsAuxLemma___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_elabAsAuxLemma___closed__4_value) as *mut LeanObject;
pub static l_elabAsAuxLemma___closed__5_value: LeanStringObject<28> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        73, 110, 118, 97, 108, 105, 100, 32, 97, 115, 95, 97, 117, 120, 95, 108, 101, 109, 109, 97,
        32, 115, 121, 110, 116, 97, 120, 0,
    ],
};
static mut l_elabAsAuxLemma___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_elabAsAuxLemma___closed__5_value) as *mut LeanObject;
static mut l_elabAsAuxLemma___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_elabAsAuxLemma___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__0_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [101, 108, 97, 98, 65, 115, 65, 117, 120, 76, 101, 109, 109, 97, 0]};
static mut l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__0_value) as *mut LeanObject,15561659288978570640 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg(
    mut v_e_534_: *mut LeanObject,
    mut v___y_535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_537_: u8 = 0;
    let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_551_: u8 = 0;
    let mut v___x_553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_557_: u8 = 0;
    let mut v_unused_558_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_537_ = l_Lean_Expr_hasMVar(v_e_534_);
                if v___x_537_ == 0 {
                    v___x_538_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_538_, 0, v_e_534_);
                    return v___x_538_;
                } else {
                    v___x_539_ = lean_st_ref_get(v___y_535_);
                    v_mctx_540_ = lean_ctor_get(v___x_539_, 0);
                    lean_inc_ref(v_mctx_540_);
                    lean_dec(v___x_539_);
                    v___x_541_ = l_Lean_instantiateMVarsCore(v_mctx_540_, v_e_534_);
                    v_fst_542_ = lean_ctor_get(v___x_541_, 0);
                    lean_inc(v_fst_542_);
                    v_snd_543_ = lean_ctor_get(v___x_541_, 1);
                    lean_inc(v_snd_543_);
                    lean_dec_ref(v___x_541_);
                    v___x_544_ = lean_st_ref_take(v___y_535_);
                    v_cache_545_ = lean_ctor_get(v___x_544_, 1);
                    v_zetaDeltaFVarIds_546_ = lean_ctor_get(v___x_544_, 2);
                    v_postponed_547_ = lean_ctor_get(v___x_544_, 3);
                    v_diag_548_ = lean_ctor_get(v___x_544_, 4);
                    v_isSharedCheck_557_ = (!lean_is_exclusive(v___x_544_)) as u8;
                    if v_isSharedCheck_557_ == 0 {
                        v_unused_558_ = lean_ctor_get(v___x_544_, 0);
                        lean_dec(v_unused_558_);
                        v___x_550_ = v___x_544_;
                        v_isShared_551_ = v_isSharedCheck_557_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_548_);
                        lean_inc(v_postponed_547_);
                        lean_inc(v_zetaDeltaFVarIds_546_);
                        lean_inc(v_cache_545_);
                        lean_dec(v___x_544_);
                        v___x_550_ = lean_box(0);
                        v_isShared_551_ = v_isSharedCheck_557_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_551_ == 0 {
                    lean_ctor_set(v___x_550_, 0, v_snd_543_);
                    v___x_553_ = v___x_550_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_556_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_556_, 0, v_snd_543_);
                    lean_ctor_set(v_reuseFailAlloc_556_, 1, v_cache_545_);
                    lean_ctor_set(v_reuseFailAlloc_556_, 2, v_zetaDeltaFVarIds_546_);
                    lean_ctor_set(v_reuseFailAlloc_556_, 3, v_postponed_547_);
                    lean_ctor_set(v_reuseFailAlloc_556_, 4, v_diag_548_);
                    v___x_553_ = v_reuseFailAlloc_556_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_554_ = lean_st_ref_set(v___y_535_, v___x_553_);
                v___x_555_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_555_, 0, v_fst_542_);
                return v___x_555_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg___boxed(
    mut v_e_559_: *mut LeanObject,
    mut v___y_560_: *mut LeanObject,
    mut v___y_561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_562_: *mut LeanObject = core::ptr::null_mut();
    v_res_562_ =
        l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg(v_e_559_, v___y_560_);
    lean_dec(v___y_560_);
    return v_res_562_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1(
    mut v_e_563_: *mut LeanObject,
    mut v___y_564_: *mut LeanObject,
    mut v___y_565_: *mut LeanObject,
    mut v___y_566_: *mut LeanObject,
    mut v___y_567_: *mut LeanObject,
    mut v___y_568_: *mut LeanObject,
    mut v___y_569_: *mut LeanObject,
    mut v___y_570_: *mut LeanObject,
    mut v___y_571_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    v___x_573_ =
        l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg(v_e_563_, v___y_569_);
    return v___x_573_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___boxed(
    mut v_e_574_: *mut LeanObject,
    mut v___y_575_: *mut LeanObject,
    mut v___y_576_: *mut LeanObject,
    mut v___y_577_: *mut LeanObject,
    mut v___y_578_: *mut LeanObject,
    mut v___y_579_: *mut LeanObject,
    mut v___y_580_: *mut LeanObject,
    mut v___y_581_: *mut LeanObject,
    mut v___y_582_: *mut LeanObject,
    mut v___y_583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_584_: *mut LeanObject = core::ptr::null_mut();
    v_res_584_ = l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1(
        v_e_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_,
        v___y_581_, v___y_582_,
    );
    lean_dec(v___y_582_);
    lean_dec_ref(v___y_581_);
    lean_dec(v___y_580_);
    lean_dec_ref(v___y_579_);
    lean_dec(v___y_578_);
    lean_dec_ref(v___y_577_);
    lean_dec(v___y_576_);
    lean_dec_ref(v___y_575_);
    return v_res_584_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(
    mut v_x_585_: *mut LeanObject,
    mut v_x_586_: *mut LeanObject,
    mut v_x_587_: *mut LeanObject,
    mut v_x_588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_593_: u8 = 0;
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: u8 = 0;
    let mut v___x_596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: u8 = 0;
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_614_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_589_ = lean_ctor_get(v_x_585_, 0);
                v_vs_590_ = lean_ctor_get(v_x_585_, 1);
                v_isSharedCheck_614_ = (!lean_is_exclusive(v_x_585_)) as u8;
                if v_isSharedCheck_614_ == 0 {
                    v___x_592_ = v_x_585_;
                    v_isShared_593_ = v_isSharedCheck_614_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_590_);
                    lean_inc(v_ks_589_);
                    lean_dec(v_x_585_);
                    v___x_592_ = lean_box(0);
                    v_isShared_593_ = v_isSharedCheck_614_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_594_ = lean_array_get_size(v_ks_589_);
                v___x_595_ = lean_nat_dec_lt(v_x_586_, v___x_594_);
                if v___x_595_ == 0 {
                    lean_dec(v_x_586_);
                    v___x_596_ = lean_array_push(v_ks_589_, v_x_587_);
                    v___x_597_ = lean_array_push(v_vs_590_, v_x_588_);
                    if v_isShared_593_ == 0 {
                        lean_ctor_set(v___x_592_, 1, v___x_597_);
                        lean_ctor_set(v___x_592_, 0, v___x_596_);
                        v___x_599_ = v___x_592_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_596_);
                        lean_ctor_set(v_reuseFailAlloc_600_, 1, v___x_597_);
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
                            v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_608_, 0, v_ks_589_);
                            lean_ctor_set(v_reuseFailAlloc_608_, 1, v_vs_590_);
                            v___x_604_ = v_reuseFailAlloc_608_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_609_ = lean_array_fset(v_ks_589_, v_x_586_, v_x_587_);
                        v___x_610_ = lean_array_fset(v_vs_590_, v_x_586_, v_x_588_);
                        lean_dec(v_x_586_);
                        if v_isShared_593_ == 0 {
                            lean_ctor_set(v___x_592_, 1, v___x_610_);
                            lean_ctor_set(v___x_592_, 0, v___x_609_);
                            v___x_612_ = v___x_592_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_613_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_613_, 0, v___x_609_);
                            lean_ctor_set(v_reuseFailAlloc_613_, 1, v___x_610_);
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
                v___x_605_ = lean_unsigned_to_nat(1);
                v___x_606_ = lean_nat_add(v_x_586_, v___x_605_);
                lean_dec(v_x_586_);
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
    mut v_n_615_: *mut LeanObject,
    mut v_k_616_: *mut LeanObject,
    mut v_v_617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_619_: *mut LeanObject = core::ptr::null_mut();
    v___x_618_ = lean_unsigned_to_nat(0);
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
    v___x_624_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__0);
    v___x_625_ = lean_usize_sub(v___x_624_, v___x_623_);
    return v___x_625_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    v___x_626_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_626_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(
    mut v_x_627_: *mut LeanObject,
    mut v_x_628_: usize,
    mut v_x_629_: usize,
    mut v_x_630_: *mut LeanObject,
    mut v_x_631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_633_: usize = 0;
    let mut v___x_634_: usize = 0;
    let mut v___x_635_: usize = 0;
    let mut v___x_636_: usize = 0;
    let mut v_j_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_639_: u8 = 0;
    let mut v___x_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_642_: u8 = 0;
    let mut v_v_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_656_: u8 = 0;
    let mut v___x_657_: u8 = 0;
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_663_: u8 = 0;
    let mut v_node_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_667_: u8 = 0;
    let mut v___x_668_: usize = 0;
    let mut v___x_669_: usize = 0;
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_674_: u8 = 0;
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_676_: u8 = 0;
    let mut v_unused_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_682_: u8 = 0;
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_687_: u8 = 0;
    let mut v_ks_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_693_: usize = 0;
    let mut v___x_694_: u8 = 0;
    let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: u8 = 0;
    let mut v_reuseFailAlloc_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_699_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_627_) == 0 {
                    v_es_632_ = lean_ctor_get(v_x_627_, 0);
                    v___x_633_ = 5usize;
                    v___x_634_ = 1usize;
                    v___x_635_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__1);
                    v___x_636_ = lean_usize_land(v_x_628_, v___x_635_);
                    v_j_637_ = lean_usize_to_nat(v___x_636_);
                    v___x_638_ = lean_array_get_size(v_es_632_);
                    v___x_639_ = lean_nat_dec_lt(v_j_637_, v___x_638_);
                    if v___x_639_ == 0 {
                        lean_dec(v_j_637_);
                        lean_dec(v_x_631_);
                        lean_dec(v_x_630_);
                        return v_x_627_;
                    } else {
                        lean_inc_ref(v_es_632_);
                        v_isSharedCheck_676_ = (!lean_is_exclusive(v_x_627_)) as u8;
                        if v_isSharedCheck_676_ == 0 {
                            v_unused_677_ = lean_ctor_get(v_x_627_, 0);
                            lean_dec(v_unused_677_);
                            v___x_641_ = v_x_627_;
                            v_isShared_642_ = v_isSharedCheck_676_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_627_);
                            v___x_641_ = lean_box(0);
                            v_isShared_642_ = v_isSharedCheck_676_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_678_ = lean_ctor_get(v_x_627_, 0);
                    v_vs_679_ = lean_ctor_get(v_x_627_, 1);
                    v_isSharedCheck_699_ = (!lean_is_exclusive(v_x_627_)) as u8;
                    if v_isSharedCheck_699_ == 0 {
                        v___x_681_ = v_x_627_;
                        v_isShared_682_ = v_isSharedCheck_699_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_679_);
                        lean_inc(v_ks_678_);
                        lean_dec(v_x_627_);
                        v___x_681_ = lean_box(0);
                        v_isShared_682_ = v_isSharedCheck_699_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_643_ = lean_array_fget(v_es_632_, v_j_637_);
                v___x_644_ = lean_box(0);
                v_xs_x27_645_ = lean_array_fset(v_es_632_, v_j_637_, v___x_644_);
                match lean_obj_tag(v_v_643_) {
                    0 => {
                        v_key_652_ = lean_ctor_get(v_v_643_, 0);
                        v_val_653_ = lean_ctor_get(v_v_643_, 1);
                        v_isSharedCheck_663_ = (!lean_is_exclusive(v_v_643_)) as u8;
                        if v_isSharedCheck_663_ == 0 {
                            v___x_655_ = v_v_643_;
                            v_isShared_656_ = v_isSharedCheck_663_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_653_);
                            lean_inc(v_key_652_);
                            lean_dec(v_v_643_);
                            v___x_655_ = lean_box(0);
                            v_isShared_656_ = v_isSharedCheck_663_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_664_ = lean_ctor_get(v_v_643_, 0);
                        v_isSharedCheck_674_ = (!lean_is_exclusive(v_v_643_)) as u8;
                        if v_isSharedCheck_674_ == 0 {
                            v___x_666_ = v_v_643_;
                            v_isShared_667_ = v_isSharedCheck_674_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_664_);
                            lean_dec(v_v_643_);
                            v___x_666_ = lean_box(0);
                            v_isShared_667_ = v_isSharedCheck_674_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_675_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_675_, 0, v_x_630_);
                        lean_ctor_set(v___x_675_, 1, v_x_631_);
                        v___y_647_ = v___x_675_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_648_ = lean_array_fset(v_xs_x27_645_, v_j_637_, v___y_647_);
                lean_dec(v_j_637_);
                if v_isShared_642_ == 0 {
                    lean_ctor_set(v___x_641_, 0, v___x_648_);
                    v___x_650_ = v___x_641_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_648_);
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
                    lean_del_object(v___x_655_);
                    v___x_658_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_652_, v_val_653_, v_x_630_, v_x_631_,
                    );
                    v___x_659_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_659_, 0, v___x_658_);
                    v___y_647_ = v___x_659_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_653_);
                    lean_dec(v_key_652_);
                    if v_isShared_656_ == 0 {
                        lean_ctor_set(v___x_655_, 1, v_x_631_);
                        lean_ctor_set(v___x_655_, 0, v_x_630_);
                        v___x_661_ = v___x_655_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_662_, 0, v_x_630_);
                        lean_ctor_set(v_reuseFailAlloc_662_, 1, v_x_631_);
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
                    lean_ctor_set(v___x_666_, 0, v___x_670_);
                    v___x_672_ = v___x_666_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_673_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_673_, 0, v___x_670_);
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
                    v_reuseFailAlloc_698_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_698_, 0, v_ks_678_);
                    lean_ctor_set(v_reuseFailAlloc_698_, 1, v_vs_679_);
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
                    v___x_696_ = lean_unsigned_to_nat(4);
                    v___x_697_ = lean_nat_dec_lt(v___x_695_, v___x_696_);
                    lean_dec(v___x_695_);
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
                    v_ks_688_ = lean_ctor_get(v_newNode_685_, 0);
                    lean_inc_ref(v_ks_688_);
                    v_vs_689_ = lean_ctor_get(v_newNode_685_, 1);
                    lean_inc_ref(v_vs_689_);
                    lean_dec_ref(v_newNode_685_);
                    v___x_690_ = lean_unsigned_to_nat(0);
                    v___x_691_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___closed__2);
                    v___x_692_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(v_x_629_, v_ks_688_, v_vs_689_, v___x_690_, v___x_691_);
                    lean_dec_ref(v_vs_689_);
                    lean_dec_ref(v_ks_688_);
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
    mut v_keys_701_: *mut LeanObject,
    mut v_vals_702_: *mut LeanObject,
    mut v_i_703_: *mut LeanObject,
    mut v_entries_704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_706_: u8 = 0;
    let mut v_k_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_709_: u64 = 0;
    let mut v_h_710_: usize = 0;
    let mut v___x_711_: usize = 0;
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_713_: usize = 0;
    let mut v___x_714_: usize = 0;
    let mut v___x_715_: usize = 0;
    let mut v_h_716_: usize = 0;
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_705_ = lean_array_get_size(v_keys_701_);
                v___x_706_ = lean_nat_dec_lt(v_i_703_, v___x_705_);
                if v___x_706_ == 0 {
                    lean_dec(v_i_703_);
                    return v_entries_704_;
                } else {
                    v_k_707_ = lean_array_fget_borrowed(v_keys_701_, v_i_703_);
                    v_v_708_ = lean_array_fget_borrowed(v_vals_702_, v_i_703_);
                    v___x_709_ = l_Lean_instHashableMVarId_hash(v_k_707_);
                    v_h_710_ = lean_uint64_to_usize(v___x_709_);
                    v___x_711_ = 5usize;
                    v___x_712_ = lean_unsigned_to_nat(1);
                    v___x_713_ = 1usize;
                    v___x_714_ = lean_usize_sub(v_depth_700_, v___x_713_);
                    v___x_715_ = lean_usize_mul(v___x_711_, v___x_714_);
                    v_h_716_ = lean_usize_shift_right(v_h_710_, v___x_715_);
                    v___x_717_ = lean_nat_add(v_i_703_, v___x_712_);
                    lean_dec(v_i_703_);
                    lean_inc(v_v_708_);
                    lean_inc(v_k_707_);
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
    mut v_depth_720_: *mut LeanObject,
    mut v_keys_721_: *mut LeanObject,
    mut v_vals_722_: *mut LeanObject,
    mut v_i_723_: *mut LeanObject,
    mut v_entries_724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_725_: usize = 0;
    let mut v_res_726_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_725_ = lean_unbox_usize(v_depth_720_);
    lean_dec(v_depth_720_);
    v_res_726_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_boxed_725_, v_keys_721_, v_vals_722_, v_i_723_, v_entries_724_);
    lean_dec_ref(v_vals_722_);
    lean_dec_ref(v_keys_721_);
    return v_res_726_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg___boxed(
    mut v_x_727_: *mut LeanObject,
    mut v_x_728_: *mut LeanObject,
    mut v_x_729_: *mut LeanObject,
    mut v_x_730_: *mut LeanObject,
    mut v_x_731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4592__boxed_732_: usize = 0;
    let mut v_x_4593__boxed_733_: usize = 0;
    let mut v_res_734_: *mut LeanObject = core::ptr::null_mut();
    v_x_4592__boxed_732_ = lean_unbox_usize(v_x_728_);
    lean_dec(v_x_728_);
    v_x_4593__boxed_733_ = lean_unbox_usize(v_x_729_);
    lean_dec(v_x_729_);
    v_res_734_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_x_727_, v_x_4592__boxed_732_, v_x_4593__boxed_733_, v_x_730_, v_x_731_);
    return v_res_734_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3___redArg(
    mut v_x_735_: *mut LeanObject,
    mut v_x_736_: *mut LeanObject,
    mut v_x_737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_738_: u64 = 0;
    let mut v___x_739_: usize = 0;
    let mut v___x_740_: usize = 0;
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    v___x_738_ = l_Lean_instHashableMVarId_hash(v_x_736_);
    v___x_739_ = lean_uint64_to_usize(v___x_738_);
    v___x_740_ = 1usize;
    v___x_741_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_x_735_, v___x_739_, v___x_740_, v_x_736_, v_x_737_);
    return v___x_741_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg(
    mut v_mvarId_742_: *mut LeanObject,
    mut v_val_743_: *mut LeanObject,
    mut v___y_744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_754_: u8 = 0;
    let mut v_depth_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_767_: u8 = 0;
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_778_: u8 = 0;
    let mut v_isSharedCheck_779_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_746_ = lean_st_ref_take(v___y_744_);
                v_mctx_747_ = lean_ctor_get(v___x_746_, 0);
                v_cache_748_ = lean_ctor_get(v___x_746_, 1);
                v_zetaDeltaFVarIds_749_ = lean_ctor_get(v___x_746_, 2);
                v_postponed_750_ = lean_ctor_get(v___x_746_, 3);
                v_diag_751_ = lean_ctor_get(v___x_746_, 4);
                v_isSharedCheck_779_ = (!lean_is_exclusive(v___x_746_)) as u8;
                if v_isSharedCheck_779_ == 0 {
                    v___x_753_ = v___x_746_;
                    v_isShared_754_ = v_isSharedCheck_779_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_751_);
                    lean_inc(v_postponed_750_);
                    lean_inc(v_zetaDeltaFVarIds_749_);
                    lean_inc(v_cache_748_);
                    lean_inc(v_mctx_747_);
                    lean_dec(v___x_746_);
                    v___x_753_ = lean_box(0);
                    v_isShared_754_ = v_isSharedCheck_779_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_755_ = lean_ctor_get(v_mctx_747_, 0);
                v_levelAssignDepth_756_ = lean_ctor_get(v_mctx_747_, 1);
                v_lmvarCounter_757_ = lean_ctor_get(v_mctx_747_, 2);
                v_mvarCounter_758_ = lean_ctor_get(v_mctx_747_, 3);
                v_lDecls_759_ = lean_ctor_get(v_mctx_747_, 4);
                v_decls_760_ = lean_ctor_get(v_mctx_747_, 5);
                v_userNames_761_ = lean_ctor_get(v_mctx_747_, 6);
                v_lAssignment_762_ = lean_ctor_get(v_mctx_747_, 7);
                v_eAssignment_763_ = lean_ctor_get(v_mctx_747_, 8);
                v_dAssignment_764_ = lean_ctor_get(v_mctx_747_, 9);
                v_isSharedCheck_778_ = (!lean_is_exclusive(v_mctx_747_)) as u8;
                if v_isSharedCheck_778_ == 0 {
                    v___x_766_ = v_mctx_747_;
                    v_isShared_767_ = v_isSharedCheck_778_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_764_);
                    lean_inc(v_eAssignment_763_);
                    lean_inc(v_lAssignment_762_);
                    lean_inc(v_userNames_761_);
                    lean_inc(v_decls_760_);
                    lean_inc(v_lDecls_759_);
                    lean_inc(v_mvarCounter_758_);
                    lean_inc(v_lmvarCounter_757_);
                    lean_inc(v_levelAssignDepth_756_);
                    lean_inc(v_depth_755_);
                    lean_dec(v_mctx_747_);
                    v___x_766_ = lean_box(0);
                    v_isShared_767_ = v_isSharedCheck_778_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_768_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3___redArg(v_eAssignment_763_, v_mvarId_742_, v_val_743_);
                if v_isShared_767_ == 0 {
                    lean_ctor_set(v___x_766_, 8, v___x_768_);
                    v___x_770_ = v___x_766_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_777_, 0, v_depth_755_);
                    lean_ctor_set(v_reuseFailAlloc_777_, 1, v_levelAssignDepth_756_);
                    lean_ctor_set(v_reuseFailAlloc_777_, 2, v_lmvarCounter_757_);
                    lean_ctor_set(v_reuseFailAlloc_777_, 3, v_mvarCounter_758_);
                    lean_ctor_set(v_reuseFailAlloc_777_, 4, v_lDecls_759_);
                    lean_ctor_set(v_reuseFailAlloc_777_, 5, v_decls_760_);
                    lean_ctor_set(v_reuseFailAlloc_777_, 6, v_userNames_761_);
                    lean_ctor_set(v_reuseFailAlloc_777_, 7, v_lAssignment_762_);
                    lean_ctor_set(v_reuseFailAlloc_777_, 8, v___x_768_);
                    lean_ctor_set(v_reuseFailAlloc_777_, 9, v_dAssignment_764_);
                    v___x_770_ = v_reuseFailAlloc_777_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_754_ == 0 {
                    lean_ctor_set(v___x_753_, 0, v___x_770_);
                    v___x_772_ = v___x_753_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_776_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_776_, 0, v___x_770_);
                    lean_ctor_set(v_reuseFailAlloc_776_, 1, v_cache_748_);
                    lean_ctor_set(v_reuseFailAlloc_776_, 2, v_zetaDeltaFVarIds_749_);
                    lean_ctor_set(v_reuseFailAlloc_776_, 3, v_postponed_750_);
                    lean_ctor_set(v_reuseFailAlloc_776_, 4, v_diag_751_);
                    v___x_772_ = v_reuseFailAlloc_776_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_773_ = lean_st_ref_set(v___y_744_, v___x_772_);
                v___x_774_ = lean_box(0);
                v___x_775_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_775_, 0, v___x_774_);
                return v___x_775_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg___boxed(
    mut v_mvarId_780_: *mut LeanObject,
    mut v_val_781_: *mut LeanObject,
    mut v___y_782_: *mut LeanObject,
    mut v___y_783_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_784_: *mut LeanObject = core::ptr::null_mut();
    v_res_784_ = l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg(
        v_mvarId_780_,
        v_val_781_,
        v___y_782_,
    );
    lean_dec(v___y_782_);
    return v_res_784_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabAsAuxLemma_spec__0_spec__0(
    mut v_msgData_785_: *mut LeanObject,
    mut v___y_786_: *mut LeanObject,
    mut v___y_787_: *mut LeanObject,
    mut v___y_788_: *mut LeanObject,
    mut v___y_789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    v___x_791_ = lean_st_ref_get(v___y_789_);
    v_env_792_ = lean_ctor_get(v___x_791_, 0);
    lean_inc_ref(v_env_792_);
    lean_dec(v___x_791_);
    v___x_793_ = lean_st_ref_get(v___y_787_);
    v_mctx_794_ = lean_ctor_get(v___x_793_, 0);
    lean_inc_ref(v_mctx_794_);
    lean_dec(v___x_793_);
    v_lctx_795_ = lean_ctor_get(v___y_786_, 2);
    v_options_796_ = lean_ctor_get(v___y_788_, 2);
    lean_inc_ref(v_options_796_);
    lean_inc_ref(v_lctx_795_);
    v___x_797_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_797_, 0, v_env_792_);
    lean_ctor_set(v___x_797_, 1, v_mctx_794_);
    lean_ctor_set(v___x_797_, 2, v_lctx_795_);
    lean_ctor_set(v___x_797_, 3, v_options_796_);
    v___x_798_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_798_, 0, v___x_797_);
    lean_ctor_set(v___x_798_, 1, v_msgData_785_);
    v___x_799_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_799_, 0, v___x_798_);
    return v___x_799_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabAsAuxLemma_spec__0_spec__0___boxed(
    mut v_msgData_800_: *mut LeanObject,
    mut v___y_801_: *mut LeanObject,
    mut v___y_802_: *mut LeanObject,
    mut v___y_803_: *mut LeanObject,
    mut v___y_804_: *mut LeanObject,
    mut v___y_805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_806_: *mut LeanObject = core::ptr::null_mut();
    v_res_806_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabAsAuxLemma_spec__0_spec__0(v_msgData_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
    lean_dec(v___y_804_);
    lean_dec_ref(v___y_803_);
    lean_dec(v___y_802_);
    lean_dec_ref(v___y_801_);
    return v_res_806_;
}
pub unsafe fn l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg(
    mut v_msg_807_: *mut LeanObject,
    mut v___y_808_: *mut LeanObject,
    mut v___y_809_: *mut LeanObject,
    mut v___y_810_: *mut LeanObject,
    mut v___y_811_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_818_: u8 = 0;
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_823_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_813_ = lean_ctor_get(v___y_810_, 5);
                v___x_814_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00elabAsAuxLemma_spec__0_spec__0(v_msg_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
                v_a_815_ = lean_ctor_get(v___x_814_, 0);
                v_isSharedCheck_823_ = (!lean_is_exclusive(v___x_814_)) as u8;
                if v_isSharedCheck_823_ == 0 {
                    v___x_817_ = v___x_814_;
                    v_isShared_818_ = v_isSharedCheck_823_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_815_);
                    lean_dec(v___x_814_);
                    v___x_817_ = lean_box(0);
                    v_isShared_818_ = v_isSharedCheck_823_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_813_);
                v___x_819_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_819_, 0, v_ref_813_);
                lean_ctor_set(v___x_819_, 1, v_a_815_);
                if v_isShared_818_ == 0 {
                    lean_ctor_set_tag(v___x_817_, 1);
                    lean_ctor_set(v___x_817_, 0, v___x_819_);
                    v___x_821_ = v___x_817_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_819_);
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
    mut v_msg_824_: *mut LeanObject,
    mut v___y_825_: *mut LeanObject,
    mut v___y_826_: *mut LeanObject,
    mut v___y_827_: *mut LeanObject,
    mut v___y_828_: *mut LeanObject,
    mut v___y_829_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_830_: *mut LeanObject = core::ptr::null_mut();
    v_res_830_ = l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg(
        v_msg_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_,
    );
    lean_dec(v___y_828_);
    lean_dec_ref(v___y_827_);
    lean_dec(v___y_826_);
    lean_dec_ref(v___y_825_);
    return v_res_830_;
}
pub unsafe fn _init_l_elabAsAuxLemma___lam__0___closed__1() -> *mut LeanObject {
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    v___x_832_ = l_elabAsAuxLemma___lam__0___closed__0;
    v___x_833_ = l_Lean_stringToMessageData(v___x_832_);
    return v___x_833_;
}
pub unsafe fn l_elabAsAuxLemma___lam__0(
    mut v___x_834_: *mut LeanObject,
    mut v___x_835_: u8,
    mut v___y_836_: *mut LeanObject,
    mut v___y_837_: *mut LeanObject,
    mut v___y_838_: *mut LeanObject,
    mut v___y_839_: *mut LeanObject,
    mut v___y_840_: *mut LeanObject,
    mut v___y_841_: *mut LeanObject,
    mut v___y_842_: *mut LeanObject,
    mut v___y_843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: u8 = 0;
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_869_: u8 = 0;
    let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_873_: u8 = 0;
    let mut v_a_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_877_: u8 = 0;
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_881_: u8 = 0;
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: u8 = 0;
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_891_: u8 = 0;
    let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_895_: u8 = 0;
    let mut v_a_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_899_: u8 = 0;
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_903_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_845_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v___y_837_, v___y_840_, v___y_841_, v___y_842_, v___y_843_,
                );
                if lean_obj_tag(v___x_845_) == 0 {
                    v_a_846_ = lean_ctor_get(v___x_845_, 0);
                    lean_inc_n(v_a_846_, 2);
                    lean_dec_ref_known(v___x_845_, 1);
                    v___x_882_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_evalTactic___boxed as *mut core::ffi::c_void,
                        10,
                        1,
                    );
                    lean_closure_set(v___x_882_, 0, v___x_834_);
                    v___x_883_ = l_Lean_Elab_Tactic_run(
                        v_a_846_, v___x_882_, v___y_838_, v___y_839_, v___y_840_, v___y_841_,
                        v___y_842_, v___y_843_,
                    );
                    if lean_obj_tag(v___x_883_) == 0 {
                        v_a_884_ = lean_ctor_get(v___x_883_, 0);
                        lean_inc(v_a_884_);
                        lean_dec_ref_known(v___x_883_, 1);
                        v___x_885_ = l_List_isEmpty___redArg(v_a_884_);
                        lean_dec(v_a_884_);
                        if v___x_885_ == 0 {
                            lean_dec(v_a_846_);
                            v___x_886_ = lean_obj_once(
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
                        lean_dec(v_a_846_);
                        v_a_888_ = lean_ctor_get(v___x_883_, 0);
                        v_isSharedCheck_895_ = (!lean_is_exclusive(v___x_883_)) as u8;
                        if v_isSharedCheck_895_ == 0 {
                            v___x_890_ = v___x_883_;
                            v_isShared_891_ = v_isSharedCheck_895_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_888_);
                            lean_dec(v___x_883_);
                            v___x_890_ = lean_box(0);
                            v_isShared_891_ = v_isSharedCheck_895_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_834_);
                    v_a_896_ = lean_ctor_get(v___x_845_, 0);
                    v_isSharedCheck_903_ = (!lean_is_exclusive(v___x_845_)) as u8;
                    if v_isSharedCheck_903_ == 0 {
                        v___x_898_ = v___x_845_;
                        v_isShared_899_ = v_isSharedCheck_903_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_896_);
                        lean_dec(v___x_845_);
                        v___x_898_ = lean_box(0);
                        v_isShared_899_ = v_isSharedCheck_903_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_n(v_a_846_, 2);
                v___x_856_ = l_Lean_mkMVar(v_a_846_);
                v___x_857_ = l_Lean_instantiateMVars___at___00elabAsAuxLemma_spec__1___redArg(
                    v___x_856_, v___y_853_,
                );
                v_a_858_ = lean_ctor_get(v___x_857_, 0);
                lean_inc(v_a_858_);
                lean_dec_ref(v___x_857_);
                v___x_859_ =
                    l_Lean_MVarId_getType(v_a_846_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
                if lean_obj_tag(v___x_859_) == 0 {
                    v_a_860_ = lean_ctor_get(v___x_859_, 0);
                    lean_inc(v_a_860_);
                    lean_dec_ref_known(v___x_859_, 1);
                    v___x_861_ = 0;
                    v___x_862_ = lean_box(0);
                    v___x_863_ = l_Lean_Meta_mkAuxTheorem(
                        v_a_860_, v_a_858_, v___x_861_, v___x_862_, v___x_835_, v___y_852_,
                        v___y_853_, v___y_854_, v___y_855_,
                    );
                    if lean_obj_tag(v___x_863_) == 0 {
                        v_a_864_ = lean_ctor_get(v___x_863_, 0);
                        lean_inc(v_a_864_);
                        lean_dec_ref_known(v___x_863_, 1);
                        v___x_865_ = l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg(
                            v_a_846_, v_a_864_, v___y_853_,
                        );
                        return v___x_865_;
                    } else {
                        lean_dec(v_a_846_);
                        v_a_866_ = lean_ctor_get(v___x_863_, 0);
                        v_isSharedCheck_873_ = (!lean_is_exclusive(v___x_863_)) as u8;
                        if v_isSharedCheck_873_ == 0 {
                            v___x_868_ = v___x_863_;
                            v_isShared_869_ = v_isSharedCheck_873_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_866_);
                            lean_dec(v___x_863_);
                            v___x_868_ = lean_box(0);
                            v_isShared_869_ = v_isSharedCheck_873_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_858_);
                    lean_dec(v_a_846_);
                    v_a_874_ = lean_ctor_get(v___x_859_, 0);
                    v_isSharedCheck_881_ = (!lean_is_exclusive(v___x_859_)) as u8;
                    if v_isSharedCheck_881_ == 0 {
                        v___x_876_ = v___x_859_;
                        v_isShared_877_ = v_isSharedCheck_881_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_874_);
                        lean_dec(v___x_859_);
                        v___x_876_ = lean_box(0);
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
                    v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
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
                    v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
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
                    v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
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
                    v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
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
    mut v___x_904_: *mut LeanObject,
    mut v___x_905_: *mut LeanObject,
    mut v___y_906_: *mut LeanObject,
    mut v___y_907_: *mut LeanObject,
    mut v___y_908_: *mut LeanObject,
    mut v___y_909_: *mut LeanObject,
    mut v___y_910_: *mut LeanObject,
    mut v___y_911_: *mut LeanObject,
    mut v___y_912_: *mut LeanObject,
    mut v___y_913_: *mut LeanObject,
    mut v___y_914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4879__boxed_915_: u8 = 0;
    let mut v_res_916_: *mut LeanObject = core::ptr::null_mut();
    v___x_4879__boxed_915_ = (lean_unbox(v___x_905_) as u8);
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
    lean_dec(v___y_913_);
    lean_dec_ref(v___y_912_);
    lean_dec(v___y_911_);
    lean_dec_ref(v___y_910_);
    lean_dec(v___y_909_);
    lean_dec_ref(v___y_908_);
    lean_dec(v___y_907_);
    lean_dec_ref(v___y_906_);
    return v_res_916_;
}
pub unsafe fn _init_l_elabAsAuxLemma___closed__6() -> *mut LeanObject {
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    v___x_927_ = l_elabAsAuxLemma___closed__5;
    v___x_928_ = l_Lean_stringToMessageData(v___x_927_);
    return v___x_928_;
}
pub unsafe fn l_elabAsAuxLemma(
    mut v_x_929_: *mut LeanObject,
    mut v_a_930_: *mut LeanObject,
    mut v_a_931_: *mut LeanObject,
    mut v_a_932_: *mut LeanObject,
    mut v_a_933_: *mut LeanObject,
    mut v_a_934_: *mut LeanObject,
    mut v_a_935_: *mut LeanObject,
    mut v_a_936_: *mut LeanObject,
    mut v_a_937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: u8 = 0;
    v___x_939_ = l_elabAsAuxLemma___closed__4;
    lean_inc(v_x_929_);
    v___x_940_ = l_Lean_Syntax_isOfKind(v_x_929_, v___x_939_);
    if v___x_940_ == 0 {
        let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_929_);
        v___x_941_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_elabAsAuxLemma___closed__6),
            core::ptr::addr_of_mut!(l_elabAsAuxLemma___closed__6_once),
            _init_l_elabAsAuxLemma___closed__6,
        );
        v___x_942_ = l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg(
            v___x_941_, v_a_934_, v_a_935_, v_a_936_, v_a_937_,
        );
        return v___x_942_;
    } else {
        let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_946_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
        v___x_943_ = lean_unsigned_to_nat(2);
        v___x_944_ = l_Lean_Syntax_getArg(v_x_929_, v___x_943_);
        lean_dec(v_x_929_);
        v___x_945_ = lean_box((v___x_940_) as usize);
        v___f_946_ = lean_alloc_closure(
            l_elabAsAuxLemma___lam__0___boxed as *mut core::ffi::c_void,
            11,
            2,
        );
        lean_closure_set(v___f_946_, 0, v___x_944_);
        lean_closure_set(v___f_946_, 1, v___x_945_);
        v___x_947_ = l_Lean_Elab_Tactic_withMainContext___redArg(
            v___f_946_, v_a_930_, v_a_931_, v_a_932_, v_a_933_, v_a_934_, v_a_935_, v_a_936_,
            v_a_937_,
        );
        return v___x_947_;
    }
}
pub unsafe fn l_elabAsAuxLemma___boxed(
    mut v_x_948_: *mut LeanObject,
    mut v_a_949_: *mut LeanObject,
    mut v_a_950_: *mut LeanObject,
    mut v_a_951_: *mut LeanObject,
    mut v_a_952_: *mut LeanObject,
    mut v_a_953_: *mut LeanObject,
    mut v_a_954_: *mut LeanObject,
    mut v_a_955_: *mut LeanObject,
    mut v_a_956_: *mut LeanObject,
    mut v_a_957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_958_: *mut LeanObject = core::ptr::null_mut();
    v_res_958_ = l_elabAsAuxLemma(
        v_x_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_,
    );
    lean_dec(v_a_956_);
    lean_dec_ref(v_a_955_);
    lean_dec(v_a_954_);
    lean_dec_ref(v_a_953_);
    lean_dec(v_a_952_);
    lean_dec_ref(v_a_951_);
    lean_dec(v_a_950_);
    lean_dec_ref(v_a_949_);
    return v_res_958_;
}
pub unsafe fn l_Lean_throwError___at___00elabAsAuxLemma_spec__0(
    mut v_00_u03b1_959_: *mut LeanObject,
    mut v_msg_960_: *mut LeanObject,
    mut v___y_961_: *mut LeanObject,
    mut v___y_962_: *mut LeanObject,
    mut v___y_963_: *mut LeanObject,
    mut v___y_964_: *mut LeanObject,
    mut v___y_965_: *mut LeanObject,
    mut v___y_966_: *mut LeanObject,
    mut v___y_967_: *mut LeanObject,
    mut v___y_968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    v___x_970_ = l_Lean_throwError___at___00elabAsAuxLemma_spec__0___redArg(
        v_msg_960_, v___y_965_, v___y_966_, v___y_967_, v___y_968_,
    );
    return v___x_970_;
}
pub unsafe fn l_Lean_throwError___at___00elabAsAuxLemma_spec__0___boxed(
    mut v_00_u03b1_971_: *mut LeanObject,
    mut v_msg_972_: *mut LeanObject,
    mut v___y_973_: *mut LeanObject,
    mut v___y_974_: *mut LeanObject,
    mut v___y_975_: *mut LeanObject,
    mut v___y_976_: *mut LeanObject,
    mut v___y_977_: *mut LeanObject,
    mut v___y_978_: *mut LeanObject,
    mut v___y_979_: *mut LeanObject,
    mut v___y_980_: *mut LeanObject,
    mut v___y_981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_982_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_980_);
    lean_dec_ref(v___y_979_);
    lean_dec(v___y_978_);
    lean_dec_ref(v___y_977_);
    lean_dec(v___y_976_);
    lean_dec_ref(v___y_975_);
    lean_dec(v___y_974_);
    lean_dec_ref(v___y_973_);
    return v_res_982_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2(
    mut v_mvarId_983_: *mut LeanObject,
    mut v_val_984_: *mut LeanObject,
    mut v___y_985_: *mut LeanObject,
    mut v___y_986_: *mut LeanObject,
    mut v___y_987_: *mut LeanObject,
    mut v___y_988_: *mut LeanObject,
    mut v___y_989_: *mut LeanObject,
    mut v___y_990_: *mut LeanObject,
    mut v___y_991_: *mut LeanObject,
    mut v___y_992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    v___x_994_ = l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___redArg(
        v_mvarId_983_,
        v_val_984_,
        v___y_990_,
    );
    return v___x_994_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2___boxed(
    mut v_mvarId_995_: *mut LeanObject,
    mut v_val_996_: *mut LeanObject,
    mut v___y_997_: *mut LeanObject,
    mut v___y_998_: *mut LeanObject,
    mut v___y_999_: *mut LeanObject,
    mut v___y_1000_: *mut LeanObject,
    mut v___y_1001_: *mut LeanObject,
    mut v___y_1002_: *mut LeanObject,
    mut v___y_1003_: *mut LeanObject,
    mut v___y_1004_: *mut LeanObject,
    mut v___y_1005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1006_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1004_);
    lean_dec_ref(v___y_1003_);
    lean_dec(v___y_1002_);
    lean_dec_ref(v___y_1001_);
    lean_dec(v___y_1000_);
    lean_dec_ref(v___y_999_);
    lean_dec(v___y_998_);
    lean_dec_ref(v___y_997_);
    return v_res_1006_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3(
    mut v_00_u03b2_1007_: *mut LeanObject,
    mut v_x_1008_: *mut LeanObject,
    mut v_x_1009_: *mut LeanObject,
    mut v_x_1010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    v___x_1011_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3___redArg(v_x_1008_, v_x_1009_, v_x_1010_);
    return v___x_1011_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4(
    mut v_00_u03b2_1012_: *mut LeanObject,
    mut v_x_1013_: *mut LeanObject,
    mut v_x_1014_: usize,
    mut v_x_1015_: usize,
    mut v_x_1016_: *mut LeanObject,
    mut v_x_1017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    v___x_1018_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___redArg(v_x_1013_, v_x_1014_, v_x_1015_, v_x_1016_, v_x_1017_);
    return v___x_1018_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4___boxed(
    mut v_00_u03b2_1019_: *mut LeanObject,
    mut v_x_1020_: *mut LeanObject,
    mut v_x_1021_: *mut LeanObject,
    mut v_x_1022_: *mut LeanObject,
    mut v_x_1023_: *mut LeanObject,
    mut v_x_1024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_5162__boxed_1025_: usize = 0;
    let mut v_x_5163__boxed_1026_: usize = 0;
    let mut v_res_1027_: *mut LeanObject = core::ptr::null_mut();
    v_x_5162__boxed_1025_ = lean_unbox_usize(v_x_1021_);
    lean_dec(v_x_1021_);
    v_x_5163__boxed_1026_ = lean_unbox_usize(v_x_1022_);
    lean_dec(v_x_1022_);
    v_res_1027_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4(v_00_u03b2_1019_, v_x_1020_, v_x_5162__boxed_1025_, v_x_5163__boxed_1026_, v_x_1023_, v_x_1024_);
    return v_res_1027_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5(
    mut v_00_u03b2_1028_: *mut LeanObject,
    mut v_n_1029_: *mut LeanObject,
    mut v_k_1030_: *mut LeanObject,
    mut v_v_1031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    v___x_1032_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5___redArg(v_n_1029_, v_k_1030_, v_v_1031_);
    return v___x_1032_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6(
    mut v_00_u03b2_1033_: *mut LeanObject,
    mut v_depth_1034_: usize,
    mut v_keys_1035_: *mut LeanObject,
    mut v_vals_1036_: *mut LeanObject,
    mut v_heq_1037_: *mut LeanObject,
    mut v_i_1038_: *mut LeanObject,
    mut v_entries_1039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    v___x_1040_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___redArg(v_depth_1034_, v_keys_1035_, v_vals_1036_, v_i_1038_, v_entries_1039_);
    return v___x_1040_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6___boxed(
    mut v_00_u03b2_1041_: *mut LeanObject,
    mut v_depth_1042_: *mut LeanObject,
    mut v_keys_1043_: *mut LeanObject,
    mut v_vals_1044_: *mut LeanObject,
    mut v_heq_1045_: *mut LeanObject,
    mut v_i_1046_: *mut LeanObject,
    mut v_entries_1047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1048_: usize = 0;
    let mut v_res_1049_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1048_ = lean_unbox_usize(v_depth_1042_);
    lean_dec(v_depth_1042_);
    v_res_1049_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__6(v_00_u03b2_1041_, v_depth_boxed_1048_, v_keys_1043_, v_vals_1044_, v_heq_1045_, v_i_1046_, v_entries_1047_);
    lean_dec_ref(v_vals_1044_);
    lean_dec_ref(v_keys_1043_);
    return v_res_1049_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6(
    mut v_00_u03b2_1050_: *mut LeanObject,
    mut v_x_1051_: *mut LeanObject,
    mut v_x_1052_: *mut LeanObject,
    mut v_x_1053_: *mut LeanObject,
    mut v_x_1054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    v___x_1055_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00elabAsAuxLemma_spec__2_spec__3_spec__4_spec__5_spec__6___redArg(v_x_1051_, v_x_1052_, v_x_1053_, v_x_1054_);
    return v___x_1055_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1()
-> *mut LeanObject {
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: *mut LeanObject = core::ptr::null_mut();
    v___x_1060_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_1061_ = l_elabAsAuxLemma___closed__4;
    v___x_1062_ = l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___closed__1;
    v___x_1063_ = lean_alloc_closure(l_elabAsAuxLemma___boxed as *mut core::ffi::c_void, 10, 0);
    v___x_1064_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1060_,
        v___x_1061_,
        v___x_1062_,
        v___x_1063_,
    );
    return v___x_1064_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1___boxed(
    mut v_a_1065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1066_: *mut LeanObject = core::ptr::null_mut();
    v_res_1066_ =
        l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1();
    return v_res_1066_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_AsAuxLemma(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_Tactic_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res =
        l___private_Lean_Elab_Tactic_AsAuxLemma_0__elabAsAuxLemma___regBuiltin_elabAsAuxLemma__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_AsAuxLemma(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_AsAuxLemma(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_Tactic_Meta(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_AsAuxLemma(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_AsAuxLemma(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_AsAuxLemma(builtin);
}

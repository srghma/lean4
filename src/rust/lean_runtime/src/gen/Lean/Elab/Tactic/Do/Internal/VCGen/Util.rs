// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Util
// Imports: Lean.Meta.Tactic.Grind.Main Lean.Elab.Tactic.Do.Internal.VCGen.Context Lean.Elab.Tactic.Do.Internal.VCGen.Reduce Lean.Meta.Sym.AlphaShareBuilder Lean.Meta.Sym.Intro Lean.Meta.Sym.Simp.Telescope Lean.Meta.Sym.Util
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Context::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context,
    l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_isGrind,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context,
};
use crate::r#gen::Lean::Elab::Tactic::Do::Internal::VCGen::Reduce::{
    initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce,
    l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead,
    runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_hasMVar,
    l_Lean_Expr_isAppOf, l_Lean_Expr_isAppOfArity, l_Lean_Expr_mvarId_x21,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_mkApp3, l_Lean_mkAppB,
    l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_Context_config,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::Sym::AlphaShareBuilder::{
    initialize_Lean_Meta_Sym_AlphaShareBuilder, runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder,
};
use crate::r#gen::Lean::Meta::Sym::Apply::l_Lean_Meta_Sym_BackwardRule_apply;
use crate::r#gen::Lean::Meta::Sym::Intro::{
    initialize_Lean_Meta_Sym_Intro, l_Lean_Meta_Sym_intros, runtime_initialize_Lean_Meta_Sym_Intro,
};
use crate::r#gen::Lean::Meta::Sym::Pattern::l_Lean_Meta_Sym_isDefEqS;
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    l_Lean_Meta_Sym_Simp_SimpM_run___redArg, l_Lean_Meta_Sym_Simp_simp___boxed,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Telescope::{
    initialize_Lean_Meta_Sym_Simp_Telescope, l_Lean_Meta_Sym_Simp_simpTelescope___boxed,
    runtime_initialize_Lean_Meta_Sym_Simp_Telescope,
};
use crate::r#gen::Lean::Meta::Sym::Util::{
    initialize_Lean_Meta_Sym_Util, l_Lean_Meta_Sym_unfoldReducible,
    runtime_initialize_Lean_Meta_Sym_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Main::{
    initialize_Lean_Meta_Tactic_Grind_Main, l_Lean_Meta_Grind_processHypotheses,
    runtime_initialize_Lean_Meta_Tactic_Grind_Main,
};
use crate::r#gen::Lean::Meta::Tactic::Replace::{
    l_Lean_MVarId_replaceTargetDefEq, l_Lean_MVarId_replaceTargetEq,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getType, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
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
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_12, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0_value: LeanStringObject<31> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 31, m_capacity: 31, m_length: 30, m_data: [91, 109, 118, 99, 103, 101, 110, 39, 32, 43, 100, 101, 98, 117, 103, 93, 32, 66, 97, 99, 107, 119, 97, 114, 100, 82, 117, 108, 101, 32, 0]};
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2_value: LeanStringObject<21> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [32, 102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 97, 112, 112, 108, 121, 32, 116, 111, 58, 0]};
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4_value: LeanStringObject<57> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 57, m_capacity: 57, m_length: 56, m_data: [10, 98, 117, 116, 32, 115, 117, 99, 99, 101, 101, 100, 101, 100, 32, 97, 102, 116, 101, 114, 32, 96, 117, 110, 102, 111, 108, 100, 82, 101, 100, 117, 99, 105, 98, 108, 101, 96, 45, 110, 111, 114, 109, 97, 108, 105, 122, 97, 116, 105, 111, 110, 32, 116, 111, 58, 0]};
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6_value: LeanStringObject<116> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 116, m_capacity: 116, m_length: 115, m_data: [10, 65, 110, 32, 101, 97, 114, 108, 105, 101, 114, 32, 115, 116, 101, 112, 32, 105, 115, 32, 109, 105, 115, 115, 105, 110, 103, 32, 97, 32, 110, 111, 114, 109, 97, 108, 105, 122, 97, 116, 105, 111, 110, 46, 32, 82, 101, 45, 114, 117, 110, 32, 119, 105, 116, 104, 32, 96, 115, 101, 116, 95, 111, 112, 116, 105, 111, 110, 32, 112, 112, 46, 97, 108, 108, 32, 116, 114, 117, 101, 96, 32, 116, 111, 32, 115, 101, 101, 32, 116, 104, 101, 32, 115, 116, 114, 117, 99, 116, 117, 114, 97, 108, 32, 100, 105, 102, 102, 101, 114, 101, 110, 99, 101, 46, 0]};
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__10_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [60, 114, 117, 108, 101, 32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 101, 100, 32, 102, 114, 111, 109, 32, 101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 62, 0]};
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__10_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Sym_Simp_simpTelescope___boxed as *const core::ffi::c_void,
    m_arity: 11,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__1_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((100000 as usize) << 1) | 1) as *mut LeanObject,
        (((2 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__0_value:
    LeanArrayObject<0> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__1_value:
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
        70, 97, 105, 108, 101, 100, 32, 116, 111, 32, 105, 110, 116, 114, 111, 32, 111, 110, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__3_value:
    LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [10, 67, 111, 110, 116, 101, 120, 116, 58, 32, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__5_value:
    LeanStringObject<2> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [46, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [84, 114, 117, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__1_value:
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
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__0_value
        ) as *mut LeanObject,
        11870096045526947150 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__1_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__2_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [65, 110, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__2_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__3_value:
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
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__2_value
        ) as *mut LeanObject,
        9743492140944907313 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__3_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__4_value:
    LeanStringObject<3> = LeanStringObject {
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
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__4_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__5_value:
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
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__4_value
        ) as *mut LeanObject,
        16122875713692181903 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__5: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__5_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__6_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__6: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__6_value
)
    as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__7_value_aux_0:
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
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__4_value
        ) as *mut LeanObject,
        16122875713692181903 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__7_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__7_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__6_value
        ) as *mut LeanObject,
        13480818501600609864 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__7: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__7_value
)
    as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__8_value:
    LeanStringObject<31> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        114, 101, 112, 101, 97, 116, 65, 110, 100, 82, 102, 108, 58, 32, 102, 97, 105, 108, 101,
        100, 32, 116, 111, 32, 97, 112, 112, 108, 121, 32, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__8: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__8_value
)
    as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__10_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [105, 110, 116, 114, 111, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__10:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__10_value
) as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__11_value_aux_0:
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
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__2_value
        ) as *mut LeanObject,
        9743492140944907313 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__11_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__11_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__10_value
        ) as *mut LeanObject,
        11695081953491693114 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__11:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__11_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__12_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [32, 116, 111, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__12:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__12_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__13_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__13:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__14_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__14:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__15_value:
    LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [108, 101, 102, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__15:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__15_value
) as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__16_value_aux_0:
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
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__2_value
        ) as *mut LeanObject,
        9743492140944907313 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__16_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__16_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__15_value
        ) as *mut LeanObject,
        10675986705697471500 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__16:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__16_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__17_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__17:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__18_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [114, 105, 103, 104, 116, 0],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__18:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__18_value
) as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__19_value_aux_0:
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
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__2_value
        ) as *mut LeanObject,
        9743492140944907313 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__19_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__19_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__18_value
        ) as *mut LeanObject,
        10515106874815532050 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__19:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__19_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__20_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__20:
    *mut LeanObject = core::ptr::null_mut();
static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__21_value_aux_0:
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
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__0_value
        ) as *mut LeanObject,
        11870096045526947150 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__21_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__21_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__10_value
        ) as *mut LeanObject,
        18067798339771668657 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__21:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__21_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__22_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__22:
    *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(
    mut v___y_1577_: *mut LeanObject,
    mut v_mctx_1578_: *mut LeanObject,
    mut v_cache_1579_: *mut LeanObject,
    mut v_a_x3f_1580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1588_: u8 = 0;
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1595_: u8 = 0;
    let mut v_unused_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1582_ = lean_st_ref_take(v___y_1577_);
                v_zetaDeltaFVarIds_1583_ = lean_ctor_get(v___x_1582_, 2);
                v_postponed_1584_ = lean_ctor_get(v___x_1582_, 3);
                v_diag_1585_ = lean_ctor_get(v___x_1582_, 4);
                v_isSharedCheck_1595_ = (!lean_is_exclusive(v___x_1582_)) as u8;
                if v_isSharedCheck_1595_ == 0 {
                    v_unused_1596_ = lean_ctor_get(v___x_1582_, 1);
                    lean_dec(v_unused_1596_);
                    v_unused_1597_ = lean_ctor_get(v___x_1582_, 0);
                    lean_dec(v_unused_1597_);
                    v___x_1587_ = v___x_1582_;
                    v_isShared_1588_ = v_isSharedCheck_1595_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_1585_);
                    lean_inc(v_postponed_1584_);
                    lean_inc(v_zetaDeltaFVarIds_1583_);
                    lean_dec(v___x_1582_);
                    v___x_1587_ = lean_box(0);
                    v_isShared_1588_ = v_isSharedCheck_1595_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_1588_ == 0 {
                    lean_ctor_set(v___x_1587_, 1, v_cache_1579_);
                    lean_ctor_set(v___x_1587_, 0, v_mctx_1578_);
                    v___x_1590_ = v___x_1587_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_mctx_1578_);
                    lean_ctor_set(v_reuseFailAlloc_1594_, 1, v_cache_1579_);
                    lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_zetaDeltaFVarIds_1583_);
                    lean_ctor_set(v_reuseFailAlloc_1594_, 3, v_postponed_1584_);
                    lean_ctor_set(v_reuseFailAlloc_1594_, 4, v_diag_1585_);
                    v___x_1590_ = v_reuseFailAlloc_1594_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1591_ = lean_st_ref_set(v___y_1577_, v___x_1590_);
                v___x_1592_ = lean_box(0);
                v___x_1593_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1593_, 0, v___x_1592_);
                return v___x_1593_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0___boxed(
    mut v___y_1598_: *mut LeanObject,
    mut v_mctx_1599_: *mut LeanObject,
    mut v_cache_1600_: *mut LeanObject,
    mut v_a_x3f_1601_: *mut LeanObject,
    mut v___y_1602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1603_: *mut LeanObject = core::ptr::null_mut();
    v_res_1603_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_1598_, v_mctx_1599_, v_cache_1600_, v_a_x3f_1601_);
    lean_dec(v_a_x3f_1601_);
    lean_dec(v___y_1598_);
    return v_res_1603_;
}
pub unsafe fn l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(
    mut v_x_1604_: *mut LeanObject,
    mut v___y_1605_: *mut LeanObject,
    mut v___y_1606_: *mut LeanObject,
    mut v___y_1607_: *mut LeanObject,
    mut v___y_1608_: *mut LeanObject,
    mut v___y_1609_: *mut LeanObject,
    mut v___y_1610_: *mut LeanObject,
    mut v___y_1611_: *mut LeanObject,
    mut v___y_1612_: *mut LeanObject,
    mut v___y_1613_: *mut LeanObject,
    mut v___y_1614_: *mut LeanObject,
    mut v___y_1615_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1625_: u8 = 0;
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1631_: u8 = 0;
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1635_: u8 = 0;
    let mut v_unused_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1638_: u8 = 0;
    let mut v_a_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1644_: u8 = 0;
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1648_: u8 = 0;
    let mut v_unused_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1617_ = lean_st_ref_get(v___y_1613_);
                v___x_1618_ = lean_st_ref_get(v___y_1613_);
                v_mctx_1619_ = lean_ctor_get(v___x_1617_, 0);
                lean_inc_ref(v_mctx_1619_);
                lean_dec(v___x_1617_);
                v_cache_1620_ = lean_ctor_get(v___x_1618_, 1);
                lean_inc_ref(v_cache_1620_);
                lean_dec(v___x_1618_);
                lean_inc(v___y_1615_);
                lean_inc_ref(v___y_1614_);
                lean_inc(v___y_1613_);
                lean_inc_ref(v___y_1612_);
                lean_inc(v___y_1611_);
                lean_inc_ref(v___y_1610_);
                lean_inc(v___y_1609_);
                lean_inc_ref(v___y_1608_);
                lean_inc(v___y_1607_);
                lean_inc(v___y_1606_);
                lean_inc_ref(v___y_1605_);
                v___x_1621_ = lean_apply_12(
                    v_x_1604_,
                    v___y_1605_,
                    v___y_1606_,
                    v___y_1607_,
                    v___y_1608_,
                    v___y_1609_,
                    v___y_1610_,
                    v___y_1611_,
                    v___y_1612_,
                    v___y_1613_,
                    v___y_1614_,
                    v___y_1615_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_1621_) == 0 {
                    v_a_1622_ = lean_ctor_get(v___x_1621_, 0);
                    v_isSharedCheck_1638_ = (!lean_is_exclusive(v___x_1621_)) as u8;
                    if v_isSharedCheck_1638_ == 0 {
                        v___x_1624_ = v___x_1621_;
                        v_isShared_1625_ = v_isSharedCheck_1638_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1622_);
                        lean_dec(v___x_1621_);
                        v___x_1624_ = lean_box(0);
                        v_isShared_1625_ = v_isSharedCheck_1638_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1639_ = lean_ctor_get(v___x_1621_, 0);
                    lean_inc(v_a_1639_);
                    lean_dec_ref_known(v___x_1621_, 1);
                    v___x_1640_ = lean_box(0);
                    v___x_1641_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_1613_, v_mctx_1619_, v_cache_1620_, v___x_1640_);
                    v_isSharedCheck_1648_ = (!lean_is_exclusive(v___x_1641_)) as u8;
                    if v_isSharedCheck_1648_ == 0 {
                        v_unused_1649_ = lean_ctor_get(v___x_1641_, 0);
                        lean_dec(v_unused_1649_);
                        v___x_1643_ = v___x_1641_;
                        v_isShared_1644_ = v_isSharedCheck_1648_;
                        state = 5;
                        continue;
                    } else {
                        lean_dec(v___x_1641_);
                        v___x_1643_ = lean_box(0);
                        v_isShared_1644_ = v_isSharedCheck_1648_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_a_1622_);
                if v_isShared_1625_ == 0 {
                    lean_ctor_set_tag(v___x_1624_, 1);
                    v___x_1627_ = v___x_1624_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1637_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1637_, 0, v_a_1622_);
                    v___x_1627_ = v_reuseFailAlloc_1637_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1628_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___lam__0(v___y_1613_, v_mctx_1619_, v_cache_1620_, v___x_1627_);
                lean_dec_ref(v___x_1627_);
                v_isSharedCheck_1635_ = (!lean_is_exclusive(v___x_1628_)) as u8;
                if v_isSharedCheck_1635_ == 0 {
                    v_unused_1636_ = lean_ctor_get(v___x_1628_, 0);
                    lean_dec(v_unused_1636_);
                    v___x_1630_ = v___x_1628_;
                    v_isShared_1631_ = v_isSharedCheck_1635_;
                    state = 3;
                    continue;
                } else {
                    lean_dec(v___x_1628_);
                    v___x_1630_ = lean_box(0);
                    v_isShared_1631_ = v_isSharedCheck_1635_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1631_ == 0 {
                    lean_ctor_set(v___x_1630_, 0, v_a_1622_);
                    v___x_1633_ = v___x_1630_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_a_1622_);
                    v___x_1633_ = v_reuseFailAlloc_1634_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1633_;
            }
            5 => {
                if v_isShared_1644_ == 0 {
                    lean_ctor_set_tag(v___x_1643_, 1);
                    lean_ctor_set(v___x_1643_, 0, v_a_1639_);
                    v___x_1646_ = v___x_1643_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1647_, 0, v_a_1639_);
                    v___x_1646_ = v_reuseFailAlloc_1647_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1646_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg___boxed(
    mut v_x_1650_: *mut LeanObject,
    mut v___y_1651_: *mut LeanObject,
    mut v___y_1652_: *mut LeanObject,
    mut v___y_1653_: *mut LeanObject,
    mut v___y_1654_: *mut LeanObject,
    mut v___y_1655_: *mut LeanObject,
    mut v___y_1656_: *mut LeanObject,
    mut v___y_1657_: *mut LeanObject,
    mut v___y_1658_: *mut LeanObject,
    mut v___y_1659_: *mut LeanObject,
    mut v___y_1660_: *mut LeanObject,
    mut v___y_1661_: *mut LeanObject,
    mut v___y_1662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1663_: *mut LeanObject = core::ptr::null_mut();
    v_res_1663_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v_x_1650_, v___y_1651_, v___y_1652_, v___y_1653_, v___y_1654_, v___y_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
    lean_dec(v___y_1661_);
    lean_dec_ref(v___y_1660_);
    lean_dec(v___y_1659_);
    lean_dec_ref(v___y_1658_);
    lean_dec(v___y_1657_);
    lean_dec_ref(v___y_1656_);
    lean_dec(v___y_1655_);
    lean_dec_ref(v___y_1654_);
    lean_dec(v___y_1653_);
    lean_dec(v___y_1652_);
    lean_dec_ref(v___y_1651_);
    return v_res_1663_;
}
pub unsafe fn l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(
    mut v_00_u03b1_1664_: *mut LeanObject,
    mut v_x_1665_: *mut LeanObject,
    mut v___y_1666_: *mut LeanObject,
    mut v___y_1667_: *mut LeanObject,
    mut v___y_1668_: *mut LeanObject,
    mut v___y_1669_: *mut LeanObject,
    mut v___y_1670_: *mut LeanObject,
    mut v___y_1671_: *mut LeanObject,
    mut v___y_1672_: *mut LeanObject,
    mut v___y_1673_: *mut LeanObject,
    mut v___y_1674_: *mut LeanObject,
    mut v___y_1675_: *mut LeanObject,
    mut v___y_1676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    v___x_1678_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v_x_1665_, v___y_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
    return v___x_1678_;
}
pub unsafe fn l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___boxed(
    mut v_00_u03b1_1679_: *mut LeanObject,
    mut v_x_1680_: *mut LeanObject,
    mut v___y_1681_: *mut LeanObject,
    mut v___y_1682_: *mut LeanObject,
    mut v___y_1683_: *mut LeanObject,
    mut v___y_1684_: *mut LeanObject,
    mut v___y_1685_: *mut LeanObject,
    mut v___y_1686_: *mut LeanObject,
    mut v___y_1687_: *mut LeanObject,
    mut v___y_1688_: *mut LeanObject,
    mut v___y_1689_: *mut LeanObject,
    mut v___y_1690_: *mut LeanObject,
    mut v___y_1691_: *mut LeanObject,
    mut v___y_1692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1693_: *mut LeanObject = core::ptr::null_mut();
    v_res_1693_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0(v_00_u03b1_1679_, v_x_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_);
    lean_dec(v___y_1691_);
    lean_dec_ref(v___y_1690_);
    lean_dec(v___y_1689_);
    lean_dec_ref(v___y_1688_);
    lean_dec(v___y_1687_);
    lean_dec_ref(v___y_1686_);
    lean_dec(v___y_1685_);
    lean_dec_ref(v___y_1684_);
    lean_dec(v___y_1683_);
    lean_dec(v___y_1682_);
    lean_dec_ref(v___y_1681_);
    return v_res_1693_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(
    mut v_a_1694_: *mut LeanObject,
    mut v___x_1695_: *mut LeanObject,
    mut v_rule_1696_: *mut LeanObject,
    mut v___x_1697_: u8,
    mut v_debug_1698_: u8,
    mut v___y_1699_: *mut LeanObject,
    mut v___y_1700_: *mut LeanObject,
    mut v___y_1701_: *mut LeanObject,
    mut v___y_1702_: *mut LeanObject,
    mut v___y_1703_: *mut LeanObject,
    mut v___y_1704_: *mut LeanObject,
    mut v___y_1705_: *mut LeanObject,
    mut v___y_1706_: *mut LeanObject,
    mut v___y_1707_: *mut LeanObject,
    mut v___y_1708_: *mut LeanObject,
    mut v___y_1709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1718_: u8 = 0;
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1727_: u8 = 0;
    let mut v_a_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1731_: u8 = 0;
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1735_: u8 = 0;
    let mut v_a_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1739_: u8 = 0;
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1743_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1711_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v_a_1694_,
                    v___x_1695_,
                    v___y_1706_,
                    v___y_1707_,
                    v___y_1708_,
                    v___y_1709_,
                );
                if lean_obj_tag(v___x_1711_) == 0 {
                    v_a_1712_ = lean_ctor_get(v___x_1711_, 0);
                    lean_inc(v_a_1712_);
                    lean_dec_ref_known(v___x_1711_, 1);
                    v___x_1713_ = l_Lean_Expr_mvarId_x21(v_a_1712_);
                    lean_dec(v_a_1712_);
                    v___x_1714_ = l_Lean_Meta_Sym_BackwardRule_apply(
                        v___x_1713_,
                        v_rule_1696_,
                        v___y_1704_,
                        v___y_1705_,
                        v___y_1706_,
                        v___y_1707_,
                        v___y_1708_,
                        v___y_1709_,
                    );
                    if lean_obj_tag(v___x_1714_) == 0 {
                        v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
                        v_isSharedCheck_1727_ = (!lean_is_exclusive(v___x_1714_)) as u8;
                        if v_isSharedCheck_1727_ == 0 {
                            v___x_1717_ = v___x_1714_;
                            v_isShared_1718_ = v_isSharedCheck_1727_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1715_);
                            lean_dec(v___x_1714_);
                            v___x_1717_ = lean_box(0);
                            v_isShared_1718_ = v_isSharedCheck_1727_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1728_ = lean_ctor_get(v___x_1714_, 0);
                        v_isSharedCheck_1735_ = (!lean_is_exclusive(v___x_1714_)) as u8;
                        if v_isSharedCheck_1735_ == 0 {
                            v___x_1730_ = v___x_1714_;
                            v_isShared_1731_ = v_isSharedCheck_1735_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_1728_);
                            lean_dec(v___x_1714_);
                            v___x_1730_ = lean_box(0);
                            v_isShared_1731_ = v_isSharedCheck_1735_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_rule_1696_);
                    v_a_1736_ = lean_ctor_get(v___x_1711_, 0);
                    v_isSharedCheck_1743_ = (!lean_is_exclusive(v___x_1711_)) as u8;
                    if v_isSharedCheck_1743_ == 0 {
                        v___x_1738_ = v___x_1711_;
                        v_isShared_1739_ = v_isSharedCheck_1743_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_1736_);
                        lean_dec(v___x_1711_);
                        v___x_1738_ = lean_box(0);
                        v_isShared_1739_ = v_isSharedCheck_1743_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1715_) == 0 {
                    v___x_1719_ = lean_box((v___x_1697_) as usize);
                    if v_isShared_1718_ == 0 {
                        lean_ctor_set(v___x_1717_, 0, v___x_1719_);
                        v___x_1721_ = v___x_1717_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1722_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1722_, 0, v___x_1719_);
                        v___x_1721_ = v_reuseFailAlloc_1722_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_a_1715_, 1);
                    v___x_1723_ = lean_box((v_debug_1698_) as usize);
                    if v_isShared_1718_ == 0 {
                        lean_ctor_set(v___x_1717_, 0, v___x_1723_);
                        v___x_1725_ = v___x_1717_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1726_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1723_);
                        v___x_1725_ = v_reuseFailAlloc_1726_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1721_;
            }
            3 => {
                return v___x_1725_;
            }
            4 => {
                if v_isShared_1731_ == 0 {
                    v___x_1733_ = v___x_1730_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
                    v___x_1733_ = v_reuseFailAlloc_1734_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1733_;
            }
            6 => {
                if v_isShared_1739_ == 0 {
                    v___x_1741_ = v___x_1738_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1742_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1742_, 0, v_a_1736_);
                    v___x_1741_ = v_reuseFailAlloc_1742_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1741_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1744_: *mut LeanObject = *_args.add(0);
    let mut v___x_1745_: *mut LeanObject = *_args.add(1);
    let mut v_rule_1746_: *mut LeanObject = *_args.add(2);
    let mut v___x_1747_: *mut LeanObject = *_args.add(3);
    let mut v_debug_1748_: *mut LeanObject = *_args.add(4);
    let mut v___y_1749_: *mut LeanObject = *_args.add(5);
    let mut v___y_1750_: *mut LeanObject = *_args.add(6);
    let mut v___y_1751_: *mut LeanObject = *_args.add(7);
    let mut v___y_1752_: *mut LeanObject = *_args.add(8);
    let mut v___y_1753_: *mut LeanObject = *_args.add(9);
    let mut v___y_1754_: *mut LeanObject = *_args.add(10);
    let mut v___y_1755_: *mut LeanObject = *_args.add(11);
    let mut v___y_1756_: *mut LeanObject = *_args.add(12);
    let mut v___y_1757_: *mut LeanObject = *_args.add(13);
    let mut v___y_1758_: *mut LeanObject = *_args.add(14);
    let mut v___y_1759_: *mut LeanObject = *_args.add(15);
    let mut v___y_1760_: *mut LeanObject = *_args.add(16);
    let mut v___x_43892__boxed_1761_: u8 = 0;
    let mut v_debug_boxed_1762_: u8 = 0;
    let mut v_res_1763_: *mut LeanObject = core::ptr::null_mut();
    v___x_43892__boxed_1761_ = (lean_unbox(v___x_1747_) as u8);
    v_debug_boxed_1762_ = (lean_unbox(v_debug_1748_) as u8);
    v_res_1763_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0(
        v_a_1744_,
        v___x_1745_,
        v_rule_1746_,
        v___x_43892__boxed_1761_,
        v_debug_boxed_1762_,
        v___y_1749_,
        v___y_1750_,
        v___y_1751_,
        v___y_1752_,
        v___y_1753_,
        v___y_1754_,
        v___y_1755_,
        v___y_1756_,
        v___y_1757_,
        v___y_1758_,
        v___y_1759_,
    );
    lean_dec(v___y_1759_);
    lean_dec_ref(v___y_1758_);
    lean_dec(v___y_1757_);
    lean_dec_ref(v___y_1756_);
    lean_dec(v___y_1755_);
    lean_dec_ref(v___y_1754_);
    lean_dec(v___y_1753_);
    lean_dec_ref(v___y_1752_);
    lean_dec(v___y_1751_);
    lean_dec(v___y_1750_);
    lean_dec_ref(v___y_1749_);
    return v_res_1763_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1(
    mut v_msgData_1764_: *mut LeanObject,
    mut v___y_1765_: *mut LeanObject,
    mut v___y_1766_: *mut LeanObject,
    mut v___y_1767_: *mut LeanObject,
    mut v___y_1768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    v___x_1770_ = lean_st_ref_get(v___y_1768_);
    v_env_1771_ = lean_ctor_get(v___x_1770_, 0);
    lean_inc_ref(v_env_1771_);
    lean_dec(v___x_1770_);
    v___x_1772_ = lean_st_ref_get(v___y_1766_);
    v_mctx_1773_ = lean_ctor_get(v___x_1772_, 0);
    lean_inc_ref(v_mctx_1773_);
    lean_dec(v___x_1772_);
    v_lctx_1774_ = lean_ctor_get(v___y_1765_, 2);
    v_options_1775_ = lean_ctor_get(v___y_1767_, 2);
    lean_inc_ref(v_options_1775_);
    lean_inc_ref(v_lctx_1774_);
    v___x_1776_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1776_, 0, v_env_1771_);
    lean_ctor_set(v___x_1776_, 1, v_mctx_1773_);
    lean_ctor_set(v___x_1776_, 2, v_lctx_1774_);
    lean_ctor_set(v___x_1776_, 3, v_options_1775_);
    v___x_1777_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1777_, 0, v___x_1776_);
    lean_ctor_set(v___x_1777_, 1, v_msgData_1764_);
    v___x_1778_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1778_, 0, v___x_1777_);
    return v___x_1778_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1___boxed(
    mut v_msgData_1779_: *mut LeanObject,
    mut v___y_1780_: *mut LeanObject,
    mut v___y_1781_: *mut LeanObject,
    mut v___y_1782_: *mut LeanObject,
    mut v___y_1783_: *mut LeanObject,
    mut v___y_1784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1785_: *mut LeanObject = core::ptr::null_mut();
    v_res_1785_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1(v_msgData_1779_, v___y_1780_, v___y_1781_, v___y_1782_, v___y_1783_);
    lean_dec(v___y_1783_);
    lean_dec_ref(v___y_1782_);
    lean_dec(v___y_1781_);
    lean_dec_ref(v___y_1780_);
    return v_res_1785_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(
    mut v_msg_1786_: *mut LeanObject,
    mut v___y_1787_: *mut LeanObject,
    mut v___y_1788_: *mut LeanObject,
    mut v___y_1789_: *mut LeanObject,
    mut v___y_1790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1797_: u8 = 0;
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1802_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1792_ = lean_ctor_get(v___y_1789_, 5);
                v___x_1793_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1_spec__1(v_msg_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_);
                v_a_1794_ = lean_ctor_get(v___x_1793_, 0);
                v_isSharedCheck_1802_ = (!lean_is_exclusive(v___x_1793_)) as u8;
                if v_isSharedCheck_1802_ == 0 {
                    v___x_1796_ = v___x_1793_;
                    v_isShared_1797_ = v_isSharedCheck_1802_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1794_);
                    lean_dec(v___x_1793_);
                    v___x_1796_ = lean_box(0);
                    v_isShared_1797_ = v_isSharedCheck_1802_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1792_);
                v___x_1798_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1798_, 0, v_ref_1792_);
                lean_ctor_set(v___x_1798_, 1, v_a_1794_);
                if v_isShared_1797_ == 0 {
                    lean_ctor_set_tag(v___x_1796_, 1);
                    lean_ctor_set(v___x_1796_, 0, v___x_1798_);
                    v___x_1800_ = v___x_1796_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1801_, 0, v___x_1798_);
                    v___x_1800_ = v_reuseFailAlloc_1801_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1800_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg___boxed(
    mut v_msg_1803_: *mut LeanObject,
    mut v___y_1804_: *mut LeanObject,
    mut v___y_1805_: *mut LeanObject,
    mut v___y_1806_: *mut LeanObject,
    mut v___y_1807_: *mut LeanObject,
    mut v___y_1808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1809_: *mut LeanObject = core::ptr::null_mut();
    v_res_1809_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v_msg_1803_, v___y_1804_, v___y_1805_, v___y_1806_, v___y_1807_);
    lean_dec(v___y_1807_);
    lean_dec_ref(v___y_1806_);
    lean_dec(v___y_1805_);
    lean_dec_ref(v___y_1804_);
    return v_res_1809_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1()
-> *mut LeanObject {
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    v___x_1811_ =
        l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__0;
    v___x_1812_ = l_Lean_stringToMessageData(v___x_1811_);
    return v___x_1812_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3()
-> *mut LeanObject {
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    v___x_1814_ =
        l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__2;
    v___x_1815_ = l_Lean_stringToMessageData(v___x_1814_);
    return v___x_1815_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5()
-> *mut LeanObject {
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut LeanObject = core::ptr::null_mut();
    v___x_1817_ =
        l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__4;
    v___x_1818_ = l_Lean_stringToMessageData(v___x_1817_);
    return v___x_1818_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7()
-> *mut LeanObject {
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    v___x_1820_ =
        l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__6;
    v___x_1821_ = l_Lean_stringToMessageData(v___x_1820_);
    return v___x_1821_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9()
-> *mut LeanObject {
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    v___x_1823_ =
        l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__8;
    v___x_1824_ = l_Lean_stringToMessageData(v___x_1823_);
    return v___x_1824_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11()
-> *mut LeanObject {
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    v___x_1826_ =
        l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__10;
    v___x_1827_ = l_Lean_stringToMessageData(v___x_1826_);
    return v___x_1827_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(
    mut v_rule_1828_: *mut LeanObject,
    mut v_goal_1829_: *mut LeanObject,
    mut v_ruleDesc_x3f_1830_: *mut LeanObject,
    mut v_a_1831_: *mut LeanObject,
    mut v_a_1832_: *mut LeanObject,
    mut v_a_1833_: *mut LeanObject,
    mut v_a_1834_: *mut LeanObject,
    mut v_a_1835_: *mut LeanObject,
    mut v_a_1836_: *mut LeanObject,
    mut v_a_1837_: *mut LeanObject,
    mut v_a_1838_: *mut LeanObject,
    mut v_a_1839_: *mut LeanObject,
    mut v_a_1840_: *mut LeanObject,
    mut v_a_1841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_debug_1845_: u8 = 0;
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1852_: u8 = 0;
    let mut v___x_1853_: u8 = 0;
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1862_: u8 = 0;
    let mut v___y_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1881_: u8 = 0;
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1885_: u8 = 0;
    let mut v___x_1886_: u8 = 0;
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1899_: u8 = 0;
    let mut v_a_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1903_: u8 = 0;
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1907_: u8 = 0;
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1911_: u8 = 0;
    let mut v_a_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1915_: u8 = 0;
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1919_: u8 = 0;
    let mut v_a_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1923_: u8 = 0;
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1927_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_rule_1828_);
                lean_inc(v_goal_1829_);
                v___x_1843_ = l_Lean_Meta_Sym_BackwardRule_apply(
                    v_goal_1829_,
                    v_rule_1828_,
                    v_a_1836_,
                    v_a_1837_,
                    v_a_1838_,
                    v_a_1839_,
                    v_a_1840_,
                    v_a_1841_,
                );
                if lean_obj_tag(v___x_1843_) == 0 {
                    v_a_1844_ = lean_ctor_get(v___x_1843_, 0);
                    lean_inc(v_a_1844_);
                    if lean_obj_tag(v_a_1844_) == 0 {
                        v_debug_1845_ = lean_ctor_get_uint8(
                            v_a_1831_,
                            (core::mem::size_of::<*mut LeanObject>() * 19 + 3) as u32,
                        );
                        if v_debug_1845_ == 0 {
                            lean_dec(v_ruleDesc_x3f_1830_);
                            lean_dec(v_goal_1829_);
                            lean_dec_ref(v_rule_1828_);
                            return v___x_1843_;
                        } else {
                            lean_dec_ref_known(v___x_1843_, 1);
                            v___x_1846_ = l_Lean_MVarId_getType(
                                v_goal_1829_,
                                v_a_1838_,
                                v_a_1839_,
                                v_a_1840_,
                                v_a_1841_,
                            );
                            if lean_obj_tag(v___x_1846_) == 0 {
                                v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
                                lean_inc_n(v_a_1847_, 2);
                                lean_dec_ref_known(v___x_1846_, 1);
                                v___x_1848_ = l_Lean_Meta_Sym_unfoldReducible(
                                    v_a_1847_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_,
                                );
                                if lean_obj_tag(v___x_1848_) == 0 {
                                    v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
                                    v_isSharedCheck_1911_ = (!lean_is_exclusive(v___x_1848_)) as u8;
                                    if v_isSharedCheck_1911_ == 0 {
                                        v___x_1851_ = v___x_1848_;
                                        v_isShared_1852_ = v_isSharedCheck_1911_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1849_);
                                        lean_dec(v___x_1848_);
                                        v___x_1851_ = lean_box(0);
                                        v_isShared_1852_ = v_isSharedCheck_1911_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_1847_);
                                    lean_dec(v_ruleDesc_x3f_1830_);
                                    lean_dec_ref(v_rule_1828_);
                                    v_a_1912_ = lean_ctor_get(v___x_1848_, 0);
                                    v_isSharedCheck_1919_ = (!lean_is_exclusive(v___x_1848_)) as u8;
                                    if v_isSharedCheck_1919_ == 0 {
                                        v___x_1914_ = v___x_1848_;
                                        v_isShared_1915_ = v_isSharedCheck_1919_;
                                        state = 10;
                                        continue;
                                    } else {
                                        lean_inc(v_a_1912_);
                                        lean_dec(v___x_1848_);
                                        v___x_1914_ = lean_box(0);
                                        v_isShared_1915_ = v_isSharedCheck_1919_;
                                        state = 10;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_ruleDesc_x3f_1830_);
                                lean_dec_ref(v_rule_1828_);
                                v_a_1920_ = lean_ctor_get(v___x_1846_, 0);
                                v_isSharedCheck_1927_ = (!lean_is_exclusive(v___x_1846_)) as u8;
                                if v_isSharedCheck_1927_ == 0 {
                                    v___x_1922_ = v___x_1846_;
                                    v_isShared_1923_ = v_isSharedCheck_1927_;
                                    state = 12;
                                    continue;
                                } else {
                                    lean_inc(v_a_1920_);
                                    lean_dec(v___x_1846_);
                                    v___x_1922_ = lean_box(0);
                                    v_isShared_1923_ = v_isSharedCheck_1927_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_a_1844_, 1);
                        lean_dec(v_ruleDesc_x3f_1830_);
                        lean_dec(v_goal_1829_);
                        lean_dec_ref(v_rule_1828_);
                        return v___x_1843_;
                    }
                } else {
                    lean_dec(v_ruleDesc_x3f_1830_);
                    lean_dec(v_goal_1829_);
                    lean_dec_ref(v_rule_1828_);
                    return v___x_1843_;
                }
            }
            1 => {
                v___x_1853_ = lean_expr_eqv(v_a_1849_, v_a_1847_);
                if v___x_1853_ == 0 {
                    lean_del_object(v___x_1851_);
                    v___x_1854_ = lean_box(0);
                    v___x_1855_ = lean_box((v___x_1853_) as usize);
                    v___x_1856_ = lean_box((v_debug_1845_) as usize);
                    lean_inc_ref(v_rule_1828_);
                    lean_inc(v_a_1849_);
                    v___f_1857_ = lean_alloc_closure(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___lam__0___boxed as *mut core::ffi::c_void, 17, 5);
                    lean_closure_set(v___f_1857_, 0, v_a_1849_);
                    lean_closure_set(v___f_1857_, 1, v___x_1854_);
                    lean_closure_set(v___f_1857_, 2, v_rule_1828_);
                    lean_closure_set(v___f_1857_, 3, v___x_1855_);
                    lean_closure_set(v___f_1857_, 4, v___x_1856_);
                    v___x_1858_ = l_Lean_Meta_withoutModifyingMCtx___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__0___redArg(v___f_1857_, v_a_1831_, v_a_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
                    if lean_obj_tag(v___x_1858_) == 0 {
                        v_a_1859_ = lean_ctor_get(v___x_1858_, 0);
                        v_isSharedCheck_1899_ = (!lean_is_exclusive(v___x_1858_)) as u8;
                        if v_isSharedCheck_1899_ == 0 {
                            v___x_1861_ = v___x_1858_;
                            v_isShared_1862_ = v_isSharedCheck_1899_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1859_);
                            lean_dec(v___x_1858_);
                            v___x_1861_ = lean_box(0);
                            v_isShared_1862_ = v_isSharedCheck_1899_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1849_);
                        lean_dec(v_a_1847_);
                        lean_dec(v_ruleDesc_x3f_1830_);
                        lean_dec_ref(v_rule_1828_);
                        v_a_1900_ = lean_ctor_get(v___x_1858_, 0);
                        v_isSharedCheck_1907_ = (!lean_is_exclusive(v___x_1858_)) as u8;
                        if v_isSharedCheck_1907_ == 0 {
                            v___x_1902_ = v___x_1858_;
                            v_isShared_1903_ = v_isSharedCheck_1907_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_1900_);
                            lean_dec(v___x_1858_);
                            v___x_1902_ = lean_box(0);
                            v_isShared_1903_ = v_isSharedCheck_1907_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_1849_);
                    lean_dec(v_a_1847_);
                    lean_dec(v_ruleDesc_x3f_1830_);
                    lean_dec_ref(v_rule_1828_);
                    if v_isShared_1852_ == 0 {
                        lean_ctor_set(v___x_1851_, 0, v_a_1844_);
                        v___x_1909_ = v___x_1851_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1844_);
                        v___x_1909_ = v_reuseFailAlloc_1910_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1886_ = (lean_unbox(v_a_1859_) as u8);
                lean_dec(v_a_1859_);
                if v___x_1886_ == 0 {
                    lean_dec(v_a_1849_);
                    lean_dec(v_a_1847_);
                    lean_dec(v_ruleDesc_x3f_1830_);
                    lean_dec_ref(v_rule_1828_);
                    if v_isShared_1862_ == 0 {
                        lean_ctor_set(v___x_1861_, 0, v_a_1844_);
                        v___x_1888_ = v___x_1861_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1889_, 0, v_a_1844_);
                        v___x_1888_ = v_reuseFailAlloc_1889_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1861_);
                    if lean_obj_tag(v_ruleDesc_x3f_1830_) == 0 {
                        v_expr_1890_ = lean_ctor_get(v_rule_1828_, 0);
                        lean_inc_ref(v_expr_1890_);
                        lean_dec_ref(v_rule_1828_);
                        v___x_1891_ = l_Lean_Expr_getAppFn(v_expr_1890_);
                        lean_dec_ref(v_expr_1890_);
                        if lean_obj_tag(v___x_1891_) == 4 {
                            v_declName_1892_ = lean_ctor_get(v___x_1891_, 0);
                            lean_inc(v_declName_1892_);
                            lean_dec_ref_known(v___x_1891_, 2);
                            v___x_1893_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9_once), _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__9);
                            v___x_1894_ =
                                l_Lean_MessageData_ofConstName(v_declName_1892_, v___x_1853_);
                            v___x_1895_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1895_, 0, v___x_1893_);
                            lean_ctor_set(v___x_1895_, 1, v___x_1894_);
                            v___x_1896_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v___x_1896_, 0, v___x_1895_);
                            lean_ctor_set(v___x_1896_, 1, v___x_1893_);
                            v___y_1864_ = v___x_1896_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec_ref(v___x_1891_);
                            v___x_1897_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11_once), _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__11);
                            v___y_1864_ = v___x_1897_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_rule_1828_);
                        v_val_1898_ = lean_ctor_get(v_ruleDesc_x3f_1830_, 0);
                        lean_inc(v_val_1898_);
                        lean_dec_ref_known(v_ruleDesc_x3f_1830_, 1);
                        v___y_1864_ = v_val_1898_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1865_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1_once), _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__1);
                v___x_1866_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1866_, 0, v___x_1865_);
                lean_ctor_set(v___x_1866_, 1, v___y_1864_);
                v___x_1867_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3_once), _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__3);
                v___x_1868_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1868_, 0, v___x_1866_);
                lean_ctor_set(v___x_1868_, 1, v___x_1867_);
                v___x_1869_ = l_Lean_indentExpr(v_a_1847_);
                v___x_1870_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1870_, 0, v___x_1868_);
                lean_ctor_set(v___x_1870_, 1, v___x_1869_);
                v___x_1871_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5_once), _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__5);
                v___x_1872_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1872_, 0, v___x_1870_);
                lean_ctor_set(v___x_1872_, 1, v___x_1871_);
                v___x_1873_ = l_Lean_indentExpr(v_a_1849_);
                v___x_1874_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1874_, 0, v___x_1872_);
                lean_ctor_set(v___x_1874_, 1, v___x_1873_);
                v___x_1875_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7_once), _init_l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___closed__7);
                v___x_1876_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1876_, 0, v___x_1874_);
                lean_ctor_set(v___x_1876_, 1, v___x_1875_);
                v___x_1877_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_1876_, v_a_1838_, v_a_1839_, v_a_1840_, v_a_1841_);
                v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
                v_isSharedCheck_1885_ = (!lean_is_exclusive(v___x_1877_)) as u8;
                if v_isSharedCheck_1885_ == 0 {
                    v___x_1880_ = v___x_1877_;
                    v_isShared_1881_ = v_isSharedCheck_1885_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_a_1878_);
                    lean_dec(v___x_1877_);
                    v___x_1880_ = lean_box(0);
                    v_isShared_1881_ = v_isSharedCheck_1885_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1881_ == 0 {
                    v___x_1883_ = v___x_1880_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1884_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1884_, 0, v_a_1878_);
                    v___x_1883_ = v_reuseFailAlloc_1884_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1883_;
            }
            6 => {
                return v___x_1888_;
            }
            7 => {
                if v_isShared_1903_ == 0 {
                    v___x_1905_ = v___x_1902_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_a_1900_);
                    v___x_1905_ = v_reuseFailAlloc_1906_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1905_;
            }
            9 => {
                return v___x_1909_;
            }
            10 => {
                if v_isShared_1915_ == 0 {
                    v___x_1917_ = v___x_1914_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
                    v___x_1917_ = v_reuseFailAlloc_1918_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1917_;
            }
            12 => {
                if v_isShared_1923_ == 0 {
                    v___x_1925_ = v___x_1922_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
                    v___x_1925_ = v_reuseFailAlloc_1926_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1925_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked___boxed(
    mut v_rule_1928_: *mut LeanObject,
    mut v_goal_1929_: *mut LeanObject,
    mut v_ruleDesc_x3f_1930_: *mut LeanObject,
    mut v_a_1931_: *mut LeanObject,
    mut v_a_1932_: *mut LeanObject,
    mut v_a_1933_: *mut LeanObject,
    mut v_a_1934_: *mut LeanObject,
    mut v_a_1935_: *mut LeanObject,
    mut v_a_1936_: *mut LeanObject,
    mut v_a_1937_: *mut LeanObject,
    mut v_a_1938_: *mut LeanObject,
    mut v_a_1939_: *mut LeanObject,
    mut v_a_1940_: *mut LeanObject,
    mut v_a_1941_: *mut LeanObject,
    mut v_a_1942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1943_: *mut LeanObject = core::ptr::null_mut();
    v_res_1943_ = l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(
        v_rule_1928_,
        v_goal_1929_,
        v_ruleDesc_x3f_1930_,
        v_a_1931_,
        v_a_1932_,
        v_a_1933_,
        v_a_1934_,
        v_a_1935_,
        v_a_1936_,
        v_a_1937_,
        v_a_1938_,
        v_a_1939_,
        v_a_1940_,
        v_a_1941_,
    );
    lean_dec(v_a_1941_);
    lean_dec_ref(v_a_1940_);
    lean_dec(v_a_1939_);
    lean_dec_ref(v_a_1938_);
    lean_dec(v_a_1937_);
    lean_dec_ref(v_a_1936_);
    lean_dec(v_a_1935_);
    lean_dec_ref(v_a_1934_);
    lean_dec(v_a_1933_);
    lean_dec(v_a_1932_);
    lean_dec_ref(v_a_1931_);
    return v_res_1943_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(
    mut v_00_u03b1_1944_: *mut LeanObject,
    mut v_msg_1945_: *mut LeanObject,
    mut v___y_1946_: *mut LeanObject,
    mut v___y_1947_: *mut LeanObject,
    mut v___y_1948_: *mut LeanObject,
    mut v___y_1949_: *mut LeanObject,
    mut v___y_1950_: *mut LeanObject,
    mut v___y_1951_: *mut LeanObject,
    mut v___y_1952_: *mut LeanObject,
    mut v___y_1953_: *mut LeanObject,
    mut v___y_1954_: *mut LeanObject,
    mut v___y_1955_: *mut LeanObject,
    mut v___y_1956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    v___x_1958_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v_msg_1945_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
    return v___x_1958_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___boxed(
    mut v_00_u03b1_1959_: *mut LeanObject,
    mut v_msg_1960_: *mut LeanObject,
    mut v___y_1961_: *mut LeanObject,
    mut v___y_1962_: *mut LeanObject,
    mut v___y_1963_: *mut LeanObject,
    mut v___y_1964_: *mut LeanObject,
    mut v___y_1965_: *mut LeanObject,
    mut v___y_1966_: *mut LeanObject,
    mut v___y_1967_: *mut LeanObject,
    mut v___y_1968_: *mut LeanObject,
    mut v___y_1969_: *mut LeanObject,
    mut v___y_1970_: *mut LeanObject,
    mut v___y_1971_: *mut LeanObject,
    mut v___y_1972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1973_: *mut LeanObject = core::ptr::null_mut();
    v_res_1973_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1(v_00_u03b1_1959_, v_msg_1960_, v___y_1961_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
    lean_dec(v___y_1971_);
    lean_dec_ref(v___y_1970_);
    lean_dec(v___y_1969_);
    lean_dec_ref(v___y_1968_);
    lean_dec(v___y_1967_);
    lean_dec_ref(v___y_1966_);
    lean_dec(v___y_1965_);
    lean_dec_ref(v___y_1964_);
    lean_dec(v___y_1963_);
    lean_dec(v___y_1962_);
    lean_dec_ref(v___y_1961_);
    return v_res_1973_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg(
    mut v_mvarId_1978_: *mut LeanObject,
    mut v_a_1979_: *mut LeanObject,
    mut v_a_1980_: *mut LeanObject,
    mut v_a_1981_: *mut LeanObject,
    mut v_a_1982_: *mut LeanObject,
    mut v_a_1983_: *mut LeanObject,
    mut v_a_1984_: *mut LeanObject,
    mut v_a_1985_: *mut LeanObject,
    mut v_a_1986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_hypSimpMethods_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simpState_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_post_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2003_: u8 = 0;
    let mut v_fst_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2008_: u8 = 0;
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_specBackwardRuleCache_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_splitBackwardRuleCache_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invariants_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vcs_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fuel_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inlineHandledInvariants_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_preTacFailed_2016_: u8 = 0;
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2019_: u8 = 0;
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: u8 = 0;
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_e_x27_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2037_: u8 = 0;
    let mut v___x_2038_: u8 = 0;
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2046_: u8 = 0;
    let mut v_a_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2050_: u8 = 0;
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2054_: u8 = 0;
    let mut v_reuseFailAlloc_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2056_: u8 = 0;
    let mut v_unused_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v_isSharedCheck_2059_: u8 = 0;
    let mut v_a_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2063_: u8 = 0;
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2067_: u8 = 0;
    let mut v_a_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2071_: u8 = 0;
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2075_: u8 = 0;
    let mut v___x_2076_: u8 = 0;
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_hypSimpMethods_1988_ = lean_ctor_get(v_a_1979_, 16);
                if lean_obj_tag(v_hypSimpMethods_1988_) == 1 {
                    v_val_1989_ = lean_ctor_get(v_hypSimpMethods_1988_, 0);
                    lean_inc(v_mvarId_1978_);
                    v___x_1990_ = l_Lean_MVarId_getType(
                        v_mvarId_1978_,
                        v_a_1983_,
                        v_a_1984_,
                        v_a_1985_,
                        v_a_1986_,
                    );
                    if lean_obj_tag(v___x_1990_) == 0 {
                        v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
                        lean_inc(v_a_1991_);
                        lean_dec_ref_known(v___x_1990_, 1);
                        v___x_1992_ = lean_st_ref_get(v_a_1980_);
                        v_simpState_1993_ = lean_ctor_get(v___x_1992_, 4);
                        lean_inc_ref(v_simpState_1993_);
                        lean_dec(v___x_1992_);
                        v_post_1994_ = lean_ctor_get(v_val_1989_, 1);
                        v___x_1995_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__0;
                        lean_inc_ref(v_post_1994_);
                        v___x_1996_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_1996_, 0, v___x_1995_);
                        lean_ctor_set(v___x_1996_, 1, v_post_1994_);
                        v___x_1997_ = lean_alloc_closure(
                            l_Lean_Meta_Sym_Simp_simp___boxed as *mut core::ffi::c_void,
                            11,
                            1,
                        );
                        lean_closure_set(v___x_1997_, 0, v_a_1991_);
                        v___x_1998_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___closed__1;
                        v___x_1999_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(
                            v___x_1997_,
                            v___x_1996_,
                            v___x_1998_,
                            v_simpState_1993_,
                            v_a_1981_,
                            v_a_1982_,
                            v_a_1983_,
                            v_a_1984_,
                            v_a_1985_,
                            v_a_1986_,
                        );
                        if lean_obj_tag(v___x_1999_) == 0 {
                            v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
                            v_isSharedCheck_2059_ = (!lean_is_exclusive(v___x_1999_)) as u8;
                            if v_isSharedCheck_2059_ == 0 {
                                v___x_2002_ = v___x_1999_;
                                v_isShared_2003_ = v_isSharedCheck_2059_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2000_);
                                lean_dec(v___x_1999_);
                                v___x_2002_ = lean_box(0);
                                v_isShared_2003_ = v_isSharedCheck_2059_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_mvarId_1978_);
                            v_a_2060_ = lean_ctor_get(v___x_1999_, 0);
                            v_isSharedCheck_2067_ = (!lean_is_exclusive(v___x_1999_)) as u8;
                            if v_isSharedCheck_2067_ == 0 {
                                v___x_2062_ = v___x_1999_;
                                v_isShared_2063_ = v_isSharedCheck_2067_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_2060_);
                                lean_dec(v___x_1999_);
                                v___x_2062_ = lean_box(0);
                                v_isShared_2063_ = v_isSharedCheck_2067_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_mvarId_1978_);
                        v_a_2068_ = lean_ctor_get(v___x_1990_, 0);
                        v_isSharedCheck_2075_ = (!lean_is_exclusive(v___x_1990_)) as u8;
                        if v_isSharedCheck_2075_ == 0 {
                            v___x_2070_ = v___x_1990_;
                            v_isShared_2071_ = v_isSharedCheck_2075_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_2068_);
                            lean_dec(v___x_1990_);
                            v___x_2070_ = lean_box(0);
                            v_isShared_2071_ = v_isSharedCheck_2075_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    v___x_2076_ = 0;
                    v___x_2077_ = lean_box((v___x_2076_) as usize);
                    v___x_2078_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2078_, 0, v_mvarId_1978_);
                    lean_ctor_set(v___x_2078_, 1, v___x_2077_);
                    v___x_2079_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2079_, 0, v___x_2078_);
                    return v___x_2079_;
                }
            }
            1 => {
                v_fst_2004_ = lean_ctor_get(v_a_2000_, 0);
                v_snd_2005_ = lean_ctor_get(v_a_2000_, 1);
                v_isSharedCheck_2058_ = (!lean_is_exclusive(v_a_2000_)) as u8;
                if v_isSharedCheck_2058_ == 0 {
                    v___x_2007_ = v_a_2000_;
                    v_isShared_2008_ = v_isSharedCheck_2058_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snd_2005_);
                    lean_inc(v_fst_2004_);
                    lean_dec(v_a_2000_);
                    v___x_2007_ = lean_box(0);
                    v_isShared_2008_ = v_isSharedCheck_2058_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2009_ = lean_st_ref_take(v_a_1980_);
                v_specBackwardRuleCache_2010_ = lean_ctor_get(v___x_2009_, 0);
                v_splitBackwardRuleCache_2011_ = lean_ctor_get(v___x_2009_, 1);
                v_invariants_2012_ = lean_ctor_get(v___x_2009_, 2);
                v_vcs_2013_ = lean_ctor_get(v___x_2009_, 3);
                v_fuel_2014_ = lean_ctor_get(v___x_2009_, 5);
                v_inlineHandledInvariants_2015_ = lean_ctor_get(v___x_2009_, 6);
                v_preTacFailed_2016_ = lean_ctor_get_uint8(
                    v___x_2009_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_isSharedCheck_2056_ = (!lean_is_exclusive(v___x_2009_)) as u8;
                if v_isSharedCheck_2056_ == 0 {
                    v_unused_2057_ = lean_ctor_get(v___x_2009_, 4);
                    lean_dec(v_unused_2057_);
                    v___x_2018_ = v___x_2009_;
                    v_isShared_2019_ = v_isSharedCheck_2056_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_inlineHandledInvariants_2015_);
                    lean_inc(v_fuel_2014_);
                    lean_inc(v_vcs_2013_);
                    lean_inc(v_invariants_2012_);
                    lean_inc(v_splitBackwardRuleCache_2011_);
                    lean_inc(v_specBackwardRuleCache_2010_);
                    lean_dec(v___x_2009_);
                    v___x_2018_ = lean_box(0);
                    v_isShared_2019_ = v_isSharedCheck_2056_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2019_ == 0 {
                    lean_ctor_set(v___x_2018_, 4, v_snd_2005_);
                    v___x_2021_ = v___x_2018_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_specBackwardRuleCache_2010_);
                    lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_splitBackwardRuleCache_2011_);
                    lean_ctor_set(v_reuseFailAlloc_2055_, 2, v_invariants_2012_);
                    lean_ctor_set(v_reuseFailAlloc_2055_, 3, v_vcs_2013_);
                    lean_ctor_set(v_reuseFailAlloc_2055_, 4, v_snd_2005_);
                    lean_ctor_set(v_reuseFailAlloc_2055_, 5, v_fuel_2014_);
                    lean_ctor_set(v_reuseFailAlloc_2055_, 6, v_inlineHandledInvariants_2015_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2055_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v_preTacFailed_2016_,
                    );
                    v___x_2021_ = v_reuseFailAlloc_2055_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2022_ = lean_st_ref_set(v_a_1980_, v___x_2021_);
                if lean_obj_tag(v_fst_2004_) == 0 {
                    lean_dec_ref_known(v_fst_2004_, 0);
                    v___x_2023_ = 0;
                    v___x_2024_ = lean_box((v___x_2023_) as usize);
                    if v_isShared_2008_ == 0 {
                        lean_ctor_set(v___x_2007_, 1, v___x_2024_);
                        lean_ctor_set(v___x_2007_, 0, v_mvarId_1978_);
                        v___x_2026_ = v___x_2007_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_mvarId_1978_);
                        lean_ctor_set(v_reuseFailAlloc_2030_, 1, v___x_2024_);
                        v___x_2026_ = v_reuseFailAlloc_2030_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2002_);
                    v_e_x27_2031_ = lean_ctor_get(v_fst_2004_, 0);
                    lean_inc_ref(v_e_x27_2031_);
                    v_proof_2032_ = lean_ctor_get(v_fst_2004_, 1);
                    lean_inc_ref(v_proof_2032_);
                    lean_dec_ref_known(v_fst_2004_, 2);
                    v___x_2033_ = l_Lean_MVarId_replaceTargetEq(
                        v_mvarId_1978_,
                        v_e_x27_2031_,
                        v_proof_2032_,
                        v_a_1983_,
                        v_a_1984_,
                        v_a_1985_,
                        v_a_1986_,
                    );
                    if lean_obj_tag(v___x_2033_) == 0 {
                        v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
                        v_isSharedCheck_2046_ = (!lean_is_exclusive(v___x_2033_)) as u8;
                        if v_isSharedCheck_2046_ == 0 {
                            v___x_2036_ = v___x_2033_;
                            v_isShared_2037_ = v_isSharedCheck_2046_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_2034_);
                            lean_dec(v___x_2033_);
                            v___x_2036_ = lean_box(0);
                            v_isShared_2037_ = v_isSharedCheck_2046_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2007_);
                        v_a_2047_ = lean_ctor_get(v___x_2033_, 0);
                        v_isSharedCheck_2054_ = (!lean_is_exclusive(v___x_2033_)) as u8;
                        if v_isSharedCheck_2054_ == 0 {
                            v___x_2049_ = v___x_2033_;
                            v_isShared_2050_ = v_isSharedCheck_2054_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_2047_);
                            lean_dec(v___x_2033_);
                            v___x_2049_ = lean_box(0);
                            v_isShared_2050_ = v_isSharedCheck_2054_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            5 => {
                if v_isShared_2003_ == 0 {
                    lean_ctor_set(v___x_2002_, 0, v___x_2026_);
                    v___x_2028_ = v___x_2002_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2029_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2029_, 0, v___x_2026_);
                    v___x_2028_ = v_reuseFailAlloc_2029_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2028_;
            }
            7 => {
                v___x_2038_ = 1;
                v___x_2039_ = lean_box((v___x_2038_) as usize);
                if v_isShared_2008_ == 0 {
                    lean_ctor_set(v___x_2007_, 1, v___x_2039_);
                    lean_ctor_set(v___x_2007_, 0, v_a_2034_);
                    v___x_2041_ = v___x_2007_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2034_);
                    lean_ctor_set(v_reuseFailAlloc_2045_, 1, v___x_2039_);
                    v___x_2041_ = v_reuseFailAlloc_2045_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2037_ == 0 {
                    lean_ctor_set(v___x_2036_, 0, v___x_2041_);
                    v___x_2043_ = v___x_2036_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2041_);
                    v___x_2043_ = v_reuseFailAlloc_2044_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2043_;
            }
            10 => {
                if v_isShared_2050_ == 0 {
                    v___x_2052_ = v___x_2049_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
                    v___x_2052_ = v_reuseFailAlloc_2053_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2052_;
            }
            12 => {
                if v_isShared_2063_ == 0 {
                    v___x_2065_ = v___x_2062_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
                    v___x_2065_ = v_reuseFailAlloc_2066_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2065_;
            }
            14 => {
                if v_isShared_2071_ == 0 {
                    v___x_2073_ = v___x_2070_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
                    v___x_2073_ = v_reuseFailAlloc_2074_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2073_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg___boxed(
    mut v_mvarId_2080_: *mut LeanObject,
    mut v_a_2081_: *mut LeanObject,
    mut v_a_2082_: *mut LeanObject,
    mut v_a_2083_: *mut LeanObject,
    mut v_a_2084_: *mut LeanObject,
    mut v_a_2085_: *mut LeanObject,
    mut v_a_2086_: *mut LeanObject,
    mut v_a_2087_: *mut LeanObject,
    mut v_a_2088_: *mut LeanObject,
    mut v_a_2089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2090_: *mut LeanObject = core::ptr::null_mut();
    v_res_2090_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg(
        v_mvarId_2080_,
        v_a_2081_,
        v_a_2082_,
        v_a_2083_,
        v_a_2084_,
        v_a_2085_,
        v_a_2086_,
        v_a_2087_,
        v_a_2088_,
    );
    lean_dec(v_a_2088_);
    lean_dec_ref(v_a_2087_);
    lean_dec(v_a_2086_);
    lean_dec_ref(v_a_2085_);
    lean_dec(v_a_2084_);
    lean_dec_ref(v_a_2083_);
    lean_dec(v_a_2082_);
    lean_dec_ref(v_a_2081_);
    return v_res_2090_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope(
    mut v_mvarId_2091_: *mut LeanObject,
    mut v_a_2092_: *mut LeanObject,
    mut v_a_2093_: *mut LeanObject,
    mut v_a_2094_: *mut LeanObject,
    mut v_a_2095_: *mut LeanObject,
    mut v_a_2096_: *mut LeanObject,
    mut v_a_2097_: *mut LeanObject,
    mut v_a_2098_: *mut LeanObject,
    mut v_a_2099_: *mut LeanObject,
    mut v_a_2100_: *mut LeanObject,
    mut v_a_2101_: *mut LeanObject,
    mut v_a_2102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    v___x_2104_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg(
        v_mvarId_2091_,
        v_a_2092_,
        v_a_2093_,
        v_a_2097_,
        v_a_2098_,
        v_a_2099_,
        v_a_2100_,
        v_a_2101_,
        v_a_2102_,
    );
    return v___x_2104_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___boxed(
    mut v_mvarId_2105_: *mut LeanObject,
    mut v_a_2106_: *mut LeanObject,
    mut v_a_2107_: *mut LeanObject,
    mut v_a_2108_: *mut LeanObject,
    mut v_a_2109_: *mut LeanObject,
    mut v_a_2110_: *mut LeanObject,
    mut v_a_2111_: *mut LeanObject,
    mut v_a_2112_: *mut LeanObject,
    mut v_a_2113_: *mut LeanObject,
    mut v_a_2114_: *mut LeanObject,
    mut v_a_2115_: *mut LeanObject,
    mut v_a_2116_: *mut LeanObject,
    mut v_a_2117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2118_: *mut LeanObject = core::ptr::null_mut();
    v_res_2118_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope(
        v_mvarId_2105_,
        v_a_2106_,
        v_a_2107_,
        v_a_2108_,
        v_a_2109_,
        v_a_2110_,
        v_a_2111_,
        v_a_2112_,
        v_a_2113_,
        v_a_2114_,
        v_a_2115_,
        v_a_2116_,
    );
    lean_dec(v_a_2116_);
    lean_dec_ref(v_a_2115_);
    lean_dec(v_a_2114_);
    lean_dec_ref(v_a_2113_);
    lean_dec(v_a_2112_);
    lean_dec_ref(v_a_2111_);
    lean_dec(v_a_2110_);
    lean_dec_ref(v_a_2109_);
    lean_dec(v_a_2108_);
    lean_dec(v_a_2107_);
    lean_dec_ref(v_a_2106_);
    return v_res_2118_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    v___x_2122_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__1;
    v___x_2123_ = l_Lean_stringToMessageData(v___x_2122_);
    return v___x_2123_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    v___x_2125_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__3;
    v___x_2126_ = l_Lean_stringToMessageData(v___x_2125_);
    return v___x_2126_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__6()
-> *mut LeanObject {
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    v___x_2128_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__5;
    v___x_2129_ = l_Lean_stringToMessageData(v___x_2128_);
    return v___x_2129_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(
    mut v_mvarId_2130_: *mut LeanObject,
    mut v_errorMsg_2131_: *mut LeanObject,
    mut v_a_2132_: *mut LeanObject,
    mut v_a_2133_: *mut LeanObject,
    mut v_a_2134_: *mut LeanObject,
    mut v_a_2135_: *mut LeanObject,
    mut v_a_2136_: *mut LeanObject,
    mut v_a_2137_: *mut LeanObject,
    mut v_a_2138_: *mut LeanObject,
    mut v_a_2139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2147_: u8 = 0;
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2153_: u8 = 0;
    let mut v___x_2154_: u8 = 0;
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarId_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2173_: u8 = 0;
    let mut v_a_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2177_: u8 = 0;
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2181_: u8 = 0;
    let mut v_isSharedCheck_2182_: u8 = 0;
    let mut v_a_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2186_: u8 = 0;
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2190_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2141_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_simpTargetTelescope___redArg(
                    v_mvarId_2130_,
                    v_a_2132_,
                    v_a_2133_,
                    v_a_2134_,
                    v_a_2135_,
                    v_a_2136_,
                    v_a_2137_,
                    v_a_2138_,
                    v_a_2139_,
                );
                if lean_obj_tag(v___x_2141_) == 0 {
                    v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
                    lean_inc(v_a_2142_);
                    lean_dec_ref_known(v___x_2141_, 1);
                    v_fst_2143_ = lean_ctor_get(v_a_2142_, 0);
                    v_snd_2144_ = lean_ctor_get(v_a_2142_, 1);
                    v_isSharedCheck_2182_ = (!lean_is_exclusive(v_a_2142_)) as u8;
                    if v_isSharedCheck_2182_ == 0 {
                        v___x_2146_ = v_a_2142_;
                        v_isShared_2147_ = v_isSharedCheck_2182_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2144_);
                        lean_inc(v_fst_2143_);
                        lean_dec(v_a_2142_);
                        v___x_2146_ = lean_box(0);
                        v_isShared_2147_ = v_isSharedCheck_2182_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_errorMsg_2131_);
                    v_a_2183_ = lean_ctor_get(v___x_2141_, 0);
                    v_isSharedCheck_2190_ = (!lean_is_exclusive(v___x_2141_)) as u8;
                    if v_isSharedCheck_2190_ == 0 {
                        v___x_2185_ = v___x_2141_;
                        v_isShared_2186_ = v_isSharedCheck_2190_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2183_);
                        lean_dec(v___x_2141_);
                        v___x_2185_ = lean_box(0);
                        v_isShared_2186_ = v_isSharedCheck_2190_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2148_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__0;
                lean_inc(v_fst_2143_);
                v___x_2149_ = l_Lean_Meta_Sym_intros(
                    v_fst_2143_,
                    v___x_2148_,
                    v_a_2134_,
                    v_a_2135_,
                    v_a_2136_,
                    v_a_2137_,
                    v_a_2138_,
                    v_a_2139_,
                );
                if lean_obj_tag(v___x_2149_) == 0 {
                    v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
                    v_isSharedCheck_2173_ = (!lean_is_exclusive(v___x_2149_)) as u8;
                    if v_isSharedCheck_2173_ == 0 {
                        v___x_2152_ = v___x_2149_;
                        v_isShared_2153_ = v_isSharedCheck_2173_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2150_);
                        lean_dec(v___x_2149_);
                        v___x_2152_ = lean_box(0);
                        v_isShared_2153_ = v_isSharedCheck_2173_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2146_);
                    lean_dec(v_snd_2144_);
                    lean_dec(v_fst_2143_);
                    lean_dec_ref(v_errorMsg_2131_);
                    v_a_2174_ = lean_ctor_get(v___x_2149_, 0);
                    v_isSharedCheck_2181_ = (!lean_is_exclusive(v___x_2149_)) as u8;
                    if v_isSharedCheck_2181_ == 0 {
                        v___x_2176_ = v___x_2149_;
                        v_isShared_2177_ = v_isSharedCheck_2181_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2174_);
                        lean_dec(v___x_2149_);
                        v___x_2176_ = lean_box(0);
                        v_isShared_2177_ = v_isSharedCheck_2181_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_2150_) == 0 {
                    v___x_2154_ = (lean_unbox(v_snd_2144_) as u8);
                    lean_dec(v_snd_2144_);
                    if v___x_2154_ == 0 {
                        lean_del_object(v___x_2152_);
                        v___x_2155_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__2_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__2);
                        v___x_2156_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2156_, 0, v_fst_2143_);
                        if v_isShared_2147_ == 0 {
                            lean_ctor_set_tag(v___x_2146_, 7);
                            lean_ctor_set(v___x_2146_, 1, v___x_2156_);
                            lean_ctor_set(v___x_2146_, 0, v___x_2155_);
                            v___x_2158_ = v___x_2146_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2165_ = lean_alloc_ctor(7, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2155_);
                            lean_ctor_set(v_reuseFailAlloc_2165_, 1, v___x_2156_);
                            v___x_2158_ = v_reuseFailAlloc_2165_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2146_);
                        lean_dec_ref(v_errorMsg_2131_);
                        if v_isShared_2153_ == 0 {
                            lean_ctor_set(v___x_2152_, 0, v_fst_2143_);
                            v___x_2167_ = v___x_2152_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_fst_2143_);
                            v___x_2167_ = v_reuseFailAlloc_2168_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2146_);
                    lean_dec(v_snd_2144_);
                    lean_dec(v_fst_2143_);
                    lean_dec_ref(v_errorMsg_2131_);
                    v_mvarId_2169_ = lean_ctor_get(v_a_2150_, 1);
                    lean_inc(v_mvarId_2169_);
                    lean_dec_ref_known(v_a_2150_, 2);
                    if v_isShared_2153_ == 0 {
                        lean_ctor_set(v___x_2152_, 0, v_mvarId_2169_);
                        v___x_2171_ = v___x_2152_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_mvarId_2169_);
                        v___x_2171_ = v_reuseFailAlloc_2172_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2159_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__4_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__4,
                );
                v___x_2160_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2160_, 0, v___x_2158_);
                lean_ctor_set(v___x_2160_, 1, v___x_2159_);
                v___x_2161_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2161_, 0, v___x_2160_);
                lean_ctor_set(v___x_2161_, 1, v_errorMsg_2131_);
                v___x_2162_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__6
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__6_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__6,
                );
                v___x_2163_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2163_, 0, v___x_2161_);
                lean_ctor_set(v___x_2163_, 1, v___x_2162_);
                v___x_2164_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_2163_, v_a_2136_, v_a_2137_, v_a_2138_, v_a_2139_);
                return v___x_2164_;
            }
            4 => {
                return v___x_2167_;
            }
            5 => {
                return v___x_2171_;
            }
            6 => {
                if v_isShared_2177_ == 0 {
                    v___x_2179_ = v___x_2176_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
                    v___x_2179_ = v_reuseFailAlloc_2180_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2179_;
            }
            8 => {
                if v_isShared_2186_ == 0 {
                    v___x_2188_ = v___x_2185_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
                    v___x_2188_ = v_reuseFailAlloc_2189_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2188_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___boxed(
    mut v_mvarId_2191_: *mut LeanObject,
    mut v_errorMsg_2192_: *mut LeanObject,
    mut v_a_2193_: *mut LeanObject,
    mut v_a_2194_: *mut LeanObject,
    mut v_a_2195_: *mut LeanObject,
    mut v_a_2196_: *mut LeanObject,
    mut v_a_2197_: *mut LeanObject,
    mut v_a_2198_: *mut LeanObject,
    mut v_a_2199_: *mut LeanObject,
    mut v_a_2200_: *mut LeanObject,
    mut v_a_2201_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2202_: *mut LeanObject = core::ptr::null_mut();
    v_res_2202_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(
        v_mvarId_2191_,
        v_errorMsg_2192_,
        v_a_2193_,
        v_a_2194_,
        v_a_2195_,
        v_a_2196_,
        v_a_2197_,
        v_a_2198_,
        v_a_2199_,
        v_a_2200_,
    );
    lean_dec(v_a_2200_);
    lean_dec_ref(v_a_2199_);
    lean_dec(v_a_2198_);
    lean_dec_ref(v_a_2197_);
    lean_dec(v_a_2196_);
    lean_dec_ref(v_a_2195_);
    lean_dec(v_a_2194_);
    lean_dec_ref(v_a_2193_);
    return v_res_2202_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp(
    mut v_mvarId_2203_: *mut LeanObject,
    mut v_errorMsg_2204_: *mut LeanObject,
    mut v_a_2205_: *mut LeanObject,
    mut v_a_2206_: *mut LeanObject,
    mut v_a_2207_: *mut LeanObject,
    mut v_a_2208_: *mut LeanObject,
    mut v_a_2209_: *mut LeanObject,
    mut v_a_2210_: *mut LeanObject,
    mut v_a_2211_: *mut LeanObject,
    mut v_a_2212_: *mut LeanObject,
    mut v_a_2213_: *mut LeanObject,
    mut v_a_2214_: *mut LeanObject,
    mut v_a_2215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    v___x_2217_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg(
        v_mvarId_2203_,
        v_errorMsg_2204_,
        v_a_2205_,
        v_a_2206_,
        v_a_2210_,
        v_a_2211_,
        v_a_2212_,
        v_a_2213_,
        v_a_2214_,
        v_a_2215_,
    );
    return v___x_2217_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___boxed(
    mut v_mvarId_2218_: *mut LeanObject,
    mut v_errorMsg_2219_: *mut LeanObject,
    mut v_a_2220_: *mut LeanObject,
    mut v_a_2221_: *mut LeanObject,
    mut v_a_2222_: *mut LeanObject,
    mut v_a_2223_: *mut LeanObject,
    mut v_a_2224_: *mut LeanObject,
    mut v_a_2225_: *mut LeanObject,
    mut v_a_2226_: *mut LeanObject,
    mut v_a_2227_: *mut LeanObject,
    mut v_a_2228_: *mut LeanObject,
    mut v_a_2229_: *mut LeanObject,
    mut v_a_2230_: *mut LeanObject,
    mut v_a_2231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2232_: *mut LeanObject = core::ptr::null_mut();
    v_res_2232_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp(
        v_mvarId_2218_,
        v_errorMsg_2219_,
        v_a_2220_,
        v_a_2221_,
        v_a_2222_,
        v_a_2223_,
        v_a_2224_,
        v_a_2225_,
        v_a_2226_,
        v_a_2227_,
        v_a_2228_,
        v_a_2229_,
        v_a_2230_,
    );
    lean_dec(v_a_2230_);
    lean_dec_ref(v_a_2229_);
    lean_dec(v_a_2228_);
    lean_dec_ref(v_a_2227_);
    lean_dec(v_a_2226_);
    lean_dec_ref(v_a_2225_);
    lean_dec(v_a_2224_);
    lean_dec_ref(v_a_2223_);
    lean_dec(v_a_2222_);
    lean_dec(v_a_2221_);
    lean_dec_ref(v_a_2220_);
    return v_res_2232_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___redArg(
    mut v_preTac_2233_: *mut LeanObject,
    mut v_goal_2234_: *mut LeanObject,
    mut v_a_2235_: *mut LeanObject,
    mut v_a_2236_: *mut LeanObject,
    mut v_a_2237_: *mut LeanObject,
    mut v_a_2238_: *mut LeanObject,
    mut v_a_2239_: *mut LeanObject,
    mut v_a_2240_: *mut LeanObject,
    mut v_a_2241_: *mut LeanObject,
    mut v_a_2242_: *mut LeanObject,
    mut v_a_2243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2245_: u8 = 0;
    v___x_2245_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_isGrind(v_preTac_2233_);
    if v___x_2245_ == 0 {
        let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
        v___x_2246_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2246_, 0, v_goal_2234_);
        return v___x_2246_;
    } else {
        let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
        v___x_2247_ = lean_box(0);
        v___x_2248_ = l_Lean_Meta_Grind_processHypotheses(
            v_goal_2234_,
            v___x_2247_,
            v_a_2235_,
            v_a_2236_,
            v_a_2237_,
            v_a_2238_,
            v_a_2239_,
            v_a_2240_,
            v_a_2241_,
            v_a_2242_,
            v_a_2243_,
        );
        return v___x_2248_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___redArg___boxed(
    mut v_preTac_2249_: *mut LeanObject,
    mut v_goal_2250_: *mut LeanObject,
    mut v_a_2251_: *mut LeanObject,
    mut v_a_2252_: *mut LeanObject,
    mut v_a_2253_: *mut LeanObject,
    mut v_a_2254_: *mut LeanObject,
    mut v_a_2255_: *mut LeanObject,
    mut v_a_2256_: *mut LeanObject,
    mut v_a_2257_: *mut LeanObject,
    mut v_a_2258_: *mut LeanObject,
    mut v_a_2259_: *mut LeanObject,
    mut v_a_2260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2261_: *mut LeanObject = core::ptr::null_mut();
    v_res_2261_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___redArg(
        v_preTac_2249_,
        v_goal_2250_,
        v_a_2251_,
        v_a_2252_,
        v_a_2253_,
        v_a_2254_,
        v_a_2255_,
        v_a_2256_,
        v_a_2257_,
        v_a_2258_,
        v_a_2259_,
    );
    lean_dec(v_a_2259_);
    lean_dec_ref(v_a_2258_);
    lean_dec(v_a_2257_);
    lean_dec_ref(v_a_2256_);
    lean_dec(v_a_2255_);
    lean_dec_ref(v_a_2254_);
    lean_dec(v_a_2253_);
    lean_dec_ref(v_a_2252_);
    lean_dec(v_a_2251_);
    lean_dec(v_preTac_2249_);
    return v_res_2261_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses(
    mut v_preTac_2262_: *mut LeanObject,
    mut v_goal_2263_: *mut LeanObject,
    mut v_a_2264_: *mut LeanObject,
    mut v_a_2265_: *mut LeanObject,
    mut v_a_2266_: *mut LeanObject,
    mut v_a_2267_: *mut LeanObject,
    mut v_a_2268_: *mut LeanObject,
    mut v_a_2269_: *mut LeanObject,
    mut v_a_2270_: *mut LeanObject,
    mut v_a_2271_: *mut LeanObject,
    mut v_a_2272_: *mut LeanObject,
    mut v_a_2273_: *mut LeanObject,
    mut v_a_2274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    v___x_2276_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___redArg(
        v_preTac_2262_,
        v_goal_2263_,
        v_a_2266_,
        v_a_2267_,
        v_a_2268_,
        v_a_2269_,
        v_a_2270_,
        v_a_2271_,
        v_a_2272_,
        v_a_2273_,
        v_a_2274_,
    );
    return v___x_2276_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses___boxed(
    mut v_preTac_2277_: *mut LeanObject,
    mut v_goal_2278_: *mut LeanObject,
    mut v_a_2279_: *mut LeanObject,
    mut v_a_2280_: *mut LeanObject,
    mut v_a_2281_: *mut LeanObject,
    mut v_a_2282_: *mut LeanObject,
    mut v_a_2283_: *mut LeanObject,
    mut v_a_2284_: *mut LeanObject,
    mut v_a_2285_: *mut LeanObject,
    mut v_a_2286_: *mut LeanObject,
    mut v_a_2287_: *mut LeanObject,
    mut v_a_2288_: *mut LeanObject,
    mut v_a_2289_: *mut LeanObject,
    mut v_a_2290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2291_: *mut LeanObject = core::ptr::null_mut();
    v_res_2291_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_PreTac_processHypotheses(
        v_preTac_2277_,
        v_goal_2278_,
        v_a_2279_,
        v_a_2280_,
        v_a_2281_,
        v_a_2282_,
        v_a_2283_,
        v_a_2284_,
        v_a_2285_,
        v_a_2286_,
        v_a_2287_,
        v_a_2288_,
        v_a_2289_,
    );
    lean_dec(v_a_2289_);
    lean_dec_ref(v_a_2288_);
    lean_dec(v_a_2287_);
    lean_dec_ref(v_a_2286_);
    lean_dec(v_a_2285_);
    lean_dec_ref(v_a_2284_);
    lean_dec(v_a_2283_);
    lean_dec_ref(v_a_2282_);
    lean_dec(v_a_2281_);
    lean_dec(v_a_2280_);
    lean_dec_ref(v_a_2279_);
    lean_dec(v_preTac_2277_);
    return v_res_2291_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0___redArg(
    mut v_e_2292_: *mut LeanObject,
    mut v___y_2293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2295_: u8 = 0;
    let mut v___x_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2309_: u8 = 0;
    let mut v___x_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2315_: u8 = 0;
    let mut v_unused_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2295_ = l_Lean_Expr_hasMVar(v_e_2292_);
                if v___x_2295_ == 0 {
                    v___x_2296_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2296_, 0, v_e_2292_);
                    return v___x_2296_;
                } else {
                    v___x_2297_ = lean_st_ref_get(v___y_2293_);
                    v_mctx_2298_ = lean_ctor_get(v___x_2297_, 0);
                    lean_inc_ref(v_mctx_2298_);
                    lean_dec(v___x_2297_);
                    v___x_2299_ = l_Lean_instantiateMVarsCore(v_mctx_2298_, v_e_2292_);
                    v_fst_2300_ = lean_ctor_get(v___x_2299_, 0);
                    lean_inc(v_fst_2300_);
                    v_snd_2301_ = lean_ctor_get(v___x_2299_, 1);
                    lean_inc(v_snd_2301_);
                    lean_dec_ref(v___x_2299_);
                    v___x_2302_ = lean_st_ref_take(v___y_2293_);
                    v_cache_2303_ = lean_ctor_get(v___x_2302_, 1);
                    v_zetaDeltaFVarIds_2304_ = lean_ctor_get(v___x_2302_, 2);
                    v_postponed_2305_ = lean_ctor_get(v___x_2302_, 3);
                    v_diag_2306_ = lean_ctor_get(v___x_2302_, 4);
                    v_isSharedCheck_2315_ = (!lean_is_exclusive(v___x_2302_)) as u8;
                    if v_isSharedCheck_2315_ == 0 {
                        v_unused_2316_ = lean_ctor_get(v___x_2302_, 0);
                        lean_dec(v_unused_2316_);
                        v___x_2308_ = v___x_2302_;
                        v_isShared_2309_ = v_isSharedCheck_2315_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_2306_);
                        lean_inc(v_postponed_2305_);
                        lean_inc(v_zetaDeltaFVarIds_2304_);
                        lean_inc(v_cache_2303_);
                        lean_dec(v___x_2302_);
                        v___x_2308_ = lean_box(0);
                        v_isShared_2309_ = v_isSharedCheck_2315_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2309_ == 0 {
                    lean_ctor_set(v___x_2308_, 0, v_snd_2301_);
                    v___x_2311_ = v___x_2308_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_snd_2301_);
                    lean_ctor_set(v_reuseFailAlloc_2314_, 1, v_cache_2303_);
                    lean_ctor_set(v_reuseFailAlloc_2314_, 2, v_zetaDeltaFVarIds_2304_);
                    lean_ctor_set(v_reuseFailAlloc_2314_, 3, v_postponed_2305_);
                    lean_ctor_set(v_reuseFailAlloc_2314_, 4, v_diag_2306_);
                    v___x_2311_ = v_reuseFailAlloc_2314_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2312_ = lean_st_ref_set(v___y_2293_, v___x_2311_);
                v___x_2313_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2313_, 0, v_fst_2300_);
                return v___x_2313_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0___redArg___boxed(
    mut v_e_2317_: *mut LeanObject,
    mut v___y_2318_: *mut LeanObject,
    mut v___y_2319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2320_: *mut LeanObject = core::ptr::null_mut();
    v_res_2320_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0___redArg(v_e_2317_, v___y_2318_);
    lean_dec(v___y_2318_);
    return v_res_2320_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0(
    mut v_e_2321_: *mut LeanObject,
    mut v___y_2322_: *mut LeanObject,
    mut v___y_2323_: *mut LeanObject,
    mut v___y_2324_: *mut LeanObject,
    mut v___y_2325_: *mut LeanObject,
    mut v___y_2326_: *mut LeanObject,
    mut v___y_2327_: *mut LeanObject,
    mut v___y_2328_: *mut LeanObject,
    mut v___y_2329_: *mut LeanObject,
    mut v___y_2330_: *mut LeanObject,
    mut v___y_2331_: *mut LeanObject,
    mut v___y_2332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    v___x_2334_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0___redArg(v_e_2321_, v___y_2330_);
    return v___x_2334_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0___boxed(
    mut v_e_2335_: *mut LeanObject,
    mut v___y_2336_: *mut LeanObject,
    mut v___y_2337_: *mut LeanObject,
    mut v___y_2338_: *mut LeanObject,
    mut v___y_2339_: *mut LeanObject,
    mut v___y_2340_: *mut LeanObject,
    mut v___y_2341_: *mut LeanObject,
    mut v___y_2342_: *mut LeanObject,
    mut v___y_2343_: *mut LeanObject,
    mut v___y_2344_: *mut LeanObject,
    mut v___y_2345_: *mut LeanObject,
    mut v___y_2346_: *mut LeanObject,
    mut v___y_2347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2348_: *mut LeanObject = core::ptr::null_mut();
    v_res_2348_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0(
            v_e_2335_,
            v___y_2336_,
            v___y_2337_,
            v___y_2338_,
            v___y_2339_,
            v___y_2340_,
            v___y_2341_,
            v___y_2342_,
            v___y_2343_,
            v___y_2344_,
            v___y_2345_,
            v___y_2346_,
        );
    lean_dec(v___y_2346_);
    lean_dec_ref(v___y_2345_);
    lean_dec(v___y_2344_);
    lean_dec_ref(v___y_2343_);
    lean_dec(v___y_2342_);
    lean_dec_ref(v___y_2341_);
    lean_dec(v___y_2340_);
    lean_dec_ref(v___y_2339_);
    lean_dec(v___y_2338_);
    lean_dec(v___y_2337_);
    lean_dec_ref(v___y_2336_);
    return v_res_2348_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg___lam__0(
    mut v_x_2349_: *mut LeanObject,
    mut v___y_2350_: *mut LeanObject,
    mut v___y_2351_: *mut LeanObject,
    mut v___y_2352_: *mut LeanObject,
    mut v___y_2353_: *mut LeanObject,
    mut v___y_2354_: *mut LeanObject,
    mut v___y_2355_: *mut LeanObject,
    mut v___y_2356_: *mut LeanObject,
    mut v___y_2357_: *mut LeanObject,
    mut v___y_2358_: *mut LeanObject,
    mut v___y_2359_: *mut LeanObject,
    mut v___y_2360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_2356_);
    lean_inc_ref(v___y_2355_);
    lean_inc(v___y_2354_);
    lean_inc_ref(v___y_2353_);
    lean_inc(v___y_2352_);
    lean_inc(v___y_2351_);
    lean_inc_ref(v___y_2350_);
    v___x_2362_ = lean_apply_12(
        v_x_2349_,
        v___y_2350_,
        v___y_2351_,
        v___y_2352_,
        v___y_2353_,
        v___y_2354_,
        v___y_2355_,
        v___y_2356_,
        v___y_2357_,
        v___y_2358_,
        v___y_2359_,
        v___y_2360_,
        lean_box(0),
    );
    return v___x_2362_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg___lam__0___boxed(
    mut v_x_2363_: *mut LeanObject,
    mut v___y_2364_: *mut LeanObject,
    mut v___y_2365_: *mut LeanObject,
    mut v___y_2366_: *mut LeanObject,
    mut v___y_2367_: *mut LeanObject,
    mut v___y_2368_: *mut LeanObject,
    mut v___y_2369_: *mut LeanObject,
    mut v___y_2370_: *mut LeanObject,
    mut v___y_2371_: *mut LeanObject,
    mut v___y_2372_: *mut LeanObject,
    mut v___y_2373_: *mut LeanObject,
    mut v___y_2374_: *mut LeanObject,
    mut v___y_2375_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2376_: *mut LeanObject = core::ptr::null_mut();
    v_res_2376_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg___lam__0(v_x_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
    lean_dec(v___y_2370_);
    lean_dec_ref(v___y_2369_);
    lean_dec(v___y_2368_);
    lean_dec_ref(v___y_2367_);
    lean_dec(v___y_2366_);
    lean_dec(v___y_2365_);
    lean_dec_ref(v___y_2364_);
    return v_res_2376_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg(
    mut v_mvarId_2377_: *mut LeanObject,
    mut v_x_2378_: *mut LeanObject,
    mut v___y_2379_: *mut LeanObject,
    mut v___y_2380_: *mut LeanObject,
    mut v___y_2381_: *mut LeanObject,
    mut v___y_2382_: *mut LeanObject,
    mut v___y_2383_: *mut LeanObject,
    mut v___y_2384_: *mut LeanObject,
    mut v___y_2385_: *mut LeanObject,
    mut v___y_2386_: *mut LeanObject,
    mut v___y_2387_: *mut LeanObject,
    mut v___y_2388_: *mut LeanObject,
    mut v___y_2389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2396_: u8 = 0;
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2400_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_2385_);
                lean_inc_ref(v___y_2384_);
                lean_inc(v___y_2383_);
                lean_inc_ref(v___y_2382_);
                lean_inc(v___y_2381_);
                lean_inc(v___y_2380_);
                lean_inc_ref(v___y_2379_);
                v___f_2391_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 13, 8);
                lean_closure_set(v___f_2391_, 0, v_x_2378_);
                lean_closure_set(v___f_2391_, 1, v___y_2379_);
                lean_closure_set(v___f_2391_, 2, v___y_2380_);
                lean_closure_set(v___f_2391_, 3, v___y_2381_);
                lean_closure_set(v___f_2391_, 4, v___y_2382_);
                lean_closure_set(v___f_2391_, 5, v___y_2383_);
                lean_closure_set(v___f_2391_, 6, v___y_2384_);
                lean_closure_set(v___f_2391_, 7, v___y_2385_);
                v___x_2392_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_2377_,
                    v___f_2391_,
                    v___y_2386_,
                    v___y_2387_,
                    v___y_2388_,
                    v___y_2389_,
                );
                if lean_obj_tag(v___x_2392_) == 0 {
                    return v___x_2392_;
                } else {
                    v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
                    v_isSharedCheck_2400_ = (!lean_is_exclusive(v___x_2392_)) as u8;
                    if v_isSharedCheck_2400_ == 0 {
                        v___x_2395_ = v___x_2392_;
                        v_isShared_2396_ = v_isSharedCheck_2400_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2393_);
                        lean_dec(v___x_2392_);
                        v___x_2395_ = lean_box(0);
                        v_isShared_2396_ = v_isSharedCheck_2400_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2396_ == 0 {
                    v___x_2398_ = v___x_2395_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2399_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2393_);
                    v___x_2398_ = v_reuseFailAlloc_2399_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2398_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg___boxed(
    mut v_mvarId_2401_: *mut LeanObject,
    mut v_x_2402_: *mut LeanObject,
    mut v___y_2403_: *mut LeanObject,
    mut v___y_2404_: *mut LeanObject,
    mut v___y_2405_: *mut LeanObject,
    mut v___y_2406_: *mut LeanObject,
    mut v___y_2407_: *mut LeanObject,
    mut v___y_2408_: *mut LeanObject,
    mut v___y_2409_: *mut LeanObject,
    mut v___y_2410_: *mut LeanObject,
    mut v___y_2411_: *mut LeanObject,
    mut v___y_2412_: *mut LeanObject,
    mut v___y_2413_: *mut LeanObject,
    mut v___y_2414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2415_: *mut LeanObject = core::ptr::null_mut();
    v_res_2415_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg(v_mvarId_2401_, v_x_2402_, v___y_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_);
    lean_dec(v___y_2413_);
    lean_dec_ref(v___y_2412_);
    lean_dec(v___y_2411_);
    lean_dec_ref(v___y_2410_);
    lean_dec(v___y_2409_);
    lean_dec_ref(v___y_2408_);
    lean_dec(v___y_2407_);
    lean_dec_ref(v___y_2406_);
    lean_dec(v___y_2405_);
    lean_dec(v___y_2404_);
    lean_dec_ref(v___y_2403_);
    return v_res_2415_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2(
    mut v_00_u03b1_2416_: *mut LeanObject,
    mut v_mvarId_2417_: *mut LeanObject,
    mut v_x_2418_: *mut LeanObject,
    mut v___y_2419_: *mut LeanObject,
    mut v___y_2420_: *mut LeanObject,
    mut v___y_2421_: *mut LeanObject,
    mut v___y_2422_: *mut LeanObject,
    mut v___y_2423_: *mut LeanObject,
    mut v___y_2424_: *mut LeanObject,
    mut v___y_2425_: *mut LeanObject,
    mut v___y_2426_: *mut LeanObject,
    mut v___y_2427_: *mut LeanObject,
    mut v___y_2428_: *mut LeanObject,
    mut v___y_2429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    v___x_2431_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg(v_mvarId_2417_, v_x_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
    return v___x_2431_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___boxed(
    mut v_00_u03b1_2432_: *mut LeanObject,
    mut v_mvarId_2433_: *mut LeanObject,
    mut v_x_2434_: *mut LeanObject,
    mut v___y_2435_: *mut LeanObject,
    mut v___y_2436_: *mut LeanObject,
    mut v___y_2437_: *mut LeanObject,
    mut v___y_2438_: *mut LeanObject,
    mut v___y_2439_: *mut LeanObject,
    mut v___y_2440_: *mut LeanObject,
    mut v___y_2441_: *mut LeanObject,
    mut v___y_2442_: *mut LeanObject,
    mut v___y_2443_: *mut LeanObject,
    mut v___y_2444_: *mut LeanObject,
    mut v___y_2445_: *mut LeanObject,
    mut v___y_2446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2447_: *mut LeanObject = core::ptr::null_mut();
    v_res_2447_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2(
            v_00_u03b1_2432_,
            v_mvarId_2433_,
            v_x_2434_,
            v___y_2435_,
            v___y_2436_,
            v___y_2437_,
            v___y_2438_,
            v___y_2439_,
            v___y_2440_,
            v___y_2441_,
            v___y_2442_,
            v___y_2443_,
            v___y_2444_,
            v___y_2445_,
        );
    lean_dec(v___y_2445_);
    lean_dec_ref(v___y_2444_);
    lean_dec(v___y_2443_);
    lean_dec_ref(v___y_2442_);
    lean_dec(v___y_2441_);
    lean_dec_ref(v___y_2440_);
    lean_dec(v___y_2439_);
    lean_dec_ref(v___y_2438_);
    lean_dec(v___y_2437_);
    lean_dec(v___y_2436_);
    lean_dec_ref(v___y_2435_);
    return v_res_2447_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_2448_: *mut LeanObject,
    mut v_x_2449_: *mut LeanObject,
    mut v_x_2450_: *mut LeanObject,
    mut v_x_2451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2456_: u8 = 0;
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: u8 = 0;
    let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: u8 = 0;
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2477_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2452_ = lean_ctor_get(v_x_2448_, 0);
                v_vs_2453_ = lean_ctor_get(v_x_2448_, 1);
                v_isSharedCheck_2477_ = (!lean_is_exclusive(v_x_2448_)) as u8;
                if v_isSharedCheck_2477_ == 0 {
                    v___x_2455_ = v_x_2448_;
                    v_isShared_2456_ = v_isSharedCheck_2477_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_2453_);
                    lean_inc(v_ks_2452_);
                    lean_dec(v_x_2448_);
                    v___x_2455_ = lean_box(0);
                    v_isShared_2456_ = v_isSharedCheck_2477_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2457_ = lean_array_get_size(v_ks_2452_);
                v___x_2458_ = lean_nat_dec_lt(v_x_2449_, v___x_2457_);
                if v___x_2458_ == 0 {
                    lean_dec(v_x_2449_);
                    v___x_2459_ = lean_array_push(v_ks_2452_, v_x_2450_);
                    v___x_2460_ = lean_array_push(v_vs_2453_, v_x_2451_);
                    if v_isShared_2456_ == 0 {
                        lean_ctor_set(v___x_2455_, 1, v___x_2460_);
                        lean_ctor_set(v___x_2455_, 0, v___x_2459_);
                        v___x_2462_ = v___x_2455_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2459_);
                        lean_ctor_set(v_reuseFailAlloc_2463_, 1, v___x_2460_);
                        v___x_2462_ = v_reuseFailAlloc_2463_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2464_ = lean_array_fget_borrowed(v_ks_2452_, v_x_2449_);
                    v___x_2465_ = l_Lean_instBEqMVarId_beq(v_x_2450_, v_k_x27_2464_);
                    if v___x_2465_ == 0 {
                        if v_isShared_2456_ == 0 {
                            v___x_2467_ = v___x_2455_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_ks_2452_);
                            lean_ctor_set(v_reuseFailAlloc_2471_, 1, v_vs_2453_);
                            v___x_2467_ = v_reuseFailAlloc_2471_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2472_ = lean_array_fset(v_ks_2452_, v_x_2449_, v_x_2450_);
                        v___x_2473_ = lean_array_fset(v_vs_2453_, v_x_2449_, v_x_2451_);
                        lean_dec(v_x_2449_);
                        if v_isShared_2456_ == 0 {
                            lean_ctor_set(v___x_2455_, 1, v___x_2473_);
                            lean_ctor_set(v___x_2455_, 0, v___x_2472_);
                            v___x_2475_ = v___x_2455_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2476_, 0, v___x_2472_);
                            lean_ctor_set(v_reuseFailAlloc_2476_, 1, v___x_2473_);
                            v___x_2475_ = v_reuseFailAlloc_2476_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2462_;
            }
            3 => {
                v___x_2468_ = lean_unsigned_to_nat(1);
                v___x_2469_ = lean_nat_add(v_x_2449_, v___x_2468_);
                lean_dec(v_x_2449_);
                v_x_2448_ = v___x_2467_;
                v_x_2449_ = v___x_2469_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2475_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4___redArg(
    mut v_n_2478_: *mut LeanObject,
    mut v_k_2479_: *mut LeanObject,
    mut v_v_2480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    v___x_2481_ = lean_unsigned_to_nat(0);
    v___x_2482_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_n_2478_, v___x_2481_, v_k_2479_, v_v_2480_);
    return v___x_2482_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__0()
-> usize {
    let mut v___x_2483_: usize = 0;
    let mut v___x_2484_: usize = 0;
    let mut v___x_2485_: usize = 0;
    v___x_2483_ = 5usize;
    v___x_2484_ = 1usize;
    v___x_2485_ = lean_usize_shift_left(v___x_2484_, v___x_2483_);
    return v___x_2485_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__1()
-> usize {
    let mut v___x_2486_: usize = 0;
    let mut v___x_2487_: usize = 0;
    let mut v___x_2488_: usize = 0;
    v___x_2486_ = 1usize;
    v___x_2487_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__0);
    v___x_2488_ = lean_usize_sub(v___x_2487_, v___x_2486_);
    return v___x_2488_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    v___x_2489_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2489_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg(
    mut v_x_2490_: *mut LeanObject,
    mut v_x_2491_: usize,
    mut v_x_2492_: usize,
    mut v_x_2493_: *mut LeanObject,
    mut v_x_2494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: usize = 0;
    let mut v___x_2497_: usize = 0;
    let mut v___x_2498_: usize = 0;
    let mut v___x_2499_: usize = 0;
    let mut v_j_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2502_: u8 = 0;
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2505_: u8 = 0;
    let mut v_v_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2519_: u8 = 0;
    let mut v___x_2520_: u8 = 0;
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2526_: u8 = 0;
    let mut v_node_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2530_: u8 = 0;
    let mut v___x_2531_: usize = 0;
    let mut v___x_2532_: usize = 0;
    let mut v___x_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2537_: u8 = 0;
    let mut v___x_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2539_: u8 = 0;
    let mut v_unused_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2545_: u8 = 0;
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2550_: u8 = 0;
    let mut v_ks_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: usize = 0;
    let mut v___x_2557_: u8 = 0;
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: u8 = 0;
    let mut v_reuseFailAlloc_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2562_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2490_) == 0 {
                    v_es_2495_ = lean_ctor_get(v_x_2490_, 0);
                    v___x_2496_ = 5usize;
                    v___x_2497_ = 1usize;
                    v___x_2498_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__1);
                    v___x_2499_ = lean_usize_land(v_x_2491_, v___x_2498_);
                    v_j_2500_ = lean_usize_to_nat(v___x_2499_);
                    v___x_2501_ = lean_array_get_size(v_es_2495_);
                    v___x_2502_ = lean_nat_dec_lt(v_j_2500_, v___x_2501_);
                    if v___x_2502_ == 0 {
                        lean_dec(v_j_2500_);
                        lean_dec(v_x_2494_);
                        lean_dec(v_x_2493_);
                        return v_x_2490_;
                    } else {
                        lean_inc_ref(v_es_2495_);
                        v_isSharedCheck_2539_ = (!lean_is_exclusive(v_x_2490_)) as u8;
                        if v_isSharedCheck_2539_ == 0 {
                            v_unused_2540_ = lean_ctor_get(v_x_2490_, 0);
                            lean_dec(v_unused_2540_);
                            v___x_2504_ = v_x_2490_;
                            v_isShared_2505_ = v_isSharedCheck_2539_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2490_);
                            v___x_2504_ = lean_box(0);
                            v_isShared_2505_ = v_isSharedCheck_2539_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2541_ = lean_ctor_get(v_x_2490_, 0);
                    v_vs_2542_ = lean_ctor_get(v_x_2490_, 1);
                    v_isSharedCheck_2562_ = (!lean_is_exclusive(v_x_2490_)) as u8;
                    if v_isSharedCheck_2562_ == 0 {
                        v___x_2544_ = v_x_2490_;
                        v_isShared_2545_ = v_isSharedCheck_2562_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2542_);
                        lean_inc(v_ks_2541_);
                        lean_dec(v_x_2490_);
                        v___x_2544_ = lean_box(0);
                        v_isShared_2545_ = v_isSharedCheck_2562_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2506_ = lean_array_fget(v_es_2495_, v_j_2500_);
                v___x_2507_ = lean_box(0);
                v_xs_x27_2508_ = lean_array_fset(v_es_2495_, v_j_2500_, v___x_2507_);
                match lean_obj_tag(v_v_2506_) {
                    0 => {
                        v_key_2515_ = lean_ctor_get(v_v_2506_, 0);
                        v_val_2516_ = lean_ctor_get(v_v_2506_, 1);
                        v_isSharedCheck_2526_ = (!lean_is_exclusive(v_v_2506_)) as u8;
                        if v_isSharedCheck_2526_ == 0 {
                            v___x_2518_ = v_v_2506_;
                            v_isShared_2519_ = v_isSharedCheck_2526_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2516_);
                            lean_inc(v_key_2515_);
                            lean_dec(v_v_2506_);
                            v___x_2518_ = lean_box(0);
                            v_isShared_2519_ = v_isSharedCheck_2526_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2527_ = lean_ctor_get(v_v_2506_, 0);
                        v_isSharedCheck_2537_ = (!lean_is_exclusive(v_v_2506_)) as u8;
                        if v_isSharedCheck_2537_ == 0 {
                            v___x_2529_ = v_v_2506_;
                            v_isShared_2530_ = v_isSharedCheck_2537_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2527_);
                            lean_dec(v_v_2506_);
                            v___x_2529_ = lean_box(0);
                            v_isShared_2530_ = v_isSharedCheck_2537_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2538_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2538_, 0, v_x_2493_);
                        lean_ctor_set(v___x_2538_, 1, v_x_2494_);
                        v___y_2510_ = v___x_2538_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2511_ = lean_array_fset(v_xs_x27_2508_, v_j_2500_, v___y_2510_);
                lean_dec(v_j_2500_);
                if v_isShared_2505_ == 0 {
                    lean_ctor_set(v___x_2504_, 0, v___x_2511_);
                    v___x_2513_ = v___x_2504_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2511_);
                    v___x_2513_ = v_reuseFailAlloc_2514_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2513_;
            }
            4 => {
                v___x_2520_ = l_Lean_instBEqMVarId_beq(v_x_2493_, v_key_2515_);
                if v___x_2520_ == 0 {
                    lean_del_object(v___x_2518_);
                    v___x_2521_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2515_,
                        v_val_2516_,
                        v_x_2493_,
                        v_x_2494_,
                    );
                    v___x_2522_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2522_, 0, v___x_2521_);
                    v___y_2510_ = v___x_2522_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2516_);
                    lean_dec(v_key_2515_);
                    if v_isShared_2519_ == 0 {
                        lean_ctor_set(v___x_2518_, 1, v_x_2494_);
                        lean_ctor_set(v___x_2518_, 0, v_x_2493_);
                        v___x_2524_ = v___x_2518_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_x_2493_);
                        lean_ctor_set(v_reuseFailAlloc_2525_, 1, v_x_2494_);
                        v___x_2524_ = v_reuseFailAlloc_2525_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2510_ = v___x_2524_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2531_ = lean_usize_shift_right(v_x_2491_, v___x_2496_);
                v___x_2532_ = lean_usize_add(v_x_2492_, v___x_2497_);
                v___x_2533_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg(v_node_2527_, v___x_2531_, v___x_2532_, v_x_2493_, v_x_2494_);
                if v_isShared_2530_ == 0 {
                    lean_ctor_set(v___x_2529_, 0, v___x_2533_);
                    v___x_2535_ = v___x_2529_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___x_2533_);
                    v___x_2535_ = v_reuseFailAlloc_2536_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2510_ = v___x_2535_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2545_ == 0 {
                    v___x_2547_ = v___x_2544_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_ks_2541_);
                    lean_ctor_set(v_reuseFailAlloc_2561_, 1, v_vs_2542_);
                    v___x_2547_ = v_reuseFailAlloc_2561_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2548_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4___redArg(v___x_2547_, v_x_2493_, v_x_2494_);
                v___x_2556_ = 7usize;
                v___x_2557_ = lean_usize_dec_le(v___x_2556_, v_x_2492_);
                if v___x_2557_ == 0 {
                    v___x_2558_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2548_);
                    v___x_2559_ = lean_unsigned_to_nat(4);
                    v___x_2560_ = lean_nat_dec_lt(v___x_2558_, v___x_2559_);
                    lean_dec(v___x_2558_);
                    v___y_2550_ = v___x_2560_;
                    state = 10;
                    continue;
                } else {
                    v___y_2550_ = v___x_2557_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2550_ == 0 {
                    v_ks_2551_ = lean_ctor_get(v_newNode_2548_, 0);
                    lean_inc_ref(v_ks_2551_);
                    v_vs_2552_ = lean_ctor_get(v_newNode_2548_, 1);
                    lean_inc_ref(v_vs_2552_);
                    lean_dec_ref(v_newNode_2548_);
                    v___x_2553_ = lean_unsigned_to_nat(0);
                    v___x_2554_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___closed__2);
                    v___x_2555_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5___redArg(v_x_2492_, v_ks_2551_, v_vs_2552_, v___x_2553_, v___x_2554_);
                    lean_dec_ref(v_vs_2552_);
                    lean_dec_ref(v_ks_2551_);
                    return v___x_2555_;
                } else {
                    return v_newNode_2548_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5___redArg(
    mut v_depth_2563_: usize,
    mut v_keys_2564_: *mut LeanObject,
    mut v_vals_2565_: *mut LeanObject,
    mut v_i_2566_: *mut LeanObject,
    mut v_entries_2567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: u8 = 0;
    let mut v_k_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: u64 = 0;
    let mut v_h_2573_: usize = 0;
    let mut v___x_2574_: usize = 0;
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: usize = 0;
    let mut v___x_2577_: usize = 0;
    let mut v___x_2578_: usize = 0;
    let mut v_h_2579_: usize = 0;
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2568_ = lean_array_get_size(v_keys_2564_);
                v___x_2569_ = lean_nat_dec_lt(v_i_2566_, v___x_2568_);
                if v___x_2569_ == 0 {
                    lean_dec(v_i_2566_);
                    return v_entries_2567_;
                } else {
                    v_k_2570_ = lean_array_fget_borrowed(v_keys_2564_, v_i_2566_);
                    v_v_2571_ = lean_array_fget_borrowed(v_vals_2565_, v_i_2566_);
                    v___x_2572_ = l_Lean_instHashableMVarId_hash(v_k_2570_);
                    v_h_2573_ = lean_uint64_to_usize(v___x_2572_);
                    v___x_2574_ = 5usize;
                    v___x_2575_ = lean_unsigned_to_nat(1);
                    v___x_2576_ = 1usize;
                    v___x_2577_ = lean_usize_sub(v_depth_2563_, v___x_2576_);
                    v___x_2578_ = lean_usize_mul(v___x_2574_, v___x_2577_);
                    v_h_2579_ = lean_usize_shift_right(v_h_2573_, v___x_2578_);
                    v___x_2580_ = lean_nat_add(v_i_2566_, v___x_2575_);
                    lean_dec(v_i_2566_);
                    lean_inc(v_v_2571_);
                    lean_inc(v_k_2570_);
                    v___x_2581_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg(v_entries_2567_, v_h_2579_, v_depth_2563_, v_k_2570_, v_v_2571_);
                    v_i_2566_ = v___x_2580_;
                    v_entries_2567_ = v___x_2581_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5___redArg___boxed(
    mut v_depth_2583_: *mut LeanObject,
    mut v_keys_2584_: *mut LeanObject,
    mut v_vals_2585_: *mut LeanObject,
    mut v_i_2586_: *mut LeanObject,
    mut v_entries_2587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2588_: usize = 0;
    let mut v_res_2589_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2588_ = lean_unbox_usize(v_depth_2583_);
    lean_dec(v_depth_2583_);
    v_res_2589_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_boxed_2588_, v_keys_2584_, v_vals_2585_, v_i_2586_, v_entries_2587_);
    lean_dec_ref(v_vals_2585_);
    lean_dec_ref(v_keys_2584_);
    return v_res_2589_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_x_2590_: *mut LeanObject,
    mut v_x_2591_: *mut LeanObject,
    mut v_x_2592_: *mut LeanObject,
    mut v_x_2593_: *mut LeanObject,
    mut v_x_2594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_74839__boxed_2595_: usize = 0;
    let mut v_x_74840__boxed_2596_: usize = 0;
    let mut v_res_2597_: *mut LeanObject = core::ptr::null_mut();
    v_x_74839__boxed_2595_ = lean_unbox_usize(v_x_2591_);
    lean_dec(v_x_2591_);
    v_x_74840__boxed_2596_ = lean_unbox_usize(v_x_2592_);
    lean_dec(v_x_2592_);
    v_res_2597_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg(v_x_2590_, v_x_74839__boxed_2595_, v_x_74840__boxed_2596_, v_x_2593_, v_x_2594_);
    return v_res_2597_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1___redArg(
    mut v_x_2598_: *mut LeanObject,
    mut v_x_2599_: *mut LeanObject,
    mut v_x_2600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2601_: u64 = 0;
    let mut v___x_2602_: usize = 0;
    let mut v___x_2603_: usize = 0;
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    v___x_2601_ = l_Lean_instHashableMVarId_hash(v_x_2599_);
    v___x_2602_ = lean_uint64_to_usize(v___x_2601_);
    v___x_2603_ = 1usize;
    v___x_2604_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg(v_x_2598_, v___x_2602_, v___x_2603_, v_x_2599_, v_x_2600_);
    return v___x_2604_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg(
    mut v_mvarId_2605_: *mut LeanObject,
    mut v_val_2606_: *mut LeanObject,
    mut v___y_2607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2617_: u8 = 0;
    let mut v_depth_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_2627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2630_: u8 = 0;
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2641_: u8 = 0;
    let mut v_isSharedCheck_2642_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2609_ = lean_st_ref_take(v___y_2607_);
                v_mctx_2610_ = lean_ctor_get(v___x_2609_, 0);
                v_cache_2611_ = lean_ctor_get(v___x_2609_, 1);
                v_zetaDeltaFVarIds_2612_ = lean_ctor_get(v___x_2609_, 2);
                v_postponed_2613_ = lean_ctor_get(v___x_2609_, 3);
                v_diag_2614_ = lean_ctor_get(v___x_2609_, 4);
                v_isSharedCheck_2642_ = (!lean_is_exclusive(v___x_2609_)) as u8;
                if v_isSharedCheck_2642_ == 0 {
                    v___x_2616_ = v___x_2609_;
                    v_isShared_2617_ = v_isSharedCheck_2642_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_2614_);
                    lean_inc(v_postponed_2613_);
                    lean_inc(v_zetaDeltaFVarIds_2612_);
                    lean_inc(v_cache_2611_);
                    lean_inc(v_mctx_2610_);
                    lean_dec(v___x_2609_);
                    v___x_2616_ = lean_box(0);
                    v_isShared_2617_ = v_isSharedCheck_2642_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_2618_ = lean_ctor_get(v_mctx_2610_, 0);
                v_levelAssignDepth_2619_ = lean_ctor_get(v_mctx_2610_, 1);
                v_lmvarCounter_2620_ = lean_ctor_get(v_mctx_2610_, 2);
                v_mvarCounter_2621_ = lean_ctor_get(v_mctx_2610_, 3);
                v_lDecls_2622_ = lean_ctor_get(v_mctx_2610_, 4);
                v_decls_2623_ = lean_ctor_get(v_mctx_2610_, 5);
                v_userNames_2624_ = lean_ctor_get(v_mctx_2610_, 6);
                v_lAssignment_2625_ = lean_ctor_get(v_mctx_2610_, 7);
                v_eAssignment_2626_ = lean_ctor_get(v_mctx_2610_, 8);
                v_dAssignment_2627_ = lean_ctor_get(v_mctx_2610_, 9);
                v_isSharedCheck_2641_ = (!lean_is_exclusive(v_mctx_2610_)) as u8;
                if v_isSharedCheck_2641_ == 0 {
                    v___x_2629_ = v_mctx_2610_;
                    v_isShared_2630_ = v_isSharedCheck_2641_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_2627_);
                    lean_inc(v_eAssignment_2626_);
                    lean_inc(v_lAssignment_2625_);
                    lean_inc(v_userNames_2624_);
                    lean_inc(v_decls_2623_);
                    lean_inc(v_lDecls_2622_);
                    lean_inc(v_mvarCounter_2621_);
                    lean_inc(v_lmvarCounter_2620_);
                    lean_inc(v_levelAssignDepth_2619_);
                    lean_inc(v_depth_2618_);
                    lean_dec(v_mctx_2610_);
                    v___x_2629_ = lean_box(0);
                    v_isShared_2630_ = v_isSharedCheck_2641_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2631_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1___redArg(v_eAssignment_2626_, v_mvarId_2605_, v_val_2606_);
                if v_isShared_2630_ == 0 {
                    lean_ctor_set(v___x_2629_, 8, v___x_2631_);
                    v___x_2633_ = v___x_2629_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2640_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_depth_2618_);
                    lean_ctor_set(v_reuseFailAlloc_2640_, 1, v_levelAssignDepth_2619_);
                    lean_ctor_set(v_reuseFailAlloc_2640_, 2, v_lmvarCounter_2620_);
                    lean_ctor_set(v_reuseFailAlloc_2640_, 3, v_mvarCounter_2621_);
                    lean_ctor_set(v_reuseFailAlloc_2640_, 4, v_lDecls_2622_);
                    lean_ctor_set(v_reuseFailAlloc_2640_, 5, v_decls_2623_);
                    lean_ctor_set(v_reuseFailAlloc_2640_, 6, v_userNames_2624_);
                    lean_ctor_set(v_reuseFailAlloc_2640_, 7, v_lAssignment_2625_);
                    lean_ctor_set(v_reuseFailAlloc_2640_, 8, v___x_2631_);
                    lean_ctor_set(v_reuseFailAlloc_2640_, 9, v_dAssignment_2627_);
                    v___x_2633_ = v_reuseFailAlloc_2640_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2617_ == 0 {
                    lean_ctor_set(v___x_2616_, 0, v___x_2633_);
                    v___x_2635_ = v___x_2616_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2639_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2639_, 0, v___x_2633_);
                    lean_ctor_set(v_reuseFailAlloc_2639_, 1, v_cache_2611_);
                    lean_ctor_set(v_reuseFailAlloc_2639_, 2, v_zetaDeltaFVarIds_2612_);
                    lean_ctor_set(v_reuseFailAlloc_2639_, 3, v_postponed_2613_);
                    lean_ctor_set(v_reuseFailAlloc_2639_, 4, v_diag_2614_);
                    v___x_2635_ = v_reuseFailAlloc_2639_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2636_ = lean_st_ref_set(v___y_2607_, v___x_2635_);
                v___x_2637_ = lean_box(0);
                v___x_2638_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2638_, 0, v___x_2637_);
                return v___x_2638_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg___boxed(
    mut v_mvarId_2643_: *mut LeanObject,
    mut v_val_2644_: *mut LeanObject,
    mut v___y_2645_: *mut LeanObject,
    mut v___y_2646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2647_: *mut LeanObject = core::ptr::null_mut();
    v_res_2647_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg(v_mvarId_2643_, v_val_2644_, v___y_2645_);
    lean_dec(v___y_2645_);
    return v_res_2647_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__9()
-> *mut LeanObject {
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    v___x_2662_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__8;
    v___x_2663_ = l_Lean_stringToMessageData(v___x_2662_);
    return v___x_2663_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__13()
-> *mut LeanObject {
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    v___x_2669_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__12;
    v___x_2670_ = l_Lean_stringToMessageData(v___x_2669_);
    return v___x_2670_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__14()
-> *mut LeanObject {
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2673_: *mut LeanObject = core::ptr::null_mut();
    v___x_2671_ = lean_box(0);
    v___x_2672_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__3;
    v___x_2673_ = l_Lean_mkConst(v___x_2672_, v___x_2671_);
    return v___x_2673_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__17()
-> *mut LeanObject {
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut LeanObject = core::ptr::null_mut();
    v___x_2678_ = lean_box(0);
    v___x_2679_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__16;
    v___x_2680_ = l_Lean_mkConst(v___x_2679_, v___x_2678_);
    return v___x_2680_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__20()
-> *mut LeanObject {
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    v___x_2685_ = lean_box(0);
    v___x_2686_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__19;
    v___x_2687_ = l_Lean_mkConst(v___x_2686_, v___x_2685_);
    return v___x_2687_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__22()
-> *mut LeanObject {
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    v___x_2691_ = lean_box(0);
    v___x_2692_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__21;
    v___x_2693_ = l_Lean_mkConst(v___x_2692_, v___x_2691_);
    return v___x_2693_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0(
    mut v_goal_2694_: *mut LeanObject,
    mut v___y_2695_: *mut LeanObject,
    mut v___y_2696_: *mut LeanObject,
    mut v___y_2697_: *mut LeanObject,
    mut v___y_2698_: *mut LeanObject,
    mut v___y_2699_: *mut LeanObject,
    mut v___y_2700_: *mut LeanObject,
    mut v___y_2701_: *mut LeanObject,
    mut v___y_2702_: *mut LeanObject,
    mut v___y_2703_: *mut LeanObject,
    mut v___y_2704_: *mut LeanObject,
    mut v___y_2705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2713_: u8 = 0;
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: u8 = 0;
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: u8 = 0;
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: u8 = 0;
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2744_: u8 = 0;
    let mut v_a_2746_: u8 = 0;
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2760_: u8 = 0;
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2765_: u8 = 0;
    let mut v_unused_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2770_: u8 = 0;
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2774_: u8 = 0;
    let mut v_a_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2778_: u8 = 0;
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2782_: u8 = 0;
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_2784_: u8 = 0;
    let mut v_ctxApprox_2785_: u8 = 0;
    let mut v_quasiPatternApprox_2786_: u8 = 0;
    let mut v_constApprox_2787_: u8 = 0;
    let mut v_isDefEqStuckEx_2788_: u8 = 0;
    let mut v_unificationHints_2789_: u8 = 0;
    let mut v_proofIrrelevance_2790_: u8 = 0;
    let mut v_offsetCnstrs_2791_: u8 = 0;
    let mut v_transparency_2792_: u8 = 0;
    let mut v_etaStruct_2793_: u8 = 0;
    let mut v_univApprox_2794_: u8 = 0;
    let mut v_iota_2795_: u8 = 0;
    let mut v_beta_2796_: u8 = 0;
    let mut v_proj_2797_: u8 = 0;
    let mut v_zeta_2798_: u8 = 0;
    let mut v_zetaDelta_2799_: u8 = 0;
    let mut v_zetaUnused_2800_: u8 = 0;
    let mut v_zetaHave_2801_: u8 = 0;
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2804_: u8 = 0;
    let mut v_trackZetaDelta_2805_: u8 = 0;
    let mut v_zetaDeltaSet_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2812_: u8 = 0;
    let mut v_inTypeClassResolution_2813_: u8 = 0;
    let mut v_cacheInferType_2814_: u8 = 0;
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: u64 = 0;
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: u8 = 0;
    let mut v_a_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: u8 = 0;
    let mut v_a_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2829_: u8 = 0;
    let mut v___x_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2833_: u8 = 0;
    let mut v_reuseFailAlloc_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2835_: u8 = 0;
    let mut v_isSharedCheck_2836_: u8 = 0;
    let mut v_a_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2840_: u8 = 0;
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2844_: u8 = 0;
    let mut v_a_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2848_: u8 = 0;
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2852_: u8 = 0;
    let mut v_a_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2856_: u8 = 0;
    let mut v___x_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2860_: u8 = 0;
    let mut v_a_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2864_: u8 = 0;
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2868_: u8 = 0;
    let mut v_andIntroRule_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarIds_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2890_: u8 = 0;
    let mut v_tail_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2899_: u8 = 0;
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_g_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2916_: u8 = 0;
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2934_: u8 = 0;
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2942_: u8 = 0;
    let mut v_unused_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2947_: u8 = 0;
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2951_: u8 = 0;
    let mut v_a_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2955_: u8 = 0;
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2959_: u8 = 0;
    let mut v_a_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2963_: u8 = 0;
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2967_: u8 = 0;
    let mut v_a_2968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2971_: u8 = 0;
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2975_: u8 = 0;
    let mut v_a_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2979_: u8 = 0;
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2983_: u8 = 0;
    let mut v_isSharedCheck_2984_: u8 = 0;
    let mut v_isSharedCheck_2985_: u8 = 0;
    let mut v_isSharedCheck_2986_: u8 = 0;
    let mut v_a_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2990_: u8 = 0;
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2994_: u8 = 0;
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2999_: u8 = 0;
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3004_: u8 = 0;
    let mut v_unused_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3009_: u8 = 0;
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3013_: u8 = 0;
    let mut v_isSharedCheck_3014_: u8 = 0;
    let mut v_a_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3018_: u8 = 0;
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3022_: u8 = 0;
    let mut v_a_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3026_: u8 = 0;
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3030_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_goal_2694_);
                v___x_2707_ = l_Lean_MVarId_getType(
                    v_goal_2694_,
                    v___y_2702_,
                    v___y_2703_,
                    v___y_2704_,
                    v___y_2705_,
                );
                if lean_obj_tag(v___x_2707_) == 0 {
                    v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
                    lean_inc(v_a_2708_);
                    lean_dec_ref_known(v___x_2707_, 1);
                    v___x_2709_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__0___redArg(v_a_2708_, v___y_2703_);
                    if lean_obj_tag(v___x_2709_) == 0 {
                        v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
                        v_isSharedCheck_3014_ = (!lean_is_exclusive(v___x_2709_)) as u8;
                        if v_isSharedCheck_3014_ == 0 {
                            v___x_2712_ = v___x_2709_;
                            v_isShared_2713_ = v_isSharedCheck_3014_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2710_);
                            lean_dec(v___x_2709_);
                            v___x_2712_ = lean_box(0);
                            v_isShared_2713_ = v_isSharedCheck_3014_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_goal_2694_);
                        v_a_3015_ = lean_ctor_get(v___x_2709_, 0);
                        v_isSharedCheck_3022_ = (!lean_is_exclusive(v___x_2709_)) as u8;
                        if v_isSharedCheck_3022_ == 0 {
                            v___x_3017_ = v___x_2709_;
                            v_isShared_3018_ = v_isSharedCheck_3022_;
                            state = 50;
                            continue;
                        } else {
                            lean_inc(v_a_3015_);
                            lean_dec(v___x_2709_);
                            v___x_3017_ = lean_box(0);
                            v_isShared_3018_ = v_isSharedCheck_3022_;
                            state = 50;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_goal_2694_);
                    v_a_3023_ = lean_ctor_get(v___x_2707_, 0);
                    v_isSharedCheck_3030_ = (!lean_is_exclusive(v___x_2707_)) as u8;
                    if v_isSharedCheck_3030_ == 0 {
                        v___x_3025_ = v___x_2707_;
                        v_isShared_3026_ = v_isSharedCheck_3030_;
                        state = 52;
                        continue;
                    } else {
                        lean_inc(v_a_3023_);
                        lean_dec(v___x_2707_);
                        v___x_3025_ = lean_box(0);
                        v_isShared_3026_ = v_isSharedCheck_3030_;
                        state = 52;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2714_ =
                    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__1;
                v___x_2715_ = l_Lean_Expr_isAppOf(v_a_2710_, v___x_2714_);
                if v___x_2715_ == 0 {
                    v___x_2716_ =
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__3;
                    v___x_2717_ = l_Lean_Expr_isAppOf(v_a_2710_, v___x_2716_);
                    if v___x_2717_ == 0 {
                        v___x_2718_ =
                            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__5;
                        v___x_2719_ = lean_unsigned_to_nat(3);
                        v___x_2720_ = l_Lean_Expr_isAppOfArity(v_a_2710_, v___x_2718_, v___x_2719_);
                        if v___x_2720_ == 0 {
                            lean_dec(v_a_2710_);
                            v___x_2721_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2721_, 0, v_goal_2694_);
                            if v_isShared_2713_ == 0 {
                                lean_ctor_set(v___x_2712_, 0, v___x_2721_);
                                v___x_2723_ = v___x_2712_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_2724_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2724_, 0, v___x_2721_);
                                v___x_2723_ = v_reuseFailAlloc_2724_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2712_);
                            v___x_2725_ = l_Lean_Expr_appFn_x21(v_a_2710_);
                            v___x_2726_ = l_Lean_Expr_appArg_x21(v___x_2725_);
                            v___x_2727_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(
                                v___x_2726_,
                                v___y_2700_,
                                v___y_2701_,
                                v___y_2702_,
                                v___y_2703_,
                                v___y_2704_,
                                v___y_2705_,
                            );
                            if lean_obj_tag(v___x_2727_) == 0 {
                                v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
                                lean_inc(v_a_2728_);
                                lean_dec_ref_known(v___x_2727_, 1);
                                v___x_2729_ = l_Lean_Expr_appArg_x21(v_a_2710_);
                                lean_dec(v_a_2710_);
                                v___x_2730_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_reduceHead(
                                    v___x_2729_,
                                    v___y_2700_,
                                    v___y_2701_,
                                    v___y_2702_,
                                    v___y_2703_,
                                    v___y_2704_,
                                    v___y_2705_,
                                );
                                if lean_obj_tag(v___x_2730_) == 0 {
                                    v_a_2731_ = lean_ctor_get(v___x_2730_, 0);
                                    lean_inc(v_a_2731_);
                                    lean_dec_ref_known(v___x_2730_, 1);
                                    v___x_2732_ = l_Lean_Expr_appFn_x21(v___x_2725_);
                                    lean_dec_ref(v___x_2725_);
                                    v___x_2733_ = l_Lean_Expr_appArg_x21(v___x_2732_);
                                    lean_dec_ref(v___x_2732_);
                                    lean_inc_ref(v___x_2733_);
                                    v___x_2734_ = l_Lean_Meta_getLevel(
                                        v___x_2733_,
                                        v___y_2702_,
                                        v___y_2703_,
                                        v___y_2704_,
                                        v___y_2705_,
                                    );
                                    if lean_obj_tag(v___x_2734_) == 0 {
                                        v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
                                        lean_inc(v_a_2735_);
                                        lean_dec_ref_known(v___x_2734_, 1);
                                        v___x_2736_ = lean_box(0);
                                        v___x_2737_ = lean_alloc_ctor(1, 2, (0) as u32);
                                        lean_ctor_set(v___x_2737_, 0, v_a_2735_);
                                        lean_ctor_set(v___x_2737_, 1, v___x_2736_);
                                        v___x_2738_ = l_Lean_mkConst(v___x_2718_, v___x_2737_);
                                        lean_inc(v_a_2731_);
                                        lean_inc(v_a_2728_);
                                        lean_inc_ref(v___x_2733_);
                                        v___x_2739_ = l_Lean_mkApp3(
                                            v___x_2738_,
                                            v___x_2733_,
                                            v_a_2728_,
                                            v_a_2731_,
                                        );
                                        v___x_2740_ = l_Lean_MVarId_replaceTargetDefEq(
                                            v_goal_2694_,
                                            v___x_2739_,
                                            v___y_2702_,
                                            v___y_2703_,
                                            v___y_2704_,
                                            v___y_2705_,
                                        );
                                        if lean_obj_tag(v___x_2740_) == 0 {
                                            v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
                                            v_isSharedCheck_2836_ =
                                                (!lean_is_exclusive(v___x_2740_)) as u8;
                                            if v_isSharedCheck_2836_ == 0 {
                                                v___x_2743_ = v___x_2740_;
                                                v_isShared_2744_ = v_isSharedCheck_2836_;
                                                state = 3;
                                                continue;
                                            } else {
                                                lean_inc(v_a_2741_);
                                                lean_dec(v___x_2740_);
                                                v___x_2743_ = lean_box(0);
                                                v_isShared_2744_ = v_isSharedCheck_2836_;
                                                state = 3;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref(v___x_2733_);
                                            lean_dec(v_a_2731_);
                                            lean_dec(v_a_2728_);
                                            v_a_2837_ = lean_ctor_get(v___x_2740_, 0);
                                            v_isSharedCheck_2844_ =
                                                (!lean_is_exclusive(v___x_2740_)) as u8;
                                            if v_isSharedCheck_2844_ == 0 {
                                                v___x_2839_ = v___x_2740_;
                                                v_isShared_2840_ = v_isSharedCheck_2844_;
                                                state = 16;
                                                continue;
                                            } else {
                                                lean_inc(v_a_2837_);
                                                lean_dec(v___x_2740_);
                                                v___x_2839_ = lean_box(0);
                                                v_isShared_2840_ = v_isSharedCheck_2844_;
                                                state = 16;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_2733_);
                                        lean_dec(v_a_2731_);
                                        lean_dec(v_a_2728_);
                                        lean_dec(v_goal_2694_);
                                        v_a_2845_ = lean_ctor_get(v___x_2734_, 0);
                                        v_isSharedCheck_2852_ =
                                            (!lean_is_exclusive(v___x_2734_)) as u8;
                                        if v_isSharedCheck_2852_ == 0 {
                                            v___x_2847_ = v___x_2734_;
                                            v_isShared_2848_ = v_isSharedCheck_2852_;
                                            state = 18;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2845_);
                                            lean_dec(v___x_2734_);
                                            v___x_2847_ = lean_box(0);
                                            v_isShared_2848_ = v_isSharedCheck_2852_;
                                            state = 18;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_2728_);
                                    lean_dec_ref(v___x_2725_);
                                    lean_dec(v_goal_2694_);
                                    v_a_2853_ = lean_ctor_get(v___x_2730_, 0);
                                    v_isSharedCheck_2860_ = (!lean_is_exclusive(v___x_2730_)) as u8;
                                    if v_isSharedCheck_2860_ == 0 {
                                        v___x_2855_ = v___x_2730_;
                                        v_isShared_2856_ = v_isSharedCheck_2860_;
                                        state = 20;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2853_);
                                        lean_dec(v___x_2730_);
                                        v___x_2855_ = lean_box(0);
                                        v_isShared_2856_ = v_isSharedCheck_2860_;
                                        state = 20;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_2725_);
                                lean_dec(v_a_2710_);
                                lean_dec(v_goal_2694_);
                                v_a_2861_ = lean_ctor_get(v___x_2727_, 0);
                                v_isSharedCheck_2868_ = (!lean_is_exclusive(v___x_2727_)) as u8;
                                if v_isSharedCheck_2868_ == 0 {
                                    v___x_2863_ = v___x_2727_;
                                    v_isShared_2864_ = v_isSharedCheck_2868_;
                                    state = 22;
                                    continue;
                                } else {
                                    lean_inc(v_a_2861_);
                                    lean_dec(v___x_2727_);
                                    v___x_2863_ = lean_box(0);
                                    v_isShared_2864_ = v_isSharedCheck_2868_;
                                    state = 22;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_del_object(v___x_2712_);
                        v_andIntroRule_2869_ = lean_ctor_get(v___y_2695_, 15);
                        v___x_2870_ = lean_box(0);
                        lean_inc_ref(v_andIntroRule_2869_);
                        v___x_2871_ =
                            l_Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked(
                                v_andIntroRule_2869_,
                                v_goal_2694_,
                                v___x_2870_,
                                v___y_2695_,
                                v___y_2696_,
                                v___y_2697_,
                                v___y_2698_,
                                v___y_2699_,
                                v___y_2700_,
                                v___y_2701_,
                                v___y_2702_,
                                v___y_2703_,
                                v___y_2704_,
                                v___y_2705_,
                            );
                        if lean_obj_tag(v___x_2871_) == 0 {
                            v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
                            lean_inc(v_a_2872_);
                            lean_dec_ref_known(v___x_2871_, 1);
                            if lean_obj_tag(v_a_2872_) == 1 {
                                v_mvarIds_2887_ = lean_ctor_get(v_a_2872_, 0);
                                v_isSharedCheck_2986_ = (!lean_is_exclusive(v_a_2872_)) as u8;
                                if v_isSharedCheck_2986_ == 0 {
                                    v___x_2889_ = v_a_2872_;
                                    v_isShared_2890_ = v_isSharedCheck_2986_;
                                    state = 25;
                                    continue;
                                } else {
                                    lean_inc(v_mvarIds_2887_);
                                    lean_dec(v_a_2872_);
                                    v___x_2889_ = lean_box(0);
                                    v_isShared_2890_ = v_isSharedCheck_2986_;
                                    state = 25;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_2872_);
                                v___y_2874_ = v___y_2702_;
                                v___y_2875_ = v___y_2703_;
                                v___y_2876_ = v___y_2704_;
                                v___y_2877_ = v___y_2705_;
                                state = 24;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2710_);
                            v_a_2987_ = lean_ctor_get(v___x_2871_, 0);
                            v_isSharedCheck_2994_ = (!lean_is_exclusive(v___x_2871_)) as u8;
                            if v_isSharedCheck_2994_ == 0 {
                                v___x_2989_ = v___x_2871_;
                                v_isShared_2990_ = v_isSharedCheck_2994_;
                                state = 44;
                                continue;
                            } else {
                                lean_inc(v_a_2987_);
                                lean_dec(v___x_2871_);
                                v___x_2989_ = lean_box(0);
                                v_isShared_2990_ = v_isSharedCheck_2994_;
                                state = 44;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_2712_);
                    lean_dec(v_a_2710_);
                    v___x_2995_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__22), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__22_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__22);
                    v___x_2996_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg(v_goal_2694_, v___x_2995_, v___y_2703_);
                    if lean_obj_tag(v___x_2996_) == 0 {
                        v_isSharedCheck_3004_ = (!lean_is_exclusive(v___x_2996_)) as u8;
                        if v_isSharedCheck_3004_ == 0 {
                            v_unused_3005_ = lean_ctor_get(v___x_2996_, 0);
                            lean_dec(v_unused_3005_);
                            v___x_2998_ = v___x_2996_;
                            v_isShared_2999_ = v_isSharedCheck_3004_;
                            state = 46;
                            continue;
                        } else {
                            lean_dec(v___x_2996_);
                            v___x_2998_ = lean_box(0);
                            v_isShared_2999_ = v_isSharedCheck_3004_;
                            state = 46;
                            continue;
                        }
                    } else {
                        v_a_3006_ = lean_ctor_get(v___x_2996_, 0);
                        v_isSharedCheck_3013_ = (!lean_is_exclusive(v___x_2996_)) as u8;
                        if v_isSharedCheck_3013_ == 0 {
                            v___x_3008_ = v___x_2996_;
                            v_isShared_3009_ = v_isSharedCheck_3013_;
                            state = 48;
                            continue;
                        } else {
                            lean_inc(v_a_3006_);
                            lean_dec(v___x_2996_);
                            v___x_3008_ = lean_box(0);
                            v_isShared_3009_ = v_isSharedCheck_3013_;
                            state = 48;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2723_;
            }
            3 => {
                v___x_2783_ = l_Lean_Meta_Context_config(v___y_2702_);
                v_foApprox_2784_ = lean_ctor_get_uint8(v___x_2783_, 0 as u32);
                v_ctxApprox_2785_ = lean_ctor_get_uint8(v___x_2783_, 1 as u32);
                v_quasiPatternApprox_2786_ = lean_ctor_get_uint8(v___x_2783_, 2 as u32);
                v_constApprox_2787_ = lean_ctor_get_uint8(v___x_2783_, 3 as u32);
                v_isDefEqStuckEx_2788_ = lean_ctor_get_uint8(v___x_2783_, 4 as u32);
                v_unificationHints_2789_ = lean_ctor_get_uint8(v___x_2783_, 5 as u32);
                v_proofIrrelevance_2790_ = lean_ctor_get_uint8(v___x_2783_, 6 as u32);
                v_offsetCnstrs_2791_ = lean_ctor_get_uint8(v___x_2783_, 8 as u32);
                v_transparency_2792_ = lean_ctor_get_uint8(v___x_2783_, 9 as u32);
                v_etaStruct_2793_ = lean_ctor_get_uint8(v___x_2783_, 10 as u32);
                v_univApprox_2794_ = lean_ctor_get_uint8(v___x_2783_, 11 as u32);
                v_iota_2795_ = lean_ctor_get_uint8(v___x_2783_, 12 as u32);
                v_beta_2796_ = lean_ctor_get_uint8(v___x_2783_, 13 as u32);
                v_proj_2797_ = lean_ctor_get_uint8(v___x_2783_, 14 as u32);
                v_zeta_2798_ = lean_ctor_get_uint8(v___x_2783_, 15 as u32);
                v_zetaDelta_2799_ = lean_ctor_get_uint8(v___x_2783_, 16 as u32);
                v_zetaUnused_2800_ = lean_ctor_get_uint8(v___x_2783_, 17 as u32);
                v_zetaHave_2801_ = lean_ctor_get_uint8(v___x_2783_, 18 as u32);
                v_isSharedCheck_2835_ = (!lean_is_exclusive(v___x_2783_)) as u8;
                if v_isSharedCheck_2835_ == 0 {
                    v___x_2803_ = v___x_2783_;
                    v_isShared_2804_ = v_isSharedCheck_2835_;
                    state = 12;
                    continue;
                } else {
                    lean_dec(v___x_2783_);
                    v___x_2803_ = lean_box(0);
                    v_isShared_2804_ = v_isSharedCheck_2835_;
                    state = 12;
                    continue;
                }
            }
            4 => {
                if v_a_2746_ == 0 {
                    lean_dec_ref(v___x_2733_);
                    lean_dec(v_a_2728_);
                    v___x_2747_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2747_, 0, v_a_2741_);
                    if v_isShared_2744_ == 0 {
                        lean_ctor_set(v___x_2743_, 0, v___x_2747_);
                        v___x_2749_ = v___x_2743_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2750_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2750_, 0, v___x_2747_);
                        v___x_2749_ = v_reuseFailAlloc_2750_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2743_);
                    lean_inc_ref(v___x_2733_);
                    v___x_2751_ = l_Lean_Meta_getLevel(
                        v___x_2733_,
                        v___y_2702_,
                        v___y_2703_,
                        v___y_2704_,
                        v___y_2705_,
                    );
                    if lean_obj_tag(v___x_2751_) == 0 {
                        v_a_2752_ = lean_ctor_get(v___x_2751_, 0);
                        lean_inc(v_a_2752_);
                        lean_dec_ref_known(v___x_2751_, 1);
                        v___x_2753_ =
                            l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__7;
                        v___x_2754_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_2754_, 0, v_a_2752_);
                        lean_ctor_set(v___x_2754_, 1, v___x_2736_);
                        v___x_2755_ = l_Lean_mkConst(v___x_2753_, v___x_2754_);
                        v___x_2756_ = l_Lean_mkAppB(v___x_2755_, v___x_2733_, v_a_2728_);
                        v___x_2757_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg(v_a_2741_, v___x_2756_, v___y_2703_);
                        if lean_obj_tag(v___x_2757_) == 0 {
                            v_isSharedCheck_2765_ = (!lean_is_exclusive(v___x_2757_)) as u8;
                            if v_isSharedCheck_2765_ == 0 {
                                v_unused_2766_ = lean_ctor_get(v___x_2757_, 0);
                                lean_dec(v_unused_2766_);
                                v___x_2759_ = v___x_2757_;
                                v_isShared_2760_ = v_isSharedCheck_2765_;
                                state = 6;
                                continue;
                            } else {
                                lean_dec(v___x_2757_);
                                v___x_2759_ = lean_box(0);
                                v_isShared_2760_ = v_isSharedCheck_2765_;
                                state = 6;
                                continue;
                            }
                        } else {
                            v_a_2767_ = lean_ctor_get(v___x_2757_, 0);
                            v_isSharedCheck_2774_ = (!lean_is_exclusive(v___x_2757_)) as u8;
                            if v_isSharedCheck_2774_ == 0 {
                                v___x_2769_ = v___x_2757_;
                                v_isShared_2770_ = v_isSharedCheck_2774_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_2767_);
                                lean_dec(v___x_2757_);
                                v___x_2769_ = lean_box(0);
                                v_isShared_2770_ = v_isSharedCheck_2774_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_2741_);
                        lean_dec_ref(v___x_2733_);
                        lean_dec(v_a_2728_);
                        v_a_2775_ = lean_ctor_get(v___x_2751_, 0);
                        v_isSharedCheck_2782_ = (!lean_is_exclusive(v___x_2751_)) as u8;
                        if v_isSharedCheck_2782_ == 0 {
                            v___x_2777_ = v___x_2751_;
                            v_isShared_2778_ = v_isSharedCheck_2782_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_2775_);
                            lean_dec(v___x_2751_);
                            v___x_2777_ = lean_box(0);
                            v_isShared_2778_ = v_isSharedCheck_2782_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_2749_;
            }
            6 => {
                v___x_2761_ = lean_box(0);
                if v_isShared_2760_ == 0 {
                    lean_ctor_set(v___x_2759_, 0, v___x_2761_);
                    v___x_2763_ = v___x_2759_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2764_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2761_);
                    v___x_2763_ = v_reuseFailAlloc_2764_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2763_;
            }
            8 => {
                if v_isShared_2770_ == 0 {
                    v___x_2772_ = v___x_2769_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
                    v___x_2772_ = v_reuseFailAlloc_2773_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2772_;
            }
            10 => {
                if v_isShared_2778_ == 0 {
                    v___x_2780_ = v___x_2777_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
                    v___x_2780_ = v_reuseFailAlloc_2781_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2780_;
            }
            12 => {
                v_trackZetaDelta_2805_ = lean_ctor_get_uint8(
                    v___y_2702_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2806_ = lean_ctor_get(v___y_2702_, 1);
                v_lctx_2807_ = lean_ctor_get(v___y_2702_, 2);
                v_localInstances_2808_ = lean_ctor_get(v___y_2702_, 3);
                v_defEqCtx_x3f_2809_ = lean_ctor_get(v___y_2702_, 4);
                v_synthPendingDepth_2810_ = lean_ctor_get(v___y_2702_, 5);
                v_canUnfold_x3f_2811_ = lean_ctor_get(v___y_2702_, 6);
                v_univApprox_2812_ = lean_ctor_get_uint8(
                    v___y_2702_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2813_ = lean_ctor_get_uint8(
                    v___y_2702_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2814_ = lean_ctor_get_uint8(
                    v___y_2702_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_2804_ == 0 {
                    v___x_2816_ = v___x_2803_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2834_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2834_, 0 as u32, v_foApprox_2784_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2834_, 1 as u32, v_ctxApprox_2785_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2834_,
                        2 as u32,
                        v_quasiPatternApprox_2786_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_2834_, 3 as u32, v_constApprox_2787_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2834_, 4 as u32, v_isDefEqStuckEx_2788_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2834_, 5 as u32, v_unificationHints_2789_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2834_, 6 as u32, v_proofIrrelevance_2790_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2834_, 8 as u32, v_offsetCnstrs_2791_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2834_, 9 as u32, v_transparency_2792_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2834_, 10 as u32, v_etaStruct_2793_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2834_, 11 as u32, v_univApprox_2794_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2834_, 12 as u32, v_iota_2795_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2834_, 13 as u32, v_beta_2796_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2834_, 14 as u32, v_proj_2797_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2834_, 15 as u32, v_zeta_2798_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2834_, 16 as u32, v_zetaDelta_2799_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2834_, 17 as u32, v_zetaUnused_2800_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_2834_, 18 as u32, v_zetaHave_2801_);
                    v___x_2816_ = v_reuseFailAlloc_2834_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                lean_ctor_set_uint8(v___x_2816_, 7 as u32, v___x_2720_);
                v___x_2817_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_2816_);
                v___x_2818_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_introsSimp___redArg___closed__0;
                v___x_2819_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_2819_, 0, v___x_2816_);
                lean_ctor_set_uint64(
                    v___x_2819_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_2817_,
                );
                lean_inc(v_canUnfold_x3f_2811_);
                lean_inc(v_synthPendingDepth_2810_);
                lean_inc(v_defEqCtx_x3f_2809_);
                lean_inc_ref(v_localInstances_2808_);
                lean_inc_ref(v_lctx_2807_);
                lean_inc(v_zetaDeltaSet_2806_);
                v___x_2820_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_2820_, 0, v___x_2819_);
                lean_ctor_set(v___x_2820_, 1, v_zetaDeltaSet_2806_);
                lean_ctor_set(v___x_2820_, 2, v_lctx_2807_);
                lean_ctor_set(v___x_2820_, 3, v_localInstances_2808_);
                lean_ctor_set(v___x_2820_, 4, v_defEqCtx_x3f_2809_);
                lean_ctor_set(v___x_2820_, 5, v_synthPendingDepth_2810_);
                lean_ctor_set(v___x_2820_, 6, v_canUnfold_x3f_2811_);
                lean_ctor_set_uint8(
                    v___x_2820_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2805_,
                );
                lean_ctor_set_uint8(
                    v___x_2820_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2812_,
                );
                lean_ctor_set_uint8(
                    v___x_2820_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2813_,
                );
                lean_ctor_set_uint8(
                    v___x_2820_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2814_,
                );
                lean_inc(v_a_2728_);
                v___x_2821_ = l_Lean_Meta_Sym_isDefEqS(
                    v_a_2728_,
                    v_a_2731_,
                    v___x_2720_,
                    v___x_2720_,
                    v___x_2818_,
                    v___x_2818_,
                    v___y_2700_,
                    v___y_2701_,
                    v___x_2820_,
                    v___y_2703_,
                    v___y_2704_,
                    v___y_2705_,
                );
                lean_dec_ref_known(v___x_2820_, 7);
                if lean_obj_tag(v___x_2821_) == 0 {
                    v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
                    lean_inc(v_a_2822_);
                    lean_dec_ref_known(v___x_2821_, 1);
                    v___x_2823_ = (lean_unbox(v_a_2822_) as u8);
                    lean_dec(v_a_2822_);
                    v_a_2746_ = v___x_2823_;
                    state = 4;
                    continue;
                } else {
                    if lean_obj_tag(v___x_2821_) == 0 {
                        v_a_2824_ = lean_ctor_get(v___x_2821_, 0);
                        lean_inc(v_a_2824_);
                        lean_dec_ref_known(v___x_2821_, 1);
                        v___x_2825_ = (lean_unbox(v_a_2824_) as u8);
                        lean_dec(v_a_2824_);
                        v_a_2746_ = v___x_2825_;
                        state = 4;
                        continue;
                    } else {
                        lean_del_object(v___x_2743_);
                        lean_dec(v_a_2741_);
                        lean_dec_ref(v___x_2733_);
                        lean_dec(v_a_2728_);
                        v_a_2826_ = lean_ctor_get(v___x_2821_, 0);
                        v_isSharedCheck_2833_ = (!lean_is_exclusive(v___x_2821_)) as u8;
                        if v_isSharedCheck_2833_ == 0 {
                            v___x_2828_ = v___x_2821_;
                            v_isShared_2829_ = v_isSharedCheck_2833_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_2826_);
                            lean_dec(v___x_2821_);
                            v___x_2828_ = lean_box(0);
                            v_isShared_2829_ = v_isSharedCheck_2833_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            14 => {
                if v_isShared_2829_ == 0 {
                    v___x_2831_ = v___x_2828_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
                    v___x_2831_ = v_reuseFailAlloc_2832_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2831_;
            }
            16 => {
                if v_isShared_2840_ == 0 {
                    v___x_2842_ = v___x_2839_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2843_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2843_, 0, v_a_2837_);
                    v___x_2842_ = v_reuseFailAlloc_2843_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2842_;
            }
            18 => {
                if v_isShared_2848_ == 0 {
                    v___x_2850_ = v___x_2847_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
                    v___x_2850_ = v_reuseFailAlloc_2851_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2850_;
            }
            20 => {
                if v_isShared_2856_ == 0 {
                    v___x_2858_ = v___x_2855_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2859_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2859_, 0, v_a_2853_);
                    v___x_2858_ = v_reuseFailAlloc_2859_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2858_;
            }
            22 => {
                if v_isShared_2864_ == 0 {
                    v___x_2866_ = v___x_2863_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2867_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2867_, 0, v_a_2861_);
                    v___x_2866_ = v_reuseFailAlloc_2867_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2866_;
            }
            24 => {
                v___x_2878_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__9
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__9_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__9,
                );
                v___x_2879_ =
                    l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__11;
                v___x_2880_ = l_Lean_MessageData_ofConstName(v___x_2879_, v___x_2715_);
                v___x_2881_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2881_, 0, v___x_2878_);
                lean_ctor_set(v___x_2881_, 1, v___x_2880_);
                v___x_2882_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__13), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__13_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__13);
                v___x_2883_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2883_, 0, v___x_2881_);
                lean_ctor_set(v___x_2883_, 1, v___x_2882_);
                v___x_2884_ = l_Lean_indentExpr(v_a_2710_);
                v___x_2885_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_2885_, 0, v___x_2883_);
                lean_ctor_set(v___x_2885_, 1, v___x_2884_);
                v___x_2886_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_Internal_Lean_Meta_Sym_BackwardRule_applyChecked_spec__1___redArg(v___x_2885_, v___y_2874_, v___y_2875_, v___y_2876_, v___y_2877_);
                return v___x_2886_;
            }
            25 => {
                if lean_obj_tag(v_mvarIds_2887_) == 1 {
                    v_tail_2891_ = lean_ctor_get(v_mvarIds_2887_, 1);
                    lean_inc(v_tail_2891_);
                    if lean_obj_tag(v_tail_2891_) == 1 {
                        v_tail_2892_ = lean_ctor_get(v_tail_2891_, 1);
                        if lean_obj_tag(v_tail_2892_) == 0 {
                            lean_dec(v_a_2710_);
                            v_head_2893_ = lean_ctor_get(v_mvarIds_2887_, 0);
                            lean_inc(v_head_2893_);
                            lean_dec_ref_known(v_mvarIds_2887_, 2);
                            v_head_2894_ = lean_ctor_get(v_tail_2891_, 0);
                            lean_inc(v_head_2894_);
                            lean_dec_ref_known(v_tail_2891_, 2);
                            v___x_2895_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl(
                                v_head_2893_,
                                v___y_2695_,
                                v___y_2696_,
                                v___y_2697_,
                                v___y_2698_,
                                v___y_2699_,
                                v___y_2700_,
                                v___y_2701_,
                                v___y_2702_,
                                v___y_2703_,
                                v___y_2704_,
                                v___y_2705_,
                            );
                            if lean_obj_tag(v___x_2895_) == 0 {
                                v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
                                v_isSharedCheck_2985_ = (!lean_is_exclusive(v___x_2895_)) as u8;
                                if v_isSharedCheck_2985_ == 0 {
                                    v___x_2898_ = v___x_2895_;
                                    v_isShared_2899_ = v_isSharedCheck_2985_;
                                    state = 26;
                                    continue;
                                } else {
                                    lean_inc(v_a_2896_);
                                    lean_dec(v___x_2895_);
                                    v___x_2898_ = lean_box(0);
                                    v_isShared_2899_ = v_isSharedCheck_2985_;
                                    state = 26;
                                    continue;
                                }
                            } else {
                                lean_dec(v_head_2894_);
                                lean_del_object(v___x_2889_);
                                return v___x_2895_;
                            }
                        } else {
                            lean_dec_ref_known(v_tail_2891_, 2);
                            lean_dec_ref_known(v_mvarIds_2887_, 2);
                            lean_del_object(v___x_2889_);
                            v___y_2874_ = v___y_2702_;
                            v___y_2875_ = v___y_2703_;
                            v___y_2876_ = v___y_2704_;
                            v___y_2877_ = v___y_2705_;
                            state = 24;
                            continue;
                        }
                    } else {
                        lean_dec(v_tail_2891_);
                        lean_dec_ref_known(v_mvarIds_2887_, 2);
                        lean_del_object(v___x_2889_);
                        v___y_2874_ = v___y_2702_;
                        v___y_2875_ = v___y_2703_;
                        v___y_2876_ = v___y_2704_;
                        v___y_2877_ = v___y_2705_;
                        state = 24;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2889_);
                    lean_dec(v_mvarIds_2887_);
                    v___y_2874_ = v___y_2702_;
                    v___y_2875_ = v___y_2703_;
                    v___y_2876_ = v___y_2704_;
                    v___y_2877_ = v___y_2705_;
                    state = 24;
                    continue;
                }
            }
            26 => {
                v___x_2900_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl(
                    v_head_2894_,
                    v___y_2695_,
                    v___y_2696_,
                    v___y_2697_,
                    v___y_2698_,
                    v___y_2699_,
                    v___y_2700_,
                    v___y_2701_,
                    v___y_2702_,
                    v___y_2703_,
                    v___y_2704_,
                    v___y_2705_,
                );
                if lean_obj_tag(v___x_2900_) == 0 {
                    v_a_2901_ = lean_ctor_get(v___x_2900_, 0);
                    lean_inc(v_a_2901_);
                    if lean_obj_tag(v_a_2896_) == 0 {
                        if lean_obj_tag(v_a_2901_) == 0 {
                            lean_del_object(v___x_2898_);
                            lean_del_object(v___x_2889_);
                            return v___x_2900_;
                        } else {
                            lean_dec_ref_known(v___x_2900_, 1);
                            v_val_2910_ = lean_ctor_get(v_a_2901_, 0);
                            lean_inc(v_val_2910_);
                            lean_dec_ref_known(v_a_2901_, 1);
                            v_g_2903_ = v_val_2910_;
                            state = 27;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_2900_, 1);
                        if lean_obj_tag(v_a_2901_) == 0 {
                            v_val_2911_ = lean_ctor_get(v_a_2896_, 0);
                            lean_inc(v_val_2911_);
                            lean_dec_ref_known(v_a_2896_, 1);
                            v_g_2903_ = v_val_2911_;
                            state = 27;
                            continue;
                        } else {
                            lean_del_object(v___x_2898_);
                            lean_del_object(v___x_2889_);
                            v_val_2912_ = lean_ctor_get(v_a_2896_, 0);
                            lean_inc(v_val_2912_);
                            lean_dec_ref_known(v_a_2896_, 1);
                            v_val_2913_ = lean_ctor_get(v_a_2901_, 0);
                            v_isSharedCheck_2984_ = (!lean_is_exclusive(v_a_2901_)) as u8;
                            if v_isSharedCheck_2984_ == 0 {
                                v___x_2915_ = v_a_2901_;
                                v_isShared_2916_ = v_isSharedCheck_2984_;
                                state = 30;
                                continue;
                            } else {
                                lean_inc(v_val_2913_);
                                lean_dec(v_a_2901_);
                                v___x_2915_ = lean_box(0);
                                v_isShared_2916_ = v_isSharedCheck_2984_;
                                state = 30;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_2898_);
                    lean_dec(v_a_2896_);
                    lean_del_object(v___x_2889_);
                    return v___x_2900_;
                }
            }
            27 => {
                if v_isShared_2890_ == 0 {
                    lean_ctor_set(v___x_2889_, 0, v_g_2903_);
                    v___x_2905_ = v___x_2889_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_g_2903_);
                    v___x_2905_ = v_reuseFailAlloc_2909_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_2899_ == 0 {
                    lean_ctor_set(v___x_2898_, 0, v___x_2905_);
                    v___x_2907_ = v___x_2898_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_2908_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2908_, 0, v___x_2905_);
                    v___x_2907_ = v_reuseFailAlloc_2908_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_2907_;
            }
            30 => {
                lean_inc(v_val_2912_);
                v___x_2917_ = l_Lean_MVarId_getType(
                    v_val_2912_,
                    v___y_2702_,
                    v___y_2703_,
                    v___y_2704_,
                    v___y_2705_,
                );
                if lean_obj_tag(v___x_2917_) == 0 {
                    v_a_2918_ = lean_ctor_get(v___x_2917_, 0);
                    lean_inc(v_a_2918_);
                    lean_dec_ref_known(v___x_2917_, 1);
                    lean_inc(v_val_2913_);
                    v___x_2919_ = l_Lean_MVarId_getType(
                        v_val_2913_,
                        v___y_2702_,
                        v___y_2703_,
                        v___y_2704_,
                        v___y_2705_,
                    );
                    if lean_obj_tag(v___x_2919_) == 0 {
                        v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
                        lean_inc_n(v_a_2920_, 2);
                        lean_dec_ref_known(v___x_2919_, 1);
                        v___x_2921_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__14), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__14_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__14);
                        lean_inc(v_a_2918_);
                        v___x_2922_ = l_Lean_mkAppB(v___x_2921_, v_a_2918_, v_a_2920_);
                        v___x_2923_ = lean_box(0);
                        v___x_2924_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                            v___x_2922_,
                            v___x_2923_,
                            v___y_2702_,
                            v___y_2703_,
                            v___y_2704_,
                            v___y_2705_,
                        );
                        if lean_obj_tag(v___x_2924_) == 0 {
                            v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
                            lean_inc_n(v_a_2925_, 2);
                            lean_dec_ref_known(v___x_2924_, 1);
                            v___x_2926_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__17), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__17_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__17);
                            lean_inc(v_a_2920_);
                            lean_inc(v_a_2918_);
                            v___x_2927_ =
                                l_Lean_mkApp3(v___x_2926_, v_a_2918_, v_a_2920_, v_a_2925_);
                            v___x_2928_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg(v_val_2912_, v___x_2927_, v___y_2703_);
                            if lean_obj_tag(v___x_2928_) == 0 {
                                lean_dec_ref_known(v___x_2928_, 1);
                                v___x_2929_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__20), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__20_once), _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___closed__20);
                                lean_inc(v_a_2925_);
                                v___x_2930_ =
                                    l_Lean_mkApp3(v___x_2929_, v_a_2918_, v_a_2920_, v_a_2925_);
                                v___x_2931_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg(v_val_2913_, v___x_2930_, v___y_2703_);
                                if lean_obj_tag(v___x_2931_) == 0 {
                                    v_isSharedCheck_2942_ = (!lean_is_exclusive(v___x_2931_)) as u8;
                                    if v_isSharedCheck_2942_ == 0 {
                                        v_unused_2943_ = lean_ctor_get(v___x_2931_, 0);
                                        lean_dec(v_unused_2943_);
                                        v___x_2933_ = v___x_2931_;
                                        v_isShared_2934_ = v_isSharedCheck_2942_;
                                        state = 31;
                                        continue;
                                    } else {
                                        lean_dec(v___x_2931_);
                                        v___x_2933_ = lean_box(0);
                                        v_isShared_2934_ = v_isSharedCheck_2942_;
                                        state = 31;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_2925_);
                                    lean_del_object(v___x_2915_);
                                    v_a_2944_ = lean_ctor_get(v___x_2931_, 0);
                                    v_isSharedCheck_2951_ = (!lean_is_exclusive(v___x_2931_)) as u8;
                                    if v_isSharedCheck_2951_ == 0 {
                                        v___x_2946_ = v___x_2931_;
                                        v_isShared_2947_ = v_isSharedCheck_2951_;
                                        state = 34;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2944_);
                                        lean_dec(v___x_2931_);
                                        v___x_2946_ = lean_box(0);
                                        v_isShared_2947_ = v_isSharedCheck_2951_;
                                        state = 34;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_2925_);
                                lean_dec(v_a_2920_);
                                lean_dec(v_a_2918_);
                                lean_del_object(v___x_2915_);
                                lean_dec(v_val_2913_);
                                v_a_2952_ = lean_ctor_get(v___x_2928_, 0);
                                v_isSharedCheck_2959_ = (!lean_is_exclusive(v___x_2928_)) as u8;
                                if v_isSharedCheck_2959_ == 0 {
                                    v___x_2954_ = v___x_2928_;
                                    v_isShared_2955_ = v_isSharedCheck_2959_;
                                    state = 36;
                                    continue;
                                } else {
                                    lean_inc(v_a_2952_);
                                    lean_dec(v___x_2928_);
                                    v___x_2954_ = lean_box(0);
                                    v_isShared_2955_ = v_isSharedCheck_2959_;
                                    state = 36;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_2920_);
                            lean_dec(v_a_2918_);
                            lean_del_object(v___x_2915_);
                            lean_dec(v_val_2913_);
                            lean_dec(v_val_2912_);
                            v_a_2960_ = lean_ctor_get(v___x_2924_, 0);
                            v_isSharedCheck_2967_ = (!lean_is_exclusive(v___x_2924_)) as u8;
                            if v_isSharedCheck_2967_ == 0 {
                                v___x_2962_ = v___x_2924_;
                                v_isShared_2963_ = v_isSharedCheck_2967_;
                                state = 38;
                                continue;
                            } else {
                                lean_inc(v_a_2960_);
                                lean_dec(v___x_2924_);
                                v___x_2962_ = lean_box(0);
                                v_isShared_2963_ = v_isSharedCheck_2967_;
                                state = 38;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_2918_);
                        lean_del_object(v___x_2915_);
                        lean_dec(v_val_2913_);
                        lean_dec(v_val_2912_);
                        v_a_2968_ = lean_ctor_get(v___x_2919_, 0);
                        v_isSharedCheck_2975_ = (!lean_is_exclusive(v___x_2919_)) as u8;
                        if v_isSharedCheck_2975_ == 0 {
                            v___x_2970_ = v___x_2919_;
                            v_isShared_2971_ = v_isSharedCheck_2975_;
                            state = 40;
                            continue;
                        } else {
                            lean_inc(v_a_2968_);
                            lean_dec(v___x_2919_);
                            v___x_2970_ = lean_box(0);
                            v_isShared_2971_ = v_isSharedCheck_2975_;
                            state = 40;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2915_);
                    lean_dec(v_val_2913_);
                    lean_dec(v_val_2912_);
                    v_a_2976_ = lean_ctor_get(v___x_2917_, 0);
                    v_isSharedCheck_2983_ = (!lean_is_exclusive(v___x_2917_)) as u8;
                    if v_isSharedCheck_2983_ == 0 {
                        v___x_2978_ = v___x_2917_;
                        v_isShared_2979_ = v_isSharedCheck_2983_;
                        state = 42;
                        continue;
                    } else {
                        lean_inc(v_a_2976_);
                        lean_dec(v___x_2917_);
                        v___x_2978_ = lean_box(0);
                        v_isShared_2979_ = v_isSharedCheck_2983_;
                        state = 42;
                        continue;
                    }
                }
            }
            31 => {
                v___x_2935_ = l_Lean_Expr_mvarId_x21(v_a_2925_);
                lean_dec(v_a_2925_);
                if v_isShared_2916_ == 0 {
                    lean_ctor_set(v___x_2915_, 0, v___x_2935_);
                    v___x_2937_ = v___x_2915_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2941_, 0, v___x_2935_);
                    v___x_2937_ = v_reuseFailAlloc_2941_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_2934_ == 0 {
                    lean_ctor_set(v___x_2933_, 0, v___x_2937_);
                    v___x_2939_ = v___x_2933_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_2940_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2940_, 0, v___x_2937_);
                    v___x_2939_ = v_reuseFailAlloc_2940_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_2939_;
            }
            34 => {
                if v_isShared_2947_ == 0 {
                    v___x_2949_ = v___x_2946_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2944_);
                    v___x_2949_ = v_reuseFailAlloc_2950_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_2949_;
            }
            36 => {
                if v_isShared_2955_ == 0 {
                    v___x_2957_ = v___x_2954_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
                    v___x_2957_ = v_reuseFailAlloc_2958_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_2957_;
            }
            38 => {
                if v_isShared_2963_ == 0 {
                    v___x_2965_ = v___x_2962_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
                    v___x_2965_ = v_reuseFailAlloc_2966_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_2965_;
            }
            40 => {
                if v_isShared_2971_ == 0 {
                    v___x_2973_ = v___x_2970_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
                    v___x_2973_ = v_reuseFailAlloc_2974_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_2973_;
            }
            42 => {
                if v_isShared_2979_ == 0 {
                    v___x_2981_ = v___x_2978_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
                    v___x_2981_ = v_reuseFailAlloc_2982_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_2981_;
            }
            44 => {
                if v_isShared_2990_ == 0 {
                    v___x_2992_ = v___x_2989_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2987_);
                    v___x_2992_ = v_reuseFailAlloc_2993_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_2992_;
            }
            46 => {
                v___x_3000_ = lean_box(0);
                if v_isShared_2999_ == 0 {
                    lean_ctor_set(v___x_2998_, 0, v___x_3000_);
                    v___x_3002_ = v___x_2998_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_3000_);
                    v___x_3002_ = v_reuseFailAlloc_3003_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_3002_;
            }
            48 => {
                if v_isShared_3009_ == 0 {
                    v___x_3011_ = v___x_3008_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
                    v___x_3011_ = v_reuseFailAlloc_3012_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_3011_;
            }
            50 => {
                if v_isShared_3018_ == 0 {
                    v___x_3020_ = v___x_3017_;
                    state = 51;
                    continue;
                } else {
                    v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
                    v___x_3020_ = v_reuseFailAlloc_3021_;
                    state = 51;
                    continue;
                }
            }
            51 => {
                return v___x_3020_;
            }
            52 => {
                if v_isShared_3026_ == 0 {
                    v___x_3028_ = v___x_3025_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
                    v___x_3028_ = v_reuseFailAlloc_3029_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                return v___x_3028_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___boxed(
    mut v_goal_3031_: *mut LeanObject,
    mut v___y_3032_: *mut LeanObject,
    mut v___y_3033_: *mut LeanObject,
    mut v___y_3034_: *mut LeanObject,
    mut v___y_3035_: *mut LeanObject,
    mut v___y_3036_: *mut LeanObject,
    mut v___y_3037_: *mut LeanObject,
    mut v___y_3038_: *mut LeanObject,
    mut v___y_3039_: *mut LeanObject,
    mut v___y_3040_: *mut LeanObject,
    mut v___y_3041_: *mut LeanObject,
    mut v___y_3042_: *mut LeanObject,
    mut v___y_3043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3044_: *mut LeanObject = core::ptr::null_mut();
    v_res_3044_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0(
        v_goal_3031_,
        v___y_3032_,
        v___y_3033_,
        v___y_3034_,
        v___y_3035_,
        v___y_3036_,
        v___y_3037_,
        v___y_3038_,
        v___y_3039_,
        v___y_3040_,
        v___y_3041_,
        v___y_3042_,
    );
    lean_dec(v___y_3042_);
    lean_dec_ref(v___y_3041_);
    lean_dec(v___y_3040_);
    lean_dec_ref(v___y_3039_);
    lean_dec(v___y_3038_);
    lean_dec_ref(v___y_3037_);
    lean_dec(v___y_3036_);
    lean_dec_ref(v___y_3035_);
    lean_dec(v___y_3034_);
    lean_dec(v___y_3033_);
    lean_dec_ref(v___y_3032_);
    return v_res_3044_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl(
    mut v_goal_3045_: *mut LeanObject,
    mut v_a_3046_: *mut LeanObject,
    mut v_a_3047_: *mut LeanObject,
    mut v_a_3048_: *mut LeanObject,
    mut v_a_3049_: *mut LeanObject,
    mut v_a_3050_: *mut LeanObject,
    mut v_a_3051_: *mut LeanObject,
    mut v_a_3052_: *mut LeanObject,
    mut v_a_3053_: *mut LeanObject,
    mut v_a_3054_: *mut LeanObject,
    mut v_a_3055_: *mut LeanObject,
    mut v_a_3056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_goal_3045_);
    v___f_3058_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___lam__0___boxed
            as *mut core::ffi::c_void,
        13,
        1,
    );
    lean_closure_set(v___f_3058_, 0, v_goal_3045_);
    v___x_3059_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__2___redArg(v_goal_3045_, v___f_3058_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_, v_a_3050_, v_a_3051_, v_a_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_);
    return v___x_3059_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl___boxed(
    mut v_goal_3060_: *mut LeanObject,
    mut v_a_3061_: *mut LeanObject,
    mut v_a_3062_: *mut LeanObject,
    mut v_a_3063_: *mut LeanObject,
    mut v_a_3064_: *mut LeanObject,
    mut v_a_3065_: *mut LeanObject,
    mut v_a_3066_: *mut LeanObject,
    mut v_a_3067_: *mut LeanObject,
    mut v_a_3068_: *mut LeanObject,
    mut v_a_3069_: *mut LeanObject,
    mut v_a_3070_: *mut LeanObject,
    mut v_a_3071_: *mut LeanObject,
    mut v_a_3072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3073_: *mut LeanObject = core::ptr::null_mut();
    v_res_3073_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl(
        v_goal_3060_,
        v_a_3061_,
        v_a_3062_,
        v_a_3063_,
        v_a_3064_,
        v_a_3065_,
        v_a_3066_,
        v_a_3067_,
        v_a_3068_,
        v_a_3069_,
        v_a_3070_,
        v_a_3071_,
    );
    lean_dec(v_a_3071_);
    lean_dec_ref(v_a_3070_);
    lean_dec(v_a_3069_);
    lean_dec_ref(v_a_3068_);
    lean_dec(v_a_3067_);
    lean_dec_ref(v_a_3066_);
    lean_dec(v_a_3065_);
    lean_dec_ref(v_a_3064_);
    lean_dec(v_a_3063_);
    lean_dec(v_a_3062_);
    lean_dec_ref(v_a_3061_);
    return v_res_3073_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1(
    mut v_mvarId_3074_: *mut LeanObject,
    mut v_val_3075_: *mut LeanObject,
    mut v___y_3076_: *mut LeanObject,
    mut v___y_3077_: *mut LeanObject,
    mut v___y_3078_: *mut LeanObject,
    mut v___y_3079_: *mut LeanObject,
    mut v___y_3080_: *mut LeanObject,
    mut v___y_3081_: *mut LeanObject,
    mut v___y_3082_: *mut LeanObject,
    mut v___y_3083_: *mut LeanObject,
    mut v___y_3084_: *mut LeanObject,
    mut v___y_3085_: *mut LeanObject,
    mut v___y_3086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    v___x_3088_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___redArg(v_mvarId_3074_, v_val_3075_, v___y_3084_);
    return v___x_3088_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1___boxed(
    mut v_mvarId_3089_: *mut LeanObject,
    mut v_val_3090_: *mut LeanObject,
    mut v___y_3091_: *mut LeanObject,
    mut v___y_3092_: *mut LeanObject,
    mut v___y_3093_: *mut LeanObject,
    mut v___y_3094_: *mut LeanObject,
    mut v___y_3095_: *mut LeanObject,
    mut v___y_3096_: *mut LeanObject,
    mut v___y_3097_: *mut LeanObject,
    mut v___y_3098_: *mut LeanObject,
    mut v___y_3099_: *mut LeanObject,
    mut v___y_3100_: *mut LeanObject,
    mut v___y_3101_: *mut LeanObject,
    mut v___y_3102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3103_: *mut LeanObject = core::ptr::null_mut();
    v_res_3103_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1(
            v_mvarId_3089_,
            v_val_3090_,
            v___y_3091_,
            v___y_3092_,
            v___y_3093_,
            v___y_3094_,
            v___y_3095_,
            v___y_3096_,
            v___y_3097_,
            v___y_3098_,
            v___y_3099_,
            v___y_3100_,
            v___y_3101_,
        );
    lean_dec(v___y_3101_);
    lean_dec_ref(v___y_3100_);
    lean_dec(v___y_3099_);
    lean_dec_ref(v___y_3098_);
    lean_dec(v___y_3097_);
    lean_dec_ref(v___y_3096_);
    lean_dec(v___y_3095_);
    lean_dec_ref(v___y_3094_);
    lean_dec(v___y_3093_);
    lean_dec(v___y_3092_);
    lean_dec_ref(v___y_3091_);
    return v_res_3103_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1(
    mut v_00_u03b2_3104_: *mut LeanObject,
    mut v_x_3105_: *mut LeanObject,
    mut v_x_3106_: *mut LeanObject,
    mut v_x_3107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3108_: *mut LeanObject = core::ptr::null_mut();
    v___x_3108_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1___redArg(v_x_3105_, v_x_3106_, v_x_3107_);
    return v___x_3108_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3(
    mut v_00_u03b2_3109_: *mut LeanObject,
    mut v_x_3110_: *mut LeanObject,
    mut v_x_3111_: usize,
    mut v_x_3112_: usize,
    mut v_x_3113_: *mut LeanObject,
    mut v_x_3114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    v___x_3115_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___redArg(v_x_3110_, v_x_3111_, v_x_3112_, v_x_3113_, v_x_3114_);
    return v___x_3115_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3___boxed(
    mut v_00_u03b2_3116_: *mut LeanObject,
    mut v_x_3117_: *mut LeanObject,
    mut v_x_3118_: *mut LeanObject,
    mut v_x_3119_: *mut LeanObject,
    mut v_x_3120_: *mut LeanObject,
    mut v_x_3121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_75883__boxed_3122_: usize = 0;
    let mut v_x_75884__boxed_3123_: usize = 0;
    let mut v_res_3124_: *mut LeanObject = core::ptr::null_mut();
    v_x_75883__boxed_3122_ = lean_unbox_usize(v_x_3118_);
    lean_dec(v_x_3118_);
    v_x_75884__boxed_3123_ = lean_unbox_usize(v_x_3119_);
    lean_dec(v_x_3119_);
    v_res_3124_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3(v_00_u03b2_3116_, v_x_3117_, v_x_75883__boxed_3122_, v_x_75884__boxed_3123_, v_x_3120_, v_x_3121_);
    return v_res_3124_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4(
    mut v_00_u03b2_3125_: *mut LeanObject,
    mut v_n_3126_: *mut LeanObject,
    mut v_k_3127_: *mut LeanObject,
    mut v_v_3128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    v___x_3129_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4___redArg(v_n_3126_, v_k_3127_, v_v_3128_);
    return v___x_3129_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5(
    mut v_00_u03b2_3130_: *mut LeanObject,
    mut v_depth_3131_: usize,
    mut v_keys_3132_: *mut LeanObject,
    mut v_vals_3133_: *mut LeanObject,
    mut v_heq_3134_: *mut LeanObject,
    mut v_i_3135_: *mut LeanObject,
    mut v_entries_3136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    v___x_3137_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5___redArg(v_depth_3131_, v_keys_3132_, v_vals_3133_, v_i_3135_, v_entries_3136_);
    return v___x_3137_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5___boxed(
    mut v_00_u03b2_3138_: *mut LeanObject,
    mut v_depth_3139_: *mut LeanObject,
    mut v_keys_3140_: *mut LeanObject,
    mut v_vals_3141_: *mut LeanObject,
    mut v_heq_3142_: *mut LeanObject,
    mut v_i_3143_: *mut LeanObject,
    mut v_entries_3144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3145_: usize = 0;
    let mut v_res_3146_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3145_ = lean_unbox_usize(v_depth_3139_);
    lean_dec(v_depth_3139_);
    v_res_3146_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__5(v_00_u03b2_3138_, v_depth_boxed_3145_, v_keys_3140_, v_vals_3141_, v_heq_3142_, v_i_3143_, v_entries_3144_);
    lean_dec_ref(v_vals_3141_);
    lean_dec_ref(v_keys_3140_);
    return v_res_3146_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_3147_: *mut LeanObject,
    mut v_x_3148_: *mut LeanObject,
    mut v_x_3149_: *mut LeanObject,
    mut v_x_3150_: *mut LeanObject,
    mut v_x_3151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    v___x_3152_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_Internal_VCGen_repeatAndRfl_spec__1_spec__1_spec__3_spec__4_spec__5___redArg(v_x_3148_, v_x_3149_, v_x_3150_, v_x_3151_);
    return v___x_3152_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Intro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Telescope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(
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
pub unsafe fn initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Reduce(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_AlphaShareBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Intro(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Telescope(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Util(builtin);
}

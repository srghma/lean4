// Lean compiler output
// Module: Lean.Meta.Tactic.Apply
// Imports: Lean.Meta.Tactic.Util Lean.PrettyPrinter Lean.Meta.AppBuilder Init.Omega
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::{l_List_appendTR___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Meta::Defs::lean_name_append_index_after;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_List_get___redArg,
    l_List_lengthTR___redArg,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Environment::l_Lean_Environment_find_x3f;
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_BinderInfo_isInstImplicit, l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21,
    l_Lean_Expr_beta, l_Lean_Expr_getAppFn, l_Lean_Expr_hasMVar, l_Lean_Expr_isAppOfArity,
    l_Lean_Expr_isMVar, l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq,
    l_Lean_instHashableMVarId_hash, l_Lean_instInhabitedExpr, l_Lean_mkApp4, l_Lean_mkAppB,
    l_Lean_mkAppN, l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkAppM, runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_MessageData_ofLazyM,
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_SavedState_restore___redArg, l_Lean_Meta_TransparencyMode_toUInt64,
    l_Lean_Meta_forallMetaBoundedTelescope, l_Lean_Meta_forallMetaTelescopeReducing,
    l_Lean_Meta_isExprDefEq, l_Lean_Meta_isExprDefEqGuarded,
    l_Lean_Meta_mkConstWithFreshMVarLevels, l_Lean_Meta_saveState___redArg,
};
use crate::r#gen::Lean::Meta::Check::{
    l_Lean_Meta_addPPExplicitToExposeDiff, l_Lean_Meta_mkUnfoldAxiomsNote,
};
use crate::r#gen::Lean::Meta::CollectMVars::l_Lean_Meta_getMVarsNoDelayed;
use crate::r#gen::Lean::Meta::InferType::{l_Lean_Meta_getLevel, l_Lean_Meta_isProp};
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_synthInstance;
use crate::r#gen::Lean::Meta::Tactic::Util::{
    initialize_Lean_Meta_Tactic_Util, l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getTag,
    l_Lean_MVarId_getType, l_Lean_MVarId_getType_x27, l_Lean_MVarId_headBetaType,
    l_Lean_MVarId_setTag___redArg, l_Lean_Meta_appendTag,
    l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar, l_Lean_Meta_throwTacticEx___redArg,
    runtime_initialize_Lean_Meta_Tactic_Util,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::PrettyPrinter::{
    initialize_Lean_PrettyPrinter, runtime_initialize_Lean_PrettyPrinter,
};
use crate::r#gen::Lean::Util::FindMVar::l_Lean_FindMVar_main;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_usize_land, lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::{lean_infer_type, lean_whnf};
pub static l_Lean_Meta_getExpectedNumArgsAux___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Meta_getExpectedNumArgsAux___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_getExpectedNumArgsAux___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_getExpectedNumArgsAux___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_getExpectedNumArgsAux___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_getExpectedNumArgsAux___closed__1: u64 = 0;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [10, 119, 105, 116, 104, 32, 116, 104, 101, 32, 103, 111, 97, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<21> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 117, 110, 105, 102, 121, 32, 116, 104, 101, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__6_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 104, 101, 32, 116, 101, 114, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__7_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__9_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [116, 121, 112, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__10_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 111, 110, 99, 108, 117, 115, 105, 111, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__10_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 112, 112, 108, 121, 0]};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__0_value) as *mut crate::leanh::LeanObject,110479913597202347 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [32, 105, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [84, 104, 101, 32, 102, 117, 108, 108, 32, 116, 121, 112, 101, 32, 111, 102, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__0_value: crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 97, 115, 115, 105, 103, 110, 32, 115, 121, 110, 116, 104, 101, 115, 105, 122, 101, 100, 32, 105, 110, 115, 116, 97, 110, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_applyConst___closed__0_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [39, 0],
    };
static mut l_Lean_MVarId_applyConst___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyConst___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_applyConst___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_applyConst___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_applyN___lam__0___closed__0_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            84, 121, 112, 101, 32, 109, 105, 115, 109, 97, 116, 99, 104, 58, 32, 116, 97, 114, 103,
            101, 116, 32, 105, 115, 0,
        ],
    };
static mut l_Lean_MVarId_applyN___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyN___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_applyN___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_applyN___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_applyN___lam__0___closed__2_value: crate::leanh::LeanStringObject<33> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 33,
        m_capacity: 33,
        m_length: 32,
        m_data: [
            10, 98, 117, 116, 32, 97, 112, 112, 108, 105, 101, 100, 32, 101, 120, 112, 114, 101,
            115, 115, 105, 111, 110, 32, 104, 97, 115, 32, 116, 121, 112, 101, 0,
        ],
    };
static mut l_Lean_MVarId_applyN___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyN___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_applyN___lam__0___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_applyN___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_applyN___lam__0___closed__4_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            10, 97, 102, 116, 101, 114, 32, 97, 112, 112, 108, 121, 105, 110, 103, 32, 0,
        ],
    };
static mut l_Lean_MVarId_applyN___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyN___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_applyN___lam__0___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_applyN___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_applyN___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 46, 0],
    };
static mut l_Lean_MVarId_applyN___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyN___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_applyN___lam__0___closed__7_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_applyN___lam__0___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_applyN___lam__0___closed__8_value: crate::leanh::LeanStringObject<31> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            65, 112, 112, 108, 105, 101, 100, 32, 116, 121, 112, 101, 32, 116, 97, 107, 101, 115,
            32, 102, 101, 119, 101, 114, 32, 116, 104, 97, 110, 32, 0,
        ],
    };
static mut l_Lean_MVarId_applyN___lam__0___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyN___lam__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_applyN___lam__0___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_applyN___lam__0___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_applyN___lam__0___closed__10_value: crate::leanh::LeanStringObject<13> =
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
        m_data: [32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 58, 10, 0],
    };
static mut l_Lean_MVarId_applyN___lam__0___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_applyN___lam__0___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_applyN___lam__0___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_applyN___lam__0___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        9743492140944907313 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__2_value:
    crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [104, 0],
};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3_value:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__2_value
        ) as *mut crate::leanh::LeanObject,
        8738205681931236784 as *mut crate::leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__4_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
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
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__4_value
) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5_value_aux_0:
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
        core::ptr::addr_of!(
            l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        9743492140944907313 as *mut crate::leanh::LeanObject,
    ],
};
pub static l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__4_value) as *mut crate::leanh::LeanObject,11695081953491693114 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_splitAndCore___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [115, 112, 108, 105, 116, 65, 110, 100, 0],
    };
static mut l_Lean_MVarId_splitAndCore___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_splitAndCore___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_splitAndCore___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_splitAndCore___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2306458822834130193 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_splitAndCore___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_splitAndCore___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_exfalso___lam__0___closed__0_value: crate::leanh::LeanStringObject<6> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [70, 97, 108, 115, 101, 0],
    };
static mut l_Lean_MVarId_exfalso___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_exfalso___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_exfalso___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_exfalso___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            907667957179513571 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_exfalso___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_exfalso___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_exfalso___lam__0___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_exfalso___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_exfalso___lam__0___closed__3_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [101, 108, 105, 109, 0],
    };
static mut l_Lean_MVarId_exfalso___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_exfalso___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_MVarId_exfalso___lam__0___closed__4_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_exfalso___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            907667957179513571 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_MVarId_exfalso___lam__0___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_exfalso___lam__0___closed__4_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_exfalso___lam__0___closed__3_value)
                as *mut crate::leanh::LeanObject,
            3404330064793727539 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_exfalso___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_exfalso___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_exfalso___closed__0_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [101, 120, 102, 97, 108, 115, 111, 0],
    };
static mut l_Lean_MVarId_exfalso___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_exfalso___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_exfalso___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_exfalso___closed__0_value)
                as *mut crate::leanh::LeanObject,
            10107530215740819414 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_exfalso___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_exfalso___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_nthConstructor___lam__0___closed__0_value: crate::leanh::LeanStringObject<
    36,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        116, 97, 114, 103, 101, 116, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 105, 110,
        100, 117, 99, 116, 105, 118, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 0,
    ],
};
static mut l_Lean_MVarId_nthConstructor___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_nthConstructor___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_nthConstructor___lam__0___closed__1_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_MVarId_nthConstructor___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_MVarId_nthConstructor___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_nthConstructor___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_nthConstructor___lam__0___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_nthConstructor___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MVarId_nthConstructor___lam__0___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_nthConstructor___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_nthConstructor___lam__0___closed__4_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [105, 110, 100, 101, 120, 32, 0],
};
static mut l_Lean_MVarId_nthConstructor___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_nthConstructor___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_nthConstructor___lam__0___closed__5_value: crate::leanh::LeanStringObject<
    22,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        32, 111, 117, 116, 32, 111, 102, 32, 98, 111, 117, 110, 100, 115, 44, 32, 111, 110, 108,
        121, 32, 0,
    ],
};
static mut l_Lean_MVarId_nthConstructor___lam__0___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_nthConstructor___lam__0___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_nthConstructor___lam__0___closed__6_value: crate::leanh::LeanStringObject<
    14,
> = crate::leanh::LeanStringObject {
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
        32, 99, 111, 110, 115, 116, 114, 117, 99, 116, 111, 114, 115, 0,
    ],
};
static mut l_Lean_MVarId_nthConstructor___lam__0___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_nthConstructor___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_nthConstructor___lam__0___closed__7_value: crate::leanh::LeanStringObject<
    48,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 48,
    m_capacity: 48,
    m_length: 47,
    m_data: [
        32, 116, 97, 99, 116, 105, 99, 32, 119, 111, 114, 107, 115, 32, 102, 111, 114, 32, 105,
        110, 100, 117, 99, 116, 105, 118, 101, 32, 116, 121, 112, 101, 115, 32, 119, 105, 116, 104,
        32, 101, 120, 97, 99, 116, 108, 121, 32, 0,
    ],
};
static mut l_Lean_MVarId_nthConstructor___lam__0___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_nthConstructor___lam__0___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_iffOfEq___lam__0___closed__0_value: crate::leanh::LeanStringObject<7> =
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
        m_data: [102, 97, 105, 108, 101, 100, 0],
    };
static mut l_Lean_MVarId_iffOfEq___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_iffOfEq___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_iffOfEq___lam__0___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_iffOfEq___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_iffOfEq___closed__0_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [105, 102, 102, 95, 111, 102, 95, 101, 113, 0],
    };
static mut l_Lean_MVarId_iffOfEq___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_iffOfEq___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_iffOfEq___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_iffOfEq___closed__0_value)
                as *mut crate::leanh::LeanObject,
            18095603761325883834 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_iffOfEq___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_iffOfEq___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_iffOfEq___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_iffOfEq___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_iffOfEq___closed__3_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [16777472 as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_MVarId_iffOfEq___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_iffOfEq___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_propext___lam__0___closed__0_value: crate::leanh::LeanStringObject<3> =
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
static mut l_Lean_MVarId_propext___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_propext___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_propext___lam__0___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_propext___lam__0___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16122875713692181903 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_propext___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_propext___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_propext___lam__0___closed__2_value: crate::leanh::LeanStringObject<8> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [112, 114, 111, 112, 101, 120, 116, 0],
    };
static mut l_Lean_MVarId_propext___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_propext___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_propext___lam__0___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_propext___lam__0___closed__2_value)
                as *mut crate::leanh::LeanObject,
            12404887534527682101 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_propext___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_propext___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_MVarId_propext___lam__0___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_propext___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0: u64 = 0;
pub static l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [72, 69, 113, 0],
};
static mut l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__1_value)
                as *mut crate::leanh::LeanObject,
            13589827700912665667 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3_value: crate::leanh::LeanStringObject<
    16,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        112, 114, 111, 111, 102, 95, 105, 114, 114, 101, 108, 95, 104, 101, 113, 0,
    ],
};
static mut l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_proofIrrelHeq___lam__0___closed__4_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__3_value)
                as *mut crate::leanh::LeanObject,
            16338550082024008116 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_proofIrrelHeq___lam__0___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_proofIrrelHeq___closed__0_value: crate::leanh::LeanStringObject<14> =
    crate::leanh::LeanStringObject {
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
            112, 114, 111, 111, 102, 73, 114, 114, 101, 108, 72, 101, 113, 0,
        ],
    };
static mut l_Lean_MVarId_proofIrrelHeq___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_proofIrrelHeq___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_proofIrrelHeq___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_proofIrrelHeq___closed__0_value)
                as *mut crate::leanh::LeanObject,
            8208296555560902447 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_proofIrrelHeq___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_proofIrrelHeq___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_subsingletonElim___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [83, 117, 98, 115, 105, 110, 103, 108, 101, 116, 111, 110, 0],
};
static mut l_Lean_MVarId_subsingletonElim___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_subsingletonElim___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_MVarId_subsingletonElim___lam__0___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_MVarId_subsingletonElim___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        13409365605382521367 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_MVarId_subsingletonElim___lam__0___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_MVarId_subsingletonElim___lam__0___closed__1_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_MVarId_exfalso___lam__0___closed__3_value)
            as *mut crate::leanh::LeanObject,
        15293707491349124431 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_MVarId_subsingletonElim___lam__0___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_subsingletonElim___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_subsingletonElim___closed__0_value: crate::leanh::LeanStringObject<17> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 17,
        m_capacity: 17,
        m_length: 16,
        m_data: [
            115, 117, 98, 115, 105, 110, 103, 108, 101, 116, 111, 110, 69, 108, 105, 109, 0,
        ],
    };
static mut l_Lean_MVarId_subsingletonElim___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_subsingletonElim___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_subsingletonElim___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_subsingletonElim___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16518798283969257801 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_subsingletonElim___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_subsingletonElim___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0(
    mut v_k_3654_: *mut crate::leanh::LeanObject,
    mut v_b_3655_: *mut crate::leanh::LeanObject,
    mut v_c_3656_: *mut crate::leanh::LeanObject,
    mut v___y_3657_: *mut crate::leanh::LeanObject,
    mut v___y_3658_: *mut crate::leanh::LeanObject,
    mut v___y_3659_: *mut crate::leanh::LeanObject,
    mut v___y_3660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_3660_);
    crate::leanh::lean_inc_ref(v___y_3659_);
    crate::leanh::lean_inc(v___y_3658_);
    crate::leanh::lean_inc_ref(v___y_3657_);
    v___x_3662_ = crate::leanh::lean_apply_7(
        v_k_3654_,
        v_b_3655_,
        v_c_3656_,
        v___y_3657_,
        v___y_3658_,
        v___y_3659_,
        v___y_3660_,
        crate::leanh::lean_box(0),
    );
    return v___x_3662_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0___boxed(
    mut v_k_3663_: *mut crate::leanh::LeanObject,
    mut v_b_3664_: *mut crate::leanh::LeanObject,
    mut v_c_3665_: *mut crate::leanh::LeanObject,
    mut v___y_3666_: *mut crate::leanh::LeanObject,
    mut v___y_3667_: *mut crate::leanh::LeanObject,
    mut v___y_3668_: *mut crate::leanh::LeanObject,
    mut v___y_3669_: *mut crate::leanh::LeanObject,
    mut v___y_3670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3671_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0(v_k_3663_, v_b_3664_, v_c_3665_, v___y_3666_, v___y_3667_, v___y_3668_, v___y_3669_);
    crate::leanh::lean_dec(v___y_3669_);
    crate::leanh::lean_dec_ref(v___y_3668_);
    crate::leanh::lean_dec(v___y_3667_);
    crate::leanh::lean_dec_ref(v___y_3666_);
    return v_res_3671_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(
    mut v_type_3672_: *mut crate::leanh::LeanObject,
    mut v_k_3673_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3674_: u8,
    mut v_whnfType_3675_: u8,
    mut v___y_3676_: *mut crate::leanh::LeanObject,
    mut v___y_3677_: *mut crate::leanh::LeanObject,
    mut v___y_3678_: *mut crate::leanh::LeanObject,
    mut v___y_3679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3686_: u8 = 0;
    let mut v___x_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3690_: u8 = 0;
    let mut v_a_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3694_: u8 = 0;
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3698_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_3681_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_3681_, 0, v_k_3673_);
                v___x_3682_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(
                    crate::leanh::lean_box(0),
                    v_type_3672_,
                    v___f_3681_,
                    v_cleanupAnnotations_3674_,
                    v_whnfType_3675_,
                    v___y_3676_,
                    v___y_3677_,
                    v___y_3678_,
                    v___y_3679_,
                );
                if crate::leanh::lean_obj_tag(v___x_3682_) == 0 {
                    v_a_3683_ = crate::leanh::lean_ctor_get(v___x_3682_, 0);
                    v_isSharedCheck_3690_ = (!crate::leanh::lean_is_exclusive(v___x_3682_)) as u8;
                    if v_isSharedCheck_3690_ == 0 {
                        v___x_3685_ = v___x_3682_;
                        v_isShared_3686_ = v_isSharedCheck_3690_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3683_);
                        crate::leanh::lean_dec(v___x_3682_);
                        v___x_3685_ = crate::leanh::lean_box(0);
                        v_isShared_3686_ = v_isSharedCheck_3690_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3691_ = crate::leanh::lean_ctor_get(v___x_3682_, 0);
                    v_isSharedCheck_3698_ = (!crate::leanh::lean_is_exclusive(v___x_3682_)) as u8;
                    if v_isSharedCheck_3698_ == 0 {
                        v___x_3693_ = v___x_3682_;
                        v_isShared_3694_ = v_isSharedCheck_3698_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3691_);
                        crate::leanh::lean_dec(v___x_3682_);
                        v___x_3693_ = crate::leanh::lean_box(0);
                        v_isShared_3694_ = v_isSharedCheck_3698_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3686_ == 0 {
                    v___x_3688_ = v___x_3685_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3689_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
                    v___x_3688_ = v_reuseFailAlloc_3689_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3688_;
            }
            3 => {
                if v_isShared_3694_ == 0 {
                    v___x_3696_ = v___x_3693_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3697_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
                    v___x_3696_ = v_reuseFailAlloc_3697_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3696_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg___boxed(
    mut v_type_3699_: *mut crate::leanh::LeanObject,
    mut v_k_3700_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3701_: *mut crate::leanh::LeanObject,
    mut v_whnfType_3702_: *mut crate::leanh::LeanObject,
    mut v___y_3703_: *mut crate::leanh::LeanObject,
    mut v___y_3704_: *mut crate::leanh::LeanObject,
    mut v___y_3705_: *mut crate::leanh::LeanObject,
    mut v___y_3706_: *mut crate::leanh::LeanObject,
    mut v___y_3707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_3708_: u8 = 0;
    let mut v_whnfType_boxed_3709_: u8 = 0;
    let mut v_res_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3708_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_3701_) as u8);
    v_whnfType_boxed_3709_ = (crate::leanh::lean_unbox(v_whnfType_3702_) as u8);
    v_res_3710_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(v_type_3699_, v_k_3700_, v_cleanupAnnotations_boxed_3708_, v_whnfType_boxed_3709_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3706_);
    crate::leanh::lean_dec(v___y_3706_);
    crate::leanh::lean_dec_ref(v___y_3705_);
    crate::leanh::lean_dec(v___y_3704_);
    crate::leanh::lean_dec_ref(v___y_3703_);
    return v_res_3710_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0(
    mut v_00_u03b1_3711_: *mut crate::leanh::LeanObject,
    mut v_type_3712_: *mut crate::leanh::LeanObject,
    mut v_k_3713_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3714_: u8,
    mut v_whnfType_3715_: u8,
    mut v___y_3716_: *mut crate::leanh::LeanObject,
    mut v___y_3717_: *mut crate::leanh::LeanObject,
    mut v___y_3718_: *mut crate::leanh::LeanObject,
    mut v___y_3719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3721_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(v_type_3712_, v_k_3713_, v_cleanupAnnotations_3714_, v_whnfType_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_);
    return v___x_3721_;
}
pub unsafe fn l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___boxed(
    mut v_00_u03b1_3722_: *mut crate::leanh::LeanObject,
    mut v_type_3723_: *mut crate::leanh::LeanObject,
    mut v_k_3724_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_3725_: *mut crate::leanh::LeanObject,
    mut v_whnfType_3726_: *mut crate::leanh::LeanObject,
    mut v___y_3727_: *mut crate::leanh::LeanObject,
    mut v___y_3728_: *mut crate::leanh::LeanObject,
    mut v___y_3729_: *mut crate::leanh::LeanObject,
    mut v___y_3730_: *mut crate::leanh::LeanObject,
    mut v___y_3731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_3732_: u8 = 0;
    let mut v_whnfType_boxed_3733_: u8 = 0;
    let mut v_res_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_3732_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_3725_) as u8);
    v_whnfType_boxed_3733_ = (crate::leanh::lean_unbox(v_whnfType_3726_) as u8);
    v_res_3734_ =
        l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0(
            v_00_u03b1_3722_,
            v_type_3723_,
            v_k_3724_,
            v_cleanupAnnotations_boxed_3732_,
            v_whnfType_boxed_3733_,
            v___y_3727_,
            v___y_3728_,
            v___y_3729_,
            v___y_3730_,
        );
    crate::leanh::lean_dec(v___y_3730_);
    crate::leanh::lean_dec_ref(v___y_3729_);
    crate::leanh::lean_dec(v___y_3728_);
    crate::leanh::lean_dec_ref(v___y_3727_);
    return v_res_3734_;
}
pub unsafe fn l_Lean_Meta_getExpectedNumArgsAux___lam__0(
    mut v_xs_3735_: *mut crate::leanh::LeanObject,
    mut v_body_3736_: *mut crate::leanh::LeanObject,
    mut v___y_3737_: *mut crate::leanh::LeanObject,
    mut v___y_3738_: *mut crate::leanh::LeanObject,
    mut v___y_3739_: *mut crate::leanh::LeanObject,
    mut v___y_3740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: u8 = 0;
    let mut v___x_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3742_ = lean_array_get_size(v_xs_3735_);
    v___x_3743_ = l_Lean_Expr_getAppFn(v_body_3736_);
    v___x_3744_ = l_Lean_Expr_isMVar(v___x_3743_);
    crate::leanh::lean_dec_ref(v___x_3743_);
    v___x_3745_ = crate::leanh::lean_box((v___x_3744_) as usize);
    v___x_3746_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3746_, 0, v___x_3742_);
    crate::leanh::lean_ctor_set(v___x_3746_, 1, v___x_3745_);
    v___x_3747_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3747_, 0, v___x_3746_);
    return v___x_3747_;
}
pub unsafe fn l_Lean_Meta_getExpectedNumArgsAux___lam__0___boxed(
    mut v_xs_3748_: *mut crate::leanh::LeanObject,
    mut v_body_3749_: *mut crate::leanh::LeanObject,
    mut v___y_3750_: *mut crate::leanh::LeanObject,
    mut v___y_3751_: *mut crate::leanh::LeanObject,
    mut v___y_3752_: *mut crate::leanh::LeanObject,
    mut v___y_3753_: *mut crate::leanh::LeanObject,
    mut v___y_3754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3755_ = l_Lean_Meta_getExpectedNumArgsAux___lam__0(
        v_xs_3748_,
        v_body_3749_,
        v___y_3750_,
        v___y_3751_,
        v___y_3752_,
        v___y_3753_,
    );
    crate::leanh::lean_dec(v___y_3753_);
    crate::leanh::lean_dec_ref(v___y_3752_);
    crate::leanh::lean_dec(v___y_3751_);
    crate::leanh::lean_dec_ref(v___y_3750_);
    crate::leanh::lean_dec_ref(v_body_3749_);
    crate::leanh::lean_dec_ref(v_xs_3748_);
    return v_res_3755_;
}
pub unsafe fn _init_l_Lean_Meta_getExpectedNumArgsAux___closed__1() -> u64 {
    let mut v___x_3757_: u8 = 0;
    let mut v___x_3758_: u64 = 0;
    v___x_3757_ = 1;
    v___x_3758_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3757_);
    return v___x_3758_;
}
pub unsafe fn l_Lean_Meta_getExpectedNumArgsAux(
    mut v_e_3759_: *mut crate::leanh::LeanObject,
    mut v_a_3760_: *mut crate::leanh::LeanObject,
    mut v_a_3761_: *mut crate::leanh::LeanObject,
    mut v_a_3762_: *mut crate::leanh::LeanObject,
    mut v_a_3763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_3766_: u8 = 0;
    let mut v_ctxApprox_3767_: u8 = 0;
    let mut v_quasiPatternApprox_3768_: u8 = 0;
    let mut v_constApprox_3769_: u8 = 0;
    let mut v_isDefEqStuckEx_3770_: u8 = 0;
    let mut v_unificationHints_3771_: u8 = 0;
    let mut v_proofIrrelevance_3772_: u8 = 0;
    let mut v_assignSyntheticOpaque_3773_: u8 = 0;
    let mut v_offsetCnstrs_3774_: u8 = 0;
    let mut v_etaStruct_3775_: u8 = 0;
    let mut v_univApprox_3776_: u8 = 0;
    let mut v_iota_3777_: u8 = 0;
    let mut v_beta_3778_: u8 = 0;
    let mut v_proj_3779_: u8 = 0;
    let mut v_zeta_3780_: u8 = 0;
    let mut v_zetaDelta_3781_: u8 = 0;
    let mut v_zetaUnused_3782_: u8 = 0;
    let mut v_zetaHave_3783_: u8 = 0;
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3786_: u8 = 0;
    let mut v_trackZetaDelta_3787_: u8 = 0;
    let mut v_zetaDeltaSet_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_3794_: u8 = 0;
    let mut v_inTypeClassResolution_3795_: u8 = 0;
    let mut v_cacheInferType_3796_: u8 = 0;
    let mut v___x_3797_: u8 = 0;
    let mut v_config_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: u64 = 0;
    let mut v___x_3801_: u64 = 0;
    let mut v___x_3802_: u64 = 0;
    let mut v___f_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: u8 = 0;
    let mut v___x_3805_: u64 = 0;
    let mut v___x_3806_: u64 = 0;
    let mut v_key_3807_: u64 = 0;
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3812_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3765_ = l_Lean_Meta_Context_config(v_a_3760_);
                v_foApprox_3766_ = crate::leanh::lean_ctor_get_uint8(v___x_3765_, 0 as u32);
                v_ctxApprox_3767_ = crate::leanh::lean_ctor_get_uint8(v___x_3765_, 1 as u32);
                v_quasiPatternApprox_3768_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_3765_, 2 as u32);
                v_constApprox_3769_ = crate::leanh::lean_ctor_get_uint8(v___x_3765_, 3 as u32);
                v_isDefEqStuckEx_3770_ = crate::leanh::lean_ctor_get_uint8(v___x_3765_, 4 as u32);
                v_unificationHints_3771_ = crate::leanh::lean_ctor_get_uint8(v___x_3765_, 5 as u32);
                v_proofIrrelevance_3772_ = crate::leanh::lean_ctor_get_uint8(v___x_3765_, 6 as u32);
                v_assignSyntheticOpaque_3773_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_3765_, 7 as u32);
                v_offsetCnstrs_3774_ = crate::leanh::lean_ctor_get_uint8(v___x_3765_, 8 as u32);
                v_etaStruct_3775_ = crate::leanh::lean_ctor_get_uint8(v___x_3765_, 10 as u32);
                v_univApprox_3776_ = crate::leanh::lean_ctor_get_uint8(v___x_3765_, 11 as u32);
                v_iota_3777_ = crate::leanh::lean_ctor_get_uint8(v___x_3765_, 12 as u32);
                v_beta_3778_ = crate::leanh::lean_ctor_get_uint8(v___x_3765_, 13 as u32);
                v_proj_3779_ = crate::leanh::lean_ctor_get_uint8(v___x_3765_, 14 as u32);
                v_zeta_3780_ = crate::leanh::lean_ctor_get_uint8(v___x_3765_, 15 as u32);
                v_zetaDelta_3781_ = crate::leanh::lean_ctor_get_uint8(v___x_3765_, 16 as u32);
                v_zetaUnused_3782_ = crate::leanh::lean_ctor_get_uint8(v___x_3765_, 17 as u32);
                v_zetaHave_3783_ = crate::leanh::lean_ctor_get_uint8(v___x_3765_, 18 as u32);
                v_isSharedCheck_3812_ = (!crate::leanh::lean_is_exclusive(v___x_3765_)) as u8;
                if v_isSharedCheck_3812_ == 0 {
                    v___x_3785_ = v___x_3765_;
                    v_isShared_3786_ = v_isSharedCheck_3812_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3765_);
                    v___x_3785_ = crate::leanh::lean_box(0);
                    v_isShared_3786_ = v_isSharedCheck_3812_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_3787_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3760_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_3788_ = crate::leanh::lean_ctor_get(v_a_3760_, 1);
                v_lctx_3789_ = crate::leanh::lean_ctor_get(v_a_3760_, 2);
                v_localInstances_3790_ = crate::leanh::lean_ctor_get(v_a_3760_, 3);
                v_defEqCtx_x3f_3791_ = crate::leanh::lean_ctor_get(v_a_3760_, 4);
                v_synthPendingDepth_3792_ = crate::leanh::lean_ctor_get(v_a_3760_, 5);
                v_canUnfold_x3f_3793_ = crate::leanh::lean_ctor_get(v_a_3760_, 6);
                v_univApprox_3794_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3760_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_3795_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3760_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_3796_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_3760_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_3797_ = 1;
                if v_isShared_3786_ == 0 {
                    v_config_3799_ = v___x_3785_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3811_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3811_,
                        0 as u32,
                        v_foApprox_3766_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3811_,
                        1 as u32,
                        v_ctxApprox_3767_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3811_,
                        2 as u32,
                        v_quasiPatternApprox_3768_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3811_,
                        3 as u32,
                        v_constApprox_3769_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3811_,
                        4 as u32,
                        v_isDefEqStuckEx_3770_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3811_,
                        5 as u32,
                        v_unificationHints_3771_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3811_,
                        6 as u32,
                        v_proofIrrelevance_3772_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3811_,
                        7 as u32,
                        v_assignSyntheticOpaque_3773_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3811_,
                        8 as u32,
                        v_offsetCnstrs_3774_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3811_,
                        10 as u32,
                        v_etaStruct_3775_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3811_,
                        11 as u32,
                        v_univApprox_3776_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3811_,
                        12 as u32,
                        v_iota_3777_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3811_,
                        13 as u32,
                        v_beta_3778_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3811_,
                        14 as u32,
                        v_proj_3779_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3811_,
                        15 as u32,
                        v_zeta_3780_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3811_,
                        16 as u32,
                        v_zetaDelta_3781_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3811_,
                        17 as u32,
                        v_zetaUnused_3782_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3811_,
                        18 as u32,
                        v_zetaHave_3783_,
                    );
                    v_config_3799_ = v_reuseFailAlloc_3811_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(v_config_3799_, 9 as u32, v___x_3797_);
                v___x_3800_ = l_Lean_Meta_Context_configKey(v_a_3760_);
                v___x_3801_ = 3u64;
                v___x_3802_ = lean_uint64_shift_right(v___x_3800_, v___x_3801_);
                v___f_3803_ = l_Lean_Meta_getExpectedNumArgsAux___closed__0;
                v___x_3804_ = 0;
                v___x_3805_ = lean_uint64_shift_left(v___x_3802_, v___x_3801_);
                v___x_3806_ = crate::leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_getExpectedNumArgsAux___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Meta_getExpectedNumArgsAux___closed__1_once),
                    _init_l_Lean_Meta_getExpectedNumArgsAux___closed__1,
                );
                v_key_3807_ = lean_uint64_lor(v___x_3805_, v___x_3806_);
                v___x_3808_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_3808_, 0, v_config_3799_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_3808_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_3807_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_3793_);
                crate::leanh::lean_inc(v_synthPendingDepth_3792_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_3791_);
                crate::leanh::lean_inc_ref(v_localInstances_3790_);
                crate::leanh::lean_inc_ref(v_lctx_3789_);
                crate::leanh::lean_inc(v_zetaDeltaSet_3788_);
                v___x_3809_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_3809_, 0, v___x_3808_);
                crate::leanh::lean_ctor_set(v___x_3809_, 1, v_zetaDeltaSet_3788_);
                crate::leanh::lean_ctor_set(v___x_3809_, 2, v_lctx_3789_);
                crate::leanh::lean_ctor_set(v___x_3809_, 3, v_localInstances_3790_);
                crate::leanh::lean_ctor_set(v___x_3809_, 4, v_defEqCtx_x3f_3791_);
                crate::leanh::lean_ctor_set(v___x_3809_, 5, v_synthPendingDepth_3792_);
                crate::leanh::lean_ctor_set(v___x_3809_, 6, v_canUnfold_x3f_3793_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3809_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_3787_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3809_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_3794_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3809_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_3795_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3809_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_3796_,
                );
                v___x_3810_ = l_Lean_Meta_forallTelescopeReducing___at___00Lean_Meta_getExpectedNumArgsAux_spec__0___redArg(v_e_3759_, v___f_3803_, v___x_3804_, v___x_3804_, v___x_3809_, v_a_3761_, v_a_3762_, v_a_3763_);
                crate::leanh::lean_dec_ref_known(v___x_3809_, 7);
                return v___x_3810_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getExpectedNumArgsAux___boxed(
    mut v_e_3813_: *mut crate::leanh::LeanObject,
    mut v_a_3814_: *mut crate::leanh::LeanObject,
    mut v_a_3815_: *mut crate::leanh::LeanObject,
    mut v_a_3816_: *mut crate::leanh::LeanObject,
    mut v_a_3817_: *mut crate::leanh::LeanObject,
    mut v_a_3818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3819_ =
        l_Lean_Meta_getExpectedNumArgsAux(v_e_3813_, v_a_3814_, v_a_3815_, v_a_3816_, v_a_3817_);
    crate::leanh::lean_dec(v_a_3817_);
    crate::leanh::lean_dec_ref(v_a_3816_);
    crate::leanh::lean_dec(v_a_3815_);
    crate::leanh::lean_dec_ref(v_a_3814_);
    return v_res_3819_;
}
pub unsafe fn l_Lean_Meta_getExpectedNumArgs(
    mut v_e_3820_: *mut crate::leanh::LeanObject,
    mut v_a_3821_: *mut crate::leanh::LeanObject,
    mut v_a_3822_: *mut crate::leanh::LeanObject,
    mut v_a_3823_: *mut crate::leanh::LeanObject,
    mut v_a_3824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3830_: u8 = 0;
    let mut v_fst_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3835_: u8 = 0;
    let mut v_a_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3839_: u8 = 0;
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3843_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3826_ = l_Lean_Meta_getExpectedNumArgsAux(
                    v_e_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_,
                );
                if crate::leanh::lean_obj_tag(v___x_3826_) == 0 {
                    v_a_3827_ = crate::leanh::lean_ctor_get(v___x_3826_, 0);
                    v_isSharedCheck_3835_ = (!crate::leanh::lean_is_exclusive(v___x_3826_)) as u8;
                    if v_isSharedCheck_3835_ == 0 {
                        v___x_3829_ = v___x_3826_;
                        v_isShared_3830_ = v_isSharedCheck_3835_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3827_);
                        crate::leanh::lean_dec(v___x_3826_);
                        v___x_3829_ = crate::leanh::lean_box(0);
                        v_isShared_3830_ = v_isSharedCheck_3835_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3836_ = crate::leanh::lean_ctor_get(v___x_3826_, 0);
                    v_isSharedCheck_3843_ = (!crate::leanh::lean_is_exclusive(v___x_3826_)) as u8;
                    if v_isSharedCheck_3843_ == 0 {
                        v___x_3838_ = v___x_3826_;
                        v_isShared_3839_ = v_isSharedCheck_3843_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3836_);
                        crate::leanh::lean_dec(v___x_3826_);
                        v___x_3838_ = crate::leanh::lean_box(0);
                        v_isShared_3839_ = v_isSharedCheck_3843_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3831_ = crate::leanh::lean_ctor_get(v_a_3827_, 0);
                crate::leanh::lean_inc(v_fst_3831_);
                crate::leanh::lean_dec(v_a_3827_);
                if v_isShared_3830_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3829_, 0, v_fst_3831_);
                    v___x_3833_ = v___x_3829_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3834_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_fst_3831_);
                    v___x_3833_ = v_reuseFailAlloc_3834_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3833_;
            }
            3 => {
                if v_isShared_3839_ == 0 {
                    v___x_3841_ = v___x_3838_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3842_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3836_);
                    v___x_3841_ = v_reuseFailAlloc_3842_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3841_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getExpectedNumArgs___boxed(
    mut v_e_3844_: *mut crate::leanh::LeanObject,
    mut v_a_3845_: *mut crate::leanh::LeanObject,
    mut v_a_3846_: *mut crate::leanh::LeanObject,
    mut v_a_3847_: *mut crate::leanh::LeanObject,
    mut v_a_3848_: *mut crate::leanh::LeanObject,
    mut v_a_3849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3850_ =
        l_Lean_Meta_getExpectedNumArgs(v_e_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_);
    crate::leanh::lean_dec(v_a_3848_);
    crate::leanh::lean_dec_ref(v_a_3847_);
    crate::leanh::lean_dec(v_a_3846_);
    crate::leanh::lean_dec_ref(v_a_3845_);
    return v_res_3850_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3852_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__0;
    v___x_3853_ = l_Lean_stringToMessageData(v___x_3852_);
    return v___x_3853_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3855_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__2;
    v___x_3856_ = l_Lean_stringToMessageData(v___x_3855_);
    return v___x_3856_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3858_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__4;
    v___x_3859_ = l_Lean_stringToMessageData(v___x_3858_);
    return v___x_3859_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3863_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__7;
    v___x_3864_ = l_Lean_MessageData_ofFormat(v___x_3863_);
    return v___x_3864_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0(
    mut v___y_3867_: *mut crate::leanh::LeanObject,
    mut v_targetType_3868_: *mut crate::leanh::LeanObject,
    mut v___y_3869_: *mut crate::leanh::LeanObject,
    mut v_term_x3f_3870_: *mut crate::leanh::LeanObject,
    mut v_conclusionType_x3f_3871_: *mut crate::leanh::LeanObject,
    mut v___y_3872_: *mut crate::leanh::LeanObject,
    mut v___y_3873_: *mut crate::leanh::LeanObject,
    mut v___y_3874_: *mut crate::leanh::LeanObject,
    mut v___y_3875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3881_: u8 = 0;
    let mut v_fst_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3886_: u8 = 0;
    let mut v___y_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3918_: u8 = 0;
    let mut v_isSharedCheck_3919_: u8 = 0;
    let mut v_a_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3923_: u8 = 0;
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3927_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3877_ = l_Lean_Meta_addPPExplicitToExposeDiff(
                    v___y_3867_,
                    v_targetType_3868_,
                    v___y_3872_,
                    v___y_3873_,
                    v___y_3874_,
                    v___y_3875_,
                );
                if crate::leanh::lean_obj_tag(v___x_3877_) == 0 {
                    v_a_3878_ = crate::leanh::lean_ctor_get(v___x_3877_, 0);
                    v_isSharedCheck_3919_ = (!crate::leanh::lean_is_exclusive(v___x_3877_)) as u8;
                    if v_isSharedCheck_3919_ == 0 {
                        v___x_3880_ = v___x_3877_;
                        v_isShared_3881_ = v_isSharedCheck_3919_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3878_);
                        crate::leanh::lean_dec(v___x_3877_);
                        v___x_3880_ = crate::leanh::lean_box(0);
                        v_isShared_3881_ = v_isSharedCheck_3919_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_term_x3f_3870_);
                    crate::leanh::lean_dec_ref(v___y_3869_);
                    v_a_3920_ = crate::leanh::lean_ctor_get(v___x_3877_, 0);
                    v_isSharedCheck_3927_ = (!crate::leanh::lean_is_exclusive(v___x_3877_)) as u8;
                    if v_isSharedCheck_3927_ == 0 {
                        v___x_3922_ = v___x_3877_;
                        v_isShared_3923_ = v_isSharedCheck_3927_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3920_);
                        crate::leanh::lean_dec(v___x_3877_);
                        v___x_3922_ = crate::leanh::lean_box(0);
                        v_isShared_3923_ = v_isSharedCheck_3927_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_3882_ = crate::leanh::lean_ctor_get(v_a_3878_, 0);
                v_snd_3883_ = crate::leanh::lean_ctor_get(v_a_3878_, 1);
                v_isSharedCheck_3918_ = (!crate::leanh::lean_is_exclusive(v_a_3878_)) as u8;
                if v_isSharedCheck_3918_ == 0 {
                    v___x_3885_ = v_a_3878_;
                    v_isShared_3886_ = v_isSharedCheck_3918_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3883_);
                    crate::leanh::lean_inc(v_fst_3882_);
                    crate::leanh::lean_dec(v_a_3878_);
                    v___x_3885_ = crate::leanh::lean_box(0);
                    v_isShared_3886_ = v_isSharedCheck_3918_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_conclusionType_x3f_3871_) == 0 {
                    v___x_3916_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__9;
                    v___y_3906_ = v___x_3916_;
                    state = 6;
                    continue;
                } else {
                    v___x_3917_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__10;
                    v___y_3906_ = v___x_3917_;
                    state = 6;
                    continue;
                }
            }
            3 => {
                if v_isShared_3886_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3885_, 7);
                    crate::leanh::lean_ctor_set(v___x_3885_, 1, v___y_3890_);
                    crate::leanh::lean_ctor_set(v___x_3885_, 0, v___y_3889_);
                    v___x_3892_ = v___x_3885_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3904_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___y_3889_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3904_, 1, v___y_3890_);
                    v___x_3892_ = v_reuseFailAlloc_3904_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3893_ = l_Lean_indentExpr(v_fst_3882_);
                v___x_3894_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3894_, 0, v___x_3892_);
                crate::leanh::lean_ctor_set(v___x_3894_, 1, v___x_3893_);
                v___x_3895_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__1);
                v___x_3896_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3896_, 0, v___x_3894_);
                crate::leanh::lean_ctor_set(v___x_3896_, 1, v___x_3895_);
                v___x_3897_ = l_Lean_indentExpr(v_snd_3883_);
                v___x_3898_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3898_, 0, v___x_3896_);
                crate::leanh::lean_ctor_set(v___x_3898_, 1, v___x_3897_);
                v___x_3899_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3899_, 0, v___x_3898_);
                crate::leanh::lean_ctor_set(v___x_3899_, 1, v___y_3869_);
                v___x_3900_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3900_, 0, v___x_3899_);
                crate::leanh::lean_ctor_set(v___x_3900_, 1, v___y_3888_);
                if v_isShared_3881_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3880_, 0, v___x_3900_);
                    v___x_3902_ = v___x_3880_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3903_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3903_, 0, v___x_3900_);
                    v___x_3902_ = v_reuseFailAlloc_3903_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3902_;
            }
            6 => {
                crate::leanh::lean_inc(v_snd_3883_);
                crate::leanh::lean_inc(v_fst_3882_);
                v___x_3907_ = l_Lean_Meta_mkUnfoldAxiomsNote(
                    v_fst_3882_,
                    v_snd_3883_,
                    v___y_3872_,
                    v___y_3873_,
                    v___y_3874_,
                    v___y_3875_,
                );
                if crate::leanh::lean_obj_tag(v___x_3907_) == 0 {
                    v_a_3908_ = crate::leanh::lean_ctor_get(v___x_3907_, 0);
                    crate::leanh::lean_inc(v_a_3908_);
                    crate::leanh::lean_dec_ref_known(v___x_3907_, 1);
                    v___x_3909_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__3);
                    crate::leanh::lean_inc_ref(v___y_3906_);
                    v___x_3910_ = l_Lean_stringToMessageData(v___y_3906_);
                    v___x_3911_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3911_, 0, v___x_3909_);
                    crate::leanh::lean_ctor_set(v___x_3911_, 1, v___x_3910_);
                    v___x_3912_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5_once), _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__5);
                    v___x_3913_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3913_, 0, v___x_3911_);
                    crate::leanh::lean_ctor_set(v___x_3913_, 1, v___x_3912_);
                    if crate::leanh::lean_obj_tag(v_term_x3f_3870_) == 0 {
                        v___x_3914_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8_once), _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8);
                        v___y_3888_ = v_a_3908_;
                        v___y_3889_ = v___x_3913_;
                        v___y_3890_ = v___x_3914_;
                        state = 3;
                        continue;
                    } else {
                        v_val_3915_ = crate::leanh::lean_ctor_get(v_term_x3f_3870_, 0);
                        crate::leanh::lean_inc(v_val_3915_);
                        crate::leanh::lean_dec_ref_known(v_term_x3f_3870_, 1);
                        v___y_3888_ = v_a_3908_;
                        v___y_3889_ = v___x_3913_;
                        v___y_3890_ = v_val_3915_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3885_);
                    crate::leanh::lean_dec(v_snd_3883_);
                    crate::leanh::lean_dec(v_fst_3882_);
                    crate::leanh::lean_del_object(v___x_3880_);
                    crate::leanh::lean_dec(v_term_x3f_3870_);
                    crate::leanh::lean_dec_ref(v___y_3869_);
                    return v___x_3907_;
                }
            }
            7 => {
                if v_isShared_3923_ == 0 {
                    v___x_3925_ = v___x_3922_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3926_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
                    v___x_3925_ = v_reuseFailAlloc_3926_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3925_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___boxed(
    mut v___y_3928_: *mut crate::leanh::LeanObject,
    mut v_targetType_3929_: *mut crate::leanh::LeanObject,
    mut v___y_3930_: *mut crate::leanh::LeanObject,
    mut v_term_x3f_3931_: *mut crate::leanh::LeanObject,
    mut v_conclusionType_x3f_3932_: *mut crate::leanh::LeanObject,
    mut v___y_3933_: *mut crate::leanh::LeanObject,
    mut v___y_3934_: *mut crate::leanh::LeanObject,
    mut v___y_3935_: *mut crate::leanh::LeanObject,
    mut v___y_3936_: *mut crate::leanh::LeanObject,
    mut v___y_3937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3938_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0(
        v___y_3928_,
        v_targetType_3929_,
        v___y_3930_,
        v_term_x3f_3931_,
        v_conclusionType_x3f_3932_,
        v___y_3933_,
        v___y_3934_,
        v___y_3935_,
        v___y_3936_,
    );
    crate::leanh::lean_dec(v___y_3936_);
    crate::leanh::lean_dec_ref(v___y_3935_);
    crate::leanh::lean_dec(v___y_3934_);
    crate::leanh::lean_dec_ref(v___y_3933_);
    crate::leanh::lean_dec(v_conclusionType_x3f_3932_);
    return v_res_3938_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3943_ =
        l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__2;
    v___x_3944_ = l_Lean_stringToMessageData(v___x_3943_);
    return v___x_3944_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3946_ =
        l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__4;
    v___x_3947_ = l_Lean_stringToMessageData(v___x_3946_);
    return v___x_3947_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3949_ =
        l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__6;
    v___x_3950_ = l_Lean_stringToMessageData(v___x_3949_);
    return v___x_3950_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(
    mut v_mvarId_3951_: *mut crate::leanh::LeanObject,
    mut v_eType_3952_: *mut crate::leanh::LeanObject,
    mut v_conclusionType_x3f_3953_: *mut crate::leanh::LeanObject,
    mut v_targetType_3954_: *mut crate::leanh::LeanObject,
    mut v_term_x3f_3955_: *mut crate::leanh::LeanObject,
    mut v_a_3956_: *mut crate::leanh::LeanObject,
    mut v_a_3957_: *mut crate::leanh::LeanObject,
    mut v_a_3958_: *mut crate::leanh::LeanObject,
    mut v_a_3959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3961_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1;
                if crate::leanh::lean_obj_tag(v_conclusionType_x3f_3953_) == 0 {
                    crate::leanh::lean_inc_ref(v_eType_3952_);
                    v___y_3984_ = v_eType_3952_;
                    state = 3;
                    continue;
                } else {
                    v_val_3989_ = crate::leanh::lean_ctor_get(v_conclusionType_x3f_3953_, 0);
                    crate::leanh::lean_inc(v_val_3989_);
                    v___y_3984_ = v_val_3989_;
                    state = 3;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_targetType_3954_);
                v___f_3965_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                crate::leanh::lean_closure_set(v___f_3965_, 0, v___y_3963_);
                crate::leanh::lean_closure_set(v___f_3965_, 1, v_targetType_3954_);
                crate::leanh::lean_closure_set(v___f_3965_, 2, v___y_3964_);
                crate::leanh::lean_closure_set(v___f_3965_, 3, v_term_x3f_3955_);
                crate::leanh::lean_closure_set(v___f_3965_, 4, v_conclusionType_x3f_3953_);
                v___x_3966_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3967_ = lean_mk_empty_array_with_capacity(v___x_3966_);
                v___x_3968_ = lean_array_push(v___x_3967_, v_eType_3952_);
                v___x_3969_ = lean_array_push(v___x_3968_, v_targetType_3954_);
                v___x_3970_ = l_Lean_MessageData_ofLazyM(v___f_3965_, v___x_3969_);
                v___x_3971_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3971_, 0, v___x_3970_);
                v___x_3972_ = l_Lean_Meta_throwTacticEx___redArg(
                    v___x_3961_,
                    v_mvarId_3951_,
                    v___x_3971_,
                    v_a_3956_,
                    v_a_3957_,
                    v_a_3958_,
                    v_a_3959_,
                );
                return v___x_3972_;
            }
            2 => {
                crate::leanh::lean_inc_ref(v___y_3975_);
                v___x_3977_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3977_, 0, v___y_3975_);
                crate::leanh::lean_ctor_set(v___x_3977_, 1, v___y_3976_);
                v___x_3978_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3_once), _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__3);
                v___x_3979_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3979_, 0, v___x_3977_);
                crate::leanh::lean_ctor_set(v___x_3979_, 1, v___x_3978_);
                crate::leanh::lean_inc_ref(v_eType_3952_);
                v___x_3980_ = l_Lean_indentExpr(v_eType_3952_);
                v___x_3981_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3981_, 0, v___x_3979_);
                crate::leanh::lean_ctor_set(v___x_3981_, 1, v___x_3980_);
                v___x_3982_ = l_Lean_MessageData_note(v___x_3981_);
                v___y_3963_ = v___y_3974_;
                v___y_3964_ = v___x_3982_;
                state = 1;
                continue;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_conclusionType_x3f_3953_) == 0 {
                    v___x_3985_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5_once), _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__5);
                    v___y_3963_ = v___y_3984_;
                    v___y_3964_ = v___x_3985_;
                    state = 1;
                    continue;
                } else {
                    v___x_3986_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7_once), _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__7);
                    if crate::leanh::lean_obj_tag(v_term_x3f_3955_) == 0 {
                        v___x_3987_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8_once), _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___lam__0___closed__8);
                        v___y_3974_ = v___y_3984_;
                        v___y_3975_ = v___x_3986_;
                        v___y_3976_ = v___x_3987_;
                        state = 2;
                        continue;
                    } else {
                        v_val_3988_ = crate::leanh::lean_ctor_get(v_term_x3f_3955_, 0);
                        crate::leanh::lean_inc(v_val_3988_);
                        v___y_3974_ = v___y_3984_;
                        v___y_3975_ = v___x_3986_;
                        v___y_3976_ = v_val_3988_;
                        state = 2;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___boxed(
    mut v_mvarId_3990_: *mut crate::leanh::LeanObject,
    mut v_eType_3991_: *mut crate::leanh::LeanObject,
    mut v_conclusionType_x3f_3992_: *mut crate::leanh::LeanObject,
    mut v_targetType_3993_: *mut crate::leanh::LeanObject,
    mut v_term_x3f_3994_: *mut crate::leanh::LeanObject,
    mut v_a_3995_: *mut crate::leanh::LeanObject,
    mut v_a_3996_: *mut crate::leanh::LeanObject,
    mut v_a_3997_: *mut crate::leanh::LeanObject,
    mut v_a_3998_: *mut crate::leanh::LeanObject,
    mut v_a_3999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4000_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(
        v_mvarId_3990_,
        v_eType_3991_,
        v_conclusionType_x3f_3992_,
        v_targetType_3993_,
        v_term_x3f_3994_,
        v_a_3995_,
        v_a_3996_,
        v_a_3997_,
        v_a_3998_,
    );
    crate::leanh::lean_dec(v_a_3998_);
    crate::leanh::lean_dec_ref(v_a_3997_);
    crate::leanh::lean_dec(v_a_3996_);
    crate::leanh::lean_dec_ref(v_a_3995_);
    return v_res_4000_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(
    mut v_00_u03b1_4001_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4002_: *mut crate::leanh::LeanObject,
    mut v_eType_4003_: *mut crate::leanh::LeanObject,
    mut v_conclusionType_x3f_4004_: *mut crate::leanh::LeanObject,
    mut v_targetType_4005_: *mut crate::leanh::LeanObject,
    mut v_term_x3f_4006_: *mut crate::leanh::LeanObject,
    mut v_a_4007_: *mut crate::leanh::LeanObject,
    mut v_a_4008_: *mut crate::leanh::LeanObject,
    mut v_a_4009_: *mut crate::leanh::LeanObject,
    mut v_a_4010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4012_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(
        v_mvarId_4002_,
        v_eType_4003_,
        v_conclusionType_x3f_4004_,
        v_targetType_4005_,
        v_term_x3f_4006_,
        v_a_4007_,
        v_a_4008_,
        v_a_4009_,
        v_a_4010_,
    );
    return v___x_4012_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___boxed(
    mut v_00_u03b1_4013_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4014_: *mut crate::leanh::LeanObject,
    mut v_eType_4015_: *mut crate::leanh::LeanObject,
    mut v_conclusionType_x3f_4016_: *mut crate::leanh::LeanObject,
    mut v_targetType_4017_: *mut crate::leanh::LeanObject,
    mut v_term_x3f_4018_: *mut crate::leanh::LeanObject,
    mut v_a_4019_: *mut crate::leanh::LeanObject,
    mut v_a_4020_: *mut crate::leanh::LeanObject,
    mut v_a_4021_: *mut crate::leanh::LeanObject,
    mut v_a_4022_: *mut crate::leanh::LeanObject,
    mut v_a_4023_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4024_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError(
        v_00_u03b1_4013_,
        v_mvarId_4014_,
        v_eType_4015_,
        v_conclusionType_x3f_4016_,
        v_targetType_4017_,
        v_term_x3f_4018_,
        v_a_4019_,
        v_a_4020_,
        v_a_4021_,
        v_a_4022_,
    );
    crate::leanh::lean_dec(v_a_4022_);
    crate::leanh::lean_dec_ref(v_a_4021_);
    crate::leanh::lean_dec(v_a_4020_);
    crate::leanh::lean_dec_ref(v_a_4019_);
    return v_res_4024_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(
    mut v_a_4025_: *mut crate::leanh::LeanObject,
    mut v_snd_4026_: *mut crate::leanh::LeanObject,
    mut v_fst_4027_: *mut crate::leanh::LeanObject,
    mut v_____r_4028_: *mut crate::leanh::LeanObject,
    mut v_progressAfterEx_4029_: u8,
    mut v___y_4030_: *mut crate::leanh::LeanObject,
    mut v___y_4031_: *mut crate::leanh::LeanObject,
    mut v___y_4032_: *mut crate::leanh::LeanObject,
    mut v___y_4033_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4035_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4035_, 0, v_a_4025_);
    v___x_4036_ = crate::leanh::lean_box((v_progressAfterEx_4029_) as usize);
    v___x_4037_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4037_, 0, v___x_4036_);
    crate::leanh::lean_ctor_set(v___x_4037_, 1, v_snd_4026_);
    v___x_4038_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4038_, 0, v_fst_4027_);
    crate::leanh::lean_ctor_set(v___x_4038_, 1, v___x_4037_);
    v___x_4039_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4039_, 0, v___x_4035_);
    crate::leanh::lean_ctor_set(v___x_4039_, 1, v___x_4038_);
    v___x_4040_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4040_, 0, v___x_4039_);
    return v___x_4040_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0___boxed(
    mut v_a_4041_: *mut crate::leanh::LeanObject,
    mut v_snd_4042_: *mut crate::leanh::LeanObject,
    mut v_fst_4043_: *mut crate::leanh::LeanObject,
    mut v_____r_4044_: *mut crate::leanh::LeanObject,
    mut v_progressAfterEx_4045_: *mut crate::leanh::LeanObject,
    mut v___y_4046_: *mut crate::leanh::LeanObject,
    mut v___y_4047_: *mut crate::leanh::LeanObject,
    mut v___y_4048_: *mut crate::leanh::LeanObject,
    mut v___y_4049_: *mut crate::leanh::LeanObject,
    mut v___y_4050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_progressAfterEx_boxed_4051_: u8 = 0;
    let mut v_res_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_progressAfterEx_boxed_4051_ = (crate::leanh::lean_unbox(v_progressAfterEx_4045_) as u8);
    v_res_4052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_4041_, v_snd_4042_, v_fst_4043_, v_____r_4044_, v_progressAfterEx_boxed_4051_, v___y_4046_, v___y_4047_, v___y_4048_, v___y_4049_);
    crate::leanh::lean_dec(v___y_4049_);
    crate::leanh::lean_dec_ref(v___y_4048_);
    crate::leanh::lean_dec(v___y_4047_);
    crate::leanh::lean_dec_ref(v___y_4046_);
    return v_res_4052_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4056_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__1;
    v___x_4057_ = l_Lean_MessageData_ofFormat(v___x_4056_);
    return v___x_4057_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4058_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__2);
    v___x_4059_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4059_, 0, v___x_4058_);
    return v___x_4059_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(
    mut v_allowSynthFailures_4060_: u8,
    mut v_tacticName_4061_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4062_: *mut crate::leanh::LeanObject,
    mut v_as_4063_: *mut crate::leanh::LeanObject,
    mut v_sz_4064_: usize,
    mut v_i_4065_: usize,
    mut v_b_4066_: *mut crate::leanh::LeanObject,
    mut v___y_4067_: *mut crate::leanh::LeanObject,
    mut v___y_4068_: *mut crate::leanh::LeanObject,
    mut v___y_4069_: *mut crate::leanh::LeanObject,
    mut v___y_4070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: usize = 0;
    let mut v___x_4075_: usize = 0;
    let mut v_fst_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: u8 = 0;
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4091_: u8 = 0;
    let mut v_fst_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4097_: u8 = 0;
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: u8 = 0;
    let mut v___x_4106_: u8 = 0;
    let mut v___y_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4116_: u8 = 0;
    let mut v_fst_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4121_: u8 = 0;
    let mut v_val_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: u8 = 0;
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4137_: u8 = 0;
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4141_: u8 = 0;
    let mut v___x_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4157_: u8 = 0;
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4161_: u8 = 0;
    let mut v_isSharedCheck_4162_: u8 = 0;
    let mut v_isSharedCheck_4163_: u8 = 0;
    let mut v_unused_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: u8 = 0;
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: u8 = 0;
    let mut v___x_4179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4181_: u8 = 0;
    let mut v_a_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4185_: u8 = 0;
    let mut v___x_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4189_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4083_ = lean_usize_dec_lt(v_i_4065_, v_sz_4064_);
                if v___x_4083_ == 0 {
                    crate::leanh::lean_dec(v_mvarId_4062_);
                    crate::leanh::lean_dec(v_tacticName_4061_);
                    v___x_4084_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4084_, 0, v_b_4066_);
                    return v___x_4084_;
                } else {
                    v_a_4085_ = lean_array_uget_borrowed(v_as_4063_, v_i_4065_);
                    crate::leanh::lean_inc(v___y_4070_);
                    crate::leanh::lean_inc_ref(v___y_4069_);
                    crate::leanh::lean_inc(v___y_4068_);
                    crate::leanh::lean_inc_ref(v___y_4067_);
                    crate::leanh::lean_inc(v_a_4085_);
                    v___x_4086_ = lean_infer_type(
                        v_a_4085_,
                        v___y_4067_,
                        v___y_4068_,
                        v___y_4069_,
                        v___y_4070_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4086_) == 0 {
                        v_snd_4087_ = crate::leanh::lean_ctor_get(v_b_4066_, 1);
                        crate::leanh::lean_inc(v_snd_4087_);
                        v_a_4088_ = crate::leanh::lean_ctor_get(v___x_4086_, 0);
                        v_isSharedCheck_4181_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4086_)) as u8;
                        if v_isSharedCheck_4181_ == 0 {
                            v___x_4090_ = v___x_4086_;
                            v_isShared_4091_ = v_isSharedCheck_4181_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4088_);
                            crate::leanh::lean_dec(v___x_4086_);
                            v___x_4090_ = crate::leanh::lean_box(0);
                            v_isShared_4091_ = v_isSharedCheck_4181_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_4066_);
                        crate::leanh::lean_dec(v_mvarId_4062_);
                        crate::leanh::lean_dec(v_tacticName_4061_);
                        v_a_4182_ = crate::leanh::lean_ctor_get(v___x_4086_, 0);
                        v_isSharedCheck_4189_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4086_)) as u8;
                        if v_isSharedCheck_4189_ == 0 {
                            v___x_4184_ = v___x_4086_;
                            v_isShared_4185_ = v_isSharedCheck_4189_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4182_);
                            crate::leanh::lean_dec(v___x_4086_);
                            v___x_4184_ = crate::leanh::lean_box(0);
                            v_isShared_4185_ = v_isSharedCheck_4189_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4074_ = 1usize;
                v___x_4075_ = lean_usize_add(v_i_4065_, v___x_4074_);
                v_i_4065_ = v___x_4075_;
                v_b_4066_ = v_a_4073_;
                state = 0;
                continue;
            }
            2 => {
                v___x_4081_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4081_, 0, v_fst_4079_);
                crate::leanh::lean_ctor_set(v___x_4081_, 1, v_snd_4080_);
                v___x_4082_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4082_, 0, v_fst_4078_);
                crate::leanh::lean_ctor_set(v___x_4082_, 1, v___x_4081_);
                v_a_4073_ = v___x_4082_;
                state = 1;
                continue;
            }
            3 => {
                v_fst_4092_ = crate::leanh::lean_ctor_get(v_b_4066_, 0);
                crate::leanh::lean_inc(v_fst_4092_);
                crate::leanh::lean_dec_ref(v_b_4066_);
                v_fst_4093_ = crate::leanh::lean_ctor_get(v_snd_4087_, 0);
                crate::leanh::lean_inc(v_fst_4093_);
                v_snd_4094_ = crate::leanh::lean_ctor_get(v_snd_4087_, 1);
                crate::leanh::lean_inc(v_snd_4094_);
                crate::leanh::lean_dec(v_snd_4087_);
                v___x_4169_ = crate::leanh::lean_box(0);
                v___x_4170_ = l_Lean_Meta_synthInstance(
                    v_a_4088_,
                    v___x_4169_,
                    v___y_4067_,
                    v___y_4068_,
                    v___y_4069_,
                    v___y_4070_,
                );
                if crate::leanh::lean_obj_tag(v___x_4170_) == 0 {
                    v_a_4171_ = crate::leanh::lean_ctor_get(v___x_4170_, 0);
                    crate::leanh::lean_inc(v_a_4171_);
                    crate::leanh::lean_dec_ref_known(v___x_4170_, 1);
                    v___x_4172_ = lean_array_get_size(v_snd_4094_);
                    v___x_4173_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4174_ = lean_nat_dec_eq(v___x_4172_, v___x_4173_);
                    if v___x_4174_ == 0 {
                        v___x_4175_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_snd_4094_);
                        v___x_4176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_4171_, v_snd_4094_, v_fst_4092_, v___x_4175_, v___x_4083_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
                        v___y_4108_ = v___x_4176_;
                        state = 7;
                        continue;
                    } else {
                        v___x_4177_ = crate::leanh::lean_box(0);
                        v___x_4178_ = (crate::leanh::lean_unbox(v_fst_4093_) as u8);
                        crate::leanh::lean_inc(v_snd_4094_);
                        v___x_4179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___lam__0(v_a_4171_, v_snd_4094_, v_fst_4092_, v___x_4177_, v___x_4178_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
                        v___y_4108_ = v___x_4179_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_4092_);
                    v_a_4180_ = crate::leanh::lean_ctor_get(v___x_4170_, 0);
                    crate::leanh::lean_inc(v_a_4180_);
                    crate::leanh::lean_dec_ref_known(v___x_4170_, 1);
                    v_a_4104_ = v_a_4180_;
                    state = 6;
                    continue;
                }
            }
            4 => {
                if v___y_4097_ == 0 {
                    crate::leanh::lean_del_object(v___x_4090_);
                    v___x_4098_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4098_, 0, v___y_4096_);
                    crate::leanh::lean_inc(v_a_4085_);
                    v___x_4099_ = lean_array_push(v_snd_4094_, v_a_4085_);
                    v_fst_4078_ = v___x_4098_;
                    v_fst_4079_ = v_fst_4093_;
                    v_snd_4080_ = v___x_4099_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_snd_4094_);
                    crate::leanh::lean_dec(v_fst_4093_);
                    crate::leanh::lean_dec(v_mvarId_4062_);
                    crate::leanh::lean_dec(v_tacticName_4061_);
                    if v_isShared_4091_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4090_, 1);
                        crate::leanh::lean_ctor_set(v___x_4090_, 0, v___y_4096_);
                        v___x_4101_ = v___x_4090_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4102_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4102_, 0, v___y_4096_);
                        v___x_4101_ = v_reuseFailAlloc_4102_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_4101_;
            }
            6 => {
                v___x_4105_ = l_Lean_Exception_isInterrupt(v_a_4104_);
                if v___x_4105_ == 0 {
                    crate::leanh::lean_inc_ref(v_a_4104_);
                    v___x_4106_ = l_Lean_Exception_isRuntime(v_a_4104_);
                    v___y_4096_ = v_a_4104_;
                    v___y_4097_ = v___x_4106_;
                    state = 4;
                    continue;
                } else {
                    v___y_4096_ = v_a_4104_;
                    v___y_4097_ = v___x_4105_;
                    state = 4;
                    continue;
                }
            }
            7 => {
                if crate::leanh::lean_obj_tag(v___y_4108_) == 0 {
                    crate::leanh::lean_dec(v_snd_4094_);
                    crate::leanh::lean_dec(v_fst_4093_);
                    crate::leanh::lean_del_object(v___x_4090_);
                    v_a_4109_ = crate::leanh::lean_ctor_get(v___y_4108_, 0);
                    crate::leanh::lean_inc(v_a_4109_);
                    crate::leanh::lean_dec_ref_known(v___y_4108_, 1);
                    v_snd_4110_ = crate::leanh::lean_ctor_get(v_a_4109_, 1);
                    crate::leanh::lean_inc(v_snd_4110_);
                    v_snd_4111_ = crate::leanh::lean_ctor_get(v_snd_4110_, 1);
                    crate::leanh::lean_inc(v_snd_4111_);
                    v_fst_4112_ = crate::leanh::lean_ctor_get(v_a_4109_, 0);
                    crate::leanh::lean_inc(v_fst_4112_);
                    crate::leanh::lean_dec(v_a_4109_);
                    if crate::leanh::lean_obj_tag(v_fst_4112_) == 1 {
                        v_fst_4113_ = crate::leanh::lean_ctor_get(v_snd_4110_, 0);
                        v_isSharedCheck_4163_ =
                            (!crate::leanh::lean_is_exclusive(v_snd_4110_)) as u8;
                        if v_isSharedCheck_4163_ == 0 {
                            v_unused_4164_ = crate::leanh::lean_ctor_get(v_snd_4110_, 1);
                            crate::leanh::lean_dec(v_unused_4164_);
                            v___x_4115_ = v_snd_4110_;
                            v_isShared_4116_ = v_isSharedCheck_4163_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_fst_4113_);
                            crate::leanh::lean_dec(v_snd_4110_);
                            v___x_4115_ = crate::leanh::lean_box(0);
                            v_isShared_4116_ = v_isSharedCheck_4163_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_4112_);
                        v_fst_4165_ = crate::leanh::lean_ctor_get(v_snd_4110_, 0);
                        crate::leanh::lean_inc(v_fst_4165_);
                        crate::leanh::lean_dec(v_snd_4110_);
                        v_fst_4166_ = crate::leanh::lean_ctor_get(v_snd_4111_, 0);
                        crate::leanh::lean_inc(v_fst_4166_);
                        v_snd_4167_ = crate::leanh::lean_ctor_get(v_snd_4111_, 1);
                        crate::leanh::lean_inc(v_snd_4167_);
                        crate::leanh::lean_dec(v_snd_4111_);
                        v_fst_4078_ = v_fst_4165_;
                        v_fst_4079_ = v_fst_4166_;
                        v_snd_4080_ = v_snd_4167_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_4168_ = crate::leanh::lean_ctor_get(v___y_4108_, 0);
                    crate::leanh::lean_inc(v_a_4168_);
                    crate::leanh::lean_dec_ref_known(v___y_4108_, 1);
                    v_a_4104_ = v_a_4168_;
                    state = 6;
                    continue;
                }
            }
            8 => {
                v_fst_4117_ = crate::leanh::lean_ctor_get(v_snd_4111_, 0);
                v_snd_4118_ = crate::leanh::lean_ctor_get(v_snd_4111_, 1);
                v_isSharedCheck_4162_ = (!crate::leanh::lean_is_exclusive(v_snd_4111_)) as u8;
                if v_isSharedCheck_4162_ == 0 {
                    v___x_4120_ = v_snd_4111_;
                    v_isShared_4121_ = v_isSharedCheck_4162_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4118_);
                    crate::leanh::lean_inc(v_fst_4117_);
                    crate::leanh::lean_dec(v_snd_4111_);
                    v___x_4120_ = crate::leanh::lean_box(0);
                    v_isShared_4121_ = v_isSharedCheck_4162_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_val_4122_ = crate::leanh::lean_ctor_get(v_fst_4112_, 0);
                crate::leanh::lean_inc(v_val_4122_);
                crate::leanh::lean_dec_ref_known(v_fst_4112_, 1);
                crate::leanh::lean_inc(v_a_4085_);
                v___x_4123_ = l_Lean_Meta_isExprDefEq(
                    v_a_4085_,
                    v_val_4122_,
                    v___y_4067_,
                    v___y_4068_,
                    v___y_4069_,
                    v___y_4070_,
                );
                if crate::leanh::lean_obj_tag(v___x_4123_) == 0 {
                    v_a_4124_ = crate::leanh::lean_ctor_get(v___x_4123_, 0);
                    crate::leanh::lean_inc(v_a_4124_);
                    crate::leanh::lean_dec_ref_known(v___x_4123_, 1);
                    v___x_4125_ = (crate::leanh::lean_unbox(v_a_4124_) as u8);
                    crate::leanh::lean_dec(v_a_4124_);
                    if v___x_4125_ == 0 {
                        if v_allowSynthFailures_4060_ == 0 {
                            v___x_4126_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___closed__3);
                            crate::leanh::lean_inc(v_mvarId_4062_);
                            crate::leanh::lean_inc(v_tacticName_4061_);
                            v___x_4127_ = l_Lean_Meta_throwTacticEx___redArg(
                                v_tacticName_4061_,
                                v_mvarId_4062_,
                                v___x_4126_,
                                v___y_4067_,
                                v___y_4068_,
                                v___y_4069_,
                                v___y_4070_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4127_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_4127_, 1);
                                if v_isShared_4121_ == 0 {
                                    v___x_4129_ = v___x_4120_;
                                    state = 10;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4133_ =
                                        crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4133_,
                                        0,
                                        v_fst_4117_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4133_,
                                        1,
                                        v_snd_4118_,
                                    );
                                    v___x_4129_ = v_reuseFailAlloc_4133_;
                                    state = 10;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_4120_);
                                crate::leanh::lean_dec(v_snd_4118_);
                                crate::leanh::lean_dec(v_fst_4117_);
                                crate::leanh::lean_del_object(v___x_4115_);
                                crate::leanh::lean_dec(v_fst_4113_);
                                crate::leanh::lean_dec(v_mvarId_4062_);
                                crate::leanh::lean_dec(v_tacticName_4061_);
                                v_a_4134_ = crate::leanh::lean_ctor_get(v___x_4127_, 0);
                                v_isSharedCheck_4141_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4127_)) as u8;
                                if v_isSharedCheck_4141_ == 0 {
                                    v___x_4136_ = v___x_4127_;
                                    v_isShared_4137_ = v_isSharedCheck_4141_;
                                    state = 12;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4134_);
                                    crate::leanh::lean_dec(v___x_4127_);
                                    v___x_4136_ = crate::leanh::lean_box(0);
                                    v_isShared_4137_ = v_isSharedCheck_4141_;
                                    state = 12;
                                    continue;
                                }
                            }
                        } else {
                            if v_isShared_4121_ == 0 {
                                v___x_4143_ = v___x_4120_;
                                state = 14;
                                continue;
                            } else {
                                v_reuseFailAlloc_4147_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_fst_4117_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4147_, 1, v_snd_4118_);
                                v___x_4143_ = v_reuseFailAlloc_4147_;
                                state = 14;
                                continue;
                            }
                        }
                    } else {
                        if v_isShared_4121_ == 0 {
                            v___x_4149_ = v___x_4120_;
                            state = 16;
                            continue;
                        } else {
                            v_reuseFailAlloc_4153_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_fst_4117_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4153_, 1, v_snd_4118_);
                            v___x_4149_ = v_reuseFailAlloc_4153_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4120_);
                    crate::leanh::lean_dec(v_snd_4118_);
                    crate::leanh::lean_dec(v_fst_4117_);
                    crate::leanh::lean_del_object(v___x_4115_);
                    crate::leanh::lean_dec(v_fst_4113_);
                    crate::leanh::lean_dec(v_mvarId_4062_);
                    crate::leanh::lean_dec(v_tacticName_4061_);
                    v_a_4154_ = crate::leanh::lean_ctor_get(v___x_4123_, 0);
                    v_isSharedCheck_4161_ = (!crate::leanh::lean_is_exclusive(v___x_4123_)) as u8;
                    if v_isSharedCheck_4161_ == 0 {
                        v___x_4156_ = v___x_4123_;
                        v_isShared_4157_ = v_isSharedCheck_4161_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4154_);
                        crate::leanh::lean_dec(v___x_4123_);
                        v___x_4156_ = crate::leanh::lean_box(0);
                        v_isShared_4157_ = v_isSharedCheck_4161_;
                        state = 18;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_4116_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4115_, 1, v___x_4129_);
                    v___x_4131_ = v___x_4115_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4132_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_fst_4113_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4132_, 1, v___x_4129_);
                    v___x_4131_ = v_reuseFailAlloc_4132_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v_a_4073_ = v___x_4131_;
                state = 1;
                continue;
            }
            12 => {
                if v_isShared_4137_ == 0 {
                    v___x_4139_ = v___x_4136_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4140_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
                    v___x_4139_ = v_reuseFailAlloc_4140_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4139_;
            }
            14 => {
                if v_isShared_4116_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4115_, 1, v___x_4143_);
                    v___x_4145_ = v___x_4115_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4146_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_fst_4113_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 1, v___x_4143_);
                    v___x_4145_ = v_reuseFailAlloc_4146_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v_a_4073_ = v___x_4145_;
                state = 1;
                continue;
            }
            16 => {
                if v_isShared_4116_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4115_, 1, v___x_4149_);
                    v___x_4151_ = v___x_4115_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4152_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_fst_4113_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4152_, 1, v___x_4149_);
                    v___x_4151_ = v_reuseFailAlloc_4152_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v_a_4073_ = v___x_4151_;
                state = 1;
                continue;
            }
            18 => {
                if v_isShared_4157_ == 0 {
                    v___x_4159_ = v___x_4156_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_4160_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_a_4154_);
                    v___x_4159_ = v_reuseFailAlloc_4160_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_4159_;
            }
            20 => {
                if v_isShared_4185_ == 0 {
                    v___x_4187_ = v___x_4184_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_4188_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_a_4182_);
                    v___x_4187_ = v_reuseFailAlloc_4188_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_4187_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0___boxed(
    mut v_allowSynthFailures_4190_: *mut crate::leanh::LeanObject,
    mut v_tacticName_4191_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4192_: *mut crate::leanh::LeanObject,
    mut v_as_4193_: *mut crate::leanh::LeanObject,
    mut v_sz_4194_: *mut crate::leanh::LeanObject,
    mut v_i_4195_: *mut crate::leanh::LeanObject,
    mut v_b_4196_: *mut crate::leanh::LeanObject,
    mut v___y_4197_: *mut crate::leanh::LeanObject,
    mut v___y_4198_: *mut crate::leanh::LeanObject,
    mut v___y_4199_: *mut crate::leanh::LeanObject,
    mut v___y_4200_: *mut crate::leanh::LeanObject,
    mut v___y_4201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowSynthFailures_boxed_4202_: u8 = 0;
    let mut v_sz_boxed_4203_: usize = 0;
    let mut v_i_boxed_4204_: usize = 0;
    let mut v_res_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowSynthFailures_boxed_4202_ = (crate::leanh::lean_unbox(v_allowSynthFailures_4190_) as u8);
    v_sz_boxed_4203_ = crate::leanh::lean_unbox_usize(v_sz_4194_);
    crate::leanh::lean_dec(v_sz_4194_);
    v_i_boxed_4204_ = crate::leanh::lean_unbox_usize(v_i_4195_);
    crate::leanh::lean_dec(v_i_4195_);
    v_res_4205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_boxed_4202_, v_tacticName_4191_, v_mvarId_4192_, v_as_4193_, v_sz_boxed_4203_, v_i_boxed_4204_, v_b_4196_, v___y_4197_, v___y_4198_, v___y_4199_, v___y_4200_);
    crate::leanh::lean_dec(v___y_4200_);
    crate::leanh::lean_dec_ref(v___y_4199_);
    crate::leanh::lean_dec(v___y_4198_);
    crate::leanh::lean_dec_ref(v___y_4197_);
    crate::leanh::lean_dec_ref(v_as_4193_);
    return v_res_4205_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(
    mut v_tacticName_4215_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4216_: *mut crate::leanh::LeanObject,
    mut v_allowSynthFailures_4217_: u8,
    mut v_mvars_4218_: *mut crate::leanh::LeanObject,
    mut v_a_4219_: *mut crate::leanh::LeanObject,
    mut v_a_4220_: *mut crate::leanh::LeanObject,
    mut v_a_4221_: *mut crate::leanh::LeanObject,
    mut v_a_4222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_postponed_4224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4226_: usize = 0;
    let mut v___x_4227_: usize = 0;
    let mut v___x_4228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4232_: u8 = 0;
    let mut v_fst_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: u8 = 0;
    let mut v_val_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4251_: u8 = 0;
    let mut v_a_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4255_: u8 = 0;
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4259_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_postponed_4224_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0;
                v___x_4225_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__2;
                v_sz_4226_ = lean_array_size(v_mvars_4218_);
                v___x_4227_ = 0usize;
                v___x_4228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step_spec__0(v_allowSynthFailures_4217_, v_tacticName_4215_, v_mvarId_4216_, v_mvars_4218_, v_sz_4226_, v___x_4227_, v___x_4225_, v_a_4219_, v_a_4220_, v_a_4221_, v_a_4222_);
                if crate::leanh::lean_obj_tag(v___x_4228_) == 0 {
                    v_a_4229_ = crate::leanh::lean_ctor_get(v___x_4228_, 0);
                    v_isSharedCheck_4251_ = (!crate::leanh::lean_is_exclusive(v___x_4228_)) as u8;
                    if v_isSharedCheck_4251_ == 0 {
                        v___x_4231_ = v___x_4228_;
                        v_isShared_4232_ = v_isSharedCheck_4251_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4229_);
                        crate::leanh::lean_dec(v___x_4228_);
                        v___x_4231_ = crate::leanh::lean_box(0);
                        v_isShared_4232_ = v_isSharedCheck_4251_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4252_ = crate::leanh::lean_ctor_get(v___x_4228_, 0);
                    v_isSharedCheck_4259_ = (!crate::leanh::lean_is_exclusive(v___x_4228_)) as u8;
                    if v_isSharedCheck_4259_ == 0 {
                        v___x_4254_ = v___x_4228_;
                        v_isShared_4255_ = v_isSharedCheck_4259_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4252_);
                        crate::leanh::lean_dec(v___x_4228_);
                        v___x_4254_ = crate::leanh::lean_box(0);
                        v_isShared_4255_ = v_isSharedCheck_4259_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4233_ = crate::leanh::lean_ctor_get(v_a_4229_, 0);
                crate::leanh::lean_inc(v_fst_4233_);
                if crate::leanh::lean_obj_tag(v_fst_4233_) == 1 {
                    v_snd_4234_ = crate::leanh::lean_ctor_get(v_a_4229_, 1);
                    crate::leanh::lean_inc(v_snd_4234_);
                    crate::leanh::lean_dec(v_a_4229_);
                    v_fst_4235_ = crate::leanh::lean_ctor_get(v_snd_4234_, 0);
                    v___x_4236_ = (crate::leanh::lean_unbox(v_fst_4235_) as u8);
                    if v___x_4236_ == 0 {
                        crate::leanh::lean_dec(v_snd_4234_);
                        if v_allowSynthFailures_4217_ == 0 {
                            v_val_4237_ = crate::leanh::lean_ctor_get(v_fst_4233_, 0);
                            crate::leanh::lean_inc(v_val_4237_);
                            crate::leanh::lean_dec_ref_known(v_fst_4233_, 1);
                            if v_isShared_4232_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_4231_, 1);
                                crate::leanh::lean_ctor_set(v___x_4231_, 0, v_val_4237_);
                                v___x_4239_ = v___x_4231_;
                                state = 2;
                                continue;
                            } else {
                                v_reuseFailAlloc_4240_ =
                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_val_4237_);
                                v___x_4239_ = v_reuseFailAlloc_4240_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_fst_4233_, 1);
                            if v_isShared_4232_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4231_, 0, v_postponed_4224_);
                                v___x_4242_ = v___x_4231_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_4243_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4243_,
                                    0,
                                    v_postponed_4224_,
                                );
                                v___x_4242_ = v_reuseFailAlloc_4243_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_fst_4233_, 1);
                        v_snd_4244_ = crate::leanh::lean_ctor_get(v_snd_4234_, 1);
                        crate::leanh::lean_inc(v_snd_4244_);
                        crate::leanh::lean_dec(v_snd_4234_);
                        if v_isShared_4232_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4231_, 0, v_snd_4244_);
                            v___x_4246_ = v___x_4231_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4247_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4247_, 0, v_snd_4244_);
                            v___x_4246_ = v_reuseFailAlloc_4247_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fst_4233_);
                    crate::leanh::lean_dec(v_a_4229_);
                    if v_isShared_4232_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4231_, 0, v_postponed_4224_);
                        v___x_4249_ = v___x_4231_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4250_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4250_, 0, v_postponed_4224_);
                        v___x_4249_ = v_reuseFailAlloc_4250_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4239_;
            }
            3 => {
                return v___x_4242_;
            }
            4 => {
                return v___x_4246_;
            }
            5 => {
                return v___x_4249_;
            }
            6 => {
                if v_isShared_4255_ == 0 {
                    v___x_4257_ = v___x_4254_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4258_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
                    v___x_4257_ = v_reuseFailAlloc_4258_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4257_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___boxed(
    mut v_tacticName_4260_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4261_: *mut crate::leanh::LeanObject,
    mut v_allowSynthFailures_4262_: *mut crate::leanh::LeanObject,
    mut v_mvars_4263_: *mut crate::leanh::LeanObject,
    mut v_a_4264_: *mut crate::leanh::LeanObject,
    mut v_a_4265_: *mut crate::leanh::LeanObject,
    mut v_a_4266_: *mut crate::leanh::LeanObject,
    mut v_a_4267_: *mut crate::leanh::LeanObject,
    mut v_a_4268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowSynthFailures_boxed_4269_: u8 = 0;
    let mut v_res_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowSynthFailures_boxed_4269_ = (crate::leanh::lean_unbox(v_allowSynthFailures_4262_) as u8);
    v_res_4270_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(
        v_tacticName_4260_,
        v_mvarId_4261_,
        v_allowSynthFailures_boxed_4269_,
        v_mvars_4263_,
        v_a_4264_,
        v_a_4265_,
        v_a_4266_,
        v_a_4267_,
    );
    crate::leanh::lean_dec(v_a_4267_);
    crate::leanh::lean_dec_ref(v_a_4266_);
    crate::leanh::lean_dec(v_a_4265_);
    crate::leanh::lean_dec_ref(v_a_4264_);
    crate::leanh::lean_dec_ref(v_mvars_4263_);
    return v_res_4270_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_keys_4271_: *mut crate::leanh::LeanObject,
    mut v_i_4272_: *mut crate::leanh::LeanObject,
    mut v_k_4273_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: u8 = 0;
    let mut v_k_x27_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: u8 = 0;
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4274_ = lean_array_get_size(v_keys_4271_);
                v___x_4275_ = lean_nat_dec_lt(v_i_4272_, v___x_4274_);
                if v___x_4275_ == 0 {
                    crate::leanh::lean_dec(v_i_4272_);
                    return v___x_4275_;
                } else {
                    v_k_x27_4276_ = lean_array_fget_borrowed(v_keys_4271_, v_i_4272_);
                    v___x_4277_ = l_Lean_instBEqMVarId_beq(v_k_4273_, v_k_x27_4276_);
                    if v___x_4277_ == 0 {
                        v___x_4278_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_4279_ = lean_nat_add(v_i_4272_, v___x_4278_);
                        crate::leanh::lean_dec(v_i_4272_);
                        v_i_4272_ = v___x_4279_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_4272_);
                        return v___x_4277_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_keys_4281_: *mut crate::leanh::LeanObject,
    mut v_i_4282_: *mut crate::leanh::LeanObject,
    mut v_k_4283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4284_: u8 = 0;
    let mut v_r_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4284_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_4281_, v_i_4282_, v_k_4283_);
    crate::leanh::lean_dec(v_k_4283_);
    crate::leanh::lean_dec_ref(v_keys_4281_);
    v_r_4285_ = crate::leanh::lean_box((v_res_4284_) as usize);
    return v_r_4285_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_4286_: usize = 0;
    let mut v___x_4287_: usize = 0;
    let mut v___x_4288_: usize = 0;
    v___x_4286_ = 5usize;
    v___x_4287_ = 1usize;
    v___x_4288_ = lean_usize_shift_left(v___x_4287_, v___x_4286_);
    return v___x_4288_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_4289_: usize = 0;
    let mut v___x_4290_: usize = 0;
    let mut v___x_4291_: usize = 0;
    v___x_4289_ = 1usize;
    v___x_4290_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_4291_ = lean_usize_sub(v___x_4290_, v___x_4289_);
    return v___x_4291_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(
    mut v_x_4292_: *mut crate::leanh::LeanObject,
    mut v_x_4293_: usize,
    mut v_x_4294_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_es_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: usize = 0;
    let mut v___x_4298_: usize = 0;
    let mut v___x_4299_: usize = 0;
    let mut v_j_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: u8 = 0;
    let mut v_node_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: usize = 0;
    let mut v___x_4307_: u8 = 0;
    let mut v_ks_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4292_) == 0 {
                    v_es_4295_ = crate::leanh::lean_ctor_get(v_x_4292_, 0);
                    v___x_4296_ = crate::leanh::lean_box(2);
                    v___x_4297_ = 5usize;
                    v___x_4298_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_4299_ = lean_usize_land(v_x_4293_, v___x_4298_);
                    v_j_4300_ = lean_usize_to_nat(v___x_4299_);
                    v___x_4301_ = lean_array_get_borrowed(v___x_4296_, v_es_4295_, v_j_4300_);
                    crate::leanh::lean_dec(v_j_4300_);
                    match crate::leanh::lean_obj_tag(v___x_4301_) {
                        0 => {
                            v_key_4302_ = crate::leanh::lean_ctor_get(v___x_4301_, 0);
                            v___x_4303_ = l_Lean_instBEqMVarId_beq(v_x_4294_, v_key_4302_);
                            return v___x_4303_;
                        }
                        1 => {
                            v_node_4304_ = crate::leanh::lean_ctor_get(v___x_4301_, 0);
                            v___x_4305_ = lean_usize_shift_right(v_x_4293_, v___x_4297_);
                            v_x_4292_ = v_node_4304_;
                            v_x_4293_ = v___x_4305_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4307_ = 0;
                            return v___x_4307_;
                        }
                    }
                } else {
                    v_ks_4308_ = crate::leanh::lean_ctor_get(v_x_4292_, 0);
                    v___x_4309_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4310_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_ks_4308_, v___x_4309_, v_x_4294_);
                    return v___x_4310_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_4311_: *mut crate::leanh::LeanObject,
    mut v_x_4312_: *mut crate::leanh::LeanObject,
    mut v_x_4313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_3030__boxed_4314_: usize = 0;
    let mut v_res_4315_: u8 = 0;
    let mut v_r_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_3030__boxed_4314_ = crate::leanh::lean_unbox_usize(v_x_4312_);
    crate::leanh::lean_dec(v_x_4312_);
    v_res_4315_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_4311_, v_x_3030__boxed_4314_, v_x_4313_);
    crate::leanh::lean_dec(v_x_4313_);
    crate::leanh::lean_dec_ref(v_x_4311_);
    v_r_4316_ = crate::leanh::lean_box((v_res_4315_) as usize);
    return v_r_4316_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(
    mut v_x_4317_: *mut crate::leanh::LeanObject,
    mut v_x_4318_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4319_: u64 = 0;
    let mut v___x_4320_: usize = 0;
    let mut v___x_4321_: u8 = 0;
    v___x_4319_ = l_Lean_instHashableMVarId_hash(v_x_4318_);
    v___x_4320_ = lean_uint64_to_usize(v___x_4319_);
    v___x_4321_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_4317_, v___x_4320_, v_x_4318_);
    return v___x_4321_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg___boxed(
    mut v_x_4322_: *mut crate::leanh::LeanObject,
    mut v_x_4323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4324_: u8 = 0;
    let mut v_r_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4324_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_4322_, v_x_4323_);
    crate::leanh::lean_dec(v_x_4323_);
    crate::leanh::lean_dec_ref(v_x_4322_);
    v_r_4325_ = crate::leanh::lean_box((v_res_4324_) as usize);
    return v_r_4325_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(
    mut v_mvarId_4326_: *mut crate::leanh::LeanObject,
    mut v___y_4327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: u8 = 0;
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4329_ = lean_st_ref_get(v___y_4327_);
    v_mctx_4330_ = crate::leanh::lean_ctor_get(v___x_4329_, 0);
    crate::leanh::lean_inc_ref(v_mctx_4330_);
    crate::leanh::lean_dec(v___x_4329_);
    v_eAssignment_4331_ = crate::leanh::lean_ctor_get(v_mctx_4330_, 8);
    crate::leanh::lean_inc_ref(v_eAssignment_4331_);
    crate::leanh::lean_dec_ref(v_mctx_4330_);
    v___x_4332_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_eAssignment_4331_, v_mvarId_4326_);
    crate::leanh::lean_dec_ref(v_eAssignment_4331_);
    v___x_4333_ = crate::leanh::lean_box((v___x_4332_) as usize);
    v___x_4334_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4334_, 0, v___x_4333_);
    return v___x_4334_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg___boxed(
    mut v_mvarId_4335_: *mut crate::leanh::LeanObject,
    mut v___y_4336_: *mut crate::leanh::LeanObject,
    mut v___y_4337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4338_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(
        v_mvarId_4335_,
        v___y_4336_,
    );
    crate::leanh::lean_dec(v___y_4336_);
    crate::leanh::lean_dec(v_mvarId_4335_);
    return v_res_4338_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(
    mut v_synthAssignedInstances_4339_: u8,
    mut v_as_4340_: *mut crate::leanh::LeanObject,
    mut v_sz_4341_: usize,
    mut v_i_4342_: usize,
    mut v_b_4343_: *mut crate::leanh::LeanObject,
    mut v___y_4344_: *mut crate::leanh::LeanObject,
    mut v___y_4345_: *mut crate::leanh::LeanObject,
    mut v___y_4346_: *mut crate::leanh::LeanObject,
    mut v___y_4347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4351_: usize = 0;
    let mut v___x_4352_: usize = 0;
    let mut v___x_4354_: u8 = 0;
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4360_: u8 = 0;
    let mut v_array_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: u8 = 0;
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4371_: u8 = 0;
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: u8 = 0;
    let mut v___x_4378_: u8 = 0;
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: u8 = 0;
    let mut v_a_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4397_: u8 = 0;
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4401_: u8 = 0;
    let mut v_reuseFailAlloc_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4403_: u8 = 0;
    let mut v_unused_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4407_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4354_ = lean_usize_dec_lt(v_i_4342_, v_sz_4341_);
                if v___x_4354_ == 0 {
                    v___x_4355_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4355_, 0, v_b_4343_);
                    return v___x_4355_;
                } else {
                    v_snd_4356_ = crate::leanh::lean_ctor_get(v_b_4343_, 1);
                    v_fst_4357_ = crate::leanh::lean_ctor_get(v_b_4343_, 0);
                    v_isSharedCheck_4407_ = (!crate::leanh::lean_is_exclusive(v_b_4343_)) as u8;
                    if v_isSharedCheck_4407_ == 0 {
                        v___x_4359_ = v_b_4343_;
                        v_isShared_4360_ = v_isSharedCheck_4407_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4356_);
                        crate::leanh::lean_inc(v_fst_4357_);
                        crate::leanh::lean_dec(v_b_4343_);
                        v___x_4359_ = crate::leanh::lean_box(0);
                        v_isShared_4360_ = v_isSharedCheck_4407_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4351_ = 1usize;
                v___x_4352_ = lean_usize_add(v_i_4342_, v___x_4351_);
                v_i_4342_ = v___x_4352_;
                v_b_4343_ = v_a_4350_;
                state = 0;
                continue;
            }
            2 => {
                v_array_4361_ = crate::leanh::lean_ctor_get(v_snd_4356_, 0);
                v_start_4362_ = crate::leanh::lean_ctor_get(v_snd_4356_, 1);
                v_stop_4363_ = crate::leanh::lean_ctor_get(v_snd_4356_, 2);
                v___x_4364_ = lean_nat_dec_lt(v_start_4362_, v_stop_4363_);
                if v___x_4364_ == 0 {
                    if v_isShared_4360_ == 0 {
                        v___x_4366_ = v___x_4359_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4368_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_fst_4357_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 1, v_snd_4356_);
                        v___x_4366_ = v_reuseFailAlloc_4368_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_stop_4363_);
                    crate::leanh::lean_inc(v_start_4362_);
                    crate::leanh::lean_inc_ref(v_array_4361_);
                    v_isSharedCheck_4403_ = (!crate::leanh::lean_is_exclusive(v_snd_4356_)) as u8;
                    if v_isSharedCheck_4403_ == 0 {
                        v_unused_4404_ = crate::leanh::lean_ctor_get(v_snd_4356_, 2);
                        crate::leanh::lean_dec(v_unused_4404_);
                        v_unused_4405_ = crate::leanh::lean_ctor_get(v_snd_4356_, 1);
                        crate::leanh::lean_dec(v_unused_4405_);
                        v_unused_4406_ = crate::leanh::lean_ctor_get(v_snd_4356_, 0);
                        crate::leanh::lean_dec(v_unused_4406_);
                        v___x_4370_ = v_snd_4356_;
                        v_isShared_4371_ = v_isSharedCheck_4403_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_4356_);
                        v___x_4370_ = crate::leanh::lean_box(0);
                        v_isShared_4371_ = v_isSharedCheck_4403_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4367_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4367_, 0, v___x_4366_);
                return v___x_4367_;
            }
            4 => {
                v___x_4372_ = lean_array_fget(v_array_4361_, v_start_4362_);
                v___x_4373_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4374_ = lean_nat_add(v_start_4362_, v___x_4373_);
                crate::leanh::lean_dec(v_start_4362_);
                if v_isShared_4371_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4370_, 1, v___x_4374_);
                    v___x_4376_ = v___x_4370_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4402_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_array_4361_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4402_, 1, v___x_4374_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4402_, 2, v_stop_4363_);
                    v___x_4376_ = v_reuseFailAlloc_4402_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4377_ = (crate::leanh::lean_unbox(v___x_4372_) as u8);
                crate::leanh::lean_dec(v___x_4372_);
                v___x_4378_ = l_Lean_BinderInfo_isInstImplicit(v___x_4377_);
                if v___x_4378_ == 0 {
                    if v_isShared_4360_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4359_, 1, v___x_4376_);
                        v___x_4380_ = v___x_4359_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4381_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_fst_4357_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4381_, 1, v___x_4376_);
                        v___x_4380_ = v_reuseFailAlloc_4381_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_a_4382_ = lean_array_uget_borrowed(v_as_4340_, v_i_4342_);
                    v___x_4383_ = l_Lean_Expr_mvarId_x21(v_a_4382_);
                    v___x_4384_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_4383_, v___y_4345_);
                    crate::leanh::lean_dec(v___x_4383_);
                    if crate::leanh::lean_obj_tag(v___x_4384_) == 0 {
                        v_a_4385_ = crate::leanh::lean_ctor_get(v___x_4384_, 0);
                        crate::leanh::lean_inc(v_a_4385_);
                        crate::leanh::lean_dec_ref_known(v___x_4384_, 1);
                        if v_synthAssignedInstances_4339_ == 0 {
                            v___x_4393_ = (crate::leanh::lean_unbox(v_a_4385_) as u8);
                            crate::leanh::lean_dec(v_a_4385_);
                            if v___x_4393_ == 0 {
                                if v___x_4378_ == 0 {
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_del_object(v___x_4359_);
                                    state = 9;
                                    continue;
                                }
                            } else {
                                state = 7;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4385_);
                            crate::leanh::lean_del_object(v___x_4359_);
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_4376_);
                        crate::leanh::lean_del_object(v___x_4359_);
                        crate::leanh::lean_dec(v_fst_4357_);
                        v_a_4394_ = crate::leanh::lean_ctor_get(v___x_4384_, 0);
                        v_isSharedCheck_4401_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4384_)) as u8;
                        if v_isSharedCheck_4401_ == 0 {
                            v___x_4396_ = v___x_4384_;
                            v_isShared_4397_ = v_isSharedCheck_4401_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4394_);
                            crate::leanh::lean_dec(v___x_4384_);
                            v___x_4396_ = crate::leanh::lean_box(0);
                            v_isShared_4397_ = v_isSharedCheck_4401_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            6 => {
                v_a_4350_ = v___x_4380_;
                state = 1;
                continue;
            }
            7 => {
                if v_isShared_4360_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4359_, 1, v___x_4376_);
                    v___x_4388_ = v___x_4359_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4389_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_fst_4357_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4389_, 1, v___x_4376_);
                    v___x_4388_ = v_reuseFailAlloc_4389_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_a_4350_ = v___x_4388_;
                state = 1;
                continue;
            }
            9 => {
                crate::leanh::lean_inc(v_a_4382_);
                v___x_4391_ = lean_array_push(v_fst_4357_, v_a_4382_);
                v___x_4392_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4392_, 0, v___x_4391_);
                crate::leanh::lean_ctor_set(v___x_4392_, 1, v___x_4376_);
                v_a_4350_ = v___x_4392_;
                state = 1;
                continue;
            }
            10 => {
                if v_isShared_4397_ == 0 {
                    v___x_4399_ = v___x_4396_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4400_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4400_, 0, v_a_4394_);
                    v___x_4399_ = v_reuseFailAlloc_4400_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4399_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1___boxed(
    mut v_synthAssignedInstances_4408_: *mut crate::leanh::LeanObject,
    mut v_as_4409_: *mut crate::leanh::LeanObject,
    mut v_sz_4410_: *mut crate::leanh::LeanObject,
    mut v_i_4411_: *mut crate::leanh::LeanObject,
    mut v_b_4412_: *mut crate::leanh::LeanObject,
    mut v___y_4413_: *mut crate::leanh::LeanObject,
    mut v___y_4414_: *mut crate::leanh::LeanObject,
    mut v___y_4415_: *mut crate::leanh::LeanObject,
    mut v___y_4416_: *mut crate::leanh::LeanObject,
    mut v___y_4417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_synthAssignedInstances_boxed_4418_: u8 = 0;
    let mut v_sz_boxed_4419_: usize = 0;
    let mut v_i_boxed_4420_: usize = 0;
    let mut v_res_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_synthAssignedInstances_boxed_4418_ =
        (crate::leanh::lean_unbox(v_synthAssignedInstances_4408_) as u8);
    v_sz_boxed_4419_ = crate::leanh::lean_unbox_usize(v_sz_4410_);
    crate::leanh::lean_dec(v_sz_4410_);
    v_i_boxed_4420_ = crate::leanh::lean_unbox_usize(v_i_4411_);
    crate::leanh::lean_dec(v_i_4411_);
    v_res_4421_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_boxed_4418_, v_as_4409_, v_sz_boxed_4419_, v_i_boxed_4420_, v_b_4412_, v___y_4413_, v___y_4414_, v___y_4415_, v___y_4416_);
    crate::leanh::lean_dec(v___y_4416_);
    crate::leanh::lean_dec_ref(v___y_4415_);
    crate::leanh::lean_dec(v___y_4414_);
    crate::leanh::lean_dec_ref(v___y_4413_);
    crate::leanh::lean_dec_ref(v_as_4409_);
    return v_res_4421_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(
    mut v_tacticName_4422_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4423_: *mut crate::leanh::LeanObject,
    mut v_allowSynthFailures_4424_: u8,
    mut v_a_4425_: *mut crate::leanh::LeanObject,
    mut v___y_4426_: *mut crate::leanh::LeanObject,
    mut v___y_4427_: *mut crate::leanh::LeanObject,
    mut v___y_4428_: *mut crate::leanh::LeanObject,
    mut v___y_4429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: u8 = 0;
    let mut v___x_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4431_ = lean_array_get_size(v_a_4425_);
                v___x_4432_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4433_ = lean_nat_dec_eq(v___x_4431_, v___x_4432_);
                if v___x_4433_ == 0 {
                    crate::leanh::lean_inc(v_mvarId_4423_);
                    crate::leanh::lean_inc(v_tacticName_4422_);
                    v___x_4434_ =
                        l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step(
                            v_tacticName_4422_,
                            v_mvarId_4423_,
                            v_allowSynthFailures_4424_,
                            v_a_4425_,
                            v___y_4426_,
                            v___y_4427_,
                            v___y_4428_,
                            v___y_4429_,
                        );
                    crate::leanh::lean_dec_ref(v_a_4425_);
                    if crate::leanh::lean_obj_tag(v___x_4434_) == 0 {
                        v_a_4435_ = crate::leanh::lean_ctor_get(v___x_4434_, 0);
                        crate::leanh::lean_inc(v_a_4435_);
                        crate::leanh::lean_dec_ref_known(v___x_4434_, 1);
                        v_a_4425_ = v_a_4435_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_mvarId_4423_);
                        crate::leanh::lean_dec(v_tacticName_4422_);
                        return v___x_4434_;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_4423_);
                    crate::leanh::lean_dec(v_tacticName_4422_);
                    v___x_4437_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4437_, 0, v_a_4425_);
                    return v___x_4437_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg___boxed(
    mut v_tacticName_4438_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4439_: *mut crate::leanh::LeanObject,
    mut v_allowSynthFailures_4440_: *mut crate::leanh::LeanObject,
    mut v_a_4441_: *mut crate::leanh::LeanObject,
    mut v___y_4442_: *mut crate::leanh::LeanObject,
    mut v___y_4443_: *mut crate::leanh::LeanObject,
    mut v___y_4444_: *mut crate::leanh::LeanObject,
    mut v___y_4445_: *mut crate::leanh::LeanObject,
    mut v___y_4446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowSynthFailures_boxed_4447_: u8 = 0;
    let mut v_res_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowSynthFailures_boxed_4447_ = (crate::leanh::lean_unbox(v_allowSynthFailures_4440_) as u8);
    v_res_4448_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_4438_, v_mvarId_4439_, v_allowSynthFailures_boxed_4447_, v_a_4441_, v___y_4442_, v___y_4443_, v___y_4444_, v___y_4445_);
    crate::leanh::lean_dec(v___y_4445_);
    crate::leanh::lean_dec_ref(v___y_4444_);
    crate::leanh::lean_dec(v___y_4443_);
    crate::leanh::lean_dec_ref(v___y_4442_);
    return v_res_4448_;
}
pub unsafe fn l_Lean_Meta_synthAppInstances(
    mut v_tacticName_4449_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4450_: *mut crate::leanh::LeanObject,
    mut v_mvarsNew_4451_: *mut crate::leanh::LeanObject,
    mut v_binderInfos_4452_: *mut crate::leanh::LeanObject,
    mut v_synthAssignedInstances_4453_: u8,
    mut v_allowSynthFailures_4454_: u8,
    mut v_a_4455_: *mut crate::leanh::LeanObject,
    mut v_a_4456_: *mut crate::leanh::LeanObject,
    mut v_a_4457_: *mut crate::leanh::LeanObject,
    mut v_a_4458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_todo_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4465_: usize = 0;
    let mut v___x_4466_: usize = 0;
    let mut v___x_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4473_: u8 = 0;
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4478_: u8 = 0;
    let mut v_unused_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4483_: u8 = 0;
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4487_: u8 = 0;
    let mut v_a_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4491_: u8 = 0;
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4495_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4460_ = crate::leanh::lean_unsigned_to_nat(0);
                v_todo_4461_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0;
                v___x_4462_ = lean_array_get_size(v_binderInfos_4452_);
                v___x_4463_ =
                    l_Array_toSubarray___redArg(v_binderInfos_4452_, v___x_4460_, v___x_4462_);
                v___x_4464_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4464_, 0, v_todo_4461_);
                crate::leanh::lean_ctor_set(v___x_4464_, 1, v___x_4463_);
                v_sz_4465_ = lean_array_size(v_mvarsNew_4451_);
                v___x_4466_ = 0usize;
                v___x_4467_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_synthAppInstances_spec__1(v_synthAssignedInstances_4453_, v_mvarsNew_4451_, v_sz_4465_, v___x_4466_, v___x_4464_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_);
                if crate::leanh::lean_obj_tag(v___x_4467_) == 0 {
                    v_a_4468_ = crate::leanh::lean_ctor_get(v___x_4467_, 0);
                    crate::leanh::lean_inc(v_a_4468_);
                    crate::leanh::lean_dec_ref_known(v___x_4467_, 1);
                    v_fst_4469_ = crate::leanh::lean_ctor_get(v_a_4468_, 0);
                    crate::leanh::lean_inc(v_fst_4469_);
                    crate::leanh::lean_dec(v_a_4468_);
                    v___x_4470_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_4449_, v_mvarId_4450_, v_allowSynthFailures_4454_, v_fst_4469_, v_a_4455_, v_a_4456_, v_a_4457_, v_a_4458_);
                    if crate::leanh::lean_obj_tag(v___x_4470_) == 0 {
                        v_isSharedCheck_4478_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4470_)) as u8;
                        if v_isSharedCheck_4478_ == 0 {
                            v_unused_4479_ = crate::leanh::lean_ctor_get(v___x_4470_, 0);
                            crate::leanh::lean_dec(v_unused_4479_);
                            v___x_4472_ = v___x_4470_;
                            v_isShared_4473_ = v_isSharedCheck_4478_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4470_);
                            v___x_4472_ = crate::leanh::lean_box(0);
                            v_isShared_4473_ = v_isSharedCheck_4478_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4480_ = crate::leanh::lean_ctor_get(v___x_4470_, 0);
                        v_isSharedCheck_4487_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4470_)) as u8;
                        if v_isSharedCheck_4487_ == 0 {
                            v___x_4482_ = v___x_4470_;
                            v_isShared_4483_ = v_isSharedCheck_4487_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4480_);
                            crate::leanh::lean_dec(v___x_4470_);
                            v___x_4482_ = crate::leanh::lean_box(0);
                            v_isShared_4483_ = v_isSharedCheck_4487_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_4450_);
                    crate::leanh::lean_dec(v_tacticName_4449_);
                    v_a_4488_ = crate::leanh::lean_ctor_get(v___x_4467_, 0);
                    v_isSharedCheck_4495_ = (!crate::leanh::lean_is_exclusive(v___x_4467_)) as u8;
                    if v_isSharedCheck_4495_ == 0 {
                        v___x_4490_ = v___x_4467_;
                        v_isShared_4491_ = v_isSharedCheck_4495_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4488_);
                        crate::leanh::lean_dec(v___x_4467_);
                        v___x_4490_ = crate::leanh::lean_box(0);
                        v_isShared_4491_ = v_isSharedCheck_4495_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4474_ = crate::leanh::lean_box(0);
                if v_isShared_4473_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4472_, 0, v___x_4474_);
                    v___x_4476_ = v___x_4472_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4477_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4477_, 0, v___x_4474_);
                    v___x_4476_ = v_reuseFailAlloc_4477_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4476_;
            }
            3 => {
                if v_isShared_4483_ == 0 {
                    v___x_4485_ = v___x_4482_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4486_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4486_, 0, v_a_4480_);
                    v___x_4485_ = v_reuseFailAlloc_4486_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4485_;
            }
            5 => {
                if v_isShared_4491_ == 0 {
                    v___x_4493_ = v___x_4490_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4494_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_a_4488_);
                    v___x_4493_ = v_reuseFailAlloc_4494_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4493_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_synthAppInstances___boxed(
    mut v_tacticName_4496_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4497_: *mut crate::leanh::LeanObject,
    mut v_mvarsNew_4498_: *mut crate::leanh::LeanObject,
    mut v_binderInfos_4499_: *mut crate::leanh::LeanObject,
    mut v_synthAssignedInstances_4500_: *mut crate::leanh::LeanObject,
    mut v_allowSynthFailures_4501_: *mut crate::leanh::LeanObject,
    mut v_a_4502_: *mut crate::leanh::LeanObject,
    mut v_a_4503_: *mut crate::leanh::LeanObject,
    mut v_a_4504_: *mut crate::leanh::LeanObject,
    mut v_a_4505_: *mut crate::leanh::LeanObject,
    mut v_a_4506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_synthAssignedInstances_boxed_4507_: u8 = 0;
    let mut v_allowSynthFailures_boxed_4508_: u8 = 0;
    let mut v_res_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_synthAssignedInstances_boxed_4507_ =
        (crate::leanh::lean_unbox(v_synthAssignedInstances_4500_) as u8);
    v_allowSynthFailures_boxed_4508_ = (crate::leanh::lean_unbox(v_allowSynthFailures_4501_) as u8);
    v_res_4509_ = l_Lean_Meta_synthAppInstances(
        v_tacticName_4496_,
        v_mvarId_4497_,
        v_mvarsNew_4498_,
        v_binderInfos_4499_,
        v_synthAssignedInstances_boxed_4507_,
        v_allowSynthFailures_boxed_4508_,
        v_a_4502_,
        v_a_4503_,
        v_a_4504_,
        v_a_4505_,
    );
    crate::leanh::lean_dec(v_a_4505_);
    crate::leanh::lean_dec_ref(v_a_4504_);
    crate::leanh::lean_dec(v_a_4503_);
    crate::leanh::lean_dec_ref(v_a_4502_);
    crate::leanh::lean_dec_ref(v_mvarsNew_4498_);
    return v_res_4509_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(
    mut v_mvarId_4510_: *mut crate::leanh::LeanObject,
    mut v___y_4511_: *mut crate::leanh::LeanObject,
    mut v___y_4512_: *mut crate::leanh::LeanObject,
    mut v___y_4513_: *mut crate::leanh::LeanObject,
    mut v___y_4514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4516_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(
        v_mvarId_4510_,
        v___y_4512_,
    );
    return v___x_4516_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___boxed(
    mut v_mvarId_4517_: *mut crate::leanh::LeanObject,
    mut v___y_4518_: *mut crate::leanh::LeanObject,
    mut v___y_4519_: *mut crate::leanh::LeanObject,
    mut v___y_4520_: *mut crate::leanh::LeanObject,
    mut v___y_4521_: *mut crate::leanh::LeanObject,
    mut v___y_4522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4523_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0(
        v_mvarId_4517_,
        v___y_4518_,
        v___y_4519_,
        v___y_4520_,
        v___y_4521_,
    );
    crate::leanh::lean_dec(v___y_4521_);
    crate::leanh::lean_dec_ref(v___y_4520_);
    crate::leanh::lean_dec(v___y_4519_);
    crate::leanh::lean_dec_ref(v___y_4518_);
    crate::leanh::lean_dec(v_mvarId_4517_);
    return v_res_4523_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2(
    mut v_tacticName_4524_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4525_: *mut crate::leanh::LeanObject,
    mut v_allowSynthFailures_4526_: u8,
    mut v_inst_4527_: *mut crate::leanh::LeanObject,
    mut v_a_4528_: *mut crate::leanh::LeanObject,
    mut v___y_4529_: *mut crate::leanh::LeanObject,
    mut v___y_4530_: *mut crate::leanh::LeanObject,
    mut v___y_4531_: *mut crate::leanh::LeanObject,
    mut v___y_4532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4534_ = l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2___redArg(v_tacticName_4524_, v_mvarId_4525_, v_allowSynthFailures_4526_, v_a_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_);
    return v___x_4534_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2___boxed(
    mut v_tacticName_4535_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4536_: *mut crate::leanh::LeanObject,
    mut v_allowSynthFailures_4537_: *mut crate::leanh::LeanObject,
    mut v_inst_4538_: *mut crate::leanh::LeanObject,
    mut v_a_4539_: *mut crate::leanh::LeanObject,
    mut v___y_4540_: *mut crate::leanh::LeanObject,
    mut v___y_4541_: *mut crate::leanh::LeanObject,
    mut v___y_4542_: *mut crate::leanh::LeanObject,
    mut v___y_4543_: *mut crate::leanh::LeanObject,
    mut v___y_4544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowSynthFailures_boxed_4545_: u8 = 0;
    let mut v_res_4546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowSynthFailures_boxed_4545_ = (crate::leanh::lean_unbox(v_allowSynthFailures_4537_) as u8);
    v_res_4546_ =
        l___private_Init_While_0__whileM_erased___at___00Lean_Meta_synthAppInstances_spec__2(
            v_tacticName_4535_,
            v_mvarId_4536_,
            v_allowSynthFailures_boxed_4545_,
            v_inst_4538_,
            v_a_4539_,
            v___y_4540_,
            v___y_4541_,
            v___y_4542_,
            v___y_4543_,
        );
    crate::leanh::lean_dec(v___y_4543_);
    crate::leanh::lean_dec_ref(v___y_4542_);
    crate::leanh::lean_dec(v___y_4541_);
    crate::leanh::lean_dec_ref(v___y_4540_);
    return v_res_4546_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(
    mut v_00_u03b2_4547_: *mut crate::leanh::LeanObject,
    mut v_x_4548_: *mut crate::leanh::LeanObject,
    mut v_x_4549_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4550_: u8 = 0;
    v___x_4550_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___redArg(v_x_4548_, v_x_4549_);
    return v___x_4550_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0___boxed(
    mut v_00_u03b2_4551_: *mut crate::leanh::LeanObject,
    mut v_x_4552_: *mut crate::leanh::LeanObject,
    mut v_x_4553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4554_: u8 = 0;
    let mut v_r_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4554_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0(v_00_u03b2_4551_, v_x_4552_, v_x_4553_);
    crate::leanh::lean_dec(v_x_4553_);
    crate::leanh::lean_dec_ref(v_x_4552_);
    v_r_4555_ = crate::leanh::lean_box((v_res_4554_) as usize);
    return v_r_4555_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4556_: *mut crate::leanh::LeanObject,
    mut v_x_4557_: *mut crate::leanh::LeanObject,
    mut v_x_4558_: usize,
    mut v_x_4559_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4560_: u8 = 0;
    v___x_4560_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg(v_x_4557_, v_x_4558_, v_x_4559_);
    return v___x_4560_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4561_: *mut crate::leanh::LeanObject,
    mut v_x_4562_: *mut crate::leanh::LeanObject,
    mut v_x_4563_: *mut crate::leanh::LeanObject,
    mut v_x_4564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_3370__boxed_4565_: usize = 0;
    let mut v_res_4566_: u8 = 0;
    let mut v_r_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_3370__boxed_4565_ = crate::leanh::lean_unbox_usize(v_x_4563_);
    crate::leanh::lean_dec(v_x_4563_);
    v_res_4566_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1(v_00_u03b2_4561_, v_x_4562_, v_x_3370__boxed_4565_, v_x_4564_);
    crate::leanh::lean_dec(v_x_4564_);
    crate::leanh::lean_dec_ref(v_x_4562_);
    v_r_4567_ = crate::leanh::lean_box((v_res_4566_) as usize);
    return v_r_4567_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b2_4568_: *mut crate::leanh::LeanObject,
    mut v_keys_4569_: *mut crate::leanh::LeanObject,
    mut v_vals_4570_: *mut crate::leanh::LeanObject,
    mut v_heq_4571_: *mut crate::leanh::LeanObject,
    mut v_i_4572_: *mut crate::leanh::LeanObject,
    mut v_k_4573_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4574_: u8 = 0;
    v___x_4574_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___redArg(v_keys_4569_, v_i_4572_, v_k_4573_);
    return v___x_4574_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b2_4575_: *mut crate::leanh::LeanObject,
    mut v_keys_4576_: *mut crate::leanh::LeanObject,
    mut v_vals_4577_: *mut crate::leanh::LeanObject,
    mut v_heq_4578_: *mut crate::leanh::LeanObject,
    mut v_i_4579_: *mut crate::leanh::LeanObject,
    mut v_k_4580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4581_: u8 = 0;
    let mut v_r_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4581_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1_spec__4(v_00_u03b2_4575_, v_keys_4576_, v_vals_4577_, v_heq_4578_, v_i_4579_, v_k_4580_);
    crate::leanh::lean_dec(v_k_4580_);
    crate::leanh::lean_dec_ref(v_vals_4577_);
    crate::leanh::lean_dec_ref(v_keys_4576_);
    v_r_4582_ = crate::leanh::lean_box((v_res_4581_) as usize);
    return v_r_4582_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(
    mut v_newMVars_4583_: *mut crate::leanh::LeanObject,
    mut v_binderInfos_4584_: *mut crate::leanh::LeanObject,
    mut v_a_4585_: *mut crate::leanh::LeanObject,
    mut v_n_4586_: *mut crate::leanh::LeanObject,
    mut v_i_4587_: *mut crate::leanh::LeanObject,
    mut v___y_4588_: *mut crate::leanh::LeanObject,
    mut v___y_4589_: *mut crate::leanh::LeanObject,
    mut v___y_4590_: *mut crate::leanh::LeanObject,
    mut v___y_4591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_4594_: u8 = 0;
    let mut v___x_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_4597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_4598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: u8 = 0;
    let mut v___x_4606_: u8 = 0;
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4609_: u8 = 0;
    let mut v___x_4610_: u8 = 0;
    let mut v___x_4611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4619_: u8 = 0;
    let mut v___x_4621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4623_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_4593_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_4594_ = lean_nat_dec_eq(v_i_4587_, v_zero_4593_);
                if v_isZero_4594_ == 1 {
                    crate::leanh::lean_dec(v_i_4587_);
                    crate::leanh::lean_dec(v_a_4585_);
                    v___x_4595_ = crate::leanh::lean_box(0);
                    v___x_4596_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4596_, 0, v___x_4595_);
                    return v___x_4596_;
                } else {
                    v_one_4597_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_4598_ = lean_nat_sub(v_i_4587_, v_one_4597_);
                    crate::leanh::lean_dec(v_i_4587_);
                    v___x_4599_ = lean_nat_sub(v_n_4586_, v_n_4598_);
                    v___x_4600_ = lean_nat_sub(v___x_4599_, v_one_4597_);
                    crate::leanh::lean_dec(v___x_4599_);
                    v___x_4601_ = lean_array_fget_borrowed(v_newMVars_4583_, v___x_4600_);
                    v___x_4602_ = l_Lean_Expr_mvarId_x21(v___x_4601_);
                    v___x_4603_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_4602_, v___y_4589_);
                    v_a_4604_ = crate::leanh::lean_ctor_get(v___x_4603_, 0);
                    crate::leanh::lean_inc(v_a_4604_);
                    crate::leanh::lean_dec_ref(v___x_4603_);
                    v___x_4605_ = (crate::leanh::lean_unbox(v_a_4604_) as u8);
                    crate::leanh::lean_dec(v_a_4604_);
                    if v___x_4605_ == 0 {
                        v___x_4606_ = 0;
                        v___x_4607_ = crate::leanh::lean_box((v___x_4606_) as usize);
                        v___x_4608_ = lean_array_get(v___x_4607_, v_binderInfos_4584_, v___x_4600_);
                        crate::leanh::lean_dec(v___x_4600_);
                        crate::leanh::lean_dec(v___x_4607_);
                        v___x_4609_ = (crate::leanh::lean_unbox(v___x_4608_) as u8);
                        crate::leanh::lean_dec(v___x_4608_);
                        v___x_4610_ = l_Lean_BinderInfo_isInstImplicit(v___x_4609_);
                        if v___x_4610_ == 0 {
                            crate::leanh::lean_inc(v___x_4602_);
                            v___x_4611_ = l_Lean_MVarId_getTag(
                                v___x_4602_,
                                v___y_4588_,
                                v___y_4589_,
                                v___y_4590_,
                                v___y_4591_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4611_) == 0 {
                                v_a_4612_ = crate::leanh::lean_ctor_get(v___x_4611_, 0);
                                crate::leanh::lean_inc(v_a_4612_);
                                crate::leanh::lean_dec_ref_known(v___x_4611_, 1);
                                crate::leanh::lean_inc(v_a_4585_);
                                v___x_4613_ = l_Lean_Meta_appendTag(v_a_4585_, v_a_4612_);
                                v___x_4614_ = l_Lean_MVarId_setTag___redArg(
                                    v___x_4602_,
                                    v___x_4613_,
                                    v___y_4589_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_4614_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_4614_, 1);
                                    v_i_4587_ = v_n_4598_;
                                    state = 0;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_n_4598_);
                                    crate::leanh::lean_dec(v_a_4585_);
                                    return v___x_4614_;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_4602_);
                                crate::leanh::lean_dec(v_n_4598_);
                                crate::leanh::lean_dec(v_a_4585_);
                                v_a_4616_ = crate::leanh::lean_ctor_get(v___x_4611_, 0);
                                v_isSharedCheck_4623_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4611_)) as u8;
                                if v_isSharedCheck_4623_ == 0 {
                                    v___x_4618_ = v___x_4611_;
                                    v_isShared_4619_ = v_isSharedCheck_4623_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4616_);
                                    crate::leanh::lean_dec(v___x_4611_);
                                    v___x_4618_ = crate::leanh::lean_box(0);
                                    v_isShared_4619_ = v_isSharedCheck_4623_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_4602_);
                            v_i_4587_ = v_n_4598_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4602_);
                        crate::leanh::lean_dec(v___x_4600_);
                        v_i_4587_ = v_n_4598_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4619_ == 0 {
                    v___x_4621_ = v___x_4618_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4622_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4622_, 0, v_a_4616_);
                    v___x_4621_ = v_reuseFailAlloc_4622_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4621_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg___boxed(
    mut v_newMVars_4626_: *mut crate::leanh::LeanObject,
    mut v_binderInfos_4627_: *mut crate::leanh::LeanObject,
    mut v_a_4628_: *mut crate::leanh::LeanObject,
    mut v_n_4629_: *mut crate::leanh::LeanObject,
    mut v_i_4630_: *mut crate::leanh::LeanObject,
    mut v___y_4631_: *mut crate::leanh::LeanObject,
    mut v___y_4632_: *mut crate::leanh::LeanObject,
    mut v___y_4633_: *mut crate::leanh::LeanObject,
    mut v___y_4634_: *mut crate::leanh::LeanObject,
    mut v___y_4635_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4636_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_4626_, v_binderInfos_4627_, v_a_4628_, v_n_4629_, v_i_4630_, v___y_4631_, v___y_4632_, v___y_4633_, v___y_4634_);
    crate::leanh::lean_dec(v___y_4634_);
    crate::leanh::lean_dec_ref(v___y_4633_);
    crate::leanh::lean_dec(v___y_4632_);
    crate::leanh::lean_dec_ref(v___y_4631_);
    crate::leanh::lean_dec(v_n_4629_);
    crate::leanh::lean_dec_ref(v_binderInfos_4627_);
    crate::leanh::lean_dec_ref(v_newMVars_4626_);
    return v_res_4636_;
}
pub unsafe fn l_Lean_Meta_appendParentTag(
    mut v_mvarId_4637_: *mut crate::leanh::LeanObject,
    mut v_newMVars_4638_: *mut crate::leanh::LeanObject,
    mut v_binderInfos_4639_: *mut crate::leanh::LeanObject,
    mut v_a_4640_: *mut crate::leanh::LeanObject,
    mut v_a_4641_: *mut crate::leanh::LeanObject,
    mut v_a_4642_: *mut crate::leanh::LeanObject,
    mut v_a_4643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4649_: u8 = 0;
    let mut v___x_4650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: u8 = 0;
    let mut v___x_4653_: u8 = 0;
    let mut v___x_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4664_: u8 = 0;
    let mut v_a_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4668_: u8 = 0;
    let mut v___x_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4672_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4645_ = l_Lean_MVarId_getTag(
                    v_mvarId_4637_,
                    v_a_4640_,
                    v_a_4641_,
                    v_a_4642_,
                    v_a_4643_,
                );
                if crate::leanh::lean_obj_tag(v___x_4645_) == 0 {
                    v_a_4646_ = crate::leanh::lean_ctor_get(v___x_4645_, 0);
                    v_isSharedCheck_4664_ = (!crate::leanh::lean_is_exclusive(v___x_4645_)) as u8;
                    if v_isSharedCheck_4664_ == 0 {
                        v___x_4648_ = v___x_4645_;
                        v_isShared_4649_ = v_isSharedCheck_4664_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4646_);
                        crate::leanh::lean_dec(v___x_4645_);
                        v___x_4648_ = crate::leanh::lean_box(0);
                        v_isShared_4649_ = v_isSharedCheck_4664_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4665_ = crate::leanh::lean_ctor_get(v___x_4645_, 0);
                    v_isSharedCheck_4672_ = (!crate::leanh::lean_is_exclusive(v___x_4645_)) as u8;
                    if v_isSharedCheck_4672_ == 0 {
                        v___x_4667_ = v___x_4645_;
                        v_isShared_4668_ = v_isSharedCheck_4672_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4665_);
                        crate::leanh::lean_dec(v___x_4645_);
                        v___x_4667_ = crate::leanh::lean_box(0);
                        v_isShared_4668_ = v_isSharedCheck_4672_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4650_ = lean_array_get_size(v_newMVars_4638_);
                v___x_4651_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4652_ = lean_nat_dec_eq(v___x_4650_, v___x_4651_);
                if v___x_4652_ == 0 {
                    v___x_4653_ = l_Lean_Name_isAnonymous(v_a_4646_);
                    if v___x_4653_ == 0 {
                        crate::leanh::lean_del_object(v___x_4648_);
                        v___x_4654_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_4638_, v_binderInfos_4639_, v_a_4646_, v___x_4650_, v___x_4650_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_);
                        return v___x_4654_;
                    } else {
                        crate::leanh::lean_dec(v_a_4646_);
                        v___x_4655_ = crate::leanh::lean_box(0);
                        if v_isShared_4649_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4648_, 0, v___x_4655_);
                            v___x_4657_ = v___x_4648_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_4658_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4658_, 0, v___x_4655_);
                            v___x_4657_ = v_reuseFailAlloc_4658_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4648_);
                    v___x_4659_ = l_Lean_instInhabitedExpr;
                    v___x_4660_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4661_ =
                        lean_array_get_borrowed(v___x_4659_, v_newMVars_4638_, v___x_4660_);
                    v___x_4662_ = l_Lean_Expr_mvarId_x21(v___x_4661_);
                    v___x_4663_ = l_Lean_MVarId_setTag___redArg(v___x_4662_, v_a_4646_, v_a_4641_);
                    return v___x_4663_;
                }
            }
            2 => {
                return v___x_4657_;
            }
            3 => {
                if v_isShared_4668_ == 0 {
                    v___x_4670_ = v___x_4667_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4671_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4671_, 0, v_a_4665_);
                    v___x_4670_ = v_reuseFailAlloc_4671_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4670_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_appendParentTag___boxed(
    mut v_mvarId_4673_: *mut crate::leanh::LeanObject,
    mut v_newMVars_4674_: *mut crate::leanh::LeanObject,
    mut v_binderInfos_4675_: *mut crate::leanh::LeanObject,
    mut v_a_4676_: *mut crate::leanh::LeanObject,
    mut v_a_4677_: *mut crate::leanh::LeanObject,
    mut v_a_4678_: *mut crate::leanh::LeanObject,
    mut v_a_4679_: *mut crate::leanh::LeanObject,
    mut v_a_4680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4681_ = l_Lean_Meta_appendParentTag(
        v_mvarId_4673_,
        v_newMVars_4674_,
        v_binderInfos_4675_,
        v_a_4676_,
        v_a_4677_,
        v_a_4678_,
        v_a_4679_,
    );
    crate::leanh::lean_dec(v_a_4679_);
    crate::leanh::lean_dec_ref(v_a_4678_);
    crate::leanh::lean_dec(v_a_4677_);
    crate::leanh::lean_dec_ref(v_a_4676_);
    crate::leanh::lean_dec_ref(v_binderInfos_4675_);
    crate::leanh::lean_dec_ref(v_newMVars_4674_);
    return v_res_4681_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(
    mut v_newMVars_4682_: *mut crate::leanh::LeanObject,
    mut v_binderInfos_4683_: *mut crate::leanh::LeanObject,
    mut v_a_4684_: *mut crate::leanh::LeanObject,
    mut v_n_4685_: *mut crate::leanh::LeanObject,
    mut v_i_4686_: *mut crate::leanh::LeanObject,
    mut v_a_4687_: *mut crate::leanh::LeanObject,
    mut v___y_4688_: *mut crate::leanh::LeanObject,
    mut v___y_4689_: *mut crate::leanh::LeanObject,
    mut v___y_4690_: *mut crate::leanh::LeanObject,
    mut v___y_4691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4693_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___redArg(v_newMVars_4682_, v_binderInfos_4683_, v_a_4684_, v_n_4685_, v_i_4686_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_);
    return v___x_4693_;
}
pub unsafe fn l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0___boxed(
    mut v_newMVars_4694_: *mut crate::leanh::LeanObject,
    mut v_binderInfos_4695_: *mut crate::leanh::LeanObject,
    mut v_a_4696_: *mut crate::leanh::LeanObject,
    mut v_n_4697_: *mut crate::leanh::LeanObject,
    mut v_i_4698_: *mut crate::leanh::LeanObject,
    mut v_a_4699_: *mut crate::leanh::LeanObject,
    mut v___y_4700_: *mut crate::leanh::LeanObject,
    mut v___y_4701_: *mut crate::leanh::LeanObject,
    mut v___y_4702_: *mut crate::leanh::LeanObject,
    mut v___y_4703_: *mut crate::leanh::LeanObject,
    mut v___y_4704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4705_ = l___private_Init_Data_Nat_Control_0__Nat_forM_loop___at___00Lean_Meta_appendParentTag_spec__0(v_newMVars_4694_, v_binderInfos_4695_, v_a_4696_, v_n_4697_, v_i_4698_, v_a_4699_, v___y_4700_, v___y_4701_, v___y_4702_, v___y_4703_);
    crate::leanh::lean_dec(v___y_4703_);
    crate::leanh::lean_dec_ref(v___y_4702_);
    crate::leanh::lean_dec(v___y_4701_);
    crate::leanh::lean_dec_ref(v___y_4700_);
    crate::leanh::lean_dec(v_n_4697_);
    crate::leanh::lean_dec_ref(v_binderInfos_4695_);
    crate::leanh::lean_dec_ref(v_newMVars_4694_);
    return v_res_4705_;
}
pub unsafe fn l_Lean_Meta_postprocessAppMVars(
    mut v_tacticName_4706_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4707_: *mut crate::leanh::LeanObject,
    mut v_newMVars_4708_: *mut crate::leanh::LeanObject,
    mut v_binderInfos_4709_: *mut crate::leanh::LeanObject,
    mut v_synthAssignedInstances_4710_: u8,
    mut v_allowSynthFailures_4711_: u8,
    mut v_a_4712_: *mut crate::leanh::LeanObject,
    mut v_a_4713_: *mut crate::leanh::LeanObject,
    mut v_a_4714_: *mut crate::leanh::LeanObject,
    mut v_a_4715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4717_ = l_Lean_Meta_synthAppInstances(
        v_tacticName_4706_,
        v_mvarId_4707_,
        v_newMVars_4708_,
        v_binderInfos_4709_,
        v_synthAssignedInstances_4710_,
        v_allowSynthFailures_4711_,
        v_a_4712_,
        v_a_4713_,
        v_a_4714_,
        v_a_4715_,
    );
    return v___x_4717_;
}
pub unsafe fn l_Lean_Meta_postprocessAppMVars___boxed(
    mut v_tacticName_4718_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4719_: *mut crate::leanh::LeanObject,
    mut v_newMVars_4720_: *mut crate::leanh::LeanObject,
    mut v_binderInfos_4721_: *mut crate::leanh::LeanObject,
    mut v_synthAssignedInstances_4722_: *mut crate::leanh::LeanObject,
    mut v_allowSynthFailures_4723_: *mut crate::leanh::LeanObject,
    mut v_a_4724_: *mut crate::leanh::LeanObject,
    mut v_a_4725_: *mut crate::leanh::LeanObject,
    mut v_a_4726_: *mut crate::leanh::LeanObject,
    mut v_a_4727_: *mut crate::leanh::LeanObject,
    mut v_a_4728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_synthAssignedInstances_boxed_4729_: u8 = 0;
    let mut v_allowSynthFailures_boxed_4730_: u8 = 0;
    let mut v_res_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_synthAssignedInstances_boxed_4729_ =
        (crate::leanh::lean_unbox(v_synthAssignedInstances_4722_) as u8);
    v_allowSynthFailures_boxed_4730_ = (crate::leanh::lean_unbox(v_allowSynthFailures_4723_) as u8);
    v_res_4731_ = l_Lean_Meta_postprocessAppMVars(
        v_tacticName_4718_,
        v_mvarId_4719_,
        v_newMVars_4720_,
        v_binderInfos_4721_,
        v_synthAssignedInstances_boxed_4729_,
        v_allowSynthFailures_boxed_4730_,
        v_a_4724_,
        v_a_4725_,
        v_a_4726_,
        v_a_4727_,
    );
    crate::leanh::lean_dec(v_a_4727_);
    crate::leanh::lean_dec_ref(v_a_4726_);
    crate::leanh::lean_dec(v_a_4725_);
    crate::leanh::lean_dec_ref(v_a_4724_);
    crate::leanh::lean_dec_ref(v_newMVars_4720_);
    return v_res_4731_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(
    mut v_mvar_4732_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4733_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: u8 = 0;
    v___x_4734_ = l_Lean_Expr_mvarId_x21(v_mvar_4732_);
    v___x_4735_ = l_Lean_instBEqMVarId_beq(v_mvarId_4733_, v___x_4734_);
    crate::leanh::lean_dec(v___x_4734_);
    return v___x_4735_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed(
    mut v_mvar_4736_: *mut crate::leanh::LeanObject,
    mut v_mvarId_4737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4738_: u8 = 0;
    let mut v_r_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4738_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0(v_mvar_4736_, v_mvarId_4737_);
    crate::leanh::lean_dec(v_mvarId_4737_);
    crate::leanh::lean_dec_ref(v_mvar_4736_);
    v_r_4739_ = crate::leanh::lean_box((v_res_4738_) as usize);
    return v_r_4739_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(
    mut v_mvar_4740_: *mut crate::leanh::LeanObject,
    mut v_as_4741_: *mut crate::leanh::LeanObject,
    mut v_i_4742_: usize,
    mut v_stop_4743_: usize,
    mut v___y_4744_: *mut crate::leanh::LeanObject,
    mut v___y_4745_: *mut crate::leanh::LeanObject,
    mut v___y_4746_: *mut crate::leanh::LeanObject,
    mut v___y_4747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4749_: u8 = 0;
    let mut v___x_4750_: u8 = 0;
    let mut v_a_4752_: u8 = 0;
    let mut v___x_4753_: usize = 0;
    let mut v___x_4754_: usize = 0;
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4759_: u8 = 0;
    let mut v___x_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4764_: u8 = 0;
    let mut v___f_4765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4772_: u8 = 0;
    let mut v_a_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4776_: u8 = 0;
    let mut v___x_4778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4780_: u8 = 0;
    let mut v___x_4781_: u8 = 0;
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4749_ = lean_usize_dec_eq(v_i_4742_, v_stop_4743_);
                if v___x_4749_ == 0 {
                    v___x_4750_ = 1;
                    v___x_4758_ = lean_array_uget_borrowed(v_as_4741_, v_i_4742_);
                    v___x_4759_ = lean_expr_eqv(v_mvar_4740_, v___x_4758_);
                    if v___x_4759_ == 0 {
                        crate::leanh::lean_inc(v___y_4747_);
                        crate::leanh::lean_inc_ref(v___y_4746_);
                        crate::leanh::lean_inc(v___y_4745_);
                        crate::leanh::lean_inc_ref(v___y_4744_);
                        crate::leanh::lean_inc(v___x_4758_);
                        v___x_4760_ = lean_infer_type(
                            v___x_4758_,
                            v___y_4744_,
                            v___y_4745_,
                            v___y_4746_,
                            v___y_4747_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4760_) == 0 {
                            v_a_4761_ = crate::leanh::lean_ctor_get(v___x_4760_, 0);
                            v_isSharedCheck_4772_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4760_)) as u8;
                            if v_isSharedCheck_4772_ == 0 {
                                v___x_4763_ = v___x_4760_;
                                v_isShared_4764_ = v_isSharedCheck_4772_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4761_);
                                crate::leanh::lean_dec(v___x_4760_);
                                v___x_4763_ = crate::leanh::lean_box(0);
                                v_isShared_4764_ = v_isSharedCheck_4772_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_mvar_4740_);
                            v_a_4773_ = crate::leanh::lean_ctor_get(v___x_4760_, 0);
                            v_isSharedCheck_4780_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4760_)) as u8;
                            if v_isSharedCheck_4780_ == 0 {
                                v___x_4775_ = v___x_4760_;
                                v_isShared_4776_ = v_isSharedCheck_4780_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4773_);
                                crate::leanh::lean_dec(v___x_4760_);
                                v___x_4775_ = crate::leanh::lean_box(0);
                                v_isShared_4776_ = v_isSharedCheck_4780_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_a_4752_ = v___x_4749_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_mvar_4740_);
                    v___x_4781_ = 0;
                    v___x_4782_ = crate::leanh::lean_box((v___x_4781_) as usize);
                    v___x_4783_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4783_, 0, v___x_4782_);
                    return v___x_4783_;
                }
            }
            1 => {
                if v_a_4752_ == 0 {
                    v___x_4753_ = 1usize;
                    v___x_4754_ = lean_usize_add(v_i_4742_, v___x_4753_);
                    v_i_4742_ = v___x_4754_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_mvar_4740_);
                    v___x_4756_ = crate::leanh::lean_box((v___x_4750_) as usize);
                    v___x_4757_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4757_, 0, v___x_4756_);
                    return v___x_4757_;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_mvar_4740_);
                v___f_4765_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_4765_, 0, v_mvar_4740_);
                v___x_4766_ = crate::leanh::lean_box(0);
                v___x_4767_ = l_Lean_FindMVar_main(v___f_4765_, v_a_4761_, v___x_4766_);
                if crate::leanh::lean_obj_tag(v___x_4767_) == 0 {
                    crate::leanh::lean_del_object(v___x_4763_);
                    v_a_4752_ = v___x_4759_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_4767_, 1);
                    crate::leanh::lean_dec_ref(v_mvar_4740_);
                    v___x_4768_ = crate::leanh::lean_box((v___x_4750_) as usize);
                    if v_isShared_4764_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4763_, 0, v___x_4768_);
                        v___x_4770_ = v___x_4763_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4771_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4771_, 0, v___x_4768_);
                        v___x_4770_ = v_reuseFailAlloc_4771_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4770_;
            }
            4 => {
                if v_isShared_4776_ == 0 {
                    v___x_4778_ = v___x_4775_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4779_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4779_, 0, v_a_4773_);
                    v___x_4778_ = v_reuseFailAlloc_4779_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4778_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0___boxed(
    mut v_mvar_4784_: *mut crate::leanh::LeanObject,
    mut v_as_4785_: *mut crate::leanh::LeanObject,
    mut v_i_4786_: *mut crate::leanh::LeanObject,
    mut v_stop_4787_: *mut crate::leanh::LeanObject,
    mut v___y_4788_: *mut crate::leanh::LeanObject,
    mut v___y_4789_: *mut crate::leanh::LeanObject,
    mut v___y_4790_: *mut crate::leanh::LeanObject,
    mut v___y_4791_: *mut crate::leanh::LeanObject,
    mut v___y_4792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4793_: usize = 0;
    let mut v_stop_boxed_4794_: usize = 0;
    let mut v_res_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4793_ = crate::leanh::lean_unbox_usize(v_i_4786_);
    crate::leanh::lean_dec(v_i_4786_);
    v_stop_boxed_4794_ = crate::leanh::lean_unbox_usize(v_stop_4787_);
    crate::leanh::lean_dec(v_stop_4787_);
    v_res_4795_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_4784_, v_as_4785_, v_i_boxed_4793_, v_stop_boxed_4794_, v___y_4788_, v___y_4789_, v___y_4790_, v___y_4791_);
    crate::leanh::lean_dec(v___y_4791_);
    crate::leanh::lean_dec_ref(v___y_4790_);
    crate::leanh::lean_dec(v___y_4789_);
    crate::leanh::lean_dec_ref(v___y_4788_);
    crate::leanh::lean_dec_ref(v_as_4785_);
    return v_res_4795_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(
    mut v_mvar_4796_: *mut crate::leanh::LeanObject,
    mut v_otherMVars_4797_: *mut crate::leanh::LeanObject,
    mut v_a_4798_: *mut crate::leanh::LeanObject,
    mut v_a_4799_: *mut crate::leanh::LeanObject,
    mut v_a_4800_: *mut crate::leanh::LeanObject,
    mut v_a_4801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4805_: u8 = 0;
    v___x_4803_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4804_ = lean_array_get_size(v_otherMVars_4797_);
    v___x_4805_ = lean_nat_dec_lt(v___x_4803_, v___x_4804_);
    if v___x_4805_ == 0 {
        let mut v___x_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_mvar_4796_);
        v___x_4806_ = crate::leanh::lean_box((v___x_4805_) as usize);
        v___x_4807_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4807_, 0, v___x_4806_);
        return v___x_4807_;
    } else {
        if v___x_4805_ == 0 {
            let mut v___x_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v_mvar_4796_);
            v___x_4808_ = crate::leanh::lean_box((v___x_4805_) as usize);
            v___x_4809_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_4809_, 0, v___x_4808_);
            return v___x_4809_;
        } else {
            let mut v___x_4810_: usize = 0;
            let mut v___x_4811_: usize = 0;
            let mut v___x_4812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4810_ = 0usize;
            v___x_4811_ = lean_usize_of_nat(v___x_4804_);
            v___x_4812_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers_spec__0(v_mvar_4796_, v_otherMVars_4797_, v___x_4810_, v___x_4811_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_);
            return v___x_4812_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers___boxed(
    mut v_mvar_4813_: *mut crate::leanh::LeanObject,
    mut v_otherMVars_4814_: *mut crate::leanh::LeanObject,
    mut v_a_4815_: *mut crate::leanh::LeanObject,
    mut v_a_4816_: *mut crate::leanh::LeanObject,
    mut v_a_4817_: *mut crate::leanh::LeanObject,
    mut v_a_4818_: *mut crate::leanh::LeanObject,
    mut v_a_4819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4820_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(
        v_mvar_4813_,
        v_otherMVars_4814_,
        v_a_4815_,
        v_a_4816_,
        v_a_4817_,
        v_a_4818_,
    );
    crate::leanh::lean_dec(v_a_4818_);
    crate::leanh::lean_dec_ref(v_a_4817_);
    crate::leanh::lean_dec(v_a_4816_);
    crate::leanh::lean_dec_ref(v_a_4815_);
    crate::leanh::lean_dec_ref(v_otherMVars_4814_);
    return v_res_4820_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(
    mut v_mvars_4821_: *mut crate::leanh::LeanObject,
    mut v_as_4822_: *mut crate::leanh::LeanObject,
    mut v_i_4823_: usize,
    mut v_stop_4824_: usize,
    mut v_b_4825_: *mut crate::leanh::LeanObject,
    mut v___y_4826_: *mut crate::leanh::LeanObject,
    mut v___y_4827_: *mut crate::leanh::LeanObject,
    mut v___y_4828_: *mut crate::leanh::LeanObject,
    mut v___y_4829_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4831_: u8 = 0;
    let mut v_fst_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4836_: u8 = 0;
    let mut v___x_4837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMVarId_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: usize = 0;
    let mut v___x_4844_: usize = 0;
    let mut v___x_4846_: u8 = 0;
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4858_: u8 = 0;
    let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4862_: u8 = 0;
    let mut v_isSharedCheck_4863_: u8 = 0;
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4831_ = lean_usize_dec_eq(v_i_4823_, v_stop_4824_);
                if v___x_4831_ == 0 {
                    v_fst_4832_ = crate::leanh::lean_ctor_get(v_b_4825_, 0);
                    v_snd_4833_ = crate::leanh::lean_ctor_get(v_b_4825_, 1);
                    v_isSharedCheck_4863_ = (!crate::leanh::lean_is_exclusive(v_b_4825_)) as u8;
                    if v_isSharedCheck_4863_ == 0 {
                        v___x_4835_ = v_b_4825_;
                        v_isShared_4836_ = v_isSharedCheck_4863_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4833_);
                        crate::leanh::lean_inc(v_fst_4832_);
                        crate::leanh::lean_dec(v_b_4825_);
                        v___x_4835_ = crate::leanh::lean_box(0);
                        v_isShared_4836_ = v_isSharedCheck_4863_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_4864_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4864_, 0, v_b_4825_);
                    return v___x_4864_;
                }
            }
            1 => {
                v___x_4837_ = lean_array_uget_borrowed(v_as_4822_, v_i_4823_);
                v_currMVarId_4838_ = l_Lean_Expr_mvarId_x21(v___x_4837_);
                crate::leanh::lean_inc(v___x_4837_);
                v___x_4839_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_dependsOnOthers(
                    v___x_4837_,
                    v_mvars_4821_,
                    v___y_4826_,
                    v___y_4827_,
                    v___y_4828_,
                    v___y_4829_,
                );
                if crate::leanh::lean_obj_tag(v___x_4839_) == 0 {
                    v_a_4840_ = crate::leanh::lean_ctor_get(v___x_4839_, 0);
                    crate::leanh::lean_inc(v_a_4840_);
                    crate::leanh::lean_dec_ref_known(v___x_4839_, 1);
                    v___x_4846_ = (crate::leanh::lean_unbox(v_a_4840_) as u8);
                    crate::leanh::lean_dec(v_a_4840_);
                    if v___x_4846_ == 0 {
                        v___x_4847_ = lean_array_push(v_fst_4832_, v_currMVarId_4838_);
                        if v_isShared_4836_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4835_, 0, v___x_4847_);
                            v___x_4849_ = v___x_4835_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4850_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4850_, 0, v___x_4847_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4850_, 1, v_snd_4833_);
                            v___x_4849_ = v_reuseFailAlloc_4850_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4851_ = lean_array_push(v_snd_4833_, v_currMVarId_4838_);
                        if v_isShared_4836_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4835_, 1, v___x_4851_);
                            v___x_4853_ = v___x_4835_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4854_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4854_, 0, v_fst_4832_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4854_, 1, v___x_4851_);
                            v___x_4853_ = v_reuseFailAlloc_4854_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_currMVarId_4838_);
                    crate::leanh::lean_del_object(v___x_4835_);
                    crate::leanh::lean_dec(v_snd_4833_);
                    crate::leanh::lean_dec(v_fst_4832_);
                    v_a_4855_ = crate::leanh::lean_ctor_get(v___x_4839_, 0);
                    v_isSharedCheck_4862_ = (!crate::leanh::lean_is_exclusive(v___x_4839_)) as u8;
                    if v_isSharedCheck_4862_ == 0 {
                        v___x_4857_ = v___x_4839_;
                        v_isShared_4858_ = v_isSharedCheck_4862_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4855_);
                        crate::leanh::lean_dec(v___x_4839_);
                        v___x_4857_ = crate::leanh::lean_box(0);
                        v_isShared_4858_ = v_isSharedCheck_4862_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4843_ = 1usize;
                v___x_4844_ = lean_usize_add(v_i_4823_, v___x_4843_);
                v_i_4823_ = v___x_4844_;
                v_b_4825_ = v_a_4842_;
                state = 0;
                continue;
            }
            3 => {
                v_a_4842_ = v___x_4849_;
                state = 2;
                continue;
            }
            4 => {
                v_a_4842_ = v___x_4853_;
                state = 2;
                continue;
            }
            5 => {
                if v_isShared_4858_ == 0 {
                    v___x_4860_ = v___x_4857_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4861_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4861_, 0, v_a_4855_);
                    v___x_4860_ = v_reuseFailAlloc_4861_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4860_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0___boxed(
    mut v_mvars_4865_: *mut crate::leanh::LeanObject,
    mut v_as_4866_: *mut crate::leanh::LeanObject,
    mut v_i_4867_: *mut crate::leanh::LeanObject,
    mut v_stop_4868_: *mut crate::leanh::LeanObject,
    mut v_b_4869_: *mut crate::leanh::LeanObject,
    mut v___y_4870_: *mut crate::leanh::LeanObject,
    mut v___y_4871_: *mut crate::leanh::LeanObject,
    mut v___y_4872_: *mut crate::leanh::LeanObject,
    mut v___y_4873_: *mut crate::leanh::LeanObject,
    mut v___y_4874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4875_: usize = 0;
    let mut v_stop_boxed_4876_: usize = 0;
    let mut v_res_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4875_ = crate::leanh::lean_unbox_usize(v_i_4867_);
    crate::leanh::lean_dec(v_i_4867_);
    v_stop_boxed_4876_ = crate::leanh::lean_unbox_usize(v_stop_4868_);
    crate::leanh::lean_dec(v_stop_4868_);
    v_res_4877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_4865_, v_as_4866_, v_i_boxed_4875_, v_stop_boxed_4876_, v_b_4869_, v___y_4870_, v___y_4871_, v___y_4872_, v___y_4873_);
    crate::leanh::lean_dec(v___y_4873_);
    crate::leanh::lean_dec_ref(v___y_4872_);
    crate::leanh::lean_dec(v___y_4871_);
    crate::leanh::lean_dec_ref(v___y_4870_);
    crate::leanh::lean_dec_ref(v_as_4866_);
    crate::leanh::lean_dec_ref(v_mvars_4865_);
    return v_res_4877_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(
    mut v_mvars_4882_: *mut crate::leanh::LeanObject,
    mut v_a_4883_: *mut crate::leanh::LeanObject,
    mut v_a_4884_: *mut crate::leanh::LeanObject,
    mut v_a_4885_: *mut crate::leanh::LeanObject,
    mut v_a_4886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4891_: u8 = 0;
    v___x_4888_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4889_ =
        l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__1;
    v___x_4890_ = lean_array_get_size(v_mvars_4882_);
    v___x_4891_ = lean_nat_dec_lt(v___x_4888_, v___x_4890_);
    if v___x_4891_ == 0 {
        let mut v___x_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4892_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4892_, 0, v___x_4889_);
        return v___x_4892_;
    } else {
        let mut v___x_4893_: u8 = 0;
        v___x_4893_ = lean_nat_dec_le(v___x_4890_, v___x_4890_);
        if v___x_4893_ == 0 {
            if v___x_4891_ == 0 {
                let mut v___x_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4894_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4894_, 0, v___x_4889_);
                return v___x_4894_;
            } else {
                let mut v___x_4895_: usize = 0;
                let mut v___x_4896_: usize = 0;
                let mut v___x_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4895_ = 0usize;
                v___x_4896_ = lean_usize_of_nat(v___x_4890_);
                v___x_4897_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_4882_, v_mvars_4882_, v___x_4895_, v___x_4896_, v___x_4889_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
                return v___x_4897_;
            }
        } else {
            let mut v___x_4898_: usize = 0;
            let mut v___x_4899_: usize = 0;
            let mut v___x_4900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4898_ = 0usize;
            v___x_4899_ = lean_usize_of_nat(v___x_4890_);
            v___x_4900_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars_spec__0(v_mvars_4882_, v_mvars_4882_, v___x_4898_, v___x_4899_, v___x_4889_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
            return v___x_4900_;
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___boxed(
    mut v_mvars_4901_: *mut crate::leanh::LeanObject,
    mut v_a_4902_: *mut crate::leanh::LeanObject,
    mut v_a_4903_: *mut crate::leanh::LeanObject,
    mut v_a_4904_: *mut crate::leanh::LeanObject,
    mut v_a_4905_: *mut crate::leanh::LeanObject,
    mut v_a_4906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4907_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(
        v_mvars_4901_,
        v_a_4902_,
        v_a_4903_,
        v_a_4904_,
        v_a_4905_,
    );
    crate::leanh::lean_dec(v_a_4905_);
    crate::leanh::lean_dec_ref(v_a_4904_);
    crate::leanh::lean_dec(v_a_4903_);
    crate::leanh::lean_dec_ref(v_a_4902_);
    crate::leanh::lean_dec_ref(v_mvars_4901_);
    return v_res_4907_;
}
pub unsafe fn l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(
    mut v_a_4908_: *mut crate::leanh::LeanObject,
    mut v_a_4909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4915_: u8 = 0;
    let mut v___x_4916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4921_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_4908_) == 0 {
                    v___x_4910_ = l_List_reverse___redArg(v_a_4909_);
                    return v___x_4910_;
                } else {
                    v_head_4911_ = crate::leanh::lean_ctor_get(v_a_4908_, 0);
                    v_tail_4912_ = crate::leanh::lean_ctor_get(v_a_4908_, 1);
                    v_isSharedCheck_4921_ = (!crate::leanh::lean_is_exclusive(v_a_4908_)) as u8;
                    if v_isSharedCheck_4921_ == 0 {
                        v___x_4914_ = v_a_4908_;
                        v_isShared_4915_ = v_isSharedCheck_4921_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_4912_);
                        crate::leanh::lean_inc(v_head_4911_);
                        crate::leanh::lean_dec(v_a_4908_);
                        v___x_4914_ = crate::leanh::lean_box(0);
                        v_isShared_4915_ = v_isSharedCheck_4921_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4916_ = l_Lean_Expr_mvarId_x21(v_head_4911_);
                crate::leanh::lean_dec(v_head_4911_);
                if v_isShared_4915_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4914_, 1, v_a_4909_);
                    crate::leanh::lean_ctor_set(v___x_4914_, 0, v___x_4916_);
                    v___x_4918_ = v___x_4914_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4920_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4920_, 0, v___x_4916_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4920_, 1, v_a_4909_);
                    v___x_4918_ = v_reuseFailAlloc_4920_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4908_ = v_tail_4912_;
                v_a_4909_ = v___x_4918_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(
    mut v_mvars_4922_: *mut crate::leanh::LeanObject,
    mut v_x_4923_: u8,
    mut v_a_4924_: *mut crate::leanh::LeanObject,
    mut v_a_4925_: *mut crate::leanh::LeanObject,
    mut v_a_4926_: *mut crate::leanh::LeanObject,
    mut v_a_4927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4933_: u8 = 0;
    let mut v_fst_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4942_: u8 = 0;
    let mut v_a_4943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4946_: u8 = 0;
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4950_: u8 = 0;
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4955_: u8 = 0;
    let mut v_fst_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4961_: u8 = 0;
    let mut v_a_4962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4965_: u8 = 0;
    let mut v___x_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4969_: u8 = 0;
    let mut v___x_4970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_4923_ {
                0 => {
                    v___x_4929_ =
                        l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(
                            v_mvars_4922_,
                            v_a_4924_,
                            v_a_4925_,
                            v_a_4926_,
                            v_a_4927_,
                        );
                    crate::leanh::lean_dec_ref(v_mvars_4922_);
                    if crate::leanh::lean_obj_tag(v___x_4929_) == 0 {
                        v_a_4930_ = crate::leanh::lean_ctor_get(v___x_4929_, 0);
                        v_isSharedCheck_4942_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4929_)) as u8;
                        if v_isSharedCheck_4942_ == 0 {
                            v___x_4932_ = v___x_4929_;
                            v_isShared_4933_ = v_isSharedCheck_4942_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4930_);
                            crate::leanh::lean_dec(v___x_4929_);
                            v___x_4932_ = crate::leanh::lean_box(0);
                            v_isShared_4933_ = v_isSharedCheck_4942_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4943_ = crate::leanh::lean_ctor_get(v___x_4929_, 0);
                        v_isSharedCheck_4950_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4929_)) as u8;
                        if v_isSharedCheck_4950_ == 0 {
                            v___x_4945_ = v___x_4929_;
                            v_isShared_4946_ = v_isSharedCheck_4950_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4943_);
                            crate::leanh::lean_dec(v___x_4929_);
                            v___x_4945_ = crate::leanh::lean_box(0);
                            v_isShared_4946_ = v_isSharedCheck_4950_;
                            state = 3;
                            continue;
                        }
                    }
                }
                1 => {
                    v___x_4951_ =
                        l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars(
                            v_mvars_4922_,
                            v_a_4924_,
                            v_a_4925_,
                            v_a_4926_,
                            v_a_4927_,
                        );
                    crate::leanh::lean_dec_ref(v_mvars_4922_);
                    if crate::leanh::lean_obj_tag(v___x_4951_) == 0 {
                        v_a_4952_ = crate::leanh::lean_ctor_get(v___x_4951_, 0);
                        v_isSharedCheck_4961_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4951_)) as u8;
                        if v_isSharedCheck_4961_ == 0 {
                            v___x_4954_ = v___x_4951_;
                            v_isShared_4955_ = v_isSharedCheck_4961_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4952_);
                            crate::leanh::lean_dec(v___x_4951_);
                            v___x_4954_ = crate::leanh::lean_box(0);
                            v_isShared_4955_ = v_isSharedCheck_4961_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_4962_ = crate::leanh::lean_ctor_get(v___x_4951_, 0);
                        v_isSharedCheck_4969_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4951_)) as u8;
                        if v_isSharedCheck_4969_ == 0 {
                            v___x_4964_ = v___x_4951_;
                            v_isShared_4965_ = v_isSharedCheck_4969_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4962_);
                            crate::leanh::lean_dec(v___x_4951_);
                            v___x_4964_ = crate::leanh::lean_box(0);
                            v_isShared_4965_ = v_isSharedCheck_4969_;
                            state = 7;
                            continue;
                        }
                    }
                }
                _ => {
                    v___x_4970_ = lean_array_to_list(v_mvars_4922_);
                    v___x_4971_ = crate::leanh::lean_box(0);
                    v___x_4972_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals_spec__0(v___x_4970_, v___x_4971_);
                    v___x_4973_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4973_, 0, v___x_4972_);
                    return v___x_4973_;
                }
            },
            1 => {
                v_fst_4934_ = crate::leanh::lean_ctor_get(v_a_4930_, 0);
                crate::leanh::lean_inc(v_fst_4934_);
                v_snd_4935_ = crate::leanh::lean_ctor_get(v_a_4930_, 1);
                crate::leanh::lean_inc(v_snd_4935_);
                crate::leanh::lean_dec(v_a_4930_);
                v___x_4936_ = lean_array_to_list(v_fst_4934_);
                v___x_4937_ = lean_array_to_list(v_snd_4935_);
                v___x_4938_ = l_List_appendTR___redArg(v___x_4936_, v___x_4937_);
                if v_isShared_4933_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4932_, 0, v___x_4938_);
                    v___x_4940_ = v___x_4932_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4941_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4941_, 0, v___x_4938_);
                    v___x_4940_ = v_reuseFailAlloc_4941_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4940_;
            }
            3 => {
                if v_isShared_4946_ == 0 {
                    v___x_4948_ = v___x_4945_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4949_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4949_, 0, v_a_4943_);
                    v___x_4948_ = v_reuseFailAlloc_4949_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4948_;
            }
            5 => {
                v_fst_4956_ = crate::leanh::lean_ctor_get(v_a_4952_, 0);
                crate::leanh::lean_inc(v_fst_4956_);
                crate::leanh::lean_dec(v_a_4952_);
                v___x_4957_ = lean_array_to_list(v_fst_4956_);
                if v_isShared_4955_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4954_, 0, v___x_4957_);
                    v___x_4959_ = v___x_4954_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4960_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4960_, 0, v___x_4957_);
                    v___x_4959_ = v_reuseFailAlloc_4960_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4959_;
            }
            7 => {
                if v_isShared_4965_ == 0 {
                    v___x_4967_ = v___x_4964_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4968_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4968_, 0, v_a_4962_);
                    v___x_4967_ = v_reuseFailAlloc_4968_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4967_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals___boxed(
    mut v_mvars_4974_: *mut crate::leanh::LeanObject,
    mut v_x_4975_: *mut crate::leanh::LeanObject,
    mut v_a_4976_: *mut crate::leanh::LeanObject,
    mut v_a_4977_: *mut crate::leanh::LeanObject,
    mut v_a_4978_: *mut crate::leanh::LeanObject,
    mut v_a_4979_: *mut crate::leanh::LeanObject,
    mut v_a_4980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_820__boxed_4981_: u8 = 0;
    let mut v_res_4982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_820__boxed_4981_ = (crate::leanh::lean_unbox(v_x_4975_) as u8);
    v_res_4982_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(
        v_mvars_4974_,
        v_x_820__boxed_4981_,
        v_a_4976_,
        v_a_4977_,
        v_a_4978_,
        v_a_4979_,
    );
    crate::leanh::lean_dec(v_a_4979_);
    crate::leanh::lean_dec_ref(v_a_4978_);
    crate::leanh::lean_dec(v_a_4977_);
    crate::leanh::lean_dec_ref(v_a_4976_);
    return v_res_4982_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(
    mut v_approx_4983_: u8,
    mut v_a_4984_: *mut crate::leanh::LeanObject,
    mut v_b_4985_: *mut crate::leanh::LeanObject,
    mut v_a_4986_: *mut crate::leanh::LeanObject,
    mut v_a_4987_: *mut crate::leanh::LeanObject,
    mut v_a_4988_: *mut crate::leanh::LeanObject,
    mut v_a_4989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_constApprox_4993_: u8 = 0;
    let mut v_isDefEqStuckEx_4994_: u8 = 0;
    let mut v_unificationHints_4995_: u8 = 0;
    let mut v_proofIrrelevance_4996_: u8 = 0;
    let mut v_assignSyntheticOpaque_4997_: u8 = 0;
    let mut v_offsetCnstrs_4998_: u8 = 0;
    let mut v_transparency_4999_: u8 = 0;
    let mut v_etaStruct_5000_: u8 = 0;
    let mut v_univApprox_5001_: u8 = 0;
    let mut v_iota_5002_: u8 = 0;
    let mut v_beta_5003_: u8 = 0;
    let mut v_proj_5004_: u8 = 0;
    let mut v_zeta_5005_: u8 = 0;
    let mut v_zetaDelta_5006_: u8 = 0;
    let mut v_zetaUnused_5007_: u8 = 0;
    let mut v_zetaHave_5008_: u8 = 0;
    let mut v___x_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5011_: u8 = 0;
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_5014_: u8 = 0;
    let mut v_zetaDeltaSet_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_5021_: u8 = 0;
    let mut v_inTypeClassResolution_5022_: u8 = 0;
    let mut v_cacheInferType_5023_: u8 = 0;
    let mut v___x_5024_: u64 = 0;
    let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5029_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_approx_4983_ == 0 {
                    v___x_4991_ = l_Lean_Meta_isExprDefEqGuarded(
                        v_a_4984_, v_b_4985_, v_a_4986_, v_a_4987_, v_a_4988_, v_a_4989_,
                    );
                    return v___x_4991_;
                } else {
                    v___x_4992_ = l_Lean_Meta_Context_config(v_a_4986_);
                    v_constApprox_4993_ = crate::leanh::lean_ctor_get_uint8(v___x_4992_, 3 as u32);
                    v_isDefEqStuckEx_4994_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_4992_, 4 as u32);
                    v_unificationHints_4995_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_4992_, 5 as u32);
                    v_proofIrrelevance_4996_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_4992_, 6 as u32);
                    v_assignSyntheticOpaque_4997_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_4992_, 7 as u32);
                    v_offsetCnstrs_4998_ = crate::leanh::lean_ctor_get_uint8(v___x_4992_, 8 as u32);
                    v_transparency_4999_ = crate::leanh::lean_ctor_get_uint8(v___x_4992_, 9 as u32);
                    v_etaStruct_5000_ = crate::leanh::lean_ctor_get_uint8(v___x_4992_, 10 as u32);
                    v_univApprox_5001_ = crate::leanh::lean_ctor_get_uint8(v___x_4992_, 11 as u32);
                    v_iota_5002_ = crate::leanh::lean_ctor_get_uint8(v___x_4992_, 12 as u32);
                    v_beta_5003_ = crate::leanh::lean_ctor_get_uint8(v___x_4992_, 13 as u32);
                    v_proj_5004_ = crate::leanh::lean_ctor_get_uint8(v___x_4992_, 14 as u32);
                    v_zeta_5005_ = crate::leanh::lean_ctor_get_uint8(v___x_4992_, 15 as u32);
                    v_zetaDelta_5006_ = crate::leanh::lean_ctor_get_uint8(v___x_4992_, 16 as u32);
                    v_zetaUnused_5007_ = crate::leanh::lean_ctor_get_uint8(v___x_4992_, 17 as u32);
                    v_zetaHave_5008_ = crate::leanh::lean_ctor_get_uint8(v___x_4992_, 18 as u32);
                    v_isSharedCheck_5029_ = (!crate::leanh::lean_is_exclusive(v___x_4992_)) as u8;
                    if v_isSharedCheck_5029_ == 0 {
                        v___x_5010_ = v___x_4992_;
                        v_isShared_5011_ = v_isSharedCheck_5029_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4992_);
                        v___x_5010_ = crate::leanh::lean_box(0);
                        v_isShared_5011_ = v_isSharedCheck_5029_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5011_ == 0 {
                    v___x_5013_ = v___x_5010_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5028_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5028_,
                        3 as u32,
                        v_constApprox_4993_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5028_,
                        4 as u32,
                        v_isDefEqStuckEx_4994_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5028_,
                        5 as u32,
                        v_unificationHints_4995_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5028_,
                        6 as u32,
                        v_proofIrrelevance_4996_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5028_,
                        7 as u32,
                        v_assignSyntheticOpaque_4997_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5028_,
                        8 as u32,
                        v_offsetCnstrs_4998_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5028_,
                        9 as u32,
                        v_transparency_4999_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5028_,
                        10 as u32,
                        v_etaStruct_5000_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5028_,
                        11 as u32,
                        v_univApprox_5001_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5028_,
                        12 as u32,
                        v_iota_5002_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5028_,
                        13 as u32,
                        v_beta_5003_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5028_,
                        14 as u32,
                        v_proj_5004_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5028_,
                        15 as u32,
                        v_zeta_5005_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5028_,
                        16 as u32,
                        v_zetaDelta_5006_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5028_,
                        17 as u32,
                        v_zetaUnused_5007_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5028_,
                        18 as u32,
                        v_zetaHave_5008_,
                    );
                    v___x_5013_ = v_reuseFailAlloc_5028_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(v___x_5013_, 0 as u32, v_approx_4983_);
                crate::leanh::lean_ctor_set_uint8(v___x_5013_, 1 as u32, v_approx_4983_);
                crate::leanh::lean_ctor_set_uint8(v___x_5013_, 2 as u32, v_approx_4983_);
                v_trackZetaDelta_5014_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4986_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_5015_ = crate::leanh::lean_ctor_get(v_a_4986_, 1);
                v_lctx_5016_ = crate::leanh::lean_ctor_get(v_a_4986_, 2);
                v_localInstances_5017_ = crate::leanh::lean_ctor_get(v_a_4986_, 3);
                v_defEqCtx_x3f_5018_ = crate::leanh::lean_ctor_get(v_a_4986_, 4);
                v_synthPendingDepth_5019_ = crate::leanh::lean_ctor_get(v_a_4986_, 5);
                v_canUnfold_x3f_5020_ = crate::leanh::lean_ctor_get(v_a_4986_, 6);
                v_univApprox_5021_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4986_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_5022_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4986_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_5023_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_4986_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_5024_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5013_);
                v___x_5025_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_5025_, 0, v___x_5013_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_5025_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_5024_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_5020_);
                crate::leanh::lean_inc(v_synthPendingDepth_5019_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_5018_);
                crate::leanh::lean_inc_ref(v_localInstances_5017_);
                crate::leanh::lean_inc_ref(v_lctx_5016_);
                crate::leanh::lean_inc(v_zetaDeltaSet_5015_);
                v___x_5026_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_5026_, 0, v___x_5025_);
                crate::leanh::lean_ctor_set(v___x_5026_, 1, v_zetaDeltaSet_5015_);
                crate::leanh::lean_ctor_set(v___x_5026_, 2, v_lctx_5016_);
                crate::leanh::lean_ctor_set(v___x_5026_, 3, v_localInstances_5017_);
                crate::leanh::lean_ctor_set(v___x_5026_, 4, v_defEqCtx_x3f_5018_);
                crate::leanh::lean_ctor_set(v___x_5026_, 5, v_synthPendingDepth_5019_);
                crate::leanh::lean_ctor_set(v___x_5026_, 6, v_canUnfold_x3f_5020_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5026_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_5014_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5026_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_5021_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5026_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_5022_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_5026_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_5023_,
                );
                v___x_5027_ = l_Lean_Meta_isExprDefEqGuarded(
                    v_a_4984_,
                    v_b_4985_,
                    v___x_5026_,
                    v_a_4987_,
                    v_a_4988_,
                    v_a_4989_,
                );
                crate::leanh::lean_dec_ref_known(v___x_5026_, 7);
                return v___x_5027_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply___boxed(
    mut v_approx_5030_: *mut crate::leanh::LeanObject,
    mut v_a_5031_: *mut crate::leanh::LeanObject,
    mut v_b_5032_: *mut crate::leanh::LeanObject,
    mut v_a_5033_: *mut crate::leanh::LeanObject,
    mut v_a_5034_: *mut crate::leanh::LeanObject,
    mut v_a_5035_: *mut crate::leanh::LeanObject,
    mut v_a_5036_: *mut crate::leanh::LeanObject,
    mut v_a_5037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_approx_boxed_5038_: u8 = 0;
    let mut v_res_5039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_approx_boxed_5038_ = (crate::leanh::lean_unbox(v_approx_5030_) as u8);
    v_res_5039_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(
        v_approx_boxed_5038_,
        v_a_5031_,
        v_b_5032_,
        v_a_5033_,
        v_a_5034_,
        v_a_5035_,
        v_a_5036_,
    );
    crate::leanh::lean_dec(v_a_5036_);
    crate::leanh::lean_dec_ref(v_a_5035_);
    crate::leanh::lean_dec(v_a_5034_);
    crate::leanh::lean_dec_ref(v_a_5033_);
    return v_res_5039_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(
    mut v_mvarId_5040_: *mut crate::leanh::LeanObject,
    mut v_cfg_5041_: *mut crate::leanh::LeanObject,
    mut v_term_x3f_5042_: *mut crate::leanh::LeanObject,
    mut v_targetType_5043_: *mut crate::leanh::LeanObject,
    mut v_eType_5044_: *mut crate::leanh::LeanObject,
    mut v_rangeNumArgs_5045_: *mut crate::leanh::LeanObject,
    mut v_i_5046_: *mut crate::leanh::LeanObject,
    mut v_a_5047_: *mut crate::leanh::LeanObject,
    mut v_a_5048_: *mut crate::leanh::LeanObject,
    mut v_a_5049_: *mut crate::leanh::LeanObject,
    mut v_a_5050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_5053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: u8 = 0;
    let mut v___x_5055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5056_: u8 = 0;
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: u8 = 0;
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5068_: u8 = 0;
    let mut v___x_5070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5072_: u8 = 0;
    let mut v___x_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5078_: u8 = 0;
    let mut v___x_5079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5087_: u8 = 0;
    let mut v_approx_5088_: u8 = 0;
    let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5093_: u8 = 0;
    let mut v___x_5094_: u8 = 0;
    let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5102_: u8 = 0;
    let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5106_: u8 = 0;
    let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5113_: u8 = 0;
    let mut v_a_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5117_: u8 = 0;
    let mut v___x_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5121_: u8 = 0;
    let mut v_isSharedCheck_5122_: u8 = 0;
    let mut v_a_5123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5126_: u8 = 0;
    let mut v___x_5128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5130_: u8 = 0;
    let mut v_a_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5134_: u8 = 0;
    let mut v___x_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5138_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_5052_ = crate::leanh::lean_ctor_get(v_rangeNumArgs_5045_, 0);
                v_upper_5053_ = crate::leanh::lean_ctor_get(v_rangeNumArgs_5045_, 1);
                v___x_5054_ = lean_nat_dec_lt(v_i_5046_, v_upper_5053_);
                if v___x_5054_ == 0 {
                    crate::leanh::lean_dec(v_i_5046_);
                    v___x_5055_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5056_ = lean_nat_dec_eq(v_lower_5052_, v___x_5055_);
                    if v___x_5056_ == 0 {
                        crate::leanh::lean_inc(v_lower_5052_);
                        v___x_5057_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5057_, 0, v_lower_5052_);
                        v___x_5058_ = 0;
                        crate::leanh::lean_inc_ref(v_eType_5044_);
                        v___x_5059_ = l_Lean_Meta_forallMetaTelescopeReducing(
                            v_eType_5044_,
                            v___x_5057_,
                            v___x_5058_,
                            v_a_5047_,
                            v_a_5048_,
                            v_a_5049_,
                            v_a_5050_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5059_) == 0 {
                            v_a_5060_ = crate::leanh::lean_ctor_get(v___x_5059_, 0);
                            crate::leanh::lean_inc(v_a_5060_);
                            crate::leanh::lean_dec_ref_known(v___x_5059_, 1);
                            v_snd_5061_ = crate::leanh::lean_ctor_get(v_a_5060_, 1);
                            crate::leanh::lean_inc(v_snd_5061_);
                            crate::leanh::lean_dec(v_a_5060_);
                            v_snd_5062_ = crate::leanh::lean_ctor_get(v_snd_5061_, 1);
                            crate::leanh::lean_inc(v_snd_5062_);
                            crate::leanh::lean_dec(v_snd_5061_);
                            v___x_5063_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_5063_, 0, v_snd_5062_);
                            v___x_5064_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_5040_, v_eType_5044_, v___x_5063_, v_targetType_5043_, v_term_x3f_5042_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_);
                            return v___x_5064_;
                        } else {
                            crate::leanh::lean_dec_ref(v_eType_5044_);
                            crate::leanh::lean_dec_ref(v_targetType_5043_);
                            crate::leanh::lean_dec(v_term_x3f_5042_);
                            crate::leanh::lean_dec(v_mvarId_5040_);
                            v_a_5065_ = crate::leanh::lean_ctor_get(v___x_5059_, 0);
                            v_isSharedCheck_5072_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5059_)) as u8;
                            if v_isSharedCheck_5072_ == 0 {
                                v___x_5067_ = v___x_5059_;
                                v_isShared_5068_ = v_isSharedCheck_5072_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5065_);
                                crate::leanh::lean_dec(v___x_5059_);
                                v___x_5067_ = crate::leanh::lean_box(0);
                                v_isShared_5068_ = v_isSharedCheck_5072_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        v___x_5073_ = crate::leanh::lean_box(0);
                        v___x_5074_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg(v_mvarId_5040_, v_eType_5044_, v___x_5073_, v_targetType_5043_, v_term_x3f_5042_, v_a_5047_, v_a_5048_, v_a_5049_, v_a_5050_);
                        return v___x_5074_;
                    }
                } else {
                    v___x_5075_ = l_Lean_Meta_saveState___redArg(v_a_5048_, v_a_5050_);
                    if crate::leanh::lean_obj_tag(v___x_5075_) == 0 {
                        v_a_5076_ = crate::leanh::lean_ctor_get(v___x_5075_, 0);
                        crate::leanh::lean_inc(v_a_5076_);
                        crate::leanh::lean_dec_ref_known(v___x_5075_, 1);
                        crate::leanh::lean_inc(v_i_5046_);
                        v___x_5077_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5077_, 0, v_i_5046_);
                        v___x_5078_ = 0;
                        crate::leanh::lean_inc_ref(v_eType_5044_);
                        v___x_5079_ = l_Lean_Meta_forallMetaTelescopeReducing(
                            v_eType_5044_,
                            v___x_5077_,
                            v___x_5078_,
                            v_a_5047_,
                            v_a_5048_,
                            v_a_5049_,
                            v_a_5050_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5079_) == 0 {
                            v_a_5080_ = crate::leanh::lean_ctor_get(v___x_5079_, 0);
                            crate::leanh::lean_inc(v_a_5080_);
                            crate::leanh::lean_dec_ref_known(v___x_5079_, 1);
                            v_snd_5081_ = crate::leanh::lean_ctor_get(v_a_5080_, 1);
                            crate::leanh::lean_inc(v_snd_5081_);
                            v_fst_5082_ = crate::leanh::lean_ctor_get(v_a_5080_, 0);
                            crate::leanh::lean_inc(v_fst_5082_);
                            crate::leanh::lean_dec(v_a_5080_);
                            v_fst_5083_ = crate::leanh::lean_ctor_get(v_snd_5081_, 0);
                            v_snd_5084_ = crate::leanh::lean_ctor_get(v_snd_5081_, 1);
                            v_isSharedCheck_5122_ =
                                (!crate::leanh::lean_is_exclusive(v_snd_5081_)) as u8;
                            if v_isSharedCheck_5122_ == 0 {
                                v___x_5086_ = v_snd_5081_;
                                v_isShared_5087_ = v_isSharedCheck_5122_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_snd_5084_);
                                crate::leanh::lean_inc(v_fst_5083_);
                                crate::leanh::lean_dec(v_snd_5081_);
                                v___x_5086_ = crate::leanh::lean_box(0);
                                v_isShared_5087_ = v_isSharedCheck_5122_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5076_);
                            crate::leanh::lean_dec(v_i_5046_);
                            crate::leanh::lean_dec_ref(v_eType_5044_);
                            crate::leanh::lean_dec_ref(v_targetType_5043_);
                            crate::leanh::lean_dec(v_term_x3f_5042_);
                            crate::leanh::lean_dec(v_mvarId_5040_);
                            v_a_5123_ = crate::leanh::lean_ctor_get(v___x_5079_, 0);
                            v_isSharedCheck_5130_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5079_)) as u8;
                            if v_isSharedCheck_5130_ == 0 {
                                v___x_5125_ = v___x_5079_;
                                v_isShared_5126_ = v_isSharedCheck_5130_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5123_);
                                crate::leanh::lean_dec(v___x_5079_);
                                v___x_5125_ = crate::leanh::lean_box(0);
                                v_isShared_5126_ = v_isSharedCheck_5130_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_i_5046_);
                        crate::leanh::lean_dec_ref(v_eType_5044_);
                        crate::leanh::lean_dec_ref(v_targetType_5043_);
                        crate::leanh::lean_dec(v_term_x3f_5042_);
                        crate::leanh::lean_dec(v_mvarId_5040_);
                        v_a_5131_ = crate::leanh::lean_ctor_get(v___x_5075_, 0);
                        v_isSharedCheck_5138_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5075_)) as u8;
                        if v_isSharedCheck_5138_ == 0 {
                            v___x_5133_ = v___x_5075_;
                            v_isShared_5134_ = v_isSharedCheck_5138_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5131_);
                            crate::leanh::lean_dec(v___x_5075_);
                            v___x_5133_ = crate::leanh::lean_box(0);
                            v_isShared_5134_ = v_isSharedCheck_5138_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5068_ == 0 {
                    v___x_5070_ = v___x_5067_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5071_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_a_5065_);
                    v___x_5070_ = v_reuseFailAlloc_5071_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5070_;
            }
            3 => {
                v_approx_5088_ = crate::leanh::lean_ctor_get_uint8(v_cfg_5041_, 3 as u32);
                crate::leanh::lean_inc_ref(v_targetType_5043_);
                v___x_5089_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(
                    v_approx_5088_,
                    v_snd_5084_,
                    v_targetType_5043_,
                    v_a_5047_,
                    v_a_5048_,
                    v_a_5049_,
                    v_a_5050_,
                );
                if crate::leanh::lean_obj_tag(v___x_5089_) == 0 {
                    v_a_5090_ = crate::leanh::lean_ctor_get(v___x_5089_, 0);
                    v_isSharedCheck_5113_ = (!crate::leanh::lean_is_exclusive(v___x_5089_)) as u8;
                    if v_isSharedCheck_5113_ == 0 {
                        v___x_5092_ = v___x_5089_;
                        v_isShared_5093_ = v_isSharedCheck_5113_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5090_);
                        crate::leanh::lean_dec(v___x_5089_);
                        v___x_5092_ = crate::leanh::lean_box(0);
                        v_isShared_5093_ = v_isSharedCheck_5113_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5086_);
                    crate::leanh::lean_dec(v_fst_5083_);
                    crate::leanh::lean_dec(v_fst_5082_);
                    crate::leanh::lean_dec(v_a_5076_);
                    crate::leanh::lean_dec(v_i_5046_);
                    crate::leanh::lean_dec_ref(v_eType_5044_);
                    crate::leanh::lean_dec_ref(v_targetType_5043_);
                    crate::leanh::lean_dec(v_term_x3f_5042_);
                    crate::leanh::lean_dec(v_mvarId_5040_);
                    v_a_5114_ = crate::leanh::lean_ctor_get(v___x_5089_, 0);
                    v_isSharedCheck_5121_ = (!crate::leanh::lean_is_exclusive(v___x_5089_)) as u8;
                    if v_isSharedCheck_5121_ == 0 {
                        v___x_5116_ = v___x_5089_;
                        v_isShared_5117_ = v_isSharedCheck_5121_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5114_);
                        crate::leanh::lean_dec(v___x_5089_);
                        v___x_5116_ = crate::leanh::lean_box(0);
                        v_isShared_5117_ = v_isSharedCheck_5121_;
                        state = 9;
                        continue;
                    }
                }
            }
            4 => {
                v___x_5094_ = (crate::leanh::lean_unbox(v_a_5090_) as u8);
                crate::leanh::lean_dec(v_a_5090_);
                if v___x_5094_ == 0 {
                    crate::leanh::lean_del_object(v___x_5092_);
                    crate::leanh::lean_del_object(v___x_5086_);
                    crate::leanh::lean_dec(v_fst_5083_);
                    crate::leanh::lean_dec(v_fst_5082_);
                    v___x_5095_ =
                        l_Lean_Meta_SavedState_restore___redArg(v_a_5076_, v_a_5048_, v_a_5050_);
                    crate::leanh::lean_dec(v_a_5076_);
                    if crate::leanh::lean_obj_tag(v___x_5095_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5095_, 1);
                        v___x_5096_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5097_ = lean_nat_add(v_i_5046_, v___x_5096_);
                        crate::leanh::lean_dec(v_i_5046_);
                        v_i_5046_ = v___x_5097_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_i_5046_);
                        crate::leanh::lean_dec_ref(v_eType_5044_);
                        crate::leanh::lean_dec_ref(v_targetType_5043_);
                        crate::leanh::lean_dec(v_term_x3f_5042_);
                        crate::leanh::lean_dec(v_mvarId_5040_);
                        v_a_5099_ = crate::leanh::lean_ctor_get(v___x_5095_, 0);
                        v_isSharedCheck_5106_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5095_)) as u8;
                        if v_isSharedCheck_5106_ == 0 {
                            v___x_5101_ = v___x_5095_;
                            v_isShared_5102_ = v_isSharedCheck_5106_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5099_);
                            crate::leanh::lean_dec(v___x_5095_);
                            v___x_5101_ = crate::leanh::lean_box(0);
                            v_isShared_5102_ = v_isSharedCheck_5106_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5076_);
                    crate::leanh::lean_dec(v_i_5046_);
                    crate::leanh::lean_dec_ref(v_eType_5044_);
                    crate::leanh::lean_dec_ref(v_targetType_5043_);
                    crate::leanh::lean_dec(v_term_x3f_5042_);
                    crate::leanh::lean_dec(v_mvarId_5040_);
                    if v_isShared_5087_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5086_, 1, v_fst_5083_);
                        crate::leanh::lean_ctor_set(v___x_5086_, 0, v_fst_5082_);
                        v___x_5108_ = v___x_5086_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5112_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5112_, 0, v_fst_5082_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5112_, 1, v_fst_5083_);
                        v___x_5108_ = v_reuseFailAlloc_5112_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_5102_ == 0 {
                    v___x_5104_ = v___x_5101_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5105_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5105_, 0, v_a_5099_);
                    v___x_5104_ = v_reuseFailAlloc_5105_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5104_;
            }
            7 => {
                if v_isShared_5093_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5092_, 0, v___x_5108_);
                    v___x_5110_ = v___x_5092_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5111_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5111_, 0, v___x_5108_);
                    v___x_5110_ = v_reuseFailAlloc_5111_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5110_;
            }
            9 => {
                if v_isShared_5117_ == 0 {
                    v___x_5119_ = v___x_5116_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5120_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5120_, 0, v_a_5114_);
                    v___x_5119_ = v_reuseFailAlloc_5120_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5119_;
            }
            11 => {
                if v_isShared_5126_ == 0 {
                    v___x_5128_ = v___x_5125_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5129_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5129_, 0, v_a_5123_);
                    v___x_5128_ = v_reuseFailAlloc_5129_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5128_;
            }
            13 => {
                if v_isShared_5134_ == 0 {
                    v___x_5136_ = v___x_5133_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5137_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5137_, 0, v_a_5131_);
                    v___x_5136_ = v_reuseFailAlloc_5137_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5136_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go___boxed(
    mut v_mvarId_5139_: *mut crate::leanh::LeanObject,
    mut v_cfg_5140_: *mut crate::leanh::LeanObject,
    mut v_term_x3f_5141_: *mut crate::leanh::LeanObject,
    mut v_targetType_5142_: *mut crate::leanh::LeanObject,
    mut v_eType_5143_: *mut crate::leanh::LeanObject,
    mut v_rangeNumArgs_5144_: *mut crate::leanh::LeanObject,
    mut v_i_5145_: *mut crate::leanh::LeanObject,
    mut v_a_5146_: *mut crate::leanh::LeanObject,
    mut v_a_5147_: *mut crate::leanh::LeanObject,
    mut v_a_5148_: *mut crate::leanh::LeanObject,
    mut v_a_5149_: *mut crate::leanh::LeanObject,
    mut v_a_5150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5151_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(
        v_mvarId_5139_,
        v_cfg_5140_,
        v_term_x3f_5141_,
        v_targetType_5142_,
        v_eType_5143_,
        v_rangeNumArgs_5144_,
        v_i_5145_,
        v_a_5146_,
        v_a_5147_,
        v_a_5148_,
        v_a_5149_,
    );
    crate::leanh::lean_dec(v_a_5149_);
    crate::leanh::lean_dec_ref(v_a_5148_);
    crate::leanh::lean_dec(v_a_5147_);
    crate::leanh::lean_dec_ref(v_a_5146_);
    crate::leanh::lean_dec_ref(v_rangeNumArgs_5144_);
    crate::leanh::lean_dec_ref(v_cfg_5140_);
    return v_res_5151_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter___redArg(
    mut v_x_5152_: *mut crate::leanh::LeanObject,
    mut v_h__1_5153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_5154_ = crate::leanh::lean_ctor_get(v_x_5152_, 1);
    crate::leanh::lean_inc(v_snd_5154_);
    v_fst_5155_ = crate::leanh::lean_ctor_get(v_x_5152_, 0);
    crate::leanh::lean_inc(v_fst_5155_);
    crate::leanh::lean_dec_ref(v_x_5152_);
    v_fst_5156_ = crate::leanh::lean_ctor_get(v_snd_5154_, 0);
    crate::leanh::lean_inc(v_fst_5156_);
    v_snd_5157_ = crate::leanh::lean_ctor_get(v_snd_5154_, 1);
    crate::leanh::lean_inc(v_snd_5157_);
    crate::leanh::lean_dec(v_snd_5154_);
    v___x_5158_ = crate::leanh::lean_apply_3(v_h__1_5153_, v_fst_5155_, v_fst_5156_, v_snd_5157_);
    return v___x_5158_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go_match__1_splitter(
    mut v_motive_5159_: *mut crate::leanh::LeanObject,
    mut v_x_5160_: *mut crate::leanh::LeanObject,
    mut v_h__1_5161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_snd_5162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_snd_5162_ = crate::leanh::lean_ctor_get(v_x_5160_, 1);
    crate::leanh::lean_inc(v_snd_5162_);
    v_fst_5163_ = crate::leanh::lean_ctor_get(v_x_5160_, 0);
    crate::leanh::lean_inc(v_fst_5163_);
    crate::leanh::lean_dec_ref(v_x_5160_);
    v_fst_5164_ = crate::leanh::lean_ctor_get(v_snd_5162_, 0);
    crate::leanh::lean_inc(v_fst_5164_);
    v_snd_5165_ = crate::leanh::lean_ctor_get(v_snd_5162_, 1);
    crate::leanh::lean_inc(v_snd_5165_);
    crate::leanh::lean_dec(v_snd_5162_);
    v___x_5166_ = crate::leanh::lean_apply_3(v_h__1_5161_, v_fst_5163_, v_fst_5164_, v_snd_5165_);
    return v___x_5166_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(
    mut v_e_5167_: *mut crate::leanh::LeanObject,
    mut v___y_5168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5170_: u8 = 0;
    let mut v___x_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5184_: u8 = 0;
    let mut v___x_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5190_: u8 = 0;
    let mut v_unused_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5170_ = l_Lean_Expr_hasMVar(v_e_5167_);
                if v___x_5170_ == 0 {
                    v___x_5171_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5171_, 0, v_e_5167_);
                    return v___x_5171_;
                } else {
                    v___x_5172_ = lean_st_ref_get(v___y_5168_);
                    v_mctx_5173_ = crate::leanh::lean_ctor_get(v___x_5172_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_5173_);
                    crate::leanh::lean_dec(v___x_5172_);
                    v___x_5174_ = l_Lean_instantiateMVarsCore(v_mctx_5173_, v_e_5167_);
                    v_fst_5175_ = crate::leanh::lean_ctor_get(v___x_5174_, 0);
                    crate::leanh::lean_inc(v_fst_5175_);
                    v_snd_5176_ = crate::leanh::lean_ctor_get(v___x_5174_, 1);
                    crate::leanh::lean_inc(v_snd_5176_);
                    crate::leanh::lean_dec_ref(v___x_5174_);
                    v___x_5177_ = lean_st_ref_take(v___y_5168_);
                    v_cache_5178_ = crate::leanh::lean_ctor_get(v___x_5177_, 1);
                    v_zetaDeltaFVarIds_5179_ = crate::leanh::lean_ctor_get(v___x_5177_, 2);
                    v_postponed_5180_ = crate::leanh::lean_ctor_get(v___x_5177_, 3);
                    v_diag_5181_ = crate::leanh::lean_ctor_get(v___x_5177_, 4);
                    v_isSharedCheck_5190_ = (!crate::leanh::lean_is_exclusive(v___x_5177_)) as u8;
                    if v_isSharedCheck_5190_ == 0 {
                        v_unused_5191_ = crate::leanh::lean_ctor_get(v___x_5177_, 0);
                        crate::leanh::lean_dec(v_unused_5191_);
                        v___x_5183_ = v___x_5177_;
                        v_isShared_5184_ = v_isSharedCheck_5190_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_5181_);
                        crate::leanh::lean_inc(v_postponed_5180_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_5179_);
                        crate::leanh::lean_inc(v_cache_5178_);
                        crate::leanh::lean_dec(v___x_5177_);
                        v___x_5183_ = crate::leanh::lean_box(0);
                        v_isShared_5184_ = v_isSharedCheck_5190_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5184_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5183_, 0, v_snd_5176_);
                    v___x_5186_ = v___x_5183_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5189_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5189_, 0, v_snd_5176_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5189_, 1, v_cache_5178_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5189_,
                        2,
                        v_zetaDeltaFVarIds_5179_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5189_, 3, v_postponed_5180_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5189_, 4, v_diag_5181_);
                    v___x_5186_ = v_reuseFailAlloc_5189_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5187_ = lean_st_ref_set(v___y_5168_, v___x_5186_);
                v___x_5188_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5188_, 0, v_fst_5175_);
                return v___x_5188_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg___boxed(
    mut v_e_5192_: *mut crate::leanh::LeanObject,
    mut v___y_5193_: *mut crate::leanh::LeanObject,
    mut v___y_5194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5195_ =
        l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_5192_, v___y_5193_);
    crate::leanh::lean_dec(v___y_5193_);
    return v_res_5195_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(
    mut v_e_5196_: *mut crate::leanh::LeanObject,
    mut v___y_5197_: *mut crate::leanh::LeanObject,
    mut v___y_5198_: *mut crate::leanh::LeanObject,
    mut v___y_5199_: *mut crate::leanh::LeanObject,
    mut v___y_5200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5202_ =
        l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(v_e_5196_, v___y_5198_);
    return v___x_5202_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___boxed(
    mut v_e_5203_: *mut crate::leanh::LeanObject,
    mut v___y_5204_: *mut crate::leanh::LeanObject,
    mut v___y_5205_: *mut crate::leanh::LeanObject,
    mut v___y_5206_: *mut crate::leanh::LeanObject,
    mut v___y_5207_: *mut crate::leanh::LeanObject,
    mut v___y_5208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5209_ = l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0(
        v_e_5203_,
        v___y_5204_,
        v___y_5205_,
        v___y_5206_,
        v___y_5207_,
    );
    crate::leanh::lean_dec(v___y_5207_);
    crate::leanh::lean_dec_ref(v___y_5206_);
    crate::leanh::lean_dec(v___y_5205_);
    crate::leanh::lean_dec_ref(v___y_5204_);
    return v_res_5209_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(
    mut v_mvarId_5210_: *mut crate::leanh::LeanObject,
    mut v_x_5211_: *mut crate::leanh::LeanObject,
    mut v___y_5212_: *mut crate::leanh::LeanObject,
    mut v___y_5213_: *mut crate::leanh::LeanObject,
    mut v___y_5214_: *mut crate::leanh::LeanObject,
    mut v___y_5215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5221_: u8 = 0;
    let mut v___x_5223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5225_: u8 = 0;
    let mut v_a_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5229_: u8 = 0;
    let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5233_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5217_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_5210_,
                    v_x_5211_,
                    v___y_5212_,
                    v___y_5213_,
                    v___y_5214_,
                    v___y_5215_,
                );
                if crate::leanh::lean_obj_tag(v___x_5217_) == 0 {
                    v_a_5218_ = crate::leanh::lean_ctor_get(v___x_5217_, 0);
                    v_isSharedCheck_5225_ = (!crate::leanh::lean_is_exclusive(v___x_5217_)) as u8;
                    if v_isSharedCheck_5225_ == 0 {
                        v___x_5220_ = v___x_5217_;
                        v_isShared_5221_ = v_isSharedCheck_5225_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5218_);
                        crate::leanh::lean_dec(v___x_5217_);
                        v___x_5220_ = crate::leanh::lean_box(0);
                        v_isShared_5221_ = v_isSharedCheck_5225_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5226_ = crate::leanh::lean_ctor_get(v___x_5217_, 0);
                    v_isSharedCheck_5233_ = (!crate::leanh::lean_is_exclusive(v___x_5217_)) as u8;
                    if v_isSharedCheck_5233_ == 0 {
                        v___x_5228_ = v___x_5217_;
                        v_isShared_5229_ = v_isSharedCheck_5233_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5226_);
                        crate::leanh::lean_dec(v___x_5217_);
                        v___x_5228_ = crate::leanh::lean_box(0);
                        v_isShared_5229_ = v_isSharedCheck_5233_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5221_ == 0 {
                    v___x_5223_ = v___x_5220_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5224_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5224_, 0, v_a_5218_);
                    v___x_5223_ = v_reuseFailAlloc_5224_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5223_;
            }
            3 => {
                if v_isShared_5229_ == 0 {
                    v___x_5231_ = v___x_5228_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5232_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5232_, 0, v_a_5226_);
                    v___x_5231_ = v_reuseFailAlloc_5232_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg___boxed(
    mut v_mvarId_5234_: *mut crate::leanh::LeanObject,
    mut v_x_5235_: *mut crate::leanh::LeanObject,
    mut v___y_5236_: *mut crate::leanh::LeanObject,
    mut v___y_5237_: *mut crate::leanh::LeanObject,
    mut v___y_5238_: *mut crate::leanh::LeanObject,
    mut v___y_5239_: *mut crate::leanh::LeanObject,
    mut v___y_5240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5241_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(
        v_mvarId_5234_,
        v_x_5235_,
        v___y_5236_,
        v___y_5237_,
        v___y_5238_,
        v___y_5239_,
    );
    crate::leanh::lean_dec(v___y_5239_);
    crate::leanh::lean_dec_ref(v___y_5238_);
    crate::leanh::lean_dec(v___y_5237_);
    crate::leanh::lean_dec_ref(v___y_5236_);
    return v_res_5241_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(
    mut v_00_u03b1_5242_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5243_: *mut crate::leanh::LeanObject,
    mut v_x_5244_: *mut crate::leanh::LeanObject,
    mut v___y_5245_: *mut crate::leanh::LeanObject,
    mut v___y_5246_: *mut crate::leanh::LeanObject,
    mut v___y_5247_: *mut crate::leanh::LeanObject,
    mut v___y_5248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5250_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(
        v_mvarId_5243_,
        v_x_5244_,
        v___y_5245_,
        v___y_5246_,
        v___y_5247_,
        v___y_5248_,
    );
    return v___x_5250_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___boxed(
    mut v_00_u03b1_5251_: *mut crate::leanh::LeanObject,
    mut v_mvarId_5252_: *mut crate::leanh::LeanObject,
    mut v_x_5253_: *mut crate::leanh::LeanObject,
    mut v___y_5254_: *mut crate::leanh::LeanObject,
    mut v___y_5255_: *mut crate::leanh::LeanObject,
    mut v___y_5256_: *mut crate::leanh::LeanObject,
    mut v___y_5257_: *mut crate::leanh::LeanObject,
    mut v___y_5258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5259_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6(
        v_00_u03b1_5251_,
        v_mvarId_5252_,
        v_x_5253_,
        v___y_5254_,
        v___y_5255_,
        v___y_5256_,
        v___y_5257_,
    );
    crate::leanh::lean_dec(v___y_5257_);
    crate::leanh::lean_dec_ref(v___y_5256_);
    crate::leanh::lean_dec(v___y_5255_);
    crate::leanh::lean_dec_ref(v___y_5254_);
    return v_res_5259_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(
    mut v_as_5260_: *mut crate::leanh::LeanObject,
    mut v_i_5261_: usize,
    mut v_stop_5262_: usize,
    mut v_b_5263_: *mut crate::leanh::LeanObject,
    mut v___y_5264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: usize = 0;
    let mut v___x_5269_: usize = 0;
    let mut v___x_5271_: u8 = 0;
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: u8 = 0;
    let mut v_a_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: u8 = 0;
    let mut v_a_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5284_: u8 = 0;
    let mut v___x_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5288_: u8 = 0;
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5271_ = lean_usize_dec_eq(v_i_5261_, v_stop_5262_);
                if v___x_5271_ == 0 {
                    v___x_5272_ = lean_array_uget_borrowed(v_as_5260_, v_i_5261_);
                    v___x_5275_ = l_Lean_Expr_mvarId_x21(v___x_5272_);
                    v___x_5276_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0___redArg(v___x_5275_, v___y_5264_);
                    crate::leanh::lean_dec(v___x_5275_);
                    if crate::leanh::lean_obj_tag(v___x_5276_) == 0 {
                        v_a_5277_ = crate::leanh::lean_ctor_get(v___x_5276_, 0);
                        crate::leanh::lean_inc(v_a_5277_);
                        crate::leanh::lean_dec_ref_known(v___x_5276_, 1);
                        v___x_5278_ = (crate::leanh::lean_unbox(v_a_5277_) as u8);
                        crate::leanh::lean_dec(v_a_5277_);
                        if v___x_5278_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v_a_5267_ = v_b_5263_;
                            state = 1;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v___x_5276_) == 0 {
                            v_a_5279_ = crate::leanh::lean_ctor_get(v___x_5276_, 0);
                            crate::leanh::lean_inc(v_a_5279_);
                            crate::leanh::lean_dec_ref_known(v___x_5276_, 1);
                            v___x_5280_ = (crate::leanh::lean_unbox(v_a_5279_) as u8);
                            crate::leanh::lean_dec(v_a_5279_);
                            if v___x_5280_ == 0 {
                                v_a_5267_ = v_b_5263_;
                                state = 1;
                                continue;
                            } else {
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_b_5263_);
                            v_a_5281_ = crate::leanh::lean_ctor_get(v___x_5276_, 0);
                            v_isSharedCheck_5288_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5276_)) as u8;
                            if v_isSharedCheck_5288_ == 0 {
                                v___x_5283_ = v___x_5276_;
                                v_isShared_5284_ = v_isSharedCheck_5288_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5281_);
                                crate::leanh::lean_dec(v___x_5276_);
                                v___x_5283_ = crate::leanh::lean_box(0);
                                v_isShared_5284_ = v_isSharedCheck_5288_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_5289_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5289_, 0, v_b_5263_);
                    return v___x_5289_;
                }
            }
            1 => {
                v___x_5268_ = 1usize;
                v___x_5269_ = lean_usize_add(v_i_5261_, v___x_5268_);
                v_i_5261_ = v___x_5269_;
                v_b_5263_ = v_a_5267_;
                state = 0;
                continue;
            }
            2 => {
                crate::leanh::lean_inc(v___x_5272_);
                v___x_5274_ = lean_array_push(v_b_5263_, v___x_5272_);
                v_a_5267_ = v___x_5274_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_5284_ == 0 {
                    v___x_5286_ = v___x_5283_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5287_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5287_, 0, v_a_5281_);
                    v___x_5286_ = v_reuseFailAlloc_5287_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5286_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg___boxed(
    mut v_as_5290_: *mut crate::leanh::LeanObject,
    mut v_i_5291_: *mut crate::leanh::LeanObject,
    mut v_stop_5292_: *mut crate::leanh::LeanObject,
    mut v_b_5293_: *mut crate::leanh::LeanObject,
    mut v___y_5294_: *mut crate::leanh::LeanObject,
    mut v___y_5295_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5296_: usize = 0;
    let mut v_stop_boxed_5297_: usize = 0;
    let mut v_res_5298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5296_ = crate::leanh::lean_unbox_usize(v_i_5291_);
    crate::leanh::lean_dec(v_i_5291_);
    v_stop_boxed_5297_ = crate::leanh::lean_unbox_usize(v_stop_5292_);
    crate::leanh::lean_dec(v_stop_5292_);
    v_res_5298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_5290_, v_i_boxed_5296_, v_stop_boxed_5297_, v_b_5293_, v___y_5294_);
    crate::leanh::lean_dec(v___y_5294_);
    crate::leanh::lean_dec_ref(v_as_5290_);
    return v_res_5298_;
}
pub unsafe fn l_List_forM___at___00Lean_MVarId_apply_spec__3(
    mut v_as_5299_: *mut crate::leanh::LeanObject,
    mut v___y_5300_: *mut crate::leanh::LeanObject,
    mut v___y_5301_: *mut crate::leanh::LeanObject,
    mut v___y_5302_: *mut crate::leanh::LeanObject,
    mut v___y_5303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_as_5299_) == 0 {
                    v___x_5305_ = crate::leanh::lean_box(0);
                    v___x_5306_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5306_, 0, v___x_5305_);
                    return v___x_5306_;
                } else {
                    v_head_5307_ = crate::leanh::lean_ctor_get(v_as_5299_, 0);
                    crate::leanh::lean_inc(v_head_5307_);
                    v_tail_5308_ = crate::leanh::lean_ctor_get(v_as_5299_, 1);
                    crate::leanh::lean_inc(v_tail_5308_);
                    crate::leanh::lean_dec_ref_known(v_as_5299_, 2);
                    v___x_5309_ = l_Lean_MVarId_headBetaType(
                        v_head_5307_,
                        v___y_5300_,
                        v___y_5301_,
                        v___y_5302_,
                        v___y_5303_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5309_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5309_, 1);
                        v_as_5299_ = v_tail_5308_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_tail_5308_);
                        return v___x_5309_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00Lean_MVarId_apply_spec__3___boxed(
    mut v_as_5311_: *mut crate::leanh::LeanObject,
    mut v___y_5312_: *mut crate::leanh::LeanObject,
    mut v___y_5313_: *mut crate::leanh::LeanObject,
    mut v___y_5314_: *mut crate::leanh::LeanObject,
    mut v___y_5315_: *mut crate::leanh::LeanObject,
    mut v___y_5316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5317_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(
        v_as_5311_,
        v___y_5312_,
        v___y_5313_,
        v___y_5314_,
        v___y_5315_,
    );
    crate::leanh::lean_dec(v___y_5315_);
    crate::leanh::lean_dec_ref(v___y_5314_);
    crate::leanh::lean_dec(v___y_5313_);
    crate::leanh::lean_dec_ref(v___y_5312_);
    return v_res_5317_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(
    mut v_x_5318_: *mut crate::leanh::LeanObject,
    mut v_x_5319_: *mut crate::leanh::LeanObject,
    mut v_x_5320_: *mut crate::leanh::LeanObject,
    mut v_x_5321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_5322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5326_: u8 = 0;
    let mut v___x_5327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5328_: u8 = 0;
    let mut v___x_5329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5335_: u8 = 0;
    let mut v___x_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5347_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_5322_ = crate::leanh::lean_ctor_get(v_x_5318_, 0);
                v_vs_5323_ = crate::leanh::lean_ctor_get(v_x_5318_, 1);
                v_isSharedCheck_5347_ = (!crate::leanh::lean_is_exclusive(v_x_5318_)) as u8;
                if v_isSharedCheck_5347_ == 0 {
                    v___x_5325_ = v_x_5318_;
                    v_isShared_5326_ = v_isSharedCheck_5347_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_5323_);
                    crate::leanh::lean_inc(v_ks_5322_);
                    crate::leanh::lean_dec(v_x_5318_);
                    v___x_5325_ = crate::leanh::lean_box(0);
                    v_isShared_5326_ = v_isSharedCheck_5347_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5327_ = lean_array_get_size(v_ks_5322_);
                v___x_5328_ = lean_nat_dec_lt(v_x_5319_, v___x_5327_);
                if v___x_5328_ == 0 {
                    crate::leanh::lean_dec(v_x_5319_);
                    v___x_5329_ = lean_array_push(v_ks_5322_, v_x_5320_);
                    v___x_5330_ = lean_array_push(v_vs_5323_, v_x_5321_);
                    if v_isShared_5326_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5325_, 1, v___x_5330_);
                        crate::leanh::lean_ctor_set(v___x_5325_, 0, v___x_5329_);
                        v___x_5332_ = v___x_5325_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5333_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5333_, 0, v___x_5329_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5333_, 1, v___x_5330_);
                        v___x_5332_ = v_reuseFailAlloc_5333_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_5334_ = lean_array_fget_borrowed(v_ks_5322_, v_x_5319_);
                    v___x_5335_ = l_Lean_instBEqMVarId_beq(v_x_5320_, v_k_x27_5334_);
                    if v___x_5335_ == 0 {
                        if v_isShared_5326_ == 0 {
                            v___x_5337_ = v___x_5325_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5341_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5341_, 0, v_ks_5322_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5341_, 1, v_vs_5323_);
                            v___x_5337_ = v_reuseFailAlloc_5341_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_5342_ = lean_array_fset(v_ks_5322_, v_x_5319_, v_x_5320_);
                        v___x_5343_ = lean_array_fset(v_vs_5323_, v_x_5319_, v_x_5321_);
                        crate::leanh::lean_dec(v_x_5319_);
                        if v_isShared_5326_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5325_, 1, v___x_5343_);
                            crate::leanh::lean_ctor_set(v___x_5325_, 0, v___x_5342_);
                            v___x_5345_ = v___x_5325_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5346_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5346_, 0, v___x_5342_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5346_, 1, v___x_5343_);
                            v___x_5345_ = v_reuseFailAlloc_5346_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5332_;
            }
            3 => {
                v___x_5338_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5339_ = lean_nat_add(v_x_5319_, v___x_5338_);
                crate::leanh::lean_dec(v_x_5319_);
                v_x_5318_ = v___x_5337_;
                v_x_5319_ = v___x_5339_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_5345_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(
    mut v_n_5348_: *mut crate::leanh::LeanObject,
    mut v_k_5349_: *mut crate::leanh::LeanObject,
    mut v_v_5350_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5351_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_5352_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_n_5348_, v___x_5351_, v_k_5349_, v_v_5350_);
    return v___x_5352_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5353_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_5353_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(
    mut v_x_5354_: *mut crate::leanh::LeanObject,
    mut v_x_5355_: usize,
    mut v_x_5356_: usize,
    mut v_x_5357_: *mut crate::leanh::LeanObject,
    mut v_x_5358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5360_: usize = 0;
    let mut v___x_5361_: usize = 0;
    let mut v___x_5362_: usize = 0;
    let mut v___x_5363_: usize = 0;
    let mut v_j_5364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5366_: u8 = 0;
    let mut v___x_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5369_: u8 = 0;
    let mut v_v_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5383_: u8 = 0;
    let mut v___x_5384_: u8 = 0;
    let mut v___x_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5390_: u8 = 0;
    let mut v_node_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5394_: u8 = 0;
    let mut v___x_5395_: usize = 0;
    let mut v___x_5396_: usize = 0;
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5401_: u8 = 0;
    let mut v___x_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5403_: u8 = 0;
    let mut v_unused_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5409_: u8 = 0;
    let mut v___x_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_5412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5414_: u8 = 0;
    let mut v_ks_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_5416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5420_: usize = 0;
    let mut v___x_5421_: u8 = 0;
    let mut v___x_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5424_: u8 = 0;
    let mut v_reuseFailAlloc_5425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5426_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5354_) == 0 {
                    v_es_5359_ = crate::leanh::lean_ctor_get(v_x_5354_, 0);
                    v___x_5360_ = 5usize;
                    v___x_5361_ = 1usize;
                    v___x_5362_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_synthAppInstances_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_5363_ = lean_usize_land(v_x_5355_, v___x_5362_);
                    v_j_5364_ = lean_usize_to_nat(v___x_5363_);
                    v___x_5365_ = lean_array_get_size(v_es_5359_);
                    v___x_5366_ = lean_nat_dec_lt(v_j_5364_, v___x_5365_);
                    if v___x_5366_ == 0 {
                        crate::leanh::lean_dec(v_j_5364_);
                        crate::leanh::lean_dec(v_x_5358_);
                        crate::leanh::lean_dec(v_x_5357_);
                        return v_x_5354_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_5359_);
                        v_isSharedCheck_5403_ = (!crate::leanh::lean_is_exclusive(v_x_5354_)) as u8;
                        if v_isSharedCheck_5403_ == 0 {
                            v_unused_5404_ = crate::leanh::lean_ctor_get(v_x_5354_, 0);
                            crate::leanh::lean_dec(v_unused_5404_);
                            v___x_5368_ = v_x_5354_;
                            v_isShared_5369_ = v_isSharedCheck_5403_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_5354_);
                            v___x_5368_ = crate::leanh::lean_box(0);
                            v_isShared_5369_ = v_isSharedCheck_5403_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_5405_ = crate::leanh::lean_ctor_get(v_x_5354_, 0);
                    v_vs_5406_ = crate::leanh::lean_ctor_get(v_x_5354_, 1);
                    v_isSharedCheck_5426_ = (!crate::leanh::lean_is_exclusive(v_x_5354_)) as u8;
                    if v_isSharedCheck_5426_ == 0 {
                        v___x_5408_ = v_x_5354_;
                        v_isShared_5409_ = v_isSharedCheck_5426_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_5406_);
                        crate::leanh::lean_inc(v_ks_5405_);
                        crate::leanh::lean_dec(v_x_5354_);
                        v___x_5408_ = crate::leanh::lean_box(0);
                        v_isShared_5409_ = v_isSharedCheck_5426_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_5370_ = lean_array_fget(v_es_5359_, v_j_5364_);
                v___x_5371_ = crate::leanh::lean_box(0);
                v_xs_x27_5372_ = lean_array_fset(v_es_5359_, v_j_5364_, v___x_5371_);
                match crate::leanh::lean_obj_tag(v_v_5370_) {
                    0 => {
                        v_key_5379_ = crate::leanh::lean_ctor_get(v_v_5370_, 0);
                        v_val_5380_ = crate::leanh::lean_ctor_get(v_v_5370_, 1);
                        v_isSharedCheck_5390_ = (!crate::leanh::lean_is_exclusive(v_v_5370_)) as u8;
                        if v_isSharedCheck_5390_ == 0 {
                            v___x_5382_ = v_v_5370_;
                            v_isShared_5383_ = v_isSharedCheck_5390_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_5380_);
                            crate::leanh::lean_inc(v_key_5379_);
                            crate::leanh::lean_dec(v_v_5370_);
                            v___x_5382_ = crate::leanh::lean_box(0);
                            v_isShared_5383_ = v_isSharedCheck_5390_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_5391_ = crate::leanh::lean_ctor_get(v_v_5370_, 0);
                        v_isSharedCheck_5401_ = (!crate::leanh::lean_is_exclusive(v_v_5370_)) as u8;
                        if v_isSharedCheck_5401_ == 0 {
                            v___x_5393_ = v_v_5370_;
                            v_isShared_5394_ = v_isSharedCheck_5401_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_5391_);
                            crate::leanh::lean_dec(v_v_5370_);
                            v___x_5393_ = crate::leanh::lean_box(0);
                            v_isShared_5394_ = v_isSharedCheck_5401_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_5402_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5402_, 0, v_x_5357_);
                        crate::leanh::lean_ctor_set(v___x_5402_, 1, v_x_5358_);
                        v___y_5374_ = v___x_5402_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5375_ = lean_array_fset(v_xs_x27_5372_, v_j_5364_, v___y_5374_);
                crate::leanh::lean_dec(v_j_5364_);
                if v_isShared_5369_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5368_, 0, v___x_5375_);
                    v___x_5377_ = v___x_5368_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5378_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5378_, 0, v___x_5375_);
                    v___x_5377_ = v_reuseFailAlloc_5378_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5377_;
            }
            4 => {
                v___x_5384_ = l_Lean_instBEqMVarId_beq(v_x_5357_, v_key_5379_);
                if v___x_5384_ == 0 {
                    crate::leanh::lean_del_object(v___x_5382_);
                    v___x_5385_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_5379_,
                        v_val_5380_,
                        v_x_5357_,
                        v_x_5358_,
                    );
                    v___x_5386_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5386_, 0, v___x_5385_);
                    v___y_5374_ = v___x_5386_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_5380_);
                    crate::leanh::lean_dec(v_key_5379_);
                    if v_isShared_5383_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5382_, 1, v_x_5358_);
                        crate::leanh::lean_ctor_set(v___x_5382_, 0, v_x_5357_);
                        v___x_5388_ = v___x_5382_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5389_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5389_, 0, v_x_5357_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5389_, 1, v_x_5358_);
                        v___x_5388_ = v_reuseFailAlloc_5389_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_5374_ = v___x_5388_;
                state = 2;
                continue;
            }
            6 => {
                v___x_5395_ = lean_usize_shift_right(v_x_5355_, v___x_5360_);
                v___x_5396_ = lean_usize_add(v_x_5356_, v___x_5361_);
                v___x_5397_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_node_5391_, v___x_5395_, v___x_5396_, v_x_5357_, v_x_5358_);
                if v_isShared_5394_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5393_, 0, v___x_5397_);
                    v___x_5399_ = v___x_5393_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5400_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5400_, 0, v___x_5397_);
                    v___x_5399_ = v_reuseFailAlloc_5400_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_5374_ = v___x_5399_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_5409_ == 0 {
                    v___x_5411_ = v___x_5408_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5425_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5425_, 0, v_ks_5405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5425_, 1, v_vs_5406_);
                    v___x_5411_ = v_reuseFailAlloc_5425_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_5412_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v___x_5411_, v_x_5357_, v_x_5358_);
                v___x_5420_ = 7usize;
                v___x_5421_ = lean_usize_dec_le(v___x_5420_, v_x_5356_);
                if v___x_5421_ == 0 {
                    v___x_5422_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_5412_);
                    v___x_5423_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_5424_ = lean_nat_dec_lt(v___x_5422_, v___x_5423_);
                    crate::leanh::lean_dec(v___x_5422_);
                    v___y_5414_ = v___x_5424_;
                    state = 10;
                    continue;
                } else {
                    v___y_5414_ = v___x_5421_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_5414_ == 0 {
                    v_ks_5415_ = crate::leanh::lean_ctor_get(v_newNode_5412_, 0);
                    crate::leanh::lean_inc_ref(v_ks_5415_);
                    v_vs_5416_ = crate::leanh::lean_ctor_get(v_newNode_5412_, 1);
                    crate::leanh::lean_inc_ref(v_vs_5416_);
                    crate::leanh::lean_dec_ref(v_newNode_5412_);
                    v___x_5417_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5418_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___closed__0);
                    v___x_5419_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_x_5356_, v_ks_5415_, v_vs_5416_, v___x_5417_, v___x_5418_);
                    crate::leanh::lean_dec_ref(v_vs_5416_);
                    crate::leanh::lean_dec_ref(v_ks_5415_);
                    return v___x_5419_;
                } else {
                    return v_newNode_5412_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(
    mut v_depth_5427_: usize,
    mut v_keys_5428_: *mut crate::leanh::LeanObject,
    mut v_vals_5429_: *mut crate::leanh::LeanObject,
    mut v_i_5430_: *mut crate::leanh::LeanObject,
    mut v_entries_5431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5433_: u8 = 0;
    let mut v_k_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5436_: u64 = 0;
    let mut v_h_5437_: usize = 0;
    let mut v___x_5438_: usize = 0;
    let mut v___x_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: usize = 0;
    let mut v___x_5441_: usize = 0;
    let mut v___x_5442_: usize = 0;
    let mut v_h_5443_: usize = 0;
    let mut v___x_5444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5432_ = lean_array_get_size(v_keys_5428_);
                v___x_5433_ = lean_nat_dec_lt(v_i_5430_, v___x_5432_);
                if v___x_5433_ == 0 {
                    crate::leanh::lean_dec(v_i_5430_);
                    return v_entries_5431_;
                } else {
                    v_k_5434_ = lean_array_fget_borrowed(v_keys_5428_, v_i_5430_);
                    v_v_5435_ = lean_array_fget_borrowed(v_vals_5429_, v_i_5430_);
                    v___x_5436_ = l_Lean_instHashableMVarId_hash(v_k_5434_);
                    v_h_5437_ = lean_uint64_to_usize(v___x_5436_);
                    v___x_5438_ = 5usize;
                    v___x_5439_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5440_ = 1usize;
                    v___x_5441_ = lean_usize_sub(v_depth_5427_, v___x_5440_);
                    v___x_5442_ = lean_usize_mul(v___x_5438_, v___x_5441_);
                    v_h_5443_ = lean_usize_shift_right(v_h_5437_, v___x_5442_);
                    v___x_5444_ = lean_nat_add(v_i_5430_, v___x_5439_);
                    crate::leanh::lean_dec(v_i_5430_);
                    crate::leanh::lean_inc(v_v_5435_);
                    crate::leanh::lean_inc(v_k_5434_);
                    v___x_5445_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_entries_5431_, v_h_5443_, v_depth_5427_, v_k_5434_, v_v_5435_);
                    v_i_5430_ = v___x_5444_;
                    v_entries_5431_ = v___x_5445_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg___boxed(
    mut v_depth_5447_: *mut crate::leanh::LeanObject,
    mut v_keys_5448_: *mut crate::leanh::LeanObject,
    mut v_vals_5449_: *mut crate::leanh::LeanObject,
    mut v_i_5450_: *mut crate::leanh::LeanObject,
    mut v_entries_5451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_5452_: usize = 0;
    let mut v_res_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5452_ = crate::leanh::lean_unbox_usize(v_depth_5447_);
    crate::leanh::lean_dec(v_depth_5447_);
    v_res_5453_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_boxed_5452_, v_keys_5448_, v_vals_5449_, v_i_5450_, v_entries_5451_);
    crate::leanh::lean_dec_ref(v_vals_5449_);
    crate::leanh::lean_dec_ref(v_keys_5448_);
    return v_res_5453_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg___boxed(
    mut v_x_5454_: *mut crate::leanh::LeanObject,
    mut v_x_5455_: *mut crate::leanh::LeanObject,
    mut v_x_5456_: *mut crate::leanh::LeanObject,
    mut v_x_5457_: *mut crate::leanh::LeanObject,
    mut v_x_5458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7242__boxed_5459_: usize = 0;
    let mut v_x_7243__boxed_5460_: usize = 0;
    let mut v_res_5461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7242__boxed_5459_ = crate::leanh::lean_unbox_usize(v_x_5455_);
    crate::leanh::lean_dec(v_x_5455_);
    v_x_7243__boxed_5460_ = crate::leanh::lean_unbox_usize(v_x_5456_);
    crate::leanh::lean_dec(v_x_5456_);
    v_res_5461_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_5454_, v_x_7242__boxed_5459_, v_x_7243__boxed_5460_, v_x_5457_, v_x_5458_);
    return v_res_5461_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(
    mut v_x_5462_: *mut crate::leanh::LeanObject,
    mut v_x_5463_: *mut crate::leanh::LeanObject,
    mut v_x_5464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5465_: u64 = 0;
    let mut v___x_5466_: usize = 0;
    let mut v___x_5467_: usize = 0;
    let mut v___x_5468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5465_ = l_Lean_instHashableMVarId_hash(v_x_5463_);
    v___x_5466_ = lean_uint64_to_usize(v___x_5465_);
    v___x_5467_ = 1usize;
    v___x_5468_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_5462_, v___x_5466_, v___x_5467_, v_x_5463_, v_x_5464_);
    return v___x_5468_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(
    mut v_mvarId_5469_: *mut crate::leanh::LeanObject,
    mut v_val_5470_: *mut crate::leanh::LeanObject,
    mut v___y_5471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5481_: u8 = 0;
    let mut v_depth_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_5489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5494_: u8 = 0;
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5505_: u8 = 0;
    let mut v_isSharedCheck_5506_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5473_ = lean_st_ref_take(v___y_5471_);
                v_mctx_5474_ = crate::leanh::lean_ctor_get(v___x_5473_, 0);
                v_cache_5475_ = crate::leanh::lean_ctor_get(v___x_5473_, 1);
                v_zetaDeltaFVarIds_5476_ = crate::leanh::lean_ctor_get(v___x_5473_, 2);
                v_postponed_5477_ = crate::leanh::lean_ctor_get(v___x_5473_, 3);
                v_diag_5478_ = crate::leanh::lean_ctor_get(v___x_5473_, 4);
                v_isSharedCheck_5506_ = (!crate::leanh::lean_is_exclusive(v___x_5473_)) as u8;
                if v_isSharedCheck_5506_ == 0 {
                    v___x_5480_ = v___x_5473_;
                    v_isShared_5481_ = v_isSharedCheck_5506_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_5478_);
                    crate::leanh::lean_inc(v_postponed_5477_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_5476_);
                    crate::leanh::lean_inc(v_cache_5475_);
                    crate::leanh::lean_inc(v_mctx_5474_);
                    crate::leanh::lean_dec(v___x_5473_);
                    v___x_5480_ = crate::leanh::lean_box(0);
                    v_isShared_5481_ = v_isSharedCheck_5506_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_5482_ = crate::leanh::lean_ctor_get(v_mctx_5474_, 0);
                v_levelAssignDepth_5483_ = crate::leanh::lean_ctor_get(v_mctx_5474_, 1);
                v_lmvarCounter_5484_ = crate::leanh::lean_ctor_get(v_mctx_5474_, 2);
                v_mvarCounter_5485_ = crate::leanh::lean_ctor_get(v_mctx_5474_, 3);
                v_lDecls_5486_ = crate::leanh::lean_ctor_get(v_mctx_5474_, 4);
                v_decls_5487_ = crate::leanh::lean_ctor_get(v_mctx_5474_, 5);
                v_userNames_5488_ = crate::leanh::lean_ctor_get(v_mctx_5474_, 6);
                v_lAssignment_5489_ = crate::leanh::lean_ctor_get(v_mctx_5474_, 7);
                v_eAssignment_5490_ = crate::leanh::lean_ctor_get(v_mctx_5474_, 8);
                v_dAssignment_5491_ = crate::leanh::lean_ctor_get(v_mctx_5474_, 9);
                v_isSharedCheck_5505_ = (!crate::leanh::lean_is_exclusive(v_mctx_5474_)) as u8;
                if v_isSharedCheck_5505_ == 0 {
                    v___x_5493_ = v_mctx_5474_;
                    v_isShared_5494_ = v_isSharedCheck_5505_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_5491_);
                    crate::leanh::lean_inc(v_eAssignment_5490_);
                    crate::leanh::lean_inc(v_lAssignment_5489_);
                    crate::leanh::lean_inc(v_userNames_5488_);
                    crate::leanh::lean_inc(v_decls_5487_);
                    crate::leanh::lean_inc(v_lDecls_5486_);
                    crate::leanh::lean_inc(v_mvarCounter_5485_);
                    crate::leanh::lean_inc(v_lmvarCounter_5484_);
                    crate::leanh::lean_inc(v_levelAssignDepth_5483_);
                    crate::leanh::lean_inc(v_depth_5482_);
                    crate::leanh::lean_dec(v_mctx_5474_);
                    v___x_5493_ = crate::leanh::lean_box(0);
                    v_isShared_5494_ = v_isSharedCheck_5505_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5495_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_eAssignment_5490_, v_mvarId_5469_, v_val_5470_);
                if v_isShared_5494_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5493_, 8, v___x_5495_);
                    v___x_5497_ = v___x_5493_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5504_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5504_, 0, v_depth_5482_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5504_,
                        1,
                        v_levelAssignDepth_5483_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5504_, 2, v_lmvarCounter_5484_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5504_, 3, v_mvarCounter_5485_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5504_, 4, v_lDecls_5486_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5504_, 5, v_decls_5487_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5504_, 6, v_userNames_5488_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5504_, 7, v_lAssignment_5489_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5504_, 8, v___x_5495_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5504_, 9, v_dAssignment_5491_);
                    v___x_5497_ = v_reuseFailAlloc_5504_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5481_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5480_, 0, v___x_5497_);
                    v___x_5499_ = v___x_5480_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5503_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5503_, 0, v___x_5497_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5503_, 1, v_cache_5475_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_5503_,
                        2,
                        v_zetaDeltaFVarIds_5476_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5503_, 3, v_postponed_5477_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5503_, 4, v_diag_5478_);
                    v___x_5499_ = v_reuseFailAlloc_5503_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5500_ = lean_st_ref_set(v___y_5471_, v___x_5499_);
                v___x_5501_ = crate::leanh::lean_box(0);
                v___x_5502_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5502_, 0, v___x_5501_);
                return v___x_5502_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg___boxed(
    mut v_mvarId_5507_: *mut crate::leanh::LeanObject,
    mut v_val_5508_: *mut crate::leanh::LeanObject,
    mut v___y_5509_: *mut crate::leanh::LeanObject,
    mut v___y_5510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5511_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(
        v_mvarId_5507_,
        v_val_5508_,
        v___y_5509_,
    );
    crate::leanh::lean_dec(v___y_5509_);
    return v_res_5511_;
}
pub unsafe fn l_List_elem___at___00Lean_MVarId_apply_spec__2(
    mut v_a_5512_: *mut crate::leanh::LeanObject,
    mut v_x_5513_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_5514_: u8 = 0;
    let mut v_head_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_5513_) == 0 {
                    v___x_5514_ = 0;
                    return v___x_5514_;
                } else {
                    v_head_5515_ = crate::leanh::lean_ctor_get(v_x_5513_, 0);
                    v_tail_5516_ = crate::leanh::lean_ctor_get(v_x_5513_, 1);
                    v___x_5517_ = l_Lean_instBEqMVarId_beq(v_a_5512_, v_head_5515_);
                    if v___x_5517_ == 0 {
                        v_x_5513_ = v_tail_5516_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5517_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00Lean_MVarId_apply_spec__2___boxed(
    mut v_a_5519_: *mut crate::leanh::LeanObject,
    mut v_x_5520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5521_: u8 = 0;
    let mut v_r_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5521_ = l_List_elem___at___00Lean_MVarId_apply_spec__2(v_a_5519_, v_x_5520_);
    crate::leanh::lean_dec(v_x_5520_);
    crate::leanh::lean_dec(v_a_5519_);
    v_r_5522_ = crate::leanh::lean_box((v_res_5521_) as usize);
    return v_r_5522_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(
    mut v_a_5523_: *mut crate::leanh::LeanObject,
    mut v_as_5524_: *mut crate::leanh::LeanObject,
    mut v_i_5525_: usize,
    mut v_stop_5526_: usize,
    mut v_b_5527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5530_: usize = 0;
    let mut v___x_5531_: usize = 0;
    let mut v___x_5533_: u8 = 0;
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5535_: u8 = 0;
    let mut v___x_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5533_ = lean_usize_dec_eq(v_i_5525_, v_stop_5526_);
                if v___x_5533_ == 0 {
                    v___x_5534_ = lean_array_uget_borrowed(v_as_5524_, v_i_5525_);
                    v___x_5535_ =
                        l_List_elem___at___00Lean_MVarId_apply_spec__2(v___x_5534_, v_a_5523_);
                    if v___x_5535_ == 0 {
                        crate::leanh::lean_inc(v___x_5534_);
                        v___x_5536_ = lean_array_push(v_b_5527_, v___x_5534_);
                        v___y_5529_ = v___x_5536_;
                        state = 1;
                        continue;
                    } else {
                        v___y_5529_ = v_b_5527_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_5527_;
                }
            }
            1 => {
                v___x_5530_ = 1usize;
                v___x_5531_ = lean_usize_add(v_i_5525_, v___x_5530_);
                v_i_5525_ = v___x_5531_;
                v_b_5527_ = v___y_5529_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4___boxed(
    mut v_a_5537_: *mut crate::leanh::LeanObject,
    mut v_as_5538_: *mut crate::leanh::LeanObject,
    mut v_i_5539_: *mut crate::leanh::LeanObject,
    mut v_stop_5540_: *mut crate::leanh::LeanObject,
    mut v_b_5541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5542_: usize = 0;
    let mut v_stop_boxed_5543_: usize = 0;
    let mut v_res_5544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5542_ = crate::leanh::lean_unbox_usize(v_i_5539_);
    crate::leanh::lean_dec(v_i_5539_);
    v_stop_boxed_5543_ = crate::leanh::lean_unbox_usize(v_stop_5540_);
    crate::leanh::lean_dec(v_stop_5540_);
    v_res_5544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_5537_, v_as_5538_, v_i_boxed_5542_, v_stop_boxed_5543_, v_b_5541_);
    crate::leanh::lean_dec_ref(v_as_5538_);
    crate::leanh::lean_dec(v_a_5537_);
    return v_res_5544_;
}
pub unsafe fn l_Lean_MVarId_apply___lam__0(
    mut v_mvarId_5545_: *mut crate::leanh::LeanObject,
    mut v___x_5546_: *mut crate::leanh::LeanObject,
    mut v_e_5547_: *mut crate::leanh::LeanObject,
    mut v_cfg_5548_: *mut crate::leanh::LeanObject,
    mut v_term_x3f_5549_: *mut crate::leanh::LeanObject,
    mut v___y_5550_: *mut crate::leanh::LeanObject,
    mut v___y_5551_: *mut crate::leanh::LeanObject,
    mut v___y_5552_: *mut crate::leanh::LeanObject,
    mut v___y_5553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5567_: u8 = 0;
    let mut v___x_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5571_: u8 = 0;
    let mut v_unused_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5576_: u8 = 0;
    let mut v___x_5578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5580_: u8 = 0;
    let mut v___y_5582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5587_: u8 = 0;
    let mut v___y_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: u8 = 0;
    let mut v___x_5599_: u8 = 0;
    let mut v___x_5600_: usize = 0;
    let mut v___x_5601_: usize = 0;
    let mut v___x_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: usize = 0;
    let mut v___x_5604_: usize = 0;
    let mut v___x_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5609_: u8 = 0;
    let mut v___x_5611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5613_: u8 = 0;
    let mut v_a_5614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5617_: u8 = 0;
    let mut v___x_5619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5621_: u8 = 0;
    let mut v___y_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5628_: u8 = 0;
    let mut v___y_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5636_: u8 = 0;
    let mut v___x_5638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5640_: u8 = 0;
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rangeNumArgs_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newGoals_5657_: u8 = 0;
    let mut v_synthAssignedInstances_5658_: u8 = 0;
    let mut v_allowSynthFailures_5659_: u8 = 0;
    let mut v___x_5660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: u8 = 0;
    let mut v___x_5669_: u8 = 0;
    let mut v___x_5670_: usize = 0;
    let mut v___x_5671_: usize = 0;
    let mut v___x_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: usize = 0;
    let mut v___x_5674_: usize = 0;
    let mut v___x_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5679_: u8 = 0;
    let mut v___x_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5683_: u8 = 0;
    let mut v_a_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5687_: u8 = 0;
    let mut v___x_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5691_: u8 = 0;
    let mut v___x_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: u8 = 0;
    let mut v_fst_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5699_: u8 = 0;
    let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5711_: u8 = 0;
    let mut v___x_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5715_: u8 = 0;
    let mut v_isSharedCheck_5716_: u8 = 0;
    let mut v_unused_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5721_: u8 = 0;
    let mut v___x_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5727_: u8 = 0;
    let mut v_unused_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5732_: u8 = 0;
    let mut v___x_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5736_: u8 = 0;
    let mut v_a_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5740_: u8 = 0;
    let mut v___x_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5744_: u8 = 0;
    let mut v_a_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5748_: u8 = 0;
    let mut v___x_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5752_: u8 = 0;
    let mut v_a_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5756_: u8 = 0;
    let mut v___x_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5760_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___x_5546_);
                crate::leanh::lean_inc(v_mvarId_5545_);
                v___x_5641_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_5545_,
                    v___x_5546_,
                    v___y_5550_,
                    v___y_5551_,
                    v___y_5552_,
                    v___y_5553_,
                );
                if crate::leanh::lean_obj_tag(v___x_5641_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5641_, 1);
                    crate::leanh::lean_inc(v_mvarId_5545_);
                    v___x_5642_ = l_Lean_MVarId_getType(
                        v_mvarId_5545_,
                        v___y_5550_,
                        v___y_5551_,
                        v___y_5552_,
                        v___y_5553_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5642_) == 0 {
                        v_a_5643_ = crate::leanh::lean_ctor_get(v___x_5642_, 0);
                        crate::leanh::lean_inc(v_a_5643_);
                        crate::leanh::lean_dec_ref_known(v___x_5642_, 1);
                        crate::leanh::lean_inc(v___y_5553_);
                        crate::leanh::lean_inc_ref(v___y_5552_);
                        crate::leanh::lean_inc(v___y_5551_);
                        crate::leanh::lean_inc_ref(v___y_5550_);
                        crate::leanh::lean_inc_ref(v_e_5547_);
                        v___x_5644_ = lean_infer_type(
                            v_e_5547_,
                            v___y_5550_,
                            v___y_5551_,
                            v___y_5552_,
                            v___y_5553_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5644_) == 0 {
                            v_a_5645_ = crate::leanh::lean_ctor_get(v___x_5644_, 0);
                            crate::leanh::lean_inc_n(v_a_5645_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_5644_, 1);
                            v___x_5692_ = l_Lean_Meta_getExpectedNumArgsAux(
                                v_a_5645_,
                                v___y_5550_,
                                v___y_5551_,
                                v___y_5552_,
                                v___y_5553_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5692_) == 0 {
                                v_a_5693_ = crate::leanh::lean_ctor_get(v___x_5692_, 0);
                                crate::leanh::lean_inc(v_a_5693_);
                                crate::leanh::lean_dec_ref_known(v___x_5692_, 1);
                                v_snd_5694_ = crate::leanh::lean_ctor_get(v_a_5693_, 1);
                                v___x_5695_ = (crate::leanh::lean_unbox(v_snd_5694_) as u8);
                                if v___x_5695_ == 0 {
                                    v_fst_5696_ = crate::leanh::lean_ctor_get(v_a_5693_, 0);
                                    v_isSharedCheck_5716_ =
                                        (!crate::leanh::lean_is_exclusive(v_a_5693_)) as u8;
                                    if v_isSharedCheck_5716_ == 0 {
                                        v_unused_5717_ = crate::leanh::lean_ctor_get(v_a_5693_, 1);
                                        crate::leanh::lean_dec(v_unused_5717_);
                                        v___x_5698_ = v_a_5693_;
                                        v_isShared_5699_ = v_isSharedCheck_5716_;
                                        state = 19;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_fst_5696_);
                                        crate::leanh::lean_dec(v_a_5693_);
                                        v___x_5698_ = crate::leanh::lean_box(0);
                                        v_isShared_5699_ = v_isSharedCheck_5716_;
                                        state = 19;
                                        continue;
                                    }
                                } else {
                                    v_fst_5718_ = crate::leanh::lean_ctor_get(v_a_5693_, 0);
                                    v_isSharedCheck_5727_ =
                                        (!crate::leanh::lean_is_exclusive(v_a_5693_)) as u8;
                                    if v_isSharedCheck_5727_ == 0 {
                                        v_unused_5728_ = crate::leanh::lean_ctor_get(v_a_5693_, 1);
                                        crate::leanh::lean_dec(v_unused_5728_);
                                        v___x_5720_ = v_a_5693_;
                                        v_isShared_5721_ = v_isSharedCheck_5727_;
                                        state = 23;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_fst_5718_);
                                        crate::leanh::lean_dec(v_a_5693_);
                                        v___x_5720_ = crate::leanh::lean_box(0);
                                        v_isShared_5721_ = v_isSharedCheck_5727_;
                                        state = 23;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5645_);
                                crate::leanh::lean_dec(v_a_5643_);
                                crate::leanh::lean_dec(v___y_5553_);
                                crate::leanh::lean_dec_ref(v___y_5552_);
                                crate::leanh::lean_dec(v___y_5551_);
                                crate::leanh::lean_dec_ref(v___y_5550_);
                                crate::leanh::lean_dec(v_term_x3f_5549_);
                                crate::leanh::lean_dec_ref(v_e_5547_);
                                crate::leanh::lean_dec(v___x_5546_);
                                crate::leanh::lean_dec(v_mvarId_5545_);
                                v_a_5729_ = crate::leanh::lean_ctor_get(v___x_5692_, 0);
                                v_isSharedCheck_5736_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5692_)) as u8;
                                if v_isSharedCheck_5736_ == 0 {
                                    v___x_5731_ = v___x_5692_;
                                    v_isShared_5732_ = v_isSharedCheck_5736_;
                                    state = 25;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5729_);
                                    crate::leanh::lean_dec(v___x_5692_);
                                    v___x_5731_ = crate::leanh::lean_box(0);
                                    v_isShared_5732_ = v_isSharedCheck_5736_;
                                    state = 25;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5643_);
                            crate::leanh::lean_dec(v___y_5553_);
                            crate::leanh::lean_dec_ref(v___y_5552_);
                            crate::leanh::lean_dec(v___y_5551_);
                            crate::leanh::lean_dec_ref(v___y_5550_);
                            crate::leanh::lean_dec(v_term_x3f_5549_);
                            crate::leanh::lean_dec_ref(v_e_5547_);
                            crate::leanh::lean_dec(v___x_5546_);
                            crate::leanh::lean_dec(v_mvarId_5545_);
                            v_a_5737_ = crate::leanh::lean_ctor_get(v___x_5644_, 0);
                            v_isSharedCheck_5744_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5644_)) as u8;
                            if v_isSharedCheck_5744_ == 0 {
                                v___x_5739_ = v___x_5644_;
                                v_isShared_5740_ = v_isSharedCheck_5744_;
                                state = 27;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5737_);
                                crate::leanh::lean_dec(v___x_5644_);
                                v___x_5739_ = crate::leanh::lean_box(0);
                                v_isShared_5740_ = v_isSharedCheck_5744_;
                                state = 27;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_5553_);
                        crate::leanh::lean_dec_ref(v___y_5552_);
                        crate::leanh::lean_dec(v___y_5551_);
                        crate::leanh::lean_dec_ref(v___y_5550_);
                        crate::leanh::lean_dec(v_term_x3f_5549_);
                        crate::leanh::lean_dec_ref(v_e_5547_);
                        crate::leanh::lean_dec(v___x_5546_);
                        crate::leanh::lean_dec(v_mvarId_5545_);
                        v_a_5745_ = crate::leanh::lean_ctor_get(v___x_5642_, 0);
                        v_isSharedCheck_5752_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5642_)) as u8;
                        if v_isSharedCheck_5752_ == 0 {
                            v___x_5747_ = v___x_5642_;
                            v_isShared_5748_ = v_isSharedCheck_5752_;
                            state = 29;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5745_);
                            crate::leanh::lean_dec(v___x_5642_);
                            v___x_5747_ = crate::leanh::lean_box(0);
                            v_isShared_5748_ = v_isSharedCheck_5752_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_5553_);
                    crate::leanh::lean_dec_ref(v___y_5552_);
                    crate::leanh::lean_dec(v___y_5551_);
                    crate::leanh::lean_dec_ref(v___y_5550_);
                    crate::leanh::lean_dec(v_term_x3f_5549_);
                    crate::leanh::lean_dec_ref(v_e_5547_);
                    crate::leanh::lean_dec(v___x_5546_);
                    crate::leanh::lean_dec(v_mvarId_5545_);
                    v_a_5753_ = crate::leanh::lean_ctor_get(v___x_5641_, 0);
                    v_isSharedCheck_5760_ = (!crate::leanh::lean_is_exclusive(v___x_5641_)) as u8;
                    if v_isSharedCheck_5760_ == 0 {
                        v___x_5755_ = v___x_5641_;
                        v_isShared_5756_ = v_isSharedCheck_5760_;
                        state = 31;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5753_);
                        crate::leanh::lean_dec(v___x_5641_);
                        v___x_5755_ = crate::leanh::lean_box(0);
                        v_isShared_5756_ = v_isSharedCheck_5760_;
                        state = 31;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5562_ = lean_array_to_list(v___y_5561_);
                v___x_5563_ = l_List_appendTR___redArg(v___y_5559_, v___x_5562_);
                crate::leanh::lean_inc(v___x_5563_);
                v___x_5564_ = l_List_forM___at___00Lean_MVarId_apply_spec__3(
                    v___x_5563_,
                    v___y_5560_,
                    v___y_5558_,
                    v___y_5557_,
                    v___y_5556_,
                );
                crate::leanh::lean_dec(v___y_5556_);
                crate::leanh::lean_dec_ref(v___y_5557_);
                crate::leanh::lean_dec(v___y_5558_);
                crate::leanh::lean_dec_ref(v___y_5560_);
                if crate::leanh::lean_obj_tag(v___x_5564_) == 0 {
                    v_isSharedCheck_5571_ = (!crate::leanh::lean_is_exclusive(v___x_5564_)) as u8;
                    if v_isSharedCheck_5571_ == 0 {
                        v_unused_5572_ = crate::leanh::lean_ctor_get(v___x_5564_, 0);
                        crate::leanh::lean_dec(v_unused_5572_);
                        v___x_5566_ = v___x_5564_;
                        v_isShared_5567_ = v_isSharedCheck_5571_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5564_);
                        v___x_5566_ = crate::leanh::lean_box(0);
                        v_isShared_5567_ = v_isSharedCheck_5571_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5563_);
                    v_a_5573_ = crate::leanh::lean_ctor_get(v___x_5564_, 0);
                    v_isSharedCheck_5580_ = (!crate::leanh::lean_is_exclusive(v___x_5564_)) as u8;
                    if v_isSharedCheck_5580_ == 0 {
                        v___x_5575_ = v___x_5564_;
                        v_isShared_5576_ = v_isSharedCheck_5580_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5573_);
                        crate::leanh::lean_dec(v___x_5564_);
                        v___x_5575_ = crate::leanh::lean_box(0);
                        v_isShared_5576_ = v_isSharedCheck_5580_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5567_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5566_, 0, v___x_5563_);
                    v___x_5569_ = v___x_5566_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5570_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5570_, 0, v___x_5563_);
                    v___x_5569_ = v_reuseFailAlloc_5570_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5569_;
            }
            4 => {
                if v_isShared_5576_ == 0 {
                    v___x_5578_ = v___x_5575_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5579_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5579_, 0, v_a_5573_);
                    v___x_5578_ = v_reuseFailAlloc_5579_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5578_;
            }
            6 => {
                v___x_5591_ = l_Lean_Meta_appendParentTag(
                    v_mvarId_5545_,
                    v_a_5590_,
                    v___y_5588_,
                    v___y_5589_,
                    v___y_5586_,
                    v___y_5585_,
                    v___y_5582_,
                );
                crate::leanh::lean_dec_ref(v___y_5588_);
                if crate::leanh::lean_obj_tag(v___x_5591_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5591_, 1);
                    v___x_5592_ = l_Lean_Meta_getMVarsNoDelayed(
                        v___y_5584_,
                        v___y_5589_,
                        v___y_5586_,
                        v___y_5585_,
                        v___y_5582_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5592_) == 0 {
                        v_a_5593_ = crate::leanh::lean_ctor_get(v___x_5592_, 0);
                        crate::leanh::lean_inc(v_a_5593_);
                        crate::leanh::lean_dec_ref_known(v___x_5592_, 1);
                        v___x_5594_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_reorderGoals(
                            v_a_5590_,
                            v___y_5587_,
                            v___y_5589_,
                            v___y_5586_,
                            v___y_5585_,
                            v___y_5582_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5594_) == 0 {
                            v_a_5595_ = crate::leanh::lean_ctor_get(v___x_5594_, 0);
                            crate::leanh::lean_inc(v_a_5595_);
                            crate::leanh::lean_dec_ref_known(v___x_5594_, 1);
                            v___x_5596_ = lean_array_get_size(v_a_5593_);
                            v___x_5597_ = lean_mk_empty_array_with_capacity(v___y_5583_);
                            v___x_5598_ = lean_nat_dec_lt(v___y_5583_, v___x_5596_);
                            if v___x_5598_ == 0 {
                                crate::leanh::lean_dec(v_a_5593_);
                                v___y_5556_ = v___y_5582_;
                                v___y_5557_ = v___y_5585_;
                                v___y_5558_ = v___y_5586_;
                                v___y_5559_ = v_a_5595_;
                                v___y_5560_ = v___y_5589_;
                                v___y_5561_ = v___x_5597_;
                                state = 1;
                                continue;
                            } else {
                                v___x_5599_ = lean_nat_dec_le(v___x_5596_, v___x_5596_);
                                if v___x_5599_ == 0 {
                                    if v___x_5598_ == 0 {
                                        crate::leanh::lean_dec(v_a_5593_);
                                        v___y_5556_ = v___y_5582_;
                                        v___y_5557_ = v___y_5585_;
                                        v___y_5558_ = v___y_5586_;
                                        v___y_5559_ = v_a_5595_;
                                        v___y_5560_ = v___y_5589_;
                                        v___y_5561_ = v___x_5597_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_5600_ = 0usize;
                                        v___x_5601_ = lean_usize_of_nat(v___x_5596_);
                                        v___x_5602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_5595_, v_a_5593_, v___x_5600_, v___x_5601_, v___x_5597_);
                                        crate::leanh::lean_dec(v_a_5593_);
                                        v___y_5556_ = v___y_5582_;
                                        v___y_5557_ = v___y_5585_;
                                        v___y_5558_ = v___y_5586_;
                                        v___y_5559_ = v_a_5595_;
                                        v___y_5560_ = v___y_5589_;
                                        v___y_5561_ = v___x_5602_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    v___x_5603_ = 0usize;
                                    v___x_5604_ = lean_usize_of_nat(v___x_5596_);
                                    v___x_5605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__4(v_a_5595_, v_a_5593_, v___x_5603_, v___x_5604_, v___x_5597_);
                                    crate::leanh::lean_dec(v_a_5593_);
                                    v___y_5556_ = v___y_5582_;
                                    v___y_5557_ = v___y_5585_;
                                    v___y_5558_ = v___y_5586_;
                                    v___y_5559_ = v_a_5595_;
                                    v___y_5560_ = v___y_5589_;
                                    v___y_5561_ = v___x_5605_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5593_);
                            crate::leanh::lean_dec_ref(v___y_5589_);
                            crate::leanh::lean_dec(v___y_5586_);
                            crate::leanh::lean_dec_ref(v___y_5585_);
                            crate::leanh::lean_dec(v___y_5582_);
                            return v___x_5594_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_a_5590_);
                        crate::leanh::lean_dec_ref(v___y_5589_);
                        crate::leanh::lean_dec(v___y_5586_);
                        crate::leanh::lean_dec_ref(v___y_5585_);
                        crate::leanh::lean_dec(v___y_5582_);
                        v_a_5606_ = crate::leanh::lean_ctor_get(v___x_5592_, 0);
                        v_isSharedCheck_5613_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5592_)) as u8;
                        if v_isSharedCheck_5613_ == 0 {
                            v___x_5608_ = v___x_5592_;
                            v_isShared_5609_ = v_isSharedCheck_5613_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5606_);
                            crate::leanh::lean_dec(v___x_5592_);
                            v___x_5608_ = crate::leanh::lean_box(0);
                            v_isShared_5609_ = v_isSharedCheck_5613_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_5590_);
                    crate::leanh::lean_dec_ref(v___y_5589_);
                    crate::leanh::lean_dec(v___y_5586_);
                    crate::leanh::lean_dec_ref(v___y_5585_);
                    crate::leanh::lean_dec_ref(v___y_5584_);
                    crate::leanh::lean_dec(v___y_5582_);
                    v_a_5614_ = crate::leanh::lean_ctor_get(v___x_5591_, 0);
                    v_isSharedCheck_5621_ = (!crate::leanh::lean_is_exclusive(v___x_5591_)) as u8;
                    if v_isSharedCheck_5621_ == 0 {
                        v___x_5616_ = v___x_5591_;
                        v_isShared_5617_ = v_isSharedCheck_5621_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5614_);
                        crate::leanh::lean_dec(v___x_5591_);
                        v___x_5616_ = crate::leanh::lean_box(0);
                        v_isShared_5617_ = v_isSharedCheck_5621_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_5609_ == 0 {
                    v___x_5611_ = v___x_5608_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5612_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5612_, 0, v_a_5606_);
                    v___x_5611_ = v_reuseFailAlloc_5612_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5611_;
            }
            9 => {
                if v_isShared_5617_ == 0 {
                    v___x_5619_ = v___x_5616_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5620_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5620_, 0, v_a_5614_);
                    v___x_5619_ = v_reuseFailAlloc_5620_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5619_;
            }
            11 => {
                if crate::leanh::lean_obj_tag(v___y_5631_) == 0 {
                    v_a_5632_ = crate::leanh::lean_ctor_get(v___y_5631_, 0);
                    crate::leanh::lean_inc(v_a_5632_);
                    crate::leanh::lean_dec_ref_known(v___y_5631_, 1);
                    v___y_5582_ = v___y_5623_;
                    v___y_5583_ = v___y_5624_;
                    v___y_5584_ = v___y_5625_;
                    v___y_5585_ = v___y_5626_;
                    v___y_5586_ = v___y_5627_;
                    v___y_5587_ = v___y_5628_;
                    v___y_5588_ = v___y_5629_;
                    v___y_5589_ = v___y_5630_;
                    v_a_5590_ = v_a_5632_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_5630_);
                    crate::leanh::lean_dec_ref(v___y_5629_);
                    crate::leanh::lean_dec(v___y_5627_);
                    crate::leanh::lean_dec_ref(v___y_5626_);
                    crate::leanh::lean_dec_ref(v___y_5625_);
                    crate::leanh::lean_dec(v___y_5623_);
                    crate::leanh::lean_dec(v_mvarId_5545_);
                    v_a_5633_ = crate::leanh::lean_ctor_get(v___y_5631_, 0);
                    v_isSharedCheck_5640_ = (!crate::leanh::lean_is_exclusive(v___y_5631_)) as u8;
                    if v_isSharedCheck_5640_ == 0 {
                        v___x_5635_ = v___y_5631_;
                        v_isShared_5636_ = v_isSharedCheck_5640_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5633_);
                        crate::leanh::lean_dec(v___y_5631_);
                        v___x_5635_ = crate::leanh::lean_box(0);
                        v_isShared_5636_ = v_isSharedCheck_5640_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                if v_isShared_5636_ == 0 {
                    v___x_5638_ = v___x_5635_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5639_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5639_, 0, v_a_5633_);
                    v___x_5638_ = v_reuseFailAlloc_5639_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5638_;
            }
            14 => {
                crate::leanh::lean_inc(v_mvarId_5545_);
                v___x_5653_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_apply_go(
                    v_mvarId_5545_,
                    v_cfg_5548_,
                    v_term_x3f_5549_,
                    v_a_5643_,
                    v_a_5645_,
                    v_rangeNumArgs_5647_,
                    v_lower_5648_,
                    v___y_5649_,
                    v___y_5650_,
                    v___y_5651_,
                    v___y_5652_,
                );
                crate::leanh::lean_dec_ref(v_rangeNumArgs_5647_);
                if crate::leanh::lean_obj_tag(v___x_5653_) == 0 {
                    v_a_5654_ = crate::leanh::lean_ctor_get(v___x_5653_, 0);
                    crate::leanh::lean_inc(v_a_5654_);
                    crate::leanh::lean_dec_ref_known(v___x_5653_, 1);
                    v_fst_5655_ = crate::leanh::lean_ctor_get(v_a_5654_, 0);
                    crate::leanh::lean_inc(v_fst_5655_);
                    v_snd_5656_ = crate::leanh::lean_ctor_get(v_a_5654_, 1);
                    crate::leanh::lean_inc_n(v_snd_5656_, 2);
                    crate::leanh::lean_dec(v_a_5654_);
                    v_newGoals_5657_ = crate::leanh::lean_ctor_get_uint8(v_cfg_5548_, 0 as u32);
                    v_synthAssignedInstances_5658_ =
                        crate::leanh::lean_ctor_get_uint8(v_cfg_5548_, 1 as u32);
                    v_allowSynthFailures_5659_ =
                        crate::leanh::lean_ctor_get_uint8(v_cfg_5548_, 2 as u32);
                    crate::leanh::lean_inc(v_mvarId_5545_);
                    v___x_5660_ = l_Lean_Meta_synthAppInstances(
                        v___x_5546_,
                        v_mvarId_5545_,
                        v_fst_5655_,
                        v_snd_5656_,
                        v_synthAssignedInstances_5658_,
                        v_allowSynthFailures_5659_,
                        v___y_5649_,
                        v___y_5650_,
                        v___y_5651_,
                        v___y_5652_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5660_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5660_, 1);
                        v___x_5661_ =
                            l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(
                                v_e_5547_,
                                v___y_5650_,
                            );
                        v_a_5662_ = crate::leanh::lean_ctor_get(v___x_5661_, 0);
                        crate::leanh::lean_inc_n(v_a_5662_, 2);
                        crate::leanh::lean_dec_ref(v___x_5661_);
                        v___x_5663_ = l_Lean_mkAppN(v_a_5662_, v_fst_5655_);
                        crate::leanh::lean_inc(v_mvarId_5545_);
                        v___x_5664_ =
                            l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(
                                v_mvarId_5545_,
                                v___x_5663_,
                                v___y_5650_,
                            );
                        crate::leanh::lean_dec_ref(v___x_5664_);
                        v___x_5665_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_5666_ = lean_array_get_size(v_fst_5655_);
                        v___x_5667_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_synthAppInstances_step___closed__0;
                        v___x_5668_ = lean_nat_dec_lt(v___x_5665_, v___x_5666_);
                        if v___x_5668_ == 0 {
                            crate::leanh::lean_dec(v_fst_5655_);
                            v___y_5582_ = v___y_5652_;
                            v___y_5583_ = v___x_5665_;
                            v___y_5584_ = v_a_5662_;
                            v___y_5585_ = v___y_5651_;
                            v___y_5586_ = v___y_5650_;
                            v___y_5587_ = v_newGoals_5657_;
                            v___y_5588_ = v_snd_5656_;
                            v___y_5589_ = v___y_5649_;
                            v_a_5590_ = v___x_5667_;
                            state = 6;
                            continue;
                        } else {
                            v___x_5669_ = lean_nat_dec_le(v___x_5666_, v___x_5666_);
                            if v___x_5669_ == 0 {
                                if v___x_5668_ == 0 {
                                    crate::leanh::lean_dec(v_fst_5655_);
                                    v___y_5582_ = v___y_5652_;
                                    v___y_5583_ = v___x_5665_;
                                    v___y_5584_ = v_a_5662_;
                                    v___y_5585_ = v___y_5651_;
                                    v___y_5586_ = v___y_5650_;
                                    v___y_5587_ = v_newGoals_5657_;
                                    v___y_5588_ = v_snd_5656_;
                                    v___y_5589_ = v___y_5649_;
                                    v_a_5590_ = v___x_5667_;
                                    state = 6;
                                    continue;
                                } else {
                                    v___x_5670_ = 0usize;
                                    v___x_5671_ = lean_usize_of_nat(v___x_5666_);
                                    v___x_5672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_5655_, v___x_5670_, v___x_5671_, v___x_5667_, v___y_5650_);
                                    crate::leanh::lean_dec(v_fst_5655_);
                                    v___y_5623_ = v___y_5652_;
                                    v___y_5624_ = v___x_5665_;
                                    v___y_5625_ = v_a_5662_;
                                    v___y_5626_ = v___y_5651_;
                                    v___y_5627_ = v___y_5650_;
                                    v___y_5628_ = v_newGoals_5657_;
                                    v___y_5629_ = v_snd_5656_;
                                    v___y_5630_ = v___y_5649_;
                                    v___y_5631_ = v___x_5672_;
                                    state = 11;
                                    continue;
                                }
                            } else {
                                v___x_5673_ = 0usize;
                                v___x_5674_ = lean_usize_of_nat(v___x_5666_);
                                v___x_5675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_fst_5655_, v___x_5673_, v___x_5674_, v___x_5667_, v___y_5650_);
                                crate::leanh::lean_dec(v_fst_5655_);
                                v___y_5623_ = v___y_5652_;
                                v___y_5624_ = v___x_5665_;
                                v___y_5625_ = v_a_5662_;
                                v___y_5626_ = v___y_5651_;
                                v___y_5627_ = v___y_5650_;
                                v___y_5628_ = v_newGoals_5657_;
                                v___y_5629_ = v_snd_5656_;
                                v___y_5630_ = v___y_5649_;
                                v___y_5631_ = v___x_5675_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_5656_);
                        crate::leanh::lean_dec(v_fst_5655_);
                        crate::leanh::lean_dec(v___y_5652_);
                        crate::leanh::lean_dec_ref(v___y_5651_);
                        crate::leanh::lean_dec(v___y_5650_);
                        crate::leanh::lean_dec_ref(v___y_5649_);
                        crate::leanh::lean_dec_ref(v_e_5547_);
                        crate::leanh::lean_dec(v_mvarId_5545_);
                        v_a_5676_ = crate::leanh::lean_ctor_get(v___x_5660_, 0);
                        v_isSharedCheck_5683_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5660_)) as u8;
                        if v_isSharedCheck_5683_ == 0 {
                            v___x_5678_ = v___x_5660_;
                            v_isShared_5679_ = v_isSharedCheck_5683_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5676_);
                            crate::leanh::lean_dec(v___x_5660_);
                            v___x_5678_ = crate::leanh::lean_box(0);
                            v_isShared_5679_ = v_isSharedCheck_5683_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_5652_);
                    crate::leanh::lean_dec_ref(v___y_5651_);
                    crate::leanh::lean_dec(v___y_5650_);
                    crate::leanh::lean_dec_ref(v___y_5649_);
                    crate::leanh::lean_dec_ref(v_e_5547_);
                    crate::leanh::lean_dec(v___x_5546_);
                    crate::leanh::lean_dec(v_mvarId_5545_);
                    v_a_5684_ = crate::leanh::lean_ctor_get(v___x_5653_, 0);
                    v_isSharedCheck_5691_ = (!crate::leanh::lean_is_exclusive(v___x_5653_)) as u8;
                    if v_isSharedCheck_5691_ == 0 {
                        v___x_5686_ = v___x_5653_;
                        v_isShared_5687_ = v_isSharedCheck_5691_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5684_);
                        crate::leanh::lean_dec(v___x_5653_);
                        v___x_5686_ = crate::leanh::lean_box(0);
                        v_isShared_5687_ = v_isSharedCheck_5691_;
                        state = 17;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_5679_ == 0 {
                    v___x_5681_ = v___x_5678_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5682_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5682_, 0, v_a_5676_);
                    v___x_5681_ = v_reuseFailAlloc_5682_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5681_;
            }
            17 => {
                if v_isShared_5687_ == 0 {
                    v___x_5689_ = v___x_5686_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5690_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5690_, 0, v_a_5684_);
                    v___x_5689_ = v_reuseFailAlloc_5690_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5689_;
            }
            19 => {
                crate::leanh::lean_inc(v_a_5643_);
                v___x_5700_ = l_Lean_Meta_getExpectedNumArgs(
                    v_a_5643_,
                    v___y_5550_,
                    v___y_5551_,
                    v___y_5552_,
                    v___y_5553_,
                );
                if crate::leanh::lean_obj_tag(v___x_5700_) == 0 {
                    v_a_5701_ = crate::leanh::lean_ctor_get(v___x_5700_, 0);
                    crate::leanh::lean_inc(v_a_5701_);
                    crate::leanh::lean_dec_ref_known(v___x_5700_, 1);
                    v___x_5702_ = lean_nat_sub(v_fst_5696_, v_a_5701_);
                    crate::leanh::lean_dec(v_a_5701_);
                    v___x_5703_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5704_ = lean_nat_add(v_fst_5696_, v___x_5703_);
                    crate::leanh::lean_dec(v_fst_5696_);
                    crate::leanh::lean_inc(v___x_5702_);
                    if v_isShared_5699_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5698_, 1, v___x_5704_);
                        crate::leanh::lean_ctor_set(v___x_5698_, 0, v___x_5702_);
                        v___x_5706_ = v___x_5698_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_5707_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5707_, 0, v___x_5702_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5707_, 1, v___x_5704_);
                        v___x_5706_ = v_reuseFailAlloc_5707_;
                        state = 20;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5698_);
                    crate::leanh::lean_dec(v_fst_5696_);
                    crate::leanh::lean_dec(v_a_5645_);
                    crate::leanh::lean_dec(v_a_5643_);
                    crate::leanh::lean_dec(v___y_5553_);
                    crate::leanh::lean_dec_ref(v___y_5552_);
                    crate::leanh::lean_dec(v___y_5551_);
                    crate::leanh::lean_dec_ref(v___y_5550_);
                    crate::leanh::lean_dec(v_term_x3f_5549_);
                    crate::leanh::lean_dec_ref(v_e_5547_);
                    crate::leanh::lean_dec(v___x_5546_);
                    crate::leanh::lean_dec(v_mvarId_5545_);
                    v_a_5708_ = crate::leanh::lean_ctor_get(v___x_5700_, 0);
                    v_isSharedCheck_5715_ = (!crate::leanh::lean_is_exclusive(v___x_5700_)) as u8;
                    if v_isSharedCheck_5715_ == 0 {
                        v___x_5710_ = v___x_5700_;
                        v_isShared_5711_ = v_isSharedCheck_5715_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5708_);
                        crate::leanh::lean_dec(v___x_5700_);
                        v___x_5710_ = crate::leanh::lean_box(0);
                        v_isShared_5711_ = v_isSharedCheck_5715_;
                        state = 21;
                        continue;
                    }
                }
            }
            20 => {
                v_rangeNumArgs_5647_ = v___x_5706_;
                v_lower_5648_ = v___x_5702_;
                v___y_5649_ = v___y_5550_;
                v___y_5650_ = v___y_5551_;
                v___y_5651_ = v___y_5552_;
                v___y_5652_ = v___y_5553_;
                state = 14;
                continue;
            }
            21 => {
                if v_isShared_5711_ == 0 {
                    v___x_5713_ = v___x_5710_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5714_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5714_, 0, v_a_5708_);
                    v___x_5713_ = v_reuseFailAlloc_5714_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5713_;
            }
            23 => {
                v___x_5722_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5723_ = lean_nat_add(v_fst_5718_, v___x_5722_);
                crate::leanh::lean_inc(v_fst_5718_);
                if v_isShared_5721_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5720_, 1, v___x_5723_);
                    v___x_5725_ = v___x_5720_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5726_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5726_, 0, v_fst_5718_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5726_, 1, v___x_5723_);
                    v___x_5725_ = v_reuseFailAlloc_5726_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v_rangeNumArgs_5647_ = v___x_5725_;
                v_lower_5648_ = v_fst_5718_;
                v___y_5649_ = v___y_5550_;
                v___y_5650_ = v___y_5551_;
                v___y_5651_ = v___y_5552_;
                v___y_5652_ = v___y_5553_;
                state = 14;
                continue;
            }
            25 => {
                if v_isShared_5732_ == 0 {
                    v___x_5734_ = v___x_5731_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5735_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5735_, 0, v_a_5729_);
                    v___x_5734_ = v_reuseFailAlloc_5735_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5734_;
            }
            27 => {
                if v_isShared_5740_ == 0 {
                    v___x_5742_ = v___x_5739_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5743_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5743_, 0, v_a_5737_);
                    v___x_5742_ = v_reuseFailAlloc_5743_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_5742_;
            }
            29 => {
                if v_isShared_5748_ == 0 {
                    v___x_5750_ = v___x_5747_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5751_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5751_, 0, v_a_5745_);
                    v___x_5750_ = v_reuseFailAlloc_5751_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_5750_;
            }
            31 => {
                if v_isShared_5756_ == 0 {
                    v___x_5758_ = v___x_5755_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_5759_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5759_, 0, v_a_5753_);
                    v___x_5758_ = v_reuseFailAlloc_5759_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_5758_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_apply___lam__0___boxed(
    mut v_mvarId_5761_: *mut crate::leanh::LeanObject,
    mut v___x_5762_: *mut crate::leanh::LeanObject,
    mut v_e_5763_: *mut crate::leanh::LeanObject,
    mut v_cfg_5764_: *mut crate::leanh::LeanObject,
    mut v_term_x3f_5765_: *mut crate::leanh::LeanObject,
    mut v___y_5766_: *mut crate::leanh::LeanObject,
    mut v___y_5767_: *mut crate::leanh::LeanObject,
    mut v___y_5768_: *mut crate::leanh::LeanObject,
    mut v___y_5769_: *mut crate::leanh::LeanObject,
    mut v___y_5770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5771_ = l_Lean_MVarId_apply___lam__0(
        v_mvarId_5761_,
        v___x_5762_,
        v_e_5763_,
        v_cfg_5764_,
        v_term_x3f_5765_,
        v___y_5766_,
        v___y_5767_,
        v___y_5768_,
        v___y_5769_,
    );
    crate::leanh::lean_dec_ref(v_cfg_5764_);
    return v_res_5771_;
}
pub unsafe fn l_Lean_MVarId_apply(
    mut v_mvarId_5772_: *mut crate::leanh::LeanObject,
    mut v_e_5773_: *mut crate::leanh::LeanObject,
    mut v_cfg_5774_: *mut crate::leanh::LeanObject,
    mut v_term_x3f_5775_: *mut crate::leanh::LeanObject,
    mut v_a_5776_: *mut crate::leanh::LeanObject,
    mut v_a_5777_: *mut crate::leanh::LeanObject,
    mut v_a_5778_: *mut crate::leanh::LeanObject,
    mut v_a_5779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5781_ =
        l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1;
    crate::leanh::lean_inc(v_mvarId_5772_);
    v___f_5782_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_apply___lam__0___boxed as *mut core::ffi::c_void,
        10,
        5,
    );
    crate::leanh::lean_closure_set(v___f_5782_, 0, v_mvarId_5772_);
    crate::leanh::lean_closure_set(v___f_5782_, 1, v___x_5781_);
    crate::leanh::lean_closure_set(v___f_5782_, 2, v_e_5773_);
    crate::leanh::lean_closure_set(v___f_5782_, 3, v_cfg_5774_);
    crate::leanh::lean_closure_set(v___f_5782_, 4, v_term_x3f_5775_);
    v___x_5783_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(
        v_mvarId_5772_,
        v___f_5782_,
        v_a_5776_,
        v_a_5777_,
        v_a_5778_,
        v_a_5779_,
    );
    return v___x_5783_;
}
pub unsafe fn l_Lean_MVarId_apply___boxed(
    mut v_mvarId_5784_: *mut crate::leanh::LeanObject,
    mut v_e_5785_: *mut crate::leanh::LeanObject,
    mut v_cfg_5786_: *mut crate::leanh::LeanObject,
    mut v_term_x3f_5787_: *mut crate::leanh::LeanObject,
    mut v_a_5788_: *mut crate::leanh::LeanObject,
    mut v_a_5789_: *mut crate::leanh::LeanObject,
    mut v_a_5790_: *mut crate::leanh::LeanObject,
    mut v_a_5791_: *mut crate::leanh::LeanObject,
    mut v_a_5792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5793_ = l_Lean_MVarId_apply(
        v_mvarId_5784_,
        v_e_5785_,
        v_cfg_5786_,
        v_term_x3f_5787_,
        v_a_5788_,
        v_a_5789_,
        v_a_5790_,
        v_a_5791_,
    );
    crate::leanh::lean_dec(v_a_5791_);
    crate::leanh::lean_dec_ref(v_a_5790_);
    crate::leanh::lean_dec(v_a_5789_);
    crate::leanh::lean_dec_ref(v_a_5788_);
    return v_res_5793_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(
    mut v_mvarId_5794_: *mut crate::leanh::LeanObject,
    mut v_val_5795_: *mut crate::leanh::LeanObject,
    mut v___y_5796_: *mut crate::leanh::LeanObject,
    mut v___y_5797_: *mut crate::leanh::LeanObject,
    mut v___y_5798_: *mut crate::leanh::LeanObject,
    mut v___y_5799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5801_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(
        v_mvarId_5794_,
        v_val_5795_,
        v___y_5797_,
    );
    return v___x_5801_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___boxed(
    mut v_mvarId_5802_: *mut crate::leanh::LeanObject,
    mut v_val_5803_: *mut crate::leanh::LeanObject,
    mut v___y_5804_: *mut crate::leanh::LeanObject,
    mut v___y_5805_: *mut crate::leanh::LeanObject,
    mut v___y_5806_: *mut crate::leanh::LeanObject,
    mut v___y_5807_: *mut crate::leanh::LeanObject,
    mut v___y_5808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5809_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1(
        v_mvarId_5802_,
        v_val_5803_,
        v___y_5804_,
        v___y_5805_,
        v___y_5806_,
        v___y_5807_,
    );
    crate::leanh::lean_dec(v___y_5807_);
    crate::leanh::lean_dec_ref(v___y_5806_);
    crate::leanh::lean_dec(v___y_5805_);
    crate::leanh::lean_dec_ref(v___y_5804_);
    return v_res_5809_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(
    mut v_as_5810_: *mut crate::leanh::LeanObject,
    mut v_i_5811_: usize,
    mut v_stop_5812_: usize,
    mut v_b_5813_: *mut crate::leanh::LeanObject,
    mut v___y_5814_: *mut crate::leanh::LeanObject,
    mut v___y_5815_: *mut crate::leanh::LeanObject,
    mut v___y_5816_: *mut crate::leanh::LeanObject,
    mut v___y_5817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5819_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___redArg(v_as_5810_, v_i_5811_, v_stop_5812_, v_b_5813_, v___y_5815_);
    return v___x_5819_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5___boxed(
    mut v_as_5820_: *mut crate::leanh::LeanObject,
    mut v_i_5821_: *mut crate::leanh::LeanObject,
    mut v_stop_5822_: *mut crate::leanh::LeanObject,
    mut v_b_5823_: *mut crate::leanh::LeanObject,
    mut v___y_5824_: *mut crate::leanh::LeanObject,
    mut v___y_5825_: *mut crate::leanh::LeanObject,
    mut v___y_5826_: *mut crate::leanh::LeanObject,
    mut v___y_5827_: *mut crate::leanh::LeanObject,
    mut v___y_5828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5829_: usize = 0;
    let mut v_stop_boxed_5830_: usize = 0;
    let mut v_res_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5829_ = crate::leanh::lean_unbox_usize(v_i_5821_);
    crate::leanh::lean_dec(v_i_5821_);
    v_stop_boxed_5830_ = crate::leanh::lean_unbox_usize(v_stop_5822_);
    crate::leanh::lean_dec(v_stop_5822_);
    v_res_5831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_MVarId_apply_spec__5(v_as_5820_, v_i_boxed_5829_, v_stop_boxed_5830_, v_b_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_);
    crate::leanh::lean_dec(v___y_5827_);
    crate::leanh::lean_dec_ref(v___y_5826_);
    crate::leanh::lean_dec(v___y_5825_);
    crate::leanh::lean_dec_ref(v___y_5824_);
    crate::leanh::lean_dec_ref(v_as_5820_);
    return v_res_5831_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1(
    mut v_00_u03b2_5832_: *mut crate::leanh::LeanObject,
    mut v_x_5833_: *mut crate::leanh::LeanObject,
    mut v_x_5834_: *mut crate::leanh::LeanObject,
    mut v_x_5835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5836_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1___redArg(v_x_5833_, v_x_5834_, v_x_5835_);
    return v___x_5836_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(
    mut v_00_u03b2_5837_: *mut crate::leanh::LeanObject,
    mut v_x_5838_: *mut crate::leanh::LeanObject,
    mut v_x_5839_: usize,
    mut v_x_5840_: usize,
    mut v_x_5841_: *mut crate::leanh::LeanObject,
    mut v_x_5842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5843_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___redArg(v_x_5838_, v_x_5839_, v_x_5840_, v_x_5841_, v_x_5842_);
    return v___x_5843_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3___boxed(
    mut v_00_u03b2_5844_: *mut crate::leanh::LeanObject,
    mut v_x_5845_: *mut crate::leanh::LeanObject,
    mut v_x_5846_: *mut crate::leanh::LeanObject,
    mut v_x_5847_: *mut crate::leanh::LeanObject,
    mut v_x_5848_: *mut crate::leanh::LeanObject,
    mut v_x_5849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7975__boxed_5850_: usize = 0;
    let mut v_x_7976__boxed_5851_: usize = 0;
    let mut v_res_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7975__boxed_5850_ = crate::leanh::lean_unbox_usize(v_x_5846_);
    crate::leanh::lean_dec(v_x_5846_);
    v_x_7976__boxed_5851_ = crate::leanh::lean_unbox_usize(v_x_5847_);
    crate::leanh::lean_dec(v_x_5847_);
    v_res_5852_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3(v_00_u03b2_5844_, v_x_5845_, v_x_7975__boxed_5850_, v_x_7976__boxed_5851_, v_x_5848_, v_x_5849_);
    return v_res_5852_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8(
    mut v_00_u03b2_5853_: *mut crate::leanh::LeanObject,
    mut v_n_5854_: *mut crate::leanh::LeanObject,
    mut v_k_5855_: *mut crate::leanh::LeanObject,
    mut v_v_5856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5857_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8___redArg(v_n_5854_, v_k_5855_, v_v_5856_);
    return v___x_5857_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(
    mut v_00_u03b2_5858_: *mut crate::leanh::LeanObject,
    mut v_depth_5859_: usize,
    mut v_keys_5860_: *mut crate::leanh::LeanObject,
    mut v_vals_5861_: *mut crate::leanh::LeanObject,
    mut v_heq_5862_: *mut crate::leanh::LeanObject,
    mut v_i_5863_: *mut crate::leanh::LeanObject,
    mut v_entries_5864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5865_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___redArg(v_depth_5859_, v_keys_5860_, v_vals_5861_, v_i_5863_, v_entries_5864_);
    return v___x_5865_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9___boxed(
    mut v_00_u03b2_5866_: *mut crate::leanh::LeanObject,
    mut v_depth_5867_: *mut crate::leanh::LeanObject,
    mut v_keys_5868_: *mut crate::leanh::LeanObject,
    mut v_vals_5869_: *mut crate::leanh::LeanObject,
    mut v_heq_5870_: *mut crate::leanh::LeanObject,
    mut v_i_5871_: *mut crate::leanh::LeanObject,
    mut v_entries_5872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_5873_: usize = 0;
    let mut v_res_5874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5873_ = crate::leanh::lean_unbox_usize(v_depth_5867_);
    crate::leanh::lean_dec(v_depth_5867_);
    v_res_5874_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__9(v_00_u03b2_5866_, v_depth_boxed_5873_, v_keys_5868_, v_vals_5869_, v_heq_5870_, v_i_5871_, v_entries_5872_);
    crate::leanh::lean_dec_ref(v_vals_5869_);
    crate::leanh::lean_dec_ref(v_keys_5868_);
    return v_res_5874_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9(
    mut v_00_u03b2_5875_: *mut crate::leanh::LeanObject,
    mut v_x_5876_: *mut crate::leanh::LeanObject,
    mut v_x_5877_: *mut crate::leanh::LeanObject,
    mut v_x_5878_: *mut crate::leanh::LeanObject,
    mut v_x_5879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5880_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1_spec__1_spec__3_spec__8_spec__9___redArg(v_x_5876_, v_x_5877_, v_x_5878_, v_x_5879_);
    return v___x_5880_;
}
pub unsafe fn _init_l_Lean_MVarId_applyConst___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_5882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5882_ = l_Lean_MVarId_applyConst___closed__0;
    v___x_5883_ = l_Lean_stringToMessageData(v___x_5882_);
    return v___x_5883_;
}
pub unsafe fn l_Lean_MVarId_applyConst(
    mut v_mvar_5884_: *mut crate::leanh::LeanObject,
    mut v_c_5885_: *mut crate::leanh::LeanObject,
    mut v_cfg_5886_: *mut crate::leanh::LeanObject,
    mut v_a_5887_: *mut crate::leanh::LeanObject,
    mut v_a_5888_: *mut crate::leanh::LeanObject,
    mut v_a_5889_: *mut crate::leanh::LeanObject,
    mut v_a_5890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5895_: u8 = 0;
    let mut v___x_5896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5904_: u8 = 0;
    let mut v___x_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_c_5885_);
                v___x_5892_ = l_Lean_Meta_mkConstWithFreshMVarLevels(
                    v_c_5885_, v_a_5887_, v_a_5888_, v_a_5889_, v_a_5890_,
                );
                if crate::leanh::lean_obj_tag(v___x_5892_) == 0 {
                    v_a_5893_ = crate::leanh::lean_ctor_get(v___x_5892_, 0);
                    crate::leanh::lean_inc(v_a_5893_);
                    crate::leanh::lean_dec_ref_known(v___x_5892_, 1);
                    v___x_5894_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_applyConst___closed__1),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_applyConst___closed__1_once),
                        _init_l_Lean_MVarId_applyConst___closed__1,
                    );
                    v___x_5895_ = 0;
                    v___x_5896_ = l_Lean_MessageData_ofConstName(v_c_5885_, v___x_5895_);
                    v___x_5897_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5897_, 0, v___x_5894_);
                    crate::leanh::lean_ctor_set(v___x_5897_, 1, v___x_5896_);
                    v___x_5898_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5898_, 0, v___x_5897_);
                    crate::leanh::lean_ctor_set(v___x_5898_, 1, v___x_5894_);
                    v___x_5899_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5899_, 0, v___x_5898_);
                    v___x_5900_ = l_Lean_MVarId_apply(
                        v_mvar_5884_,
                        v_a_5893_,
                        v_cfg_5886_,
                        v___x_5899_,
                        v_a_5887_,
                        v_a_5888_,
                        v_a_5889_,
                        v_a_5890_,
                    );
                    return v___x_5900_;
                } else {
                    crate::leanh::lean_dec_ref(v_cfg_5886_);
                    crate::leanh::lean_dec(v_c_5885_);
                    crate::leanh::lean_dec(v_mvar_5884_);
                    v_a_5901_ = crate::leanh::lean_ctor_get(v___x_5892_, 0);
                    v_isSharedCheck_5908_ = (!crate::leanh::lean_is_exclusive(v___x_5892_)) as u8;
                    if v_isSharedCheck_5908_ == 0 {
                        v___x_5903_ = v___x_5892_;
                        v_isShared_5904_ = v_isSharedCheck_5908_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5901_);
                        crate::leanh::lean_dec(v___x_5892_);
                        v___x_5903_ = crate::leanh::lean_box(0);
                        v_isShared_5904_ = v_isSharedCheck_5908_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5904_ == 0 {
                    v___x_5906_ = v___x_5903_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5907_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5907_, 0, v_a_5901_);
                    v___x_5906_ = v_reuseFailAlloc_5907_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5906_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_applyConst___boxed(
    mut v_mvar_5909_: *mut crate::leanh::LeanObject,
    mut v_c_5910_: *mut crate::leanh::LeanObject,
    mut v_cfg_5911_: *mut crate::leanh::LeanObject,
    mut v_a_5912_: *mut crate::leanh::LeanObject,
    mut v_a_5913_: *mut crate::leanh::LeanObject,
    mut v_a_5914_: *mut crate::leanh::LeanObject,
    mut v_a_5915_: *mut crate::leanh::LeanObject,
    mut v_a_5916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5917_ = l_Lean_MVarId_applyConst(
        v_mvar_5909_,
        v_c_5910_,
        v_cfg_5911_,
        v_a_5912_,
        v_a_5913_,
        v_a_5914_,
        v_a_5915_,
    );
    crate::leanh::lean_dec(v_a_5915_);
    crate::leanh::lean_dec_ref(v_a_5914_);
    crate::leanh::lean_dec(v_a_5913_);
    crate::leanh::lean_dec_ref(v_a_5912_);
    return v_res_5917_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(
    mut v_msgData_5918_: *mut crate::leanh::LeanObject,
    mut v___y_5919_: *mut crate::leanh::LeanObject,
    mut v___y_5920_: *mut crate::leanh::LeanObject,
    mut v___y_5921_: *mut crate::leanh::LeanObject,
    mut v___y_5922_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5924_ = lean_st_ref_get(v___y_5922_);
    v_env_5925_ = crate::leanh::lean_ctor_get(v___x_5924_, 0);
    crate::leanh::lean_inc_ref(v_env_5925_);
    crate::leanh::lean_dec(v___x_5924_);
    v___x_5926_ = lean_st_ref_get(v___y_5920_);
    v_mctx_5927_ = crate::leanh::lean_ctor_get(v___x_5926_, 0);
    crate::leanh::lean_inc_ref(v_mctx_5927_);
    crate::leanh::lean_dec(v___x_5926_);
    v_lctx_5928_ = crate::leanh::lean_ctor_get(v___y_5919_, 2);
    v_options_5929_ = crate::leanh::lean_ctor_get(v___y_5921_, 2);
    crate::leanh::lean_inc_ref(v_options_5929_);
    crate::leanh::lean_inc_ref(v_lctx_5928_);
    v___x_5930_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5930_, 0, v_env_5925_);
    crate::leanh::lean_ctor_set(v___x_5930_, 1, v_mctx_5927_);
    crate::leanh::lean_ctor_set(v___x_5930_, 2, v_lctx_5928_);
    crate::leanh::lean_ctor_set(v___x_5930_, 3, v_options_5929_);
    v___x_5931_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5931_, 0, v___x_5930_);
    crate::leanh::lean_ctor_set(v___x_5931_, 1, v_msgData_5918_);
    v___x_5932_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5932_, 0, v___x_5931_);
    return v___x_5932_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1___boxed(
    mut v_msgData_5933_: *mut crate::leanh::LeanObject,
    mut v___y_5934_: *mut crate::leanh::LeanObject,
    mut v___y_5935_: *mut crate::leanh::LeanObject,
    mut v___y_5936_: *mut crate::leanh::LeanObject,
    mut v___y_5937_: *mut crate::leanh::LeanObject,
    mut v___y_5938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5939_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msgData_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_);
    crate::leanh::lean_dec(v___y_5937_);
    crate::leanh::lean_dec_ref(v___y_5936_);
    crate::leanh::lean_dec(v___y_5935_);
    crate::leanh::lean_dec_ref(v___y_5934_);
    return v_res_5939_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(
    mut v_msg_5940_: *mut crate::leanh::LeanObject,
    mut v___y_5941_: *mut crate::leanh::LeanObject,
    mut v___y_5942_: *mut crate::leanh::LeanObject,
    mut v___y_5943_: *mut crate::leanh::LeanObject,
    mut v___y_5944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5951_: u8 = 0;
    let mut v___x_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5956_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5946_ = crate::leanh::lean_ctor_get(v___y_5943_, 5);
                v___x_5947_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_MVarId_applyN_spec__1_spec__1(v_msg_5940_, v___y_5941_, v___y_5942_, v___y_5943_, v___y_5944_);
                v_a_5948_ = crate::leanh::lean_ctor_get(v___x_5947_, 0);
                v_isSharedCheck_5956_ = (!crate::leanh::lean_is_exclusive(v___x_5947_)) as u8;
                if v_isSharedCheck_5956_ == 0 {
                    v___x_5950_ = v___x_5947_;
                    v_isShared_5951_ = v_isSharedCheck_5956_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_5948_);
                    crate::leanh::lean_dec(v___x_5947_);
                    v___x_5950_ = crate::leanh::lean_box(0);
                    v_isShared_5951_ = v_isSharedCheck_5956_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_5946_);
                v___x_5952_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5952_, 0, v_ref_5946_);
                crate::leanh::lean_ctor_set(v___x_5952_, 1, v_a_5948_);
                if v_isShared_5951_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5950_, 1);
                    crate::leanh::lean_ctor_set(v___x_5950_, 0, v___x_5952_);
                    v___x_5954_ = v___x_5950_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5955_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5955_, 0, v___x_5952_);
                    v___x_5954_ = v_reuseFailAlloc_5955_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5954_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg___boxed(
    mut v_msg_5957_: *mut crate::leanh::LeanObject,
    mut v___y_5958_: *mut crate::leanh::LeanObject,
    mut v___y_5959_: *mut crate::leanh::LeanObject,
    mut v___y_5960_: *mut crate::leanh::LeanObject,
    mut v___y_5961_: *mut crate::leanh::LeanObject,
    mut v___y_5962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5963_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(
        v_msg_5957_,
        v___y_5958_,
        v___y_5959_,
        v___y_5960_,
        v___y_5961_,
    );
    crate::leanh::lean_dec(v___y_5961_);
    crate::leanh::lean_dec_ref(v___y_5960_);
    crate::leanh::lean_dec(v___y_5959_);
    crate::leanh::lean_dec_ref(v___y_5958_);
    return v_res_5963_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(
    mut v_sz_5964_: usize,
    mut v_i_5965_: usize,
    mut v_bs_5966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5967_: u8 = 0;
    let mut v_v_5968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5972_: usize = 0;
    let mut v___x_5973_: usize = 0;
    let mut v___x_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5967_ = lean_usize_dec_lt(v_i_5965_, v_sz_5964_);
                if v___x_5967_ == 0 {
                    return v_bs_5966_;
                } else {
                    v_v_5968_ = lean_array_uget(v_bs_5966_, v_i_5965_);
                    v___x_5969_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5970_ = lean_array_uset(v_bs_5966_, v_i_5965_, v___x_5969_);
                    v___x_5971_ = l_Lean_Expr_mvarId_x21(v_v_5968_);
                    crate::leanh::lean_dec(v_v_5968_);
                    v___x_5972_ = 1usize;
                    v___x_5973_ = lean_usize_add(v_i_5965_, v___x_5972_);
                    v___x_5974_ = lean_array_uset(v_bs_x27_5970_, v_i_5965_, v___x_5971_);
                    v_i_5965_ = v___x_5973_;
                    v_bs_5966_ = v___x_5974_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0___boxed(
    mut v_sz_5976_: *mut crate::leanh::LeanObject,
    mut v_i_5977_: *mut crate::leanh::LeanObject,
    mut v_bs_5978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5979_: usize = 0;
    let mut v_i_boxed_5980_: usize = 0;
    let mut v_res_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5979_ = crate::leanh::lean_unbox_usize(v_sz_5976_);
    crate::leanh::lean_dec(v_sz_5976_);
    v_i_boxed_5980_ = crate::leanh::lean_unbox_usize(v_i_5977_);
    crate::leanh::lean_dec(v_i_5977_);
    v_res_5981_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_boxed_5979_, v_i_boxed_5980_, v_bs_5978_);
    return v_res_5981_;
}
pub unsafe fn _init_l_Lean_MVarId_applyN___lam__0___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5983_ = l_Lean_MVarId_applyN___lam__0___closed__0;
    v___x_5984_ = l_Lean_stringToMessageData(v___x_5983_);
    return v___x_5984_;
}
pub unsafe fn _init_l_Lean_MVarId_applyN___lam__0___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5986_ = l_Lean_MVarId_applyN___lam__0___closed__2;
    v___x_5987_ = l_Lean_stringToMessageData(v___x_5986_);
    return v___x_5987_;
}
pub unsafe fn _init_l_Lean_MVarId_applyN___lam__0___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_5989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5989_ = l_Lean_MVarId_applyN___lam__0___closed__4;
    v___x_5990_ = l_Lean_stringToMessageData(v___x_5989_);
    return v___x_5990_;
}
pub unsafe fn _init_l_Lean_MVarId_applyN___lam__0___closed__7() -> *mut crate::leanh::LeanObject {
    let mut v___x_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5992_ = l_Lean_MVarId_applyN___lam__0___closed__6;
    v___x_5993_ = l_Lean_stringToMessageData(v___x_5992_);
    return v___x_5993_;
}
pub unsafe fn _init_l_Lean_MVarId_applyN___lam__0___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5995_ = l_Lean_MVarId_applyN___lam__0___closed__8;
    v___x_5996_ = l_Lean_stringToMessageData(v___x_5995_);
    return v___x_5996_;
}
pub unsafe fn _init_l_Lean_MVarId_applyN___lam__0___closed__11() -> *mut crate::leanh::LeanObject {
    let mut v___x_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5998_ = l_Lean_MVarId_applyN___lam__0___closed__10;
    v___x_5999_ = l_Lean_stringToMessageData(v___x_5998_);
    return v___x_5999_;
}
pub unsafe fn l_Lean_MVarId_applyN___lam__0(
    mut v_mvarId_6000_: *mut crate::leanh::LeanObject,
    mut v___x_6001_: *mut crate::leanh::LeanObject,
    mut v_e_6002_: *mut crate::leanh::LeanObject,
    mut v_n_6003_: *mut crate::leanh::LeanObject,
    mut v_useApproxDefEq_6004_: u8,
    mut v___y_6005_: *mut crate::leanh::LeanObject,
    mut v___y_6006_: *mut crate::leanh::LeanObject,
    mut v___y_6007_: *mut crate::leanh::LeanObject,
    mut v___y_6008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: u8 = 0;
    let mut v___x_6016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6022_: u8 = 0;
    let mut v___y_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6029_: u8 = 0;
    let mut v_sz_6030_: usize = 0;
    let mut v___x_6031_: usize = 0;
    let mut v___x_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6037_: u8 = 0;
    let mut v_unused_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6042_: u8 = 0;
    let mut v___y_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: u8 = 0;
    let mut v___x_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6072_: u8 = 0;
    let mut v___x_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6076_: u8 = 0;
    let mut v_reuseFailAlloc_6077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6082_: u8 = 0;
    let mut v___x_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6086_: u8 = 0;
    let mut v___x_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6088_: u8 = 0;
    let mut v___x_6089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6102_: u8 = 0;
    let mut v___x_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6106_: u8 = 0;
    let mut v_isSharedCheck_6107_: u8 = 0;
    let mut v_unused_6108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6109_: u8 = 0;
    let mut v_a_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6113_: u8 = 0;
    let mut v___x_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6117_: u8 = 0;
    let mut v_a_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6121_: u8 = 0;
    let mut v___x_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6125_: u8 = 0;
    let mut v_a_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6129_: u8 = 0;
    let mut v___x_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6133_: u8 = 0;
    let mut v_a_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6137_: u8 = 0;
    let mut v___x_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6141_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_6000_);
                v___x_6010_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_6000_,
                    v___x_6001_,
                    v___y_6005_,
                    v___y_6006_,
                    v___y_6007_,
                    v___y_6008_,
                );
                if crate::leanh::lean_obj_tag(v___x_6010_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6010_, 1);
                    crate::leanh::lean_inc(v_mvarId_6000_);
                    v___x_6011_ = l_Lean_MVarId_getType(
                        v_mvarId_6000_,
                        v___y_6005_,
                        v___y_6006_,
                        v___y_6007_,
                        v___y_6008_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6011_) == 0 {
                        v_a_6012_ = crate::leanh::lean_ctor_get(v___x_6011_, 0);
                        crate::leanh::lean_inc(v_a_6012_);
                        crate::leanh::lean_dec_ref_known(v___x_6011_, 1);
                        crate::leanh::lean_inc(v___y_6008_);
                        crate::leanh::lean_inc_ref(v___y_6007_);
                        crate::leanh::lean_inc(v___y_6006_);
                        crate::leanh::lean_inc_ref(v___y_6005_);
                        crate::leanh::lean_inc_ref(v_e_6002_);
                        v___x_6013_ = lean_infer_type(
                            v_e_6002_,
                            v___y_6005_,
                            v___y_6006_,
                            v___y_6007_,
                            v___y_6008_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6013_) == 0 {
                            v_a_6014_ = crate::leanh::lean_ctor_get(v___x_6013_, 0);
                            crate::leanh::lean_inc(v_a_6014_);
                            crate::leanh::lean_dec_ref_known(v___x_6013_, 1);
                            v___x_6015_ = 0;
                            crate::leanh::lean_inc(v_n_6003_);
                            v___x_6016_ = l_Lean_Meta_forallMetaBoundedTelescope(
                                v_a_6014_,
                                v_n_6003_,
                                v___x_6015_,
                                v___y_6005_,
                                v___y_6006_,
                                v___y_6007_,
                                v___y_6008_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6016_) == 0 {
                                v_a_6017_ = crate::leanh::lean_ctor_get(v___x_6016_, 0);
                                crate::leanh::lean_inc(v_a_6017_);
                                crate::leanh::lean_dec_ref_known(v___x_6016_, 1);
                                v_fst_6018_ = crate::leanh::lean_ctor_get(v_a_6017_, 0);
                                v_snd_6019_ = crate::leanh::lean_ctor_get(v_a_6017_, 1);
                                v_isSharedCheck_6109_ =
                                    (!crate::leanh::lean_is_exclusive(v_a_6017_)) as u8;
                                if v_isSharedCheck_6109_ == 0 {
                                    v___x_6021_ = v_a_6017_;
                                    v_isShared_6022_ = v_isSharedCheck_6109_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_snd_6019_);
                                    crate::leanh::lean_inc(v_fst_6018_);
                                    crate::leanh::lean_dec(v_a_6017_);
                                    v___x_6021_ = crate::leanh::lean_box(0);
                                    v_isShared_6022_ = v_isSharedCheck_6109_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6012_);
                                crate::leanh::lean_dec(v___y_6008_);
                                crate::leanh::lean_dec_ref(v___y_6007_);
                                crate::leanh::lean_dec(v___y_6006_);
                                crate::leanh::lean_dec_ref(v___y_6005_);
                                crate::leanh::lean_dec(v_n_6003_);
                                crate::leanh::lean_dec_ref(v_e_6002_);
                                crate::leanh::lean_dec(v_mvarId_6000_);
                                v_a_6110_ = crate::leanh::lean_ctor_get(v___x_6016_, 0);
                                v_isSharedCheck_6117_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6016_)) as u8;
                                if v_isSharedCheck_6117_ == 0 {
                                    v___x_6112_ = v___x_6016_;
                                    v_isShared_6113_ = v_isSharedCheck_6117_;
                                    state = 15;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6110_);
                                    crate::leanh::lean_dec(v___x_6016_);
                                    v___x_6112_ = crate::leanh::lean_box(0);
                                    v_isShared_6113_ = v_isSharedCheck_6117_;
                                    state = 15;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6012_);
                            crate::leanh::lean_dec(v___y_6008_);
                            crate::leanh::lean_dec_ref(v___y_6007_);
                            crate::leanh::lean_dec(v___y_6006_);
                            crate::leanh::lean_dec_ref(v___y_6005_);
                            crate::leanh::lean_dec(v_n_6003_);
                            crate::leanh::lean_dec_ref(v_e_6002_);
                            crate::leanh::lean_dec(v_mvarId_6000_);
                            v_a_6118_ = crate::leanh::lean_ctor_get(v___x_6013_, 0);
                            v_isSharedCheck_6125_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6013_)) as u8;
                            if v_isSharedCheck_6125_ == 0 {
                                v___x_6120_ = v___x_6013_;
                                v_isShared_6121_ = v_isSharedCheck_6125_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6118_);
                                crate::leanh::lean_dec(v___x_6013_);
                                v___x_6120_ = crate::leanh::lean_box(0);
                                v_isShared_6121_ = v_isSharedCheck_6125_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_6008_);
                        crate::leanh::lean_dec_ref(v___y_6007_);
                        crate::leanh::lean_dec(v___y_6006_);
                        crate::leanh::lean_dec_ref(v___y_6005_);
                        crate::leanh::lean_dec(v_n_6003_);
                        crate::leanh::lean_dec_ref(v_e_6002_);
                        crate::leanh::lean_dec(v_mvarId_6000_);
                        v_a_6126_ = crate::leanh::lean_ctor_get(v___x_6011_, 0);
                        v_isSharedCheck_6133_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6011_)) as u8;
                        if v_isSharedCheck_6133_ == 0 {
                            v___x_6128_ = v___x_6011_;
                            v_isShared_6129_ = v_isSharedCheck_6133_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6126_);
                            crate::leanh::lean_dec(v___x_6011_);
                            v___x_6128_ = crate::leanh::lean_box(0);
                            v_isShared_6129_ = v_isSharedCheck_6133_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___y_6008_);
                    crate::leanh::lean_dec_ref(v___y_6007_);
                    crate::leanh::lean_dec(v___y_6006_);
                    crate::leanh::lean_dec_ref(v___y_6005_);
                    crate::leanh::lean_dec(v_n_6003_);
                    crate::leanh::lean_dec_ref(v_e_6002_);
                    crate::leanh::lean_dec(v_mvarId_6000_);
                    v_a_6134_ = crate::leanh::lean_ctor_get(v___x_6010_, 0);
                    v_isSharedCheck_6141_ = (!crate::leanh::lean_is_exclusive(v___x_6010_)) as u8;
                    if v_isSharedCheck_6141_ == 0 {
                        v___x_6136_ = v___x_6010_;
                        v_isShared_6137_ = v_isSharedCheck_6141_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6134_);
                        crate::leanh::lean_dec(v___x_6010_);
                        v___x_6136_ = crate::leanh::lean_box(0);
                        v_isShared_6137_ = v_isSharedCheck_6141_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_6039_ = crate::leanh::lean_ctor_get(v_snd_6019_, 1);
                v_isSharedCheck_6107_ = (!crate::leanh::lean_is_exclusive(v_snd_6019_)) as u8;
                if v_isSharedCheck_6107_ == 0 {
                    v_unused_6108_ = crate::leanh::lean_ctor_get(v_snd_6019_, 0);
                    crate::leanh::lean_dec(v_unused_6108_);
                    v___x_6041_ = v_snd_6019_;
                    v_isShared_6042_ = v_isSharedCheck_6107_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_6039_);
                    crate::leanh::lean_dec(v_snd_6019_);
                    v___x_6041_ = crate::leanh::lean_box(0);
                    v_isShared_6042_ = v_isSharedCheck_6107_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_fst_6018_);
                v___x_6025_ = l_Lean_Expr_beta(v_e_6002_, v_fst_6018_);
                v___x_6026_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(
                    v_mvarId_6000_,
                    v___x_6025_,
                    v___y_6024_,
                );
                crate::leanh::lean_dec(v___y_6024_);
                v_isSharedCheck_6037_ = (!crate::leanh::lean_is_exclusive(v___x_6026_)) as u8;
                if v_isSharedCheck_6037_ == 0 {
                    v_unused_6038_ = crate::leanh::lean_ctor_get(v___x_6026_, 0);
                    crate::leanh::lean_dec(v_unused_6038_);
                    v___x_6028_ = v___x_6026_;
                    v_isShared_6029_ = v_isSharedCheck_6037_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_6026_);
                    v___x_6028_ = crate::leanh::lean_box(0);
                    v_isShared_6029_ = v_isSharedCheck_6037_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_sz_6030_ = lean_array_size(v_fst_6018_);
                v___x_6031_ = 0usize;
                v___x_6032_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_MVarId_applyN_spec__0(v_sz_6030_, v___x_6031_, v_fst_6018_);
                v___x_6033_ = lean_array_to_list(v___x_6032_);
                if v_isShared_6029_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6028_, 0, v___x_6033_);
                    v___x_6035_ = v___x_6028_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6036_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6036_, 0, v___x_6033_);
                    v___x_6035_ = v_reuseFailAlloc_6036_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6035_;
            }
            5 => {
                v___x_6087_ = lean_array_get_size(v_fst_6018_);
                v___x_6088_ = lean_nat_dec_eq(v___x_6087_, v_n_6003_);
                if v___x_6088_ == 0 {
                    crate::leanh::lean_del_object(v___x_6041_);
                    crate::leanh::lean_del_object(v___x_6021_);
                    crate::leanh::lean_dec(v_fst_6018_);
                    crate::leanh::lean_dec(v_a_6012_);
                    crate::leanh::lean_dec_ref(v_e_6002_);
                    crate::leanh::lean_dec(v_mvarId_6000_);
                    v___x_6089_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__9),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__9_once),
                        _init_l_Lean_MVarId_applyN___lam__0___closed__9,
                    );
                    v___x_6090_ = l_Nat_reprFast(v_n_6003_);
                    v___x_6091_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6091_, 0, v___x_6090_);
                    v___x_6092_ = l_Lean_MessageData_ofFormat(v___x_6091_);
                    v___x_6093_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6093_, 0, v___x_6089_);
                    crate::leanh::lean_ctor_set(v___x_6093_, 1, v___x_6092_);
                    v___x_6094_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__11),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__11_once),
                        _init_l_Lean_MVarId_applyN___lam__0___closed__11,
                    );
                    v___x_6095_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6095_, 0, v___x_6093_);
                    crate::leanh::lean_ctor_set(v___x_6095_, 1, v___x_6094_);
                    v___x_6096_ = l_Lean_indentExpr(v_snd_6039_);
                    v___x_6097_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6097_, 0, v___x_6095_);
                    crate::leanh::lean_ctor_set(v___x_6097_, 1, v___x_6096_);
                    v___x_6098_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(
                        v___x_6097_,
                        v___y_6005_,
                        v___y_6006_,
                        v___y_6007_,
                        v___y_6008_,
                    );
                    crate::leanh::lean_dec(v___y_6008_);
                    crate::leanh::lean_dec_ref(v___y_6007_);
                    crate::leanh::lean_dec(v___y_6006_);
                    crate::leanh::lean_dec_ref(v___y_6005_);
                    v_a_6099_ = crate::leanh::lean_ctor_get(v___x_6098_, 0);
                    v_isSharedCheck_6106_ = (!crate::leanh::lean_is_exclusive(v___x_6098_)) as u8;
                    if v_isSharedCheck_6106_ == 0 {
                        v___x_6101_ = v___x_6098_;
                        v_isShared_6102_ = v_isSharedCheck_6106_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6099_);
                        crate::leanh::lean_dec(v___x_6098_);
                        v___x_6101_ = crate::leanh::lean_box(0);
                        v_isShared_6102_ = v_isSharedCheck_6106_;
                        state = 13;
                        continue;
                    }
                } else {
                    v___y_6044_ = v___y_6005_;
                    v___y_6045_ = v___y_6006_;
                    v___y_6046_ = v___y_6007_;
                    v___y_6047_ = v___y_6008_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                crate::leanh::lean_inc(v_a_6012_);
                crate::leanh::lean_inc(v_snd_6039_);
                v___x_6048_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_isDefEqApply(
                    v_useApproxDefEq_6004_,
                    v_snd_6039_,
                    v_a_6012_,
                    v___y_6044_,
                    v___y_6045_,
                    v___y_6046_,
                    v___y_6047_,
                );
                if crate::leanh::lean_obj_tag(v___x_6048_) == 0 {
                    v_a_6049_ = crate::leanh::lean_ctor_get(v___x_6048_, 0);
                    crate::leanh::lean_inc(v_a_6049_);
                    crate::leanh::lean_dec_ref_known(v___x_6048_, 1);
                    v___x_6050_ = (crate::leanh::lean_unbox(v_a_6049_) as u8);
                    crate::leanh::lean_dec(v_a_6049_);
                    if v___x_6050_ == 0 {
                        crate::leanh::lean_dec(v_fst_6018_);
                        crate::leanh::lean_dec_ref(v_e_6002_);
                        crate::leanh::lean_dec(v_mvarId_6000_);
                        v___x_6051_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__1),
                            core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__1_once),
                            _init_l_Lean_MVarId_applyN___lam__0___closed__1,
                        );
                        v___x_6052_ = l_Lean_indentExpr(v_a_6012_);
                        if v_isShared_6042_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_6041_, 7);
                            crate::leanh::lean_ctor_set(v___x_6041_, 1, v___x_6052_);
                            crate::leanh::lean_ctor_set(v___x_6041_, 0, v___x_6051_);
                            v___x_6054_ = v___x_6041_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_6078_ =
                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6078_, 0, v___x_6051_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6078_, 1, v___x_6052_);
                            v___x_6054_ = v_reuseFailAlloc_6078_;
                            state = 7;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___y_6047_);
                        crate::leanh::lean_dec_ref(v___y_6046_);
                        crate::leanh::lean_dec_ref(v___y_6044_);
                        crate::leanh::lean_del_object(v___x_6041_);
                        crate::leanh::lean_dec(v_snd_6039_);
                        crate::leanh::lean_del_object(v___x_6021_);
                        crate::leanh::lean_dec(v_a_6012_);
                        crate::leanh::lean_dec(v_n_6003_);
                        v___y_6024_ = v___y_6045_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_6047_);
                    crate::leanh::lean_dec_ref(v___y_6046_);
                    crate::leanh::lean_dec(v___y_6045_);
                    crate::leanh::lean_dec_ref(v___y_6044_);
                    crate::leanh::lean_del_object(v___x_6041_);
                    crate::leanh::lean_dec(v_snd_6039_);
                    crate::leanh::lean_del_object(v___x_6021_);
                    crate::leanh::lean_dec(v_fst_6018_);
                    crate::leanh::lean_dec(v_a_6012_);
                    crate::leanh::lean_dec(v_n_6003_);
                    crate::leanh::lean_dec_ref(v_e_6002_);
                    crate::leanh::lean_dec(v_mvarId_6000_);
                    v_a_6079_ = crate::leanh::lean_ctor_get(v___x_6048_, 0);
                    v_isSharedCheck_6086_ = (!crate::leanh::lean_is_exclusive(v___x_6048_)) as u8;
                    if v_isSharedCheck_6086_ == 0 {
                        v___x_6081_ = v___x_6048_;
                        v_isShared_6082_ = v_isSharedCheck_6086_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6079_);
                        crate::leanh::lean_dec(v___x_6048_);
                        v___x_6081_ = crate::leanh::lean_box(0);
                        v_isShared_6082_ = v_isSharedCheck_6086_;
                        state = 11;
                        continue;
                    }
                }
            }
            7 => {
                v___x_6055_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__3_once),
                    _init_l_Lean_MVarId_applyN___lam__0___closed__3,
                );
                if v_isShared_6022_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6021_, 7);
                    crate::leanh::lean_ctor_set(v___x_6021_, 1, v___x_6055_);
                    crate::leanh::lean_ctor_set(v___x_6021_, 0, v___x_6054_);
                    v___x_6057_ = v___x_6021_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6077_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6077_, 0, v___x_6054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6077_, 1, v___x_6055_);
                    v___x_6057_ = v_reuseFailAlloc_6077_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_6058_ = l_Lean_indentExpr(v_snd_6039_);
                v___x_6059_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6059_, 0, v___x_6057_);
                crate::leanh::lean_ctor_set(v___x_6059_, 1, v___x_6058_);
                v___x_6060_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__5),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__5_once),
                    _init_l_Lean_MVarId_applyN___lam__0___closed__5,
                );
                v___x_6061_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6061_, 0, v___x_6059_);
                crate::leanh::lean_ctor_set(v___x_6061_, 1, v___x_6060_);
                v___x_6062_ = l_Nat_reprFast(v_n_6003_);
                v___x_6063_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6063_, 0, v___x_6062_);
                v___x_6064_ = l_Lean_MessageData_ofFormat(v___x_6063_);
                v___x_6065_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6065_, 0, v___x_6061_);
                crate::leanh::lean_ctor_set(v___x_6065_, 1, v___x_6064_);
                v___x_6066_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__7),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_applyN___lam__0___closed__7_once),
                    _init_l_Lean_MVarId_applyN___lam__0___closed__7,
                );
                v___x_6067_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6067_, 0, v___x_6065_);
                crate::leanh::lean_ctor_set(v___x_6067_, 1, v___x_6066_);
                v___x_6068_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(
                    v___x_6067_,
                    v___y_6044_,
                    v___y_6045_,
                    v___y_6046_,
                    v___y_6047_,
                );
                crate::leanh::lean_dec(v___y_6047_);
                crate::leanh::lean_dec_ref(v___y_6046_);
                crate::leanh::lean_dec(v___y_6045_);
                crate::leanh::lean_dec_ref(v___y_6044_);
                v_a_6069_ = crate::leanh::lean_ctor_get(v___x_6068_, 0);
                v_isSharedCheck_6076_ = (!crate::leanh::lean_is_exclusive(v___x_6068_)) as u8;
                if v_isSharedCheck_6076_ == 0 {
                    v___x_6071_ = v___x_6068_;
                    v_isShared_6072_ = v_isSharedCheck_6076_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6069_);
                    crate::leanh::lean_dec(v___x_6068_);
                    v___x_6071_ = crate::leanh::lean_box(0);
                    v_isShared_6072_ = v_isSharedCheck_6076_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_6072_ == 0 {
                    v___x_6074_ = v___x_6071_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6075_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6075_, 0, v_a_6069_);
                    v___x_6074_ = v_reuseFailAlloc_6075_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6074_;
            }
            11 => {
                if v_isShared_6082_ == 0 {
                    v___x_6084_ = v___x_6081_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6085_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6085_, 0, v_a_6079_);
                    v___x_6084_ = v_reuseFailAlloc_6085_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6084_;
            }
            13 => {
                if v_isShared_6102_ == 0 {
                    v___x_6104_ = v___x_6101_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6105_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6105_, 0, v_a_6099_);
                    v___x_6104_ = v_reuseFailAlloc_6105_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6104_;
            }
            15 => {
                if v_isShared_6113_ == 0 {
                    v___x_6115_ = v___x_6112_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_6116_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6116_, 0, v_a_6110_);
                    v___x_6115_ = v_reuseFailAlloc_6116_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_6115_;
            }
            17 => {
                if v_isShared_6121_ == 0 {
                    v___x_6123_ = v___x_6120_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6124_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6124_, 0, v_a_6118_);
                    v___x_6123_ = v_reuseFailAlloc_6124_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6123_;
            }
            19 => {
                if v_isShared_6129_ == 0 {
                    v___x_6131_ = v___x_6128_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_6132_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6132_, 0, v_a_6126_);
                    v___x_6131_ = v_reuseFailAlloc_6132_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_6131_;
            }
            21 => {
                if v_isShared_6137_ == 0 {
                    v___x_6139_ = v___x_6136_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_6140_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6140_, 0, v_a_6134_);
                    v___x_6139_ = v_reuseFailAlloc_6140_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_6139_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_applyN___lam__0___boxed(
    mut v_mvarId_6142_: *mut crate::leanh::LeanObject,
    mut v___x_6143_: *mut crate::leanh::LeanObject,
    mut v_e_6144_: *mut crate::leanh::LeanObject,
    mut v_n_6145_: *mut crate::leanh::LeanObject,
    mut v_useApproxDefEq_6146_: *mut crate::leanh::LeanObject,
    mut v___y_6147_: *mut crate::leanh::LeanObject,
    mut v___y_6148_: *mut crate::leanh::LeanObject,
    mut v___y_6149_: *mut crate::leanh::LeanObject,
    mut v___y_6150_: *mut crate::leanh::LeanObject,
    mut v___y_6151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useApproxDefEq_boxed_6152_: u8 = 0;
    let mut v_res_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useApproxDefEq_boxed_6152_ = (crate::leanh::lean_unbox(v_useApproxDefEq_6146_) as u8);
    v_res_6153_ = l_Lean_MVarId_applyN___lam__0(
        v_mvarId_6142_,
        v___x_6143_,
        v_e_6144_,
        v_n_6145_,
        v_useApproxDefEq_boxed_6152_,
        v___y_6147_,
        v___y_6148_,
        v___y_6149_,
        v___y_6150_,
    );
    return v_res_6153_;
}
pub unsafe fn l_Lean_MVarId_applyN(
    mut v_mvarId_6154_: *mut crate::leanh::LeanObject,
    mut v_e_6155_: *mut crate::leanh::LeanObject,
    mut v_n_6156_: *mut crate::leanh::LeanObject,
    mut v_useApproxDefEq_6157_: u8,
    mut v_a_6158_: *mut crate::leanh::LeanObject,
    mut v_a_6159_: *mut crate::leanh::LeanObject,
    mut v_a_6160_: *mut crate::leanh::LeanObject,
    mut v_a_6161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6163_ =
        l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_throwApplyError___redArg___closed__1;
    v___x_6164_ = crate::leanh::lean_box((v_useApproxDefEq_6157_) as usize);
    crate::leanh::lean_inc(v_mvarId_6154_);
    v___f_6165_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_applyN___lam__0___boxed as *mut core::ffi::c_void,
        10,
        5,
    );
    crate::leanh::lean_closure_set(v___f_6165_, 0, v_mvarId_6154_);
    crate::leanh::lean_closure_set(v___f_6165_, 1, v___x_6163_);
    crate::leanh::lean_closure_set(v___f_6165_, 2, v_e_6155_);
    crate::leanh::lean_closure_set(v___f_6165_, 3, v_n_6156_);
    crate::leanh::lean_closure_set(v___f_6165_, 4, v___x_6164_);
    v___x_6166_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(
        v_mvarId_6154_,
        v___f_6165_,
        v_a_6158_,
        v_a_6159_,
        v_a_6160_,
        v_a_6161_,
    );
    return v___x_6166_;
}
pub unsafe fn l_Lean_MVarId_applyN___boxed(
    mut v_mvarId_6167_: *mut crate::leanh::LeanObject,
    mut v_e_6168_: *mut crate::leanh::LeanObject,
    mut v_n_6169_: *mut crate::leanh::LeanObject,
    mut v_useApproxDefEq_6170_: *mut crate::leanh::LeanObject,
    mut v_a_6171_: *mut crate::leanh::LeanObject,
    mut v_a_6172_: *mut crate::leanh::LeanObject,
    mut v_a_6173_: *mut crate::leanh::LeanObject,
    mut v_a_6174_: *mut crate::leanh::LeanObject,
    mut v_a_6175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_useApproxDefEq_boxed_6176_: u8 = 0;
    let mut v_res_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_useApproxDefEq_boxed_6176_ = (crate::leanh::lean_unbox(v_useApproxDefEq_6170_) as u8);
    v_res_6177_ = l_Lean_MVarId_applyN(
        v_mvarId_6167_,
        v_e_6168_,
        v_n_6169_,
        v_useApproxDefEq_boxed_6176_,
        v_a_6171_,
        v_a_6172_,
        v_a_6173_,
        v_a_6174_,
    );
    crate::leanh::lean_dec(v_a_6174_);
    crate::leanh::lean_dec_ref(v_a_6173_);
    crate::leanh::lean_dec(v_a_6172_);
    crate::leanh::lean_dec_ref(v_a_6171_);
    return v_res_6177_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(
    mut v_00_u03b1_6178_: *mut crate::leanh::LeanObject,
    mut v_msg_6179_: *mut crate::leanh::LeanObject,
    mut v___y_6180_: *mut crate::leanh::LeanObject,
    mut v___y_6181_: *mut crate::leanh::LeanObject,
    mut v___y_6182_: *mut crate::leanh::LeanObject,
    mut v___y_6183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6185_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(
        v_msg_6179_,
        v___y_6180_,
        v___y_6181_,
        v___y_6182_,
        v___y_6183_,
    );
    return v___x_6185_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___boxed(
    mut v_00_u03b1_6186_: *mut crate::leanh::LeanObject,
    mut v_msg_6187_: *mut crate::leanh::LeanObject,
    mut v___y_6188_: *mut crate::leanh::LeanObject,
    mut v___y_6189_: *mut crate::leanh::LeanObject,
    mut v___y_6190_: *mut crate::leanh::LeanObject,
    mut v___y_6191_: *mut crate::leanh::LeanObject,
    mut v___y_6192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6193_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1(
        v_00_u03b1_6186_,
        v_msg_6187_,
        v___y_6188_,
        v___y_6189_,
        v___y_6190_,
        v___y_6191_,
    );
    crate::leanh::lean_dec(v___y_6191_);
    crate::leanh::lean_dec_ref(v___y_6190_);
    crate::leanh::lean_dec(v___y_6189_);
    crate::leanh::lean_dec_ref(v___y_6188_);
    return v_res_6193_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6204_ = crate::leanh::lean_box(0);
    v___x_6205_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__5;
    v___x_6206_ = l_Lean_mkConst(v___x_6205_, v___x_6204_);
    return v___x_6206_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(
    mut v_tag_6207_: *mut crate::leanh::LeanObject,
    mut v_type_6208_: *mut crate::leanh::LeanObject,
    mut v_a_6209_: *mut crate::leanh::LeanObject,
    mut v_a_6210_: *mut crate::leanh::LeanObject,
    mut v_a_6211_: *mut crate::leanh::LeanObject,
    mut v_a_6212_: *mut crate::leanh::LeanObject,
    mut v_a_6213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: u8 = 0;
    let mut v___x_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6231_: u8 = 0;
    let mut v___x_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6239_: u8 = 0;
    let mut v___x_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6249_: u8 = 0;
    let mut v___x_6250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_a_6213_);
                crate::leanh::lean_inc_ref(v_a_6212_);
                crate::leanh::lean_inc(v_a_6211_);
                crate::leanh::lean_inc_ref(v_a_6210_);
                v___x_6215_ = lean_whnf(v_type_6208_, v_a_6210_, v_a_6211_, v_a_6212_, v_a_6213_);
                if crate::leanh::lean_obj_tag(v___x_6215_) == 0 {
                    v_a_6216_ = crate::leanh::lean_ctor_get(v___x_6215_, 0);
                    crate::leanh::lean_inc(v_a_6216_);
                    crate::leanh::lean_dec_ref_known(v___x_6215_, 1);
                    v___x_6217_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1;
                    v___x_6218_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_6219_ = l_Lean_Expr_isAppOfArity(v_a_6216_, v___x_6217_, v___x_6218_);
                    if v___x_6219_ == 0 {
                        v___x_6220_ = lean_st_ref_get(v_a_6209_);
                        v___x_6221_ = lean_array_get_size(v___x_6220_);
                        crate::leanh::lean_dec(v___x_6220_);
                        v___x_6222_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_6223_ = lean_nat_add(v___x_6221_, v___x_6222_);
                        v___x_6224_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__3;
                        v___x_6225_ = lean_name_append_index_after(v___x_6224_, v___x_6223_);
                        v___x_6226_ = l_Lean_Name_append(v_tag_6207_, v___x_6225_);
                        v___x_6227_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                            v_a_6216_,
                            v___x_6226_,
                            v_a_6210_,
                            v_a_6211_,
                            v_a_6212_,
                            v_a_6213_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6227_) == 0 {
                            v_a_6228_ = crate::leanh::lean_ctor_get(v___x_6227_, 0);
                            v_isSharedCheck_6239_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6227_)) as u8;
                            if v_isSharedCheck_6239_ == 0 {
                                v___x_6230_ = v___x_6227_;
                                v_isShared_6231_ = v_isSharedCheck_6239_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6228_);
                                crate::leanh::lean_dec(v___x_6227_);
                                v___x_6230_ = crate::leanh::lean_box(0);
                                v_isShared_6231_ = v_isSharedCheck_6239_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_6227_;
                        }
                    } else {
                        v___x_6240_ = l_Lean_Expr_appFn_x21(v_a_6216_);
                        v___x_6241_ = l_Lean_Expr_appArg_x21(v___x_6240_);
                        crate::leanh::lean_dec_ref(v___x_6240_);
                        crate::leanh::lean_inc_ref(v___x_6241_);
                        crate::leanh::lean_inc(v_tag_6207_);
                        v___x_6242_ =
                            l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(
                                v_tag_6207_,
                                v___x_6241_,
                                v_a_6209_,
                                v_a_6210_,
                                v_a_6211_,
                                v_a_6212_,
                                v_a_6213_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_6242_) == 0 {
                            v_a_6243_ = crate::leanh::lean_ctor_get(v___x_6242_, 0);
                            crate::leanh::lean_inc(v_a_6243_);
                            crate::leanh::lean_dec_ref_known(v___x_6242_, 1);
                            v___x_6244_ = l_Lean_Expr_appArg_x21(v_a_6216_);
                            crate::leanh::lean_dec(v_a_6216_);
                            crate::leanh::lean_inc_ref(v___x_6244_);
                            v___x_6245_ =
                                l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(
                                    v_tag_6207_,
                                    v___x_6244_,
                                    v_a_6209_,
                                    v_a_6210_,
                                    v_a_6211_,
                                    v_a_6212_,
                                    v_a_6213_,
                                );
                            if crate::leanh::lean_obj_tag(v___x_6245_) == 0 {
                                v_a_6246_ = crate::leanh::lean_ctor_get(v___x_6245_, 0);
                                v_isSharedCheck_6255_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6245_)) as u8;
                                if v_isSharedCheck_6255_ == 0 {
                                    v___x_6248_ = v___x_6245_;
                                    v_isShared_6249_ = v_isSharedCheck_6255_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6246_);
                                    crate::leanh::lean_dec(v___x_6245_);
                                    v___x_6248_ = crate::leanh::lean_box(0);
                                    v_isShared_6249_ = v_isSharedCheck_6255_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_6244_);
                                crate::leanh::lean_dec(v_a_6243_);
                                crate::leanh::lean_dec_ref(v___x_6241_);
                                return v___x_6245_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_6241_);
                            crate::leanh::lean_dec(v_a_6216_);
                            crate::leanh::lean_dec(v_tag_6207_);
                            return v___x_6242_;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_tag_6207_);
                    return v___x_6215_;
                }
            }
            1 => {
                v___x_6232_ = lean_st_ref_take(v_a_6209_);
                v___x_6233_ = l_Lean_Expr_mvarId_x21(v_a_6228_);
                v___x_6234_ = lean_array_push(v___x_6232_, v___x_6233_);
                v___x_6235_ = lean_st_ref_set(v_a_6209_, v___x_6234_);
                if v_isShared_6231_ == 0 {
                    v___x_6237_ = v___x_6230_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6238_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6238_, 0, v_a_6228_);
                    v___x_6237_ = v_reuseFailAlloc_6238_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6237_;
            }
            3 => {
                v___x_6250_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6_once), _init_l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__6);
                v___x_6251_ =
                    l_Lean_mkApp4(v___x_6250_, v___x_6241_, v___x_6244_, v_a_6243_, v_a_6246_);
                if v_isShared_6249_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6248_, 0, v___x_6251_);
                    v___x_6253_ = v___x_6248_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6254_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6254_, 0, v___x_6251_);
                    v___x_6253_ = v_reuseFailAlloc_6254_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6253_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___boxed(
    mut v_tag_6256_: *mut crate::leanh::LeanObject,
    mut v_type_6257_: *mut crate::leanh::LeanObject,
    mut v_a_6258_: *mut crate::leanh::LeanObject,
    mut v_a_6259_: *mut crate::leanh::LeanObject,
    mut v_a_6260_: *mut crate::leanh::LeanObject,
    mut v_a_6261_: *mut crate::leanh::LeanObject,
    mut v_a_6262_: *mut crate::leanh::LeanObject,
    mut v_a_6263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6264_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(
        v_tag_6256_,
        v_type_6257_,
        v_a_6258_,
        v_a_6259_,
        v_a_6260_,
        v_a_6261_,
        v_a_6262_,
    );
    crate::leanh::lean_dec(v_a_6262_);
    crate::leanh::lean_dec_ref(v_a_6261_);
    crate::leanh::lean_dec(v_a_6260_);
    crate::leanh::lean_dec_ref(v_a_6259_);
    crate::leanh::lean_dec(v_a_6258_);
    return v_res_6264_;
}
pub unsafe fn l_Lean_MVarId_splitAndCore___lam__0(
    mut v_mvarId_6265_: *mut crate::leanh::LeanObject,
    mut v___x_6266_: *mut crate::leanh::LeanObject,
    mut v___y_6267_: *mut crate::leanh::LeanObject,
    mut v___y_6268_: *mut crate::leanh::LeanObject,
    mut v___y_6269_: *mut crate::leanh::LeanObject,
    mut v___y_6270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6277_: u8 = 0;
    let mut v___x_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: u8 = 0;
    let mut v___x_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6296_: u8 = 0;
    let mut v___x_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6301_: u8 = 0;
    let mut v_unused_6302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6306_: u8 = 0;
    let mut v___x_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6310_: u8 = 0;
    let mut v_a_6311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6314_: u8 = 0;
    let mut v___x_6316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6318_: u8 = 0;
    let mut v_isSharedCheck_6319_: u8 = 0;
    let mut v_a_6320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6323_: u8 = 0;
    let mut v___x_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6327_: u8 = 0;
    let mut v_a_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6331_: u8 = 0;
    let mut v___x_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6335_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_6265_);
                v___x_6272_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_6265_,
                    v___x_6266_,
                    v___y_6267_,
                    v___y_6268_,
                    v___y_6269_,
                    v___y_6270_,
                );
                if crate::leanh::lean_obj_tag(v___x_6272_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6272_, 1);
                    crate::leanh::lean_inc(v_mvarId_6265_);
                    v___x_6273_ = l_Lean_MVarId_getType_x27(
                        v_mvarId_6265_,
                        v___y_6267_,
                        v___y_6268_,
                        v___y_6269_,
                        v___y_6270_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6273_) == 0 {
                        v_a_6274_ = crate::leanh::lean_ctor_get(v___x_6273_, 0);
                        v_isSharedCheck_6319_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6273_)) as u8;
                        if v_isSharedCheck_6319_ == 0 {
                            v___x_6276_ = v___x_6273_;
                            v_isShared_6277_ = v_isSharedCheck_6319_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6274_);
                            crate::leanh::lean_dec(v___x_6273_);
                            v___x_6276_ = crate::leanh::lean_box(0);
                            v_isShared_6277_ = v_isSharedCheck_6319_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarId_6265_);
                        v_a_6320_ = crate::leanh::lean_ctor_get(v___x_6273_, 0);
                        v_isSharedCheck_6327_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6273_)) as u8;
                        if v_isSharedCheck_6327_ == 0 {
                            v___x_6322_ = v___x_6273_;
                            v_isShared_6323_ = v_isSharedCheck_6327_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6320_);
                            crate::leanh::lean_dec(v___x_6273_);
                            v___x_6322_ = crate::leanh::lean_box(0);
                            v_isShared_6323_ = v_isSharedCheck_6327_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_6265_);
                    v_a_6328_ = crate::leanh::lean_ctor_get(v___x_6272_, 0);
                    v_isSharedCheck_6335_ = (!crate::leanh::lean_is_exclusive(v___x_6272_)) as u8;
                    if v_isSharedCheck_6335_ == 0 {
                        v___x_6330_ = v___x_6272_;
                        v_isShared_6331_ = v_isSharedCheck_6335_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6328_);
                        crate::leanh::lean_dec(v___x_6272_);
                        v___x_6330_ = crate::leanh::lean_box(0);
                        v_isShared_6331_ = v_isSharedCheck_6335_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6278_ =
                    l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go___closed__1;
                v___x_6279_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_6280_ = l_Lean_Expr_isAppOfArity(v_a_6274_, v___x_6278_, v___x_6279_);
                if v___x_6280_ == 0 {
                    crate::leanh::lean_dec(v_a_6274_);
                    v___x_6281_ = crate::leanh::lean_box(0);
                    v___x_6282_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6282_, 0, v_mvarId_6265_);
                    crate::leanh::lean_ctor_set(v___x_6282_, 1, v___x_6281_);
                    if v_isShared_6277_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6276_, 0, v___x_6282_);
                        v___x_6284_ = v___x_6276_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6285_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6285_, 0, v___x_6282_);
                        v___x_6284_ = v_reuseFailAlloc_6285_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6276_);
                    crate::leanh::lean_inc(v_mvarId_6265_);
                    v___x_6286_ = l_Lean_MVarId_getTag(
                        v_mvarId_6265_,
                        v___y_6267_,
                        v___y_6268_,
                        v___y_6269_,
                        v___y_6270_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6286_) == 0 {
                        v_a_6287_ = crate::leanh::lean_ctor_get(v___x_6286_, 0);
                        crate::leanh::lean_inc(v_a_6287_);
                        crate::leanh::lean_dec_ref_known(v___x_6286_, 1);
                        v___x_6288_ = l___private_Lean_Meta_Tactic_Apply_0__Lean_Meta_partitionDependentMVars___closed__0;
                        v___x_6289_ = lean_st_mk_ref(v___x_6288_);
                        v___x_6290_ =
                            l___private_Lean_Meta_Tactic_Apply_0__Lean_MVarId_splitAndCore_go(
                                v_a_6287_,
                                v_a_6274_,
                                v___x_6289_,
                                v___y_6267_,
                                v___y_6268_,
                                v___y_6269_,
                                v___y_6270_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_6290_) == 0 {
                            v_a_6291_ = crate::leanh::lean_ctor_get(v___x_6290_, 0);
                            crate::leanh::lean_inc(v_a_6291_);
                            crate::leanh::lean_dec_ref_known(v___x_6290_, 1);
                            v___x_6292_ = lean_st_ref_get(v___x_6289_);
                            crate::leanh::lean_dec(v___x_6289_);
                            v___x_6293_ =
                                l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(
                                    v_mvarId_6265_,
                                    v_a_6291_,
                                    v___y_6268_,
                                );
                            v_isSharedCheck_6301_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6293_)) as u8;
                            if v_isSharedCheck_6301_ == 0 {
                                v_unused_6302_ = crate::leanh::lean_ctor_get(v___x_6293_, 0);
                                crate::leanh::lean_dec(v_unused_6302_);
                                v___x_6295_ = v___x_6293_;
                                v_isShared_6296_ = v_isSharedCheck_6301_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_6293_);
                                v___x_6295_ = crate::leanh::lean_box(0);
                                v_isShared_6296_ = v_isSharedCheck_6301_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_6289_);
                            crate::leanh::lean_dec(v_mvarId_6265_);
                            v_a_6303_ = crate::leanh::lean_ctor_get(v___x_6290_, 0);
                            v_isSharedCheck_6310_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6290_)) as u8;
                            if v_isSharedCheck_6310_ == 0 {
                                v___x_6305_ = v___x_6290_;
                                v_isShared_6306_ = v_isSharedCheck_6310_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6303_);
                                crate::leanh::lean_dec(v___x_6290_);
                                v___x_6305_ = crate::leanh::lean_box(0);
                                v_isShared_6306_ = v_isSharedCheck_6310_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6274_);
                        crate::leanh::lean_dec(v_mvarId_6265_);
                        v_a_6311_ = crate::leanh::lean_ctor_get(v___x_6286_, 0);
                        v_isSharedCheck_6318_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6286_)) as u8;
                        if v_isSharedCheck_6318_ == 0 {
                            v___x_6313_ = v___x_6286_;
                            v_isShared_6314_ = v_isSharedCheck_6318_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6311_);
                            crate::leanh::lean_dec(v___x_6286_);
                            v___x_6313_ = crate::leanh::lean_box(0);
                            v_isShared_6314_ = v_isSharedCheck_6318_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_6284_;
            }
            3 => {
                v___x_6297_ = lean_array_to_list(v___x_6292_);
                if v_isShared_6296_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6295_, 0, v___x_6297_);
                    v___x_6299_ = v___x_6295_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6300_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6300_, 0, v___x_6297_);
                    v___x_6299_ = v_reuseFailAlloc_6300_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6299_;
            }
            5 => {
                if v_isShared_6306_ == 0 {
                    v___x_6308_ = v___x_6305_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6309_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6309_, 0, v_a_6303_);
                    v___x_6308_ = v_reuseFailAlloc_6309_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6308_;
            }
            7 => {
                if v_isShared_6314_ == 0 {
                    v___x_6316_ = v___x_6313_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6317_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6317_, 0, v_a_6311_);
                    v___x_6316_ = v_reuseFailAlloc_6317_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6316_;
            }
            9 => {
                if v_isShared_6323_ == 0 {
                    v___x_6325_ = v___x_6322_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6326_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6326_, 0, v_a_6320_);
                    v___x_6325_ = v_reuseFailAlloc_6326_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6325_;
            }
            11 => {
                if v_isShared_6331_ == 0 {
                    v___x_6333_ = v___x_6330_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6334_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6334_, 0, v_a_6328_);
                    v___x_6333_ = v_reuseFailAlloc_6334_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6333_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_splitAndCore___lam__0___boxed(
    mut v_mvarId_6336_: *mut crate::leanh::LeanObject,
    mut v___x_6337_: *mut crate::leanh::LeanObject,
    mut v___y_6338_: *mut crate::leanh::LeanObject,
    mut v___y_6339_: *mut crate::leanh::LeanObject,
    mut v___y_6340_: *mut crate::leanh::LeanObject,
    mut v___y_6341_: *mut crate::leanh::LeanObject,
    mut v___y_6342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6343_ = l_Lean_MVarId_splitAndCore___lam__0(
        v_mvarId_6336_,
        v___x_6337_,
        v___y_6338_,
        v___y_6339_,
        v___y_6340_,
        v___y_6341_,
    );
    crate::leanh::lean_dec(v___y_6341_);
    crate::leanh::lean_dec_ref(v___y_6340_);
    crate::leanh::lean_dec(v___y_6339_);
    crate::leanh::lean_dec_ref(v___y_6338_);
    return v_res_6343_;
}
pub unsafe fn l_Lean_MVarId_splitAndCore(
    mut v_mvarId_6347_: *mut crate::leanh::LeanObject,
    mut v_a_6348_: *mut crate::leanh::LeanObject,
    mut v_a_6349_: *mut crate::leanh::LeanObject,
    mut v_a_6350_: *mut crate::leanh::LeanObject,
    mut v_a_6351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6353_ = l_Lean_MVarId_splitAndCore___closed__1;
    crate::leanh::lean_inc(v_mvarId_6347_);
    v___f_6354_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_splitAndCore___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_6354_, 0, v_mvarId_6347_);
    crate::leanh::lean_closure_set(v___f_6354_, 1, v___x_6353_);
    v___x_6355_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(
        v_mvarId_6347_,
        v___f_6354_,
        v_a_6348_,
        v_a_6349_,
        v_a_6350_,
        v_a_6351_,
    );
    return v___x_6355_;
}
pub unsafe fn l_Lean_MVarId_splitAndCore___boxed(
    mut v_mvarId_6356_: *mut crate::leanh::LeanObject,
    mut v_a_6357_: *mut crate::leanh::LeanObject,
    mut v_a_6358_: *mut crate::leanh::LeanObject,
    mut v_a_6359_: *mut crate::leanh::LeanObject,
    mut v_a_6360_: *mut crate::leanh::LeanObject,
    mut v_a_6361_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6362_ =
        l_Lean_MVarId_splitAndCore(v_mvarId_6356_, v_a_6357_, v_a_6358_, v_a_6359_, v_a_6360_);
    crate::leanh::lean_dec(v_a_6360_);
    crate::leanh::lean_dec_ref(v_a_6359_);
    crate::leanh::lean_dec(v_a_6358_);
    crate::leanh::lean_dec_ref(v_a_6357_);
    return v_res_6362_;
}
pub unsafe fn l_Lean_MVarId_splitAnd(
    mut v_mvarId_6363_: *mut crate::leanh::LeanObject,
    mut v_a_6364_: *mut crate::leanh::LeanObject,
    mut v_a_6365_: *mut crate::leanh::LeanObject,
    mut v_a_6366_: *mut crate::leanh::LeanObject,
    mut v_a_6367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6369_ =
        l_Lean_MVarId_splitAndCore(v_mvarId_6363_, v_a_6364_, v_a_6365_, v_a_6366_, v_a_6367_);
    return v___x_6369_;
}
pub unsafe fn l_Lean_MVarId_splitAnd___boxed(
    mut v_mvarId_6370_: *mut crate::leanh::LeanObject,
    mut v_a_6371_: *mut crate::leanh::LeanObject,
    mut v_a_6372_: *mut crate::leanh::LeanObject,
    mut v_a_6373_: *mut crate::leanh::LeanObject,
    mut v_a_6374_: *mut crate::leanh::LeanObject,
    mut v_a_6375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6376_ =
        l_Lean_MVarId_splitAnd(v_mvarId_6370_, v_a_6371_, v_a_6372_, v_a_6373_, v_a_6374_);
    crate::leanh::lean_dec(v_a_6374_);
    crate::leanh::lean_dec_ref(v_a_6373_);
    crate::leanh::lean_dec(v_a_6372_);
    crate::leanh::lean_dec_ref(v_a_6371_);
    return v_res_6376_;
}
pub unsafe fn _init_l_Lean_MVarId_exfalso___lam__0___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6380_ = crate::leanh::lean_box(0);
    v___x_6381_ = l_Lean_MVarId_exfalso___lam__0___closed__1;
    v___x_6382_ = l_Lean_mkConst(v___x_6381_, v___x_6380_);
    return v___x_6382_;
}
pub unsafe fn l_Lean_MVarId_exfalso___lam__0(
    mut v_mvarId_6387_: *mut crate::leanh::LeanObject,
    mut v___x_6388_: *mut crate::leanh::LeanObject,
    mut v___y_6389_: *mut crate::leanh::LeanObject,
    mut v___y_6390_: *mut crate::leanh::LeanObject,
    mut v___y_6391_: *mut crate::leanh::LeanObject,
    mut v___y_6392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6414_: u8 = 0;
    let mut v___x_6415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6419_: u8 = 0;
    let mut v_unused_6420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6424_: u8 = 0;
    let mut v___x_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6428_: u8 = 0;
    let mut v_a_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6432_: u8 = 0;
    let mut v___x_6434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6436_: u8 = 0;
    let mut v_a_6437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6440_: u8 = 0;
    let mut v___x_6442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6444_: u8 = 0;
    let mut v_a_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6448_: u8 = 0;
    let mut v___x_6450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6452_: u8 = 0;
    let mut v_a_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6456_: u8 = 0;
    let mut v___x_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6460_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_6387_);
                v___x_6394_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_6387_,
                    v___x_6388_,
                    v___y_6389_,
                    v___y_6390_,
                    v___y_6391_,
                    v___y_6392_,
                );
                if crate::leanh::lean_obj_tag(v___x_6394_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6394_, 1);
                    crate::leanh::lean_inc(v_mvarId_6387_);
                    v___x_6395_ = l_Lean_MVarId_getType(
                        v_mvarId_6387_,
                        v___y_6389_,
                        v___y_6390_,
                        v___y_6391_,
                        v___y_6392_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6395_) == 0 {
                        v_a_6396_ = crate::leanh::lean_ctor_get(v___x_6395_, 0);
                        crate::leanh::lean_inc(v_a_6396_);
                        crate::leanh::lean_dec_ref_known(v___x_6395_, 1);
                        v___x_6397_ =
                            l_Lean_instantiateMVars___at___00Lean_MVarId_apply_spec__0___redArg(
                                v_a_6396_,
                                v___y_6390_,
                            );
                        v_a_6398_ = crate::leanh::lean_ctor_get(v___x_6397_, 0);
                        crate::leanh::lean_inc_n(v_a_6398_, 2);
                        crate::leanh::lean_dec_ref(v___x_6397_);
                        v___x_6399_ = l_Lean_Meta_getLevel(
                            v_a_6398_,
                            v___y_6389_,
                            v___y_6390_,
                            v___y_6391_,
                            v___y_6392_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6399_) == 0 {
                            v_a_6400_ = crate::leanh::lean_ctor_get(v___x_6399_, 0);
                            crate::leanh::lean_inc(v_a_6400_);
                            crate::leanh::lean_dec_ref_known(v___x_6399_, 1);
                            crate::leanh::lean_inc(v_mvarId_6387_);
                            v___x_6401_ = l_Lean_MVarId_getTag(
                                v_mvarId_6387_,
                                v___y_6389_,
                                v___y_6390_,
                                v___y_6391_,
                                v___y_6392_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6401_) == 0 {
                                v_a_6402_ = crate::leanh::lean_ctor_get(v___x_6401_, 0);
                                crate::leanh::lean_inc(v_a_6402_);
                                crate::leanh::lean_dec_ref_known(v___x_6401_, 1);
                                v___x_6403_ = crate::leanh::lean_box(0);
                                v___x_6404_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_MVarId_exfalso___lam__0___closed__2
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_MVarId_exfalso___lam__0___closed__2_once
                                    ),
                                    _init_l_Lean_MVarId_exfalso___lam__0___closed__2,
                                );
                                v___x_6405_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                                    v___x_6404_,
                                    v_a_6402_,
                                    v___y_6389_,
                                    v___y_6390_,
                                    v___y_6391_,
                                    v___y_6392_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_6405_) == 0 {
                                    v_a_6406_ = crate::leanh::lean_ctor_get(v___x_6405_, 0);
                                    crate::leanh::lean_inc_n(v_a_6406_, 2);
                                    crate::leanh::lean_dec_ref_known(v___x_6405_, 1);
                                    v___x_6407_ = l_Lean_MVarId_exfalso___lam__0___closed__4;
                                    v___x_6408_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_6408_, 0, v_a_6400_);
                                    crate::leanh::lean_ctor_set(v___x_6408_, 1, v___x_6403_);
                                    v___x_6409_ = l_Lean_mkConst(v___x_6407_, v___x_6408_);
                                    v___x_6410_ = l_Lean_mkAppB(v___x_6409_, v_a_6398_, v_a_6406_);
                                    v___x_6411_ = l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(v_mvarId_6387_, v___x_6410_, v___y_6390_);
                                    v_isSharedCheck_6419_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6411_)) as u8;
                                    if v_isSharedCheck_6419_ == 0 {
                                        v_unused_6420_ =
                                            crate::leanh::lean_ctor_get(v___x_6411_, 0);
                                        crate::leanh::lean_dec(v_unused_6420_);
                                        v___x_6413_ = v___x_6411_;
                                        v_isShared_6414_ = v_isSharedCheck_6419_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_6411_);
                                        v___x_6413_ = crate::leanh::lean_box(0);
                                        v_isShared_6414_ = v_isSharedCheck_6419_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_6400_);
                                    crate::leanh::lean_dec(v_a_6398_);
                                    crate::leanh::lean_dec(v_mvarId_6387_);
                                    v_a_6421_ = crate::leanh::lean_ctor_get(v___x_6405_, 0);
                                    v_isSharedCheck_6428_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6405_)) as u8;
                                    if v_isSharedCheck_6428_ == 0 {
                                        v___x_6423_ = v___x_6405_;
                                        v_isShared_6424_ = v_isSharedCheck_6428_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6421_);
                                        crate::leanh::lean_dec(v___x_6405_);
                                        v___x_6423_ = crate::leanh::lean_box(0);
                                        v_isShared_6424_ = v_isSharedCheck_6428_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6400_);
                                crate::leanh::lean_dec(v_a_6398_);
                                crate::leanh::lean_dec(v_mvarId_6387_);
                                v_a_6429_ = crate::leanh::lean_ctor_get(v___x_6401_, 0);
                                v_isSharedCheck_6436_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6401_)) as u8;
                                if v_isSharedCheck_6436_ == 0 {
                                    v___x_6431_ = v___x_6401_;
                                    v_isShared_6432_ = v_isSharedCheck_6436_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6429_);
                                    crate::leanh::lean_dec(v___x_6401_);
                                    v___x_6431_ = crate::leanh::lean_box(0);
                                    v_isShared_6432_ = v_isSharedCheck_6436_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_6398_);
                            crate::leanh::lean_dec(v_mvarId_6387_);
                            v_a_6437_ = crate::leanh::lean_ctor_get(v___x_6399_, 0);
                            v_isSharedCheck_6444_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6399_)) as u8;
                            if v_isSharedCheck_6444_ == 0 {
                                v___x_6439_ = v___x_6399_;
                                v_isShared_6440_ = v_isSharedCheck_6444_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6437_);
                                crate::leanh::lean_dec(v___x_6399_);
                                v___x_6439_ = crate::leanh::lean_box(0);
                                v_isShared_6440_ = v_isSharedCheck_6444_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarId_6387_);
                        v_a_6445_ = crate::leanh::lean_ctor_get(v___x_6395_, 0);
                        v_isSharedCheck_6452_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6395_)) as u8;
                        if v_isSharedCheck_6452_ == 0 {
                            v___x_6447_ = v___x_6395_;
                            v_isShared_6448_ = v_isSharedCheck_6452_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6445_);
                            crate::leanh::lean_dec(v___x_6395_);
                            v___x_6447_ = crate::leanh::lean_box(0);
                            v_isShared_6448_ = v_isSharedCheck_6452_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_6387_);
                    v_a_6453_ = crate::leanh::lean_ctor_get(v___x_6394_, 0);
                    v_isSharedCheck_6460_ = (!crate::leanh::lean_is_exclusive(v___x_6394_)) as u8;
                    if v_isSharedCheck_6460_ == 0 {
                        v___x_6455_ = v___x_6394_;
                        v_isShared_6456_ = v_isSharedCheck_6460_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6453_);
                        crate::leanh::lean_dec(v___x_6394_);
                        v___x_6455_ = crate::leanh::lean_box(0);
                        v_isShared_6456_ = v_isSharedCheck_6460_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6415_ = l_Lean_Expr_mvarId_x21(v_a_6406_);
                crate::leanh::lean_dec(v_a_6406_);
                if v_isShared_6414_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6413_, 0, v___x_6415_);
                    v___x_6417_ = v___x_6413_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6418_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6418_, 0, v___x_6415_);
                    v___x_6417_ = v_reuseFailAlloc_6418_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6417_;
            }
            3 => {
                if v_isShared_6424_ == 0 {
                    v___x_6426_ = v___x_6423_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6427_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6427_, 0, v_a_6421_);
                    v___x_6426_ = v_reuseFailAlloc_6427_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6426_;
            }
            5 => {
                if v_isShared_6432_ == 0 {
                    v___x_6434_ = v___x_6431_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6435_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6435_, 0, v_a_6429_);
                    v___x_6434_ = v_reuseFailAlloc_6435_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6434_;
            }
            7 => {
                if v_isShared_6440_ == 0 {
                    v___x_6442_ = v___x_6439_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6443_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6443_, 0, v_a_6437_);
                    v___x_6442_ = v_reuseFailAlloc_6443_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6442_;
            }
            9 => {
                if v_isShared_6448_ == 0 {
                    v___x_6450_ = v___x_6447_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6451_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6451_, 0, v_a_6445_);
                    v___x_6450_ = v_reuseFailAlloc_6451_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6450_;
            }
            11 => {
                if v_isShared_6456_ == 0 {
                    v___x_6458_ = v___x_6455_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6459_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6459_, 0, v_a_6453_);
                    v___x_6458_ = v_reuseFailAlloc_6459_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6458_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_exfalso___lam__0___boxed(
    mut v_mvarId_6461_: *mut crate::leanh::LeanObject,
    mut v___x_6462_: *mut crate::leanh::LeanObject,
    mut v___y_6463_: *mut crate::leanh::LeanObject,
    mut v___y_6464_: *mut crate::leanh::LeanObject,
    mut v___y_6465_: *mut crate::leanh::LeanObject,
    mut v___y_6466_: *mut crate::leanh::LeanObject,
    mut v___y_6467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6468_ = l_Lean_MVarId_exfalso___lam__0(
        v_mvarId_6461_,
        v___x_6462_,
        v___y_6463_,
        v___y_6464_,
        v___y_6465_,
        v___y_6466_,
    );
    crate::leanh::lean_dec(v___y_6466_);
    crate::leanh::lean_dec_ref(v___y_6465_);
    crate::leanh::lean_dec(v___y_6464_);
    crate::leanh::lean_dec_ref(v___y_6463_);
    return v_res_6468_;
}
pub unsafe fn l_Lean_MVarId_exfalso(
    mut v_mvarId_6472_: *mut crate::leanh::LeanObject,
    mut v_a_6473_: *mut crate::leanh::LeanObject,
    mut v_a_6474_: *mut crate::leanh::LeanObject,
    mut v_a_6475_: *mut crate::leanh::LeanObject,
    mut v_a_6476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6478_ = l_Lean_MVarId_exfalso___closed__1;
    crate::leanh::lean_inc(v_mvarId_6472_);
    v___f_6479_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_exfalso___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_6479_, 0, v_mvarId_6472_);
    crate::leanh::lean_closure_set(v___f_6479_, 1, v___x_6478_);
    v___x_6480_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(
        v_mvarId_6472_,
        v___f_6479_,
        v_a_6473_,
        v_a_6474_,
        v_a_6475_,
        v_a_6476_,
    );
    return v___x_6480_;
}
pub unsafe fn l_Lean_MVarId_exfalso___boxed(
    mut v_mvarId_6481_: *mut crate::leanh::LeanObject,
    mut v_a_6482_: *mut crate::leanh::LeanObject,
    mut v_a_6483_: *mut crate::leanh::LeanObject,
    mut v_a_6484_: *mut crate::leanh::LeanObject,
    mut v_a_6485_: *mut crate::leanh::LeanObject,
    mut v_a_6486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6487_ = l_Lean_MVarId_exfalso(v_mvarId_6481_, v_a_6482_, v_a_6483_, v_a_6484_, v_a_6485_);
    crate::leanh::lean_dec(v_a_6485_);
    crate::leanh::lean_dec_ref(v_a_6484_);
    crate::leanh::lean_dec(v_a_6483_);
    crate::leanh::lean_dec_ref(v_a_6482_);
    return v_res_6487_;
}
pub unsafe fn _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6491_ = l_Lean_MVarId_nthConstructor___lam__0___closed__1;
    v___x_6492_ = l_Lean_MessageData_ofFormat(v___x_6491_);
    return v___x_6492_;
}
pub unsafe fn _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6493_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_nthConstructor___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_MVarId_nthConstructor___lam__0___closed__2_once),
        _init_l_Lean_MVarId_nthConstructor___lam__0___closed__2,
    );
    v___x_6494_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6494_, 0, v___x_6493_);
    return v___x_6494_;
}
pub unsafe fn l_Lean_MVarId_nthConstructor___lam__0(
    mut v_goal_6499_: *mut crate::leanh::LeanObject,
    mut v_name_6500_: *mut crate::leanh::LeanObject,
    mut v_idx_6501_: *mut crate::leanh::LeanObject,
    mut v_expected_x3f_6502_: *mut crate::leanh::LeanObject,
    mut v___y_6503_: *mut crate::leanh::LeanObject,
    mut v___y_6504_: *mut crate::leanh::LeanObject,
    mut v___y_6505_: *mut crate::leanh::LeanObject,
    mut v___y_6506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: u8 = 0;
    let mut v___x_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6528_: u8 = 0;
    let mut v_val_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6532_: u8 = 0;
    let mut v___y_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6540_: u8 = 0;
    let mut v___x_6541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: u8 = 0;
    let mut v___x_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6567_: u8 = 0;
    let mut v_ctors_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: u8 = 0;
    let mut v___x_6571_: u8 = 0;
    let mut v___x_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6587_: u8 = 0;
    let mut v___x_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6591_: u8 = 0;
    let mut v_reuseFailAlloc_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6593_: u8 = 0;
    let mut v_isSharedCheck_6594_: u8 = 0;
    let mut v_isSharedCheck_6595_: u8 = 0;
    let mut v_a_6596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6599_: u8 = 0;
    let mut v___x_6601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6603_: u8 = 0;
    let mut v_a_6604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6607_: u8 = 0;
    let mut v___x_6609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6611_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_name_6500_);
                crate::leanh::lean_inc(v_goal_6499_);
                v___x_6515_ = l_Lean_MVarId_checkNotAssigned(
                    v_goal_6499_,
                    v_name_6500_,
                    v___y_6503_,
                    v___y_6504_,
                    v___y_6505_,
                    v___y_6506_,
                );
                if crate::leanh::lean_obj_tag(v___x_6515_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6515_, 1);
                    crate::leanh::lean_inc(v_goal_6499_);
                    v___x_6516_ = l_Lean_MVarId_getType_x27(
                        v_goal_6499_,
                        v___y_6503_,
                        v___y_6504_,
                        v___y_6505_,
                        v___y_6506_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6516_) == 0 {
                        v_a_6517_ = crate::leanh::lean_ctor_get(v___x_6516_, 0);
                        crate::leanh::lean_inc(v_a_6517_);
                        crate::leanh::lean_dec_ref_known(v___x_6516_, 1);
                        v___x_6518_ = l_Lean_Expr_getAppFn(v_a_6517_);
                        crate::leanh::lean_dec(v_a_6517_);
                        if crate::leanh::lean_obj_tag(v___x_6518_) == 4 {
                            v_declName_6519_ = crate::leanh::lean_ctor_get(v___x_6518_, 0);
                            crate::leanh::lean_inc(v_declName_6519_);
                            v_us_6520_ = crate::leanh::lean_ctor_get(v___x_6518_, 1);
                            crate::leanh::lean_inc(v_us_6520_);
                            crate::leanh::lean_dec_ref_known(v___x_6518_, 2);
                            v___x_6521_ = lean_st_ref_get(v___y_6506_);
                            v_env_6522_ = crate::leanh::lean_ctor_get(v___x_6521_, 0);
                            crate::leanh::lean_inc_ref(v_env_6522_);
                            crate::leanh::lean_dec(v___x_6521_);
                            v___x_6523_ = 0;
                            v___x_6524_ = l_Lean_Environment_find_x3f(
                                v_env_6522_,
                                v_declName_6519_,
                                v___x_6523_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6524_) == 0 {
                                crate::leanh::lean_dec(v_us_6520_);
                                crate::leanh::lean_dec(v_expected_x3f_6502_);
                                crate::leanh::lean_dec(v_idx_6501_);
                                v___y_6509_ = v___y_6503_;
                                v___y_6510_ = v___y_6504_;
                                v___y_6511_ = v___y_6505_;
                                v___y_6512_ = v___y_6506_;
                                state = 1;
                                continue;
                            } else {
                                v_val_6525_ = crate::leanh::lean_ctor_get(v___x_6524_, 0);
                                v_isSharedCheck_6595_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6524_)) as u8;
                                if v_isSharedCheck_6595_ == 0 {
                                    v___x_6527_ = v___x_6524_;
                                    v_isShared_6528_ = v_isSharedCheck_6595_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_6525_);
                                    crate::leanh::lean_dec(v___x_6524_);
                                    v___x_6527_ = crate::leanh::lean_box(0);
                                    v_isShared_6528_ = v_isSharedCheck_6595_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_6518_);
                            crate::leanh::lean_dec(v_expected_x3f_6502_);
                            crate::leanh::lean_dec(v_idx_6501_);
                            v___y_6509_ = v___y_6503_;
                            v___y_6510_ = v___y_6504_;
                            v___y_6511_ = v___y_6505_;
                            v___y_6512_ = v___y_6506_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_expected_x3f_6502_);
                        crate::leanh::lean_dec(v_idx_6501_);
                        crate::leanh::lean_dec(v_name_6500_);
                        crate::leanh::lean_dec(v_goal_6499_);
                        v_a_6596_ = crate::leanh::lean_ctor_get(v___x_6516_, 0);
                        v_isSharedCheck_6603_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6516_)) as u8;
                        if v_isSharedCheck_6603_ == 0 {
                            v___x_6598_ = v___x_6516_;
                            v_isShared_6599_ = v_isSharedCheck_6603_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6596_);
                            crate::leanh::lean_dec(v___x_6516_);
                            v___x_6598_ = crate::leanh::lean_box(0);
                            v_isShared_6599_ = v_isSharedCheck_6603_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_expected_x3f_6502_);
                    crate::leanh::lean_dec(v_idx_6501_);
                    crate::leanh::lean_dec(v_name_6500_);
                    crate::leanh::lean_dec(v_goal_6499_);
                    v_a_6604_ = crate::leanh::lean_ctor_get(v___x_6515_, 0);
                    v_isSharedCheck_6611_ = (!crate::leanh::lean_is_exclusive(v___x_6515_)) as u8;
                    if v_isSharedCheck_6611_ == 0 {
                        v___x_6606_ = v___x_6515_;
                        v_isShared_6607_ = v_isSharedCheck_6611_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6604_);
                        crate::leanh::lean_dec(v___x_6515_);
                        v___x_6606_ = crate::leanh::lean_box(0);
                        v_isShared_6607_ = v_isSharedCheck_6611_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6513_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_nthConstructor___lam__0___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_nthConstructor___lam__0___closed__3_once),
                    _init_l_Lean_MVarId_nthConstructor___lam__0___closed__3,
                );
                v___x_6514_ = l_Lean_Meta_throwTacticEx___redArg(
                    v_name_6500_,
                    v_goal_6499_,
                    v___x_6513_,
                    v___y_6509_,
                    v___y_6510_,
                    v___y_6511_,
                    v___y_6512_,
                );
                return v___x_6514_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_val_6525_) == 5 {
                    v_val_6529_ = crate::leanh::lean_ctor_get(v_val_6525_, 0);
                    v_isSharedCheck_6594_ = (!crate::leanh::lean_is_exclusive(v_val_6525_)) as u8;
                    if v_isSharedCheck_6594_ == 0 {
                        v___x_6531_ = v_val_6525_;
                        v_isShared_6532_ = v_isSharedCheck_6594_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6529_);
                        crate::leanh::lean_dec(v_val_6525_);
                        v___x_6531_ = crate::leanh::lean_box(0);
                        v_isShared_6532_ = v_isSharedCheck_6594_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6527_);
                    crate::leanh::lean_dec(v_val_6525_);
                    crate::leanh::lean_dec(v_us_6520_);
                    crate::leanh::lean_dec(v_expected_x3f_6502_);
                    crate::leanh::lean_dec(v_idx_6501_);
                    v___y_6509_ = v___y_6503_;
                    v___y_6510_ = v___y_6504_;
                    v___y_6511_ = v___y_6505_;
                    v___y_6512_ = v___y_6506_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_expected_x3f_6502_) == 1 {
                    v_val_6564_ = crate::leanh::lean_ctor_get(v_expected_x3f_6502_, 0);
                    v_isSharedCheck_6593_ =
                        (!crate::leanh::lean_is_exclusive(v_expected_x3f_6502_)) as u8;
                    if v_isSharedCheck_6593_ == 0 {
                        v___x_6566_ = v_expected_x3f_6502_;
                        v_isShared_6567_ = v_isSharedCheck_6593_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6564_);
                        crate::leanh::lean_dec(v_expected_x3f_6502_);
                        v___x_6566_ = crate::leanh::lean_box(0);
                        v_isShared_6567_ = v_isSharedCheck_6593_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_expected_x3f_6502_);
                    v___y_6534_ = v___y_6503_;
                    v___y_6535_ = v___y_6504_;
                    v___y_6536_ = v___y_6505_;
                    v___y_6537_ = v___y_6506_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_ctors_6538_ = crate::leanh::lean_ctor_get(v_val_6529_, 4);
                crate::leanh::lean_inc(v_ctors_6538_);
                crate::leanh::lean_dec_ref(v_val_6529_);
                v___x_6539_ = l_List_lengthTR___redArg(v_ctors_6538_);
                v___x_6540_ = lean_nat_dec_lt(v_idx_6501_, v___x_6539_);
                if v___x_6540_ == 0 {
                    crate::leanh::lean_dec(v_ctors_6538_);
                    crate::leanh::lean_dec(v_us_6520_);
                    v___x_6541_ = l_Lean_MVarId_nthConstructor___lam__0___closed__4;
                    v___x_6542_ = l_Nat_reprFast(v_idx_6501_);
                    v___x_6543_ = lean_string_append(v___x_6541_, v___x_6542_);
                    crate::leanh::lean_dec_ref(v___x_6542_);
                    v___x_6544_ = l_Lean_MVarId_nthConstructor___lam__0___closed__5;
                    v___x_6545_ = lean_string_append(v___x_6543_, v___x_6544_);
                    v___x_6546_ = l_Nat_reprFast(v___x_6539_);
                    v___x_6547_ = lean_string_append(v___x_6545_, v___x_6546_);
                    crate::leanh::lean_dec_ref(v___x_6546_);
                    v___x_6548_ = l_Lean_MVarId_nthConstructor___lam__0___closed__6;
                    v___x_6549_ = lean_string_append(v___x_6547_, v___x_6548_);
                    if v_isShared_6532_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6531_, 3);
                        crate::leanh::lean_ctor_set(v___x_6531_, 0, v___x_6549_);
                        v___x_6551_ = v___x_6531_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6557_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6557_, 0, v___x_6549_);
                        v___x_6551_ = v_reuseFailAlloc_6557_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6539_);
                    crate::leanh::lean_del_object(v___x_6531_);
                    crate::leanh::lean_del_object(v___x_6527_);
                    crate::leanh::lean_dec(v_name_6500_);
                    v___x_6558_ = l_List_get___redArg(v_ctors_6538_, v_idx_6501_);
                    crate::leanh::lean_dec(v_ctors_6538_);
                    v___x_6559_ = l_Lean_mkConst(v___x_6558_, v_us_6520_);
                    v___x_6560_ = 0;
                    v___x_6561_ = crate::leanh::lean_alloc_ctor(0, 0, (4) as u32);
                    crate::leanh::lean_ctor_set_uint8(v___x_6561_, 0 as u32, v___x_6560_);
                    crate::leanh::lean_ctor_set_uint8(v___x_6561_, 1 as u32, v___x_6540_);
                    crate::leanh::lean_ctor_set_uint8(v___x_6561_, 2 as u32, v___x_6523_);
                    crate::leanh::lean_ctor_set_uint8(v___x_6561_, 3 as u32, v___x_6540_);
                    v___x_6562_ = crate::leanh::lean_box(0);
                    v___x_6563_ = l_Lean_MVarId_apply(
                        v_goal_6499_,
                        v___x_6559_,
                        v___x_6561_,
                        v___x_6562_,
                        v___y_6534_,
                        v___y_6535_,
                        v___y_6536_,
                        v___y_6537_,
                    );
                    return v___x_6563_;
                }
            }
            5 => {
                v___x_6552_ = l_Lean_MessageData_ofFormat(v___x_6551_);
                if v_isShared_6528_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6527_, 0, v___x_6552_);
                    v___x_6554_ = v___x_6527_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6556_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6556_, 0, v___x_6552_);
                    v___x_6554_ = v_reuseFailAlloc_6556_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_6555_ = l_Lean_Meta_throwTacticEx___redArg(
                    v_name_6500_,
                    v_goal_6499_,
                    v___x_6554_,
                    v___y_6534_,
                    v___y_6535_,
                    v___y_6536_,
                    v___y_6537_,
                );
                return v___x_6555_;
            }
            7 => {
                v_ctors_6568_ = crate::leanh::lean_ctor_get(v_val_6529_, 4);
                v___x_6569_ = l_List_lengthTR___redArg(v_ctors_6568_);
                v___x_6570_ = lean_nat_dec_eq(v___x_6569_, v_val_6564_);
                crate::leanh::lean_dec(v___x_6569_);
                if v___x_6570_ == 0 {
                    v___x_6571_ = 1;
                    crate::leanh::lean_inc(v_name_6500_);
                    v___x_6572_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_name_6500_,
                        v___x_6571_,
                    );
                    v___x_6573_ = l_Lean_MVarId_nthConstructor___lam__0___closed__7;
                    v___x_6574_ = lean_string_append(v___x_6572_, v___x_6573_);
                    v___x_6575_ = l_Nat_reprFast(v_val_6564_);
                    v___x_6576_ = lean_string_append(v___x_6574_, v___x_6575_);
                    crate::leanh::lean_dec_ref(v___x_6575_);
                    v___x_6577_ = l_Lean_MVarId_nthConstructor___lam__0___closed__6;
                    v___x_6578_ = lean_string_append(v___x_6576_, v___x_6577_);
                    v___x_6579_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6579_, 0, v___x_6578_);
                    v___x_6580_ = l_Lean_MessageData_ofFormat(v___x_6579_);
                    if v_isShared_6567_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6566_, 0, v___x_6580_);
                        v___x_6582_ = v___x_6566_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6592_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6592_, 0, v___x_6580_);
                        v___x_6582_ = v_reuseFailAlloc_6592_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6566_);
                    crate::leanh::lean_dec(v_val_6564_);
                    v___y_6534_ = v___y_6503_;
                    v___y_6535_ = v___y_6504_;
                    v___y_6536_ = v___y_6505_;
                    v___y_6537_ = v___y_6506_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_inc(v_goal_6499_);
                crate::leanh::lean_inc(v_name_6500_);
                v___x_6583_ = l_Lean_Meta_throwTacticEx___redArg(
                    v_name_6500_,
                    v_goal_6499_,
                    v___x_6582_,
                    v___y_6503_,
                    v___y_6504_,
                    v___y_6505_,
                    v___y_6506_,
                );
                if crate::leanh::lean_obj_tag(v___x_6583_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6583_, 1);
                    v___y_6534_ = v___y_6503_;
                    v___y_6535_ = v___y_6504_;
                    v___y_6536_ = v___y_6505_;
                    v___y_6537_ = v___y_6506_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_6531_);
                    crate::leanh::lean_dec_ref(v_val_6529_);
                    crate::leanh::lean_del_object(v___x_6527_);
                    crate::leanh::lean_dec(v_us_6520_);
                    crate::leanh::lean_dec(v_idx_6501_);
                    crate::leanh::lean_dec(v_name_6500_);
                    crate::leanh::lean_dec(v_goal_6499_);
                    v_a_6584_ = crate::leanh::lean_ctor_get(v___x_6583_, 0);
                    v_isSharedCheck_6591_ = (!crate::leanh::lean_is_exclusive(v___x_6583_)) as u8;
                    if v_isSharedCheck_6591_ == 0 {
                        v___x_6586_ = v___x_6583_;
                        v_isShared_6587_ = v_isSharedCheck_6591_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6584_);
                        crate::leanh::lean_dec(v___x_6583_);
                        v___x_6586_ = crate::leanh::lean_box(0);
                        v_isShared_6587_ = v_isSharedCheck_6591_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_6587_ == 0 {
                    v___x_6589_ = v___x_6586_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6590_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6590_, 0, v_a_6584_);
                    v___x_6589_ = v_reuseFailAlloc_6590_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6589_;
            }
            11 => {
                if v_isShared_6599_ == 0 {
                    v___x_6601_ = v___x_6598_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6602_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6602_, 0, v_a_6596_);
                    v___x_6601_ = v_reuseFailAlloc_6602_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6601_;
            }
            13 => {
                if v_isShared_6607_ == 0 {
                    v___x_6609_ = v___x_6606_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6610_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6610_, 0, v_a_6604_);
                    v___x_6609_ = v_reuseFailAlloc_6610_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6609_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_nthConstructor___lam__0___boxed(
    mut v_goal_6612_: *mut crate::leanh::LeanObject,
    mut v_name_6613_: *mut crate::leanh::LeanObject,
    mut v_idx_6614_: *mut crate::leanh::LeanObject,
    mut v_expected_x3f_6615_: *mut crate::leanh::LeanObject,
    mut v___y_6616_: *mut crate::leanh::LeanObject,
    mut v___y_6617_: *mut crate::leanh::LeanObject,
    mut v___y_6618_: *mut crate::leanh::LeanObject,
    mut v___y_6619_: *mut crate::leanh::LeanObject,
    mut v___y_6620_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6621_ = l_Lean_MVarId_nthConstructor___lam__0(
        v_goal_6612_,
        v_name_6613_,
        v_idx_6614_,
        v_expected_x3f_6615_,
        v___y_6616_,
        v___y_6617_,
        v___y_6618_,
        v___y_6619_,
    );
    crate::leanh::lean_dec(v___y_6619_);
    crate::leanh::lean_dec_ref(v___y_6618_);
    crate::leanh::lean_dec(v___y_6617_);
    crate::leanh::lean_dec_ref(v___y_6616_);
    return v_res_6621_;
}
pub unsafe fn l_Lean_MVarId_nthConstructor(
    mut v_name_6622_: *mut crate::leanh::LeanObject,
    mut v_idx_6623_: *mut crate::leanh::LeanObject,
    mut v_expected_x3f_6624_: *mut crate::leanh::LeanObject,
    mut v_goal_6625_: *mut crate::leanh::LeanObject,
    mut v_a_6626_: *mut crate::leanh::LeanObject,
    mut v_a_6627_: *mut crate::leanh::LeanObject,
    mut v_a_6628_: *mut crate::leanh::LeanObject,
    mut v_a_6629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_goal_6625_);
    v___f_6631_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_nthConstructor___lam__0___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    crate::leanh::lean_closure_set(v___f_6631_, 0, v_goal_6625_);
    crate::leanh::lean_closure_set(v___f_6631_, 1, v_name_6622_);
    crate::leanh::lean_closure_set(v___f_6631_, 2, v_idx_6623_);
    crate::leanh::lean_closure_set(v___f_6631_, 3, v_expected_x3f_6624_);
    v___x_6632_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(
        v_goal_6625_,
        v___f_6631_,
        v_a_6626_,
        v_a_6627_,
        v_a_6628_,
        v_a_6629_,
    );
    return v___x_6632_;
}
pub unsafe fn l_Lean_MVarId_nthConstructor___boxed(
    mut v_name_6633_: *mut crate::leanh::LeanObject,
    mut v_idx_6634_: *mut crate::leanh::LeanObject,
    mut v_expected_x3f_6635_: *mut crate::leanh::LeanObject,
    mut v_goal_6636_: *mut crate::leanh::LeanObject,
    mut v_a_6637_: *mut crate::leanh::LeanObject,
    mut v_a_6638_: *mut crate::leanh::LeanObject,
    mut v_a_6639_: *mut crate::leanh::LeanObject,
    mut v_a_6640_: *mut crate::leanh::LeanObject,
    mut v_a_6641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6642_ = l_Lean_MVarId_nthConstructor(
        v_name_6633_,
        v_idx_6634_,
        v_expected_x3f_6635_,
        v_goal_6636_,
        v_a_6637_,
        v_a_6638_,
        v_a_6639_,
        v_a_6640_,
    );
    crate::leanh::lean_dec(v_a_6640_);
    crate::leanh::lean_dec_ref(v_a_6639_);
    crate::leanh::lean_dec(v_a_6638_);
    crate::leanh::lean_dec_ref(v_a_6637_);
    return v_res_6642_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(
    mut v_x_6643_: *mut crate::leanh::LeanObject,
    mut v___y_6644_: *mut crate::leanh::LeanObject,
    mut v___y_6645_: *mut crate::leanh::LeanObject,
    mut v___y_6646_: *mut crate::leanh::LeanObject,
    mut v___y_6647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6655_: u8 = 0;
    let mut v___x_6656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6660_: u8 = 0;
    let mut v_a_6661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6664_: u8 = 0;
    let mut v___y_6666_: u8 = 0;
    let mut v___x_6667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6670_: u8 = 0;
    let mut v___x_6671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6675_: u8 = 0;
    let mut v_unused_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6680_: u8 = 0;
    let mut v___x_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6684_: u8 = 0;
    let mut v___x_6686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: u8 = 0;
    let mut v___x_6689_: u8 = 0;
    let mut v_isSharedCheck_6690_: u8 = 0;
    let mut v_a_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6694_: u8 = 0;
    let mut v___x_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6698_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6649_ = l_Lean_Meta_saveState___redArg(v___y_6645_, v___y_6647_);
                if crate::leanh::lean_obj_tag(v___x_6649_) == 0 {
                    v_a_6650_ = crate::leanh::lean_ctor_get(v___x_6649_, 0);
                    crate::leanh::lean_inc(v_a_6650_);
                    crate::leanh::lean_dec_ref_known(v___x_6649_, 1);
                    crate::leanh::lean_inc(v___y_6647_);
                    crate::leanh::lean_inc_ref(v___y_6646_);
                    crate::leanh::lean_inc(v___y_6645_);
                    crate::leanh::lean_inc_ref(v___y_6644_);
                    v___x_6651_ = crate::leanh::lean_apply_5(
                        v_x_6643_,
                        v___y_6644_,
                        v___y_6645_,
                        v___y_6646_,
                        v___y_6647_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_6651_) == 0 {
                        crate::leanh::lean_dec(v_a_6650_);
                        v_a_6652_ = crate::leanh::lean_ctor_get(v___x_6651_, 0);
                        v_isSharedCheck_6660_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6651_)) as u8;
                        if v_isSharedCheck_6660_ == 0 {
                            v___x_6654_ = v___x_6651_;
                            v_isShared_6655_ = v_isSharedCheck_6660_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6652_);
                            crate::leanh::lean_dec(v___x_6651_);
                            v___x_6654_ = crate::leanh::lean_box(0);
                            v_isShared_6655_ = v_isSharedCheck_6660_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6661_ = crate::leanh::lean_ctor_get(v___x_6651_, 0);
                        v_isSharedCheck_6690_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6651_)) as u8;
                        if v_isSharedCheck_6690_ == 0 {
                            v___x_6663_ = v___x_6651_;
                            v_isShared_6664_ = v_isSharedCheck_6690_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6661_);
                            crate::leanh::lean_dec(v___x_6651_);
                            v___x_6663_ = crate::leanh::lean_box(0);
                            v_isShared_6664_ = v_isSharedCheck_6690_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_x_6643_);
                    v_a_6691_ = crate::leanh::lean_ctor_get(v___x_6649_, 0);
                    v_isSharedCheck_6698_ = (!crate::leanh::lean_is_exclusive(v___x_6649_)) as u8;
                    if v_isSharedCheck_6698_ == 0 {
                        v___x_6693_ = v___x_6649_;
                        v_isShared_6694_ = v_isSharedCheck_6698_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6691_);
                        crate::leanh::lean_dec(v___x_6649_);
                        v___x_6693_ = crate::leanh::lean_box(0);
                        v_isShared_6694_ = v_isSharedCheck_6698_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6656_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6656_, 0, v_a_6652_);
                if v_isShared_6655_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6654_, 0, v___x_6656_);
                    v___x_6658_ = v___x_6654_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6659_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6659_, 0, v___x_6656_);
                    v___x_6658_ = v_reuseFailAlloc_6659_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6658_;
            }
            3 => {
                v___x_6688_ = l_Lean_Exception_isInterrupt(v_a_6661_);
                if v___x_6688_ == 0 {
                    crate::leanh::lean_inc(v_a_6661_);
                    v___x_6689_ = l_Lean_Exception_isRuntime(v_a_6661_);
                    v___y_6666_ = v___x_6689_;
                    state = 4;
                    continue;
                } else {
                    v___y_6666_ = v___x_6688_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_6666_ == 0 {
                    crate::leanh::lean_del_object(v___x_6663_);
                    crate::leanh::lean_dec(v_a_6661_);
                    v___x_6667_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_6650_,
                        v___y_6645_,
                        v___y_6647_,
                    );
                    crate::leanh::lean_dec(v_a_6650_);
                    if crate::leanh::lean_obj_tag(v___x_6667_) == 0 {
                        v_isSharedCheck_6675_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6667_)) as u8;
                        if v_isSharedCheck_6675_ == 0 {
                            v_unused_6676_ = crate::leanh::lean_ctor_get(v___x_6667_, 0);
                            crate::leanh::lean_dec(v_unused_6676_);
                            v___x_6669_ = v___x_6667_;
                            v_isShared_6670_ = v_isSharedCheck_6675_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_6667_);
                            v___x_6669_ = crate::leanh::lean_box(0);
                            v_isShared_6670_ = v_isSharedCheck_6675_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_a_6677_ = crate::leanh::lean_ctor_get(v___x_6667_, 0);
                        v_isSharedCheck_6684_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6667_)) as u8;
                        if v_isSharedCheck_6684_ == 0 {
                            v___x_6679_ = v___x_6667_;
                            v_isShared_6680_ = v_isSharedCheck_6684_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6677_);
                            crate::leanh::lean_dec(v___x_6667_);
                            v___x_6679_ = crate::leanh::lean_box(0);
                            v_isShared_6680_ = v_isSharedCheck_6684_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_6650_);
                    if v_isShared_6664_ == 0 {
                        v___x_6686_ = v___x_6663_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_6687_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6687_, 0, v_a_6661_);
                        v___x_6686_ = v_reuseFailAlloc_6687_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                v___x_6671_ = crate::leanh::lean_box(0);
                if v_isShared_6670_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6669_, 0, v___x_6671_);
                    v___x_6673_ = v___x_6669_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6674_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6674_, 0, v___x_6671_);
                    v___x_6673_ = v_reuseFailAlloc_6674_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6673_;
            }
            7 => {
                if v_isShared_6680_ == 0 {
                    v___x_6682_ = v___x_6679_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6683_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6683_, 0, v_a_6677_);
                    v___x_6682_ = v_reuseFailAlloc_6683_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6682_;
            }
            9 => {
                return v___x_6686_;
            }
            10 => {
                if v_isShared_6694_ == 0 {
                    v___x_6696_ = v___x_6693_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6697_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6697_, 0, v_a_6691_);
                    v___x_6696_ = v_reuseFailAlloc_6697_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6696_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg___boxed(
    mut v_x_6699_: *mut crate::leanh::LeanObject,
    mut v___y_6700_: *mut crate::leanh::LeanObject,
    mut v___y_6701_: *mut crate::leanh::LeanObject,
    mut v___y_6702_: *mut crate::leanh::LeanObject,
    mut v___y_6703_: *mut crate::leanh::LeanObject,
    mut v___y_6704_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6705_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(
        v_x_6699_,
        v___y_6700_,
        v___y_6701_,
        v___y_6702_,
        v___y_6703_,
    );
    crate::leanh::lean_dec(v___y_6703_);
    crate::leanh::lean_dec_ref(v___y_6702_);
    crate::leanh::lean_dec(v___y_6701_);
    crate::leanh::lean_dec_ref(v___y_6700_);
    return v_res_6705_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(
    mut v_00_u03b1_6706_: *mut crate::leanh::LeanObject,
    mut v_x_6707_: *mut crate::leanh::LeanObject,
    mut v___y_6708_: *mut crate::leanh::LeanObject,
    mut v___y_6709_: *mut crate::leanh::LeanObject,
    mut v___y_6710_: *mut crate::leanh::LeanObject,
    mut v___y_6711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6713_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(
        v_x_6707_,
        v___y_6708_,
        v___y_6709_,
        v___y_6710_,
        v___y_6711_,
    );
    return v___x_6713_;
}
pub unsafe fn l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___boxed(
    mut v_00_u03b1_6714_: *mut crate::leanh::LeanObject,
    mut v_x_6715_: *mut crate::leanh::LeanObject,
    mut v___y_6716_: *mut crate::leanh::LeanObject,
    mut v___y_6717_: *mut crate::leanh::LeanObject,
    mut v___y_6718_: *mut crate::leanh::LeanObject,
    mut v___y_6719_: *mut crate::leanh::LeanObject,
    mut v___y_6720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6721_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0(
        v_00_u03b1_6714_,
        v_x_6715_,
        v___y_6716_,
        v___y_6717_,
        v___y_6718_,
        v___y_6719_,
    );
    crate::leanh::lean_dec(v___y_6719_);
    crate::leanh::lean_dec_ref(v___y_6718_);
    crate::leanh::lean_dec(v___y_6717_);
    crate::leanh::lean_dec_ref(v___y_6716_);
    return v_res_6721_;
}
pub unsafe fn _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_6723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6723_ = l_Lean_MVarId_iffOfEq___lam__0___closed__0;
    v___x_6724_ = l_Lean_stringToMessageData(v___x_6723_);
    return v___x_6724_;
}
pub unsafe fn l_Lean_MVarId_iffOfEq___lam__0(
    mut v_mvarId_6725_: *mut crate::leanh::LeanObject,
    mut v___x_6726_: *mut crate::leanh::LeanObject,
    mut v___x_6727_: *mut crate::leanh::LeanObject,
    mut v___x_6728_: *mut crate::leanh::LeanObject,
    mut v___y_6729_: *mut crate::leanh::LeanObject,
    mut v___y_6730_: *mut crate::leanh::LeanObject,
    mut v___y_6731_: *mut crate::leanh::LeanObject,
    mut v___y_6732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6738_: u8 = 0;
    let mut v___y_6740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6751_: u8 = 0;
    let mut v_a_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6755_: u8 = 0;
    let mut v___x_6757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6759_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6734_ = l_Lean_MVarId_apply(
                    v_mvarId_6725_,
                    v___x_6726_,
                    v___x_6727_,
                    v___x_6728_,
                    v___y_6729_,
                    v___y_6730_,
                    v___y_6731_,
                    v___y_6732_,
                );
                if crate::leanh::lean_obj_tag(v___x_6734_) == 0 {
                    v_a_6735_ = crate::leanh::lean_ctor_get(v___x_6734_, 0);
                    v_isSharedCheck_6751_ = (!crate::leanh::lean_is_exclusive(v___x_6734_)) as u8;
                    if v_isSharedCheck_6751_ == 0 {
                        v___x_6737_ = v___x_6734_;
                        v_isShared_6738_ = v_isSharedCheck_6751_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6735_);
                        crate::leanh::lean_dec(v___x_6734_);
                        v___x_6737_ = crate::leanh::lean_box(0);
                        v_isShared_6738_ = v_isSharedCheck_6751_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6752_ = crate::leanh::lean_ctor_get(v___x_6734_, 0);
                    v_isSharedCheck_6759_ = (!crate::leanh::lean_is_exclusive(v___x_6734_)) as u8;
                    if v_isSharedCheck_6759_ == 0 {
                        v___x_6754_ = v___x_6734_;
                        v_isShared_6755_ = v_isSharedCheck_6759_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6752_);
                        crate::leanh::lean_dec(v___x_6734_);
                        v___x_6754_ = crate::leanh::lean_box(0);
                        v_isShared_6755_ = v_isSharedCheck_6759_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_6735_) == 1 {
                    v_tail_6746_ = crate::leanh::lean_ctor_get(v_a_6735_, 1);
                    if crate::leanh::lean_obj_tag(v_tail_6746_) == 0 {
                        v_head_6747_ = crate::leanh::lean_ctor_get(v_a_6735_, 0);
                        crate::leanh::lean_inc(v_head_6747_);
                        crate::leanh::lean_dec_ref_known(v_a_6735_, 2);
                        if v_isShared_6738_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6737_, 0, v_head_6747_);
                            v___x_6749_ = v___x_6737_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_6750_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6750_, 0, v_head_6747_);
                            v___x_6749_ = v_reuseFailAlloc_6750_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_6735_, 2);
                        crate::leanh::lean_del_object(v___x_6737_);
                        v___y_6740_ = v___y_6729_;
                        v___y_6741_ = v___y_6730_;
                        v___y_6742_ = v___y_6731_;
                        v___y_6743_ = v___y_6732_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6737_);
                    crate::leanh::lean_dec(v_a_6735_);
                    v___y_6740_ = v___y_6729_;
                    v___y_6741_ = v___y_6730_;
                    v___y_6742_ = v___y_6731_;
                    v___y_6743_ = v___y_6732_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6744_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_iffOfEq___lam__0___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_iffOfEq___lam__0___closed__1_once),
                    _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1,
                );
                v___x_6745_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(
                    v___x_6744_,
                    v___y_6740_,
                    v___y_6741_,
                    v___y_6742_,
                    v___y_6743_,
                );
                return v___x_6745_;
            }
            3 => {
                return v___x_6749_;
            }
            4 => {
                if v_isShared_6755_ == 0 {
                    v___x_6757_ = v___x_6754_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6758_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6758_, 0, v_a_6752_);
                    v___x_6757_ = v_reuseFailAlloc_6758_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6757_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_iffOfEq___lam__0___boxed(
    mut v_mvarId_6760_: *mut crate::leanh::LeanObject,
    mut v___x_6761_: *mut crate::leanh::LeanObject,
    mut v___x_6762_: *mut crate::leanh::LeanObject,
    mut v___x_6763_: *mut crate::leanh::LeanObject,
    mut v___y_6764_: *mut crate::leanh::LeanObject,
    mut v___y_6765_: *mut crate::leanh::LeanObject,
    mut v___y_6766_: *mut crate::leanh::LeanObject,
    mut v___y_6767_: *mut crate::leanh::LeanObject,
    mut v___y_6768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6769_ = l_Lean_MVarId_iffOfEq___lam__0(
        v_mvarId_6760_,
        v___x_6761_,
        v___x_6762_,
        v___x_6763_,
        v___y_6764_,
        v___y_6765_,
        v___y_6766_,
        v___y_6767_,
    );
    crate::leanh::lean_dec(v___y_6767_);
    crate::leanh::lean_dec_ref(v___y_6766_);
    crate::leanh::lean_dec(v___y_6765_);
    crate::leanh::lean_dec_ref(v___y_6764_);
    return v_res_6769_;
}
pub unsafe fn _init_l_Lean_MVarId_iffOfEq___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_6773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6773_ = crate::leanh::lean_box(0);
    v___x_6774_ = l_Lean_MVarId_iffOfEq___closed__1;
    v___x_6775_ = l_Lean_mkConst(v___x_6774_, v___x_6773_);
    return v___x_6775_;
}
pub unsafe fn l_Lean_MVarId_iffOfEq(
    mut v_mvarId_6780_: *mut crate::leanh::LeanObject,
    mut v_a_6781_: *mut crate::leanh::LeanObject,
    mut v_a_6782_: *mut crate::leanh::LeanObject,
    mut v_a_6783_: *mut crate::leanh::LeanObject,
    mut v_a_6784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6794_: u8 = 0;
    let mut v___x_6796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6802_: u8 = 0;
    let mut v_a_6803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6806_: u8 = 0;
    let mut v___x_6808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6810_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6786_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_iffOfEq___closed__2),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_iffOfEq___closed__2_once),
                    _init_l_Lean_MVarId_iffOfEq___closed__2,
                );
                v___x_6787_ = l_Lean_MVarId_iffOfEq___closed__3;
                v___x_6788_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_mvarId_6780_);
                v___f_6789_ = crate::leanh::lean_alloc_closure(
                    l_Lean_MVarId_iffOfEq___lam__0___boxed as *mut core::ffi::c_void,
                    9,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_6789_, 0, v_mvarId_6780_);
                crate::leanh::lean_closure_set(v___f_6789_, 1, v___x_6786_);
                crate::leanh::lean_closure_set(v___f_6789_, 2, v___x_6787_);
                crate::leanh::lean_closure_set(v___f_6789_, 3, v___x_6788_);
                v___x_6790_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(
                    v___f_6789_,
                    v_a_6781_,
                    v_a_6782_,
                    v_a_6783_,
                    v_a_6784_,
                );
                if crate::leanh::lean_obj_tag(v___x_6790_) == 0 {
                    v_a_6791_ = crate::leanh::lean_ctor_get(v___x_6790_, 0);
                    v_isSharedCheck_6802_ = (!crate::leanh::lean_is_exclusive(v___x_6790_)) as u8;
                    if v_isSharedCheck_6802_ == 0 {
                        v___x_6793_ = v___x_6790_;
                        v_isShared_6794_ = v_isSharedCheck_6802_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6791_);
                        crate::leanh::lean_dec(v___x_6790_);
                        v___x_6793_ = crate::leanh::lean_box(0);
                        v_isShared_6794_ = v_isSharedCheck_6802_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_6780_);
                    v_a_6803_ = crate::leanh::lean_ctor_get(v___x_6790_, 0);
                    v_isSharedCheck_6810_ = (!crate::leanh::lean_is_exclusive(v___x_6790_)) as u8;
                    if v_isSharedCheck_6810_ == 0 {
                        v___x_6805_ = v___x_6790_;
                        v_isShared_6806_ = v_isSharedCheck_6810_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6803_);
                        crate::leanh::lean_dec(v___x_6790_);
                        v___x_6805_ = crate::leanh::lean_box(0);
                        v_isShared_6806_ = v_isSharedCheck_6810_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_6791_) == 0 {
                    if v_isShared_6794_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6793_, 0, v_mvarId_6780_);
                        v___x_6796_ = v___x_6793_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6797_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6797_, 0, v_mvarId_6780_);
                        v___x_6796_ = v_reuseFailAlloc_6797_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_6780_);
                    v_val_6798_ = crate::leanh::lean_ctor_get(v_a_6791_, 0);
                    crate::leanh::lean_inc(v_val_6798_);
                    crate::leanh::lean_dec_ref_known(v_a_6791_, 1);
                    if v_isShared_6794_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6793_, 0, v_val_6798_);
                        v___x_6800_ = v___x_6793_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6801_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6801_, 0, v_val_6798_);
                        v___x_6800_ = v_reuseFailAlloc_6801_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6796_;
            }
            3 => {
                return v___x_6800_;
            }
            4 => {
                if v_isShared_6806_ == 0 {
                    v___x_6808_ = v___x_6805_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6809_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6809_, 0, v_a_6803_);
                    v___x_6808_ = v_reuseFailAlloc_6809_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6808_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_iffOfEq___boxed(
    mut v_mvarId_6811_: *mut crate::leanh::LeanObject,
    mut v_a_6812_: *mut crate::leanh::LeanObject,
    mut v_a_6813_: *mut crate::leanh::LeanObject,
    mut v_a_6814_: *mut crate::leanh::LeanObject,
    mut v_a_6815_: *mut crate::leanh::LeanObject,
    mut v_a_6816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6817_ = l_Lean_MVarId_iffOfEq(v_mvarId_6811_, v_a_6812_, v_a_6813_, v_a_6814_, v_a_6815_);
    crate::leanh::lean_dec(v_a_6815_);
    crate::leanh::lean_dec_ref(v_a_6814_);
    crate::leanh::lean_dec(v_a_6813_);
    crate::leanh::lean_dec_ref(v_a_6812_);
    return v_res_6817_;
}
pub unsafe fn _init_l_Lean_MVarId_propext___lam__0___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_6824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6824_ = crate::leanh::lean_box(0);
    v___x_6825_ = l_Lean_MVarId_propext___lam__0___closed__3;
    v___x_6826_ = l_Lean_mkConst(v___x_6825_, v___x_6824_);
    return v___x_6826_;
}
pub unsafe fn l_Lean_MVarId_propext___lam__0(
    mut v___x_6827_: u8,
    mut v_mvarId_6828_: *mut crate::leanh::LeanObject,
    mut v___y_6829_: *mut crate::leanh::LeanObject,
    mut v___y_6830_: *mut crate::leanh::LeanObject,
    mut v___y_6831_: *mut crate::leanh::LeanObject,
    mut v___y_6832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_6842_: u8 = 0;
    let mut v_ctxApprox_6843_: u8 = 0;
    let mut v_quasiPatternApprox_6844_: u8 = 0;
    let mut v_constApprox_6845_: u8 = 0;
    let mut v_isDefEqStuckEx_6846_: u8 = 0;
    let mut v_unificationHints_6847_: u8 = 0;
    let mut v_proofIrrelevance_6848_: u8 = 0;
    let mut v_assignSyntheticOpaque_6849_: u8 = 0;
    let mut v_offsetCnstrs_6850_: u8 = 0;
    let mut v_etaStruct_6851_: u8 = 0;
    let mut v_univApprox_6852_: u8 = 0;
    let mut v_iota_6853_: u8 = 0;
    let mut v_beta_6854_: u8 = 0;
    let mut v_proj_6855_: u8 = 0;
    let mut v_zeta_6856_: u8 = 0;
    let mut v_zetaDelta_6857_: u8 = 0;
    let mut v_zetaUnused_6858_: u8 = 0;
    let mut v_zetaHave_6859_: u8 = 0;
    let mut v___x_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6862_: u8 = 0;
    let mut v_trackZetaDelta_6863_: u8 = 0;
    let mut v_zetaDeltaSet_6864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_6865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_6866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_6867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_6868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_6870_: u8 = 0;
    let mut v_inTypeClassResolution_6871_: u8 = 0;
    let mut v_cacheInferType_6872_: u8 = 0;
    let mut v_config_6874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6875_: u64 = 0;
    let mut v___x_6876_: u64 = 0;
    let mut v___x_6877_: u64 = 0;
    let mut v___x_6878_: u64 = 0;
    let mut v___x_6879_: u64 = 0;
    let mut v_key_6880_: u64 = 0;
    let mut v___x_6881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6887_: u8 = 0;
    let mut v___x_6889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6890_: u8 = 0;
    let mut v___x_6891_: u8 = 0;
    let mut v___x_6892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6898_: u8 = 0;
    let mut v_tail_6899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6904_: u8 = 0;
    let mut v_a_6905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6908_: u8 = 0;
    let mut v___x_6910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6912_: u8 = 0;
    let mut v___x_6913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6919_: u8 = 0;
    let mut v___x_6920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6925_: u8 = 0;
    let mut v___x_6927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6929_: u8 = 0;
    let mut v_a_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6933_: u8 = 0;
    let mut v___x_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6937_: u8 = 0;
    let mut v_a_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6941_: u8 = 0;
    let mut v___x_6943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6945_: u8 = 0;
    let mut v_reuseFailAlloc_6946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6947_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6841_ = l_Lean_Meta_Context_config(v___y_6829_);
                v_foApprox_6842_ = crate::leanh::lean_ctor_get_uint8(v___x_6841_, 0 as u32);
                v_ctxApprox_6843_ = crate::leanh::lean_ctor_get_uint8(v___x_6841_, 1 as u32);
                v_quasiPatternApprox_6844_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_6841_, 2 as u32);
                v_constApprox_6845_ = crate::leanh::lean_ctor_get_uint8(v___x_6841_, 3 as u32);
                v_isDefEqStuckEx_6846_ = crate::leanh::lean_ctor_get_uint8(v___x_6841_, 4 as u32);
                v_unificationHints_6847_ = crate::leanh::lean_ctor_get_uint8(v___x_6841_, 5 as u32);
                v_proofIrrelevance_6848_ = crate::leanh::lean_ctor_get_uint8(v___x_6841_, 6 as u32);
                v_assignSyntheticOpaque_6849_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_6841_, 7 as u32);
                v_offsetCnstrs_6850_ = crate::leanh::lean_ctor_get_uint8(v___x_6841_, 8 as u32);
                v_etaStruct_6851_ = crate::leanh::lean_ctor_get_uint8(v___x_6841_, 10 as u32);
                v_univApprox_6852_ = crate::leanh::lean_ctor_get_uint8(v___x_6841_, 11 as u32);
                v_iota_6853_ = crate::leanh::lean_ctor_get_uint8(v___x_6841_, 12 as u32);
                v_beta_6854_ = crate::leanh::lean_ctor_get_uint8(v___x_6841_, 13 as u32);
                v_proj_6855_ = crate::leanh::lean_ctor_get_uint8(v___x_6841_, 14 as u32);
                v_zeta_6856_ = crate::leanh::lean_ctor_get_uint8(v___x_6841_, 15 as u32);
                v_zetaDelta_6857_ = crate::leanh::lean_ctor_get_uint8(v___x_6841_, 16 as u32);
                v_zetaUnused_6858_ = crate::leanh::lean_ctor_get_uint8(v___x_6841_, 17 as u32);
                v_zetaHave_6859_ = crate::leanh::lean_ctor_get_uint8(v___x_6841_, 18 as u32);
                v_isSharedCheck_6947_ = (!crate::leanh::lean_is_exclusive(v___x_6841_)) as u8;
                if v_isSharedCheck_6947_ == 0 {
                    v___x_6861_ = v___x_6841_;
                    v_isShared_6862_ = v_isSharedCheck_6947_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_6841_);
                    v___x_6861_ = crate::leanh::lean_box(0);
                    v_isShared_6862_ = v_isSharedCheck_6947_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_6839_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_iffOfEq___lam__0___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_iffOfEq___lam__0___closed__1_once),
                    _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1,
                );
                v___x_6840_ = l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(
                    v___x_6839_,
                    v___y_6835_,
                    v___y_6836_,
                    v___y_6837_,
                    v___y_6838_,
                );
                return v___x_6840_;
            }
            2 => {
                v_trackZetaDelta_6863_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_6829_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_6864_ = crate::leanh::lean_ctor_get(v___y_6829_, 1);
                v_lctx_6865_ = crate::leanh::lean_ctor_get(v___y_6829_, 2);
                v_localInstances_6866_ = crate::leanh::lean_ctor_get(v___y_6829_, 3);
                v_defEqCtx_x3f_6867_ = crate::leanh::lean_ctor_get(v___y_6829_, 4);
                v_synthPendingDepth_6868_ = crate::leanh::lean_ctor_get(v___y_6829_, 5);
                v_canUnfold_x3f_6869_ = crate::leanh::lean_ctor_get(v___y_6829_, 6);
                v_univApprox_6870_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_6829_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_6871_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_6829_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_6872_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_6829_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                if v_isShared_6862_ == 0 {
                    v_config_6874_ = v___x_6861_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6946_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6946_,
                        0 as u32,
                        v_foApprox_6842_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6946_,
                        1 as u32,
                        v_ctxApprox_6843_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6946_,
                        2 as u32,
                        v_quasiPatternApprox_6844_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6946_,
                        3 as u32,
                        v_constApprox_6845_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6946_,
                        4 as u32,
                        v_isDefEqStuckEx_6846_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6946_,
                        5 as u32,
                        v_unificationHints_6847_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6946_,
                        6 as u32,
                        v_proofIrrelevance_6848_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6946_,
                        7 as u32,
                        v_assignSyntheticOpaque_6849_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6946_,
                        8 as u32,
                        v_offsetCnstrs_6850_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6946_,
                        10 as u32,
                        v_etaStruct_6851_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6946_,
                        11 as u32,
                        v_univApprox_6852_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6946_,
                        12 as u32,
                        v_iota_6853_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6946_,
                        13 as u32,
                        v_beta_6854_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6946_,
                        14 as u32,
                        v_proj_6855_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6946_,
                        15 as u32,
                        v_zeta_6856_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6946_,
                        16 as u32,
                        v_zetaDelta_6857_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6946_,
                        17 as u32,
                        v_zetaUnused_6858_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6946_,
                        18 as u32,
                        v_zetaHave_6859_,
                    );
                    v_config_6874_ = v_reuseFailAlloc_6946_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_ctor_set_uint8(v_config_6874_, 9 as u32, v___x_6827_);
                v___x_6875_ = l_Lean_Meta_Context_configKey(v___y_6829_);
                v___x_6876_ = 3u64;
                v___x_6877_ = lean_uint64_shift_right(v___x_6875_, v___x_6876_);
                v___x_6878_ = lean_uint64_shift_left(v___x_6877_, v___x_6876_);
                v___x_6879_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_6827_);
                v_key_6880_ = lean_uint64_lor(v___x_6878_, v___x_6879_);
                v___x_6881_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_6881_, 0, v_config_6874_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_6881_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_6880_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_6869_);
                crate::leanh::lean_inc(v_synthPendingDepth_6868_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_6867_);
                crate::leanh::lean_inc_ref(v_localInstances_6866_);
                crate::leanh::lean_inc_ref(v_lctx_6865_);
                crate::leanh::lean_inc(v_zetaDeltaSet_6864_);
                v___x_6882_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_6882_, 0, v___x_6881_);
                crate::leanh::lean_ctor_set(v___x_6882_, 1, v_zetaDeltaSet_6864_);
                crate::leanh::lean_ctor_set(v___x_6882_, 2, v_lctx_6865_);
                crate::leanh::lean_ctor_set(v___x_6882_, 3, v_localInstances_6866_);
                crate::leanh::lean_ctor_set(v___x_6882_, 4, v_defEqCtx_x3f_6867_);
                crate::leanh::lean_ctor_set(v___x_6882_, 5, v_synthPendingDepth_6868_);
                crate::leanh::lean_ctor_set(v___x_6882_, 6, v_canUnfold_x3f_6869_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6882_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_6863_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6882_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_6870_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6882_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_6871_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_6882_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_6872_,
                );
                crate::leanh::lean_inc(v_mvarId_6828_);
                v___x_6883_ = l_Lean_MVarId_getType_x27(
                    v_mvarId_6828_,
                    v___x_6882_,
                    v___y_6830_,
                    v___y_6831_,
                    v___y_6832_,
                );
                crate::leanh::lean_dec_ref_known(v___x_6882_, 7);
                if crate::leanh::lean_obj_tag(v___x_6883_) == 0 {
                    v_a_6884_ = crate::leanh::lean_ctor_get(v___x_6883_, 0);
                    crate::leanh::lean_inc(v_a_6884_);
                    crate::leanh::lean_dec_ref_known(v___x_6883_, 1);
                    v___x_6885_ = l_Lean_MVarId_propext___lam__0___closed__1;
                    v___x_6886_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_6887_ = l_Lean_Expr_isAppOfArity(v_a_6884_, v___x_6885_, v___x_6886_);
                    if v___x_6887_ == 0 {
                        crate::leanh::lean_dec(v_a_6884_);
                        crate::leanh::lean_dec(v_mvarId_6828_);
                        v___x_6913_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_iffOfEq___lam__0___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_MVarId_iffOfEq___lam__0___closed__1_once
                            ),
                            _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1,
                        );
                        v___x_6914_ =
                            l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(
                                v___x_6913_,
                                v___y_6829_,
                                v___y_6830_,
                                v___y_6831_,
                                v___y_6832_,
                            );
                        return v___x_6914_;
                    } else {
                        v___x_6915_ = l_Lean_Expr_appFn_x21(v_a_6884_);
                        crate::leanh::lean_dec(v_a_6884_);
                        v___x_6916_ = l_Lean_Expr_appArg_x21(v___x_6915_);
                        crate::leanh::lean_dec_ref(v___x_6915_);
                        v___x_6917_ = l_Lean_Meta_isProp(
                            v___x_6916_,
                            v___y_6829_,
                            v___y_6830_,
                            v___y_6831_,
                            v___y_6832_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6917_) == 0 {
                            v_a_6918_ = crate::leanh::lean_ctor_get(v___x_6917_, 0);
                            crate::leanh::lean_inc(v_a_6918_);
                            crate::leanh::lean_dec_ref_known(v___x_6917_, 1);
                            v___x_6919_ = (crate::leanh::lean_unbox(v_a_6918_) as u8);
                            crate::leanh::lean_dec(v_a_6918_);
                            if v___x_6919_ == 0 {
                                crate::leanh::lean_dec(v_mvarId_6828_);
                                v___x_6920_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_MVarId_iffOfEq___lam__0___closed__1
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_MVarId_iffOfEq___lam__0___closed__1_once
                                    ),
                                    _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1,
                                );
                                v___x_6921_ =
                                    l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(
                                        v___x_6920_,
                                        v___y_6829_,
                                        v___y_6830_,
                                        v___y_6831_,
                                        v___y_6832_,
                                    );
                                v_a_6922_ = crate::leanh::lean_ctor_get(v___x_6921_, 0);
                                v_isSharedCheck_6929_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6921_)) as u8;
                                if v_isSharedCheck_6929_ == 0 {
                                    v___x_6924_ = v___x_6921_;
                                    v_isShared_6925_ = v_isSharedCheck_6929_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6922_);
                                    crate::leanh::lean_dec(v___x_6921_);
                                    v___x_6924_ = crate::leanh::lean_box(0);
                                    v_isShared_6925_ = v_isSharedCheck_6929_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_mvarId_6828_);
                            v_a_6930_ = crate::leanh::lean_ctor_get(v___x_6917_, 0);
                            v_isSharedCheck_6937_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6917_)) as u8;
                            if v_isSharedCheck_6937_ == 0 {
                                v___x_6932_ = v___x_6917_;
                                v_isShared_6933_ = v_isSharedCheck_6937_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6930_);
                                crate::leanh::lean_dec(v___x_6917_);
                                v___x_6932_ = crate::leanh::lean_box(0);
                                v_isShared_6933_ = v_isSharedCheck_6937_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_6828_);
                    v_a_6938_ = crate::leanh::lean_ctor_get(v___x_6883_, 0);
                    v_isSharedCheck_6945_ = (!crate::leanh::lean_is_exclusive(v___x_6883_)) as u8;
                    if v_isSharedCheck_6945_ == 0 {
                        v___x_6940_ = v___x_6883_;
                        v_isShared_6941_ = v_isSharedCheck_6945_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6938_);
                        crate::leanh::lean_dec(v___x_6883_);
                        v___x_6940_ = crate::leanh::lean_box(0);
                        v_isShared_6941_ = v_isSharedCheck_6945_;
                        state = 13;
                        continue;
                    }
                }
            }
            4 => {
                v___x_6889_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_propext___lam__0___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_propext___lam__0___closed__4_once),
                    _init_l_Lean_MVarId_propext___lam__0___closed__4,
                );
                v___x_6890_ = 0;
                v___x_6891_ = 0;
                v___x_6892_ = crate::leanh::lean_alloc_ctor(0, 0, (4) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_6892_, 0 as u32, v___x_6890_);
                crate::leanh::lean_ctor_set_uint8(v___x_6892_, 1 as u32, v___x_6887_);
                crate::leanh::lean_ctor_set_uint8(v___x_6892_, 2 as u32, v___x_6891_);
                crate::leanh::lean_ctor_set_uint8(v___x_6892_, 3 as u32, v___x_6887_);
                v___x_6893_ = crate::leanh::lean_box(0);
                v___x_6894_ = l_Lean_MVarId_apply(
                    v_mvarId_6828_,
                    v___x_6889_,
                    v___x_6892_,
                    v___x_6893_,
                    v___y_6829_,
                    v___y_6830_,
                    v___y_6831_,
                    v___y_6832_,
                );
                if crate::leanh::lean_obj_tag(v___x_6894_) == 0 {
                    v_a_6895_ = crate::leanh::lean_ctor_get(v___x_6894_, 0);
                    v_isSharedCheck_6904_ = (!crate::leanh::lean_is_exclusive(v___x_6894_)) as u8;
                    if v_isSharedCheck_6904_ == 0 {
                        v___x_6897_ = v___x_6894_;
                        v_isShared_6898_ = v_isSharedCheck_6904_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6895_);
                        crate::leanh::lean_dec(v___x_6894_);
                        v___x_6897_ = crate::leanh::lean_box(0);
                        v_isShared_6898_ = v_isSharedCheck_6904_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_6905_ = crate::leanh::lean_ctor_get(v___x_6894_, 0);
                    v_isSharedCheck_6912_ = (!crate::leanh::lean_is_exclusive(v___x_6894_)) as u8;
                    if v_isSharedCheck_6912_ == 0 {
                        v___x_6907_ = v___x_6894_;
                        v_isShared_6908_ = v_isSharedCheck_6912_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6905_);
                        crate::leanh::lean_dec(v___x_6894_);
                        v___x_6907_ = crate::leanh::lean_box(0);
                        v_isShared_6908_ = v_isSharedCheck_6912_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_6895_) == 1 {
                    v_tail_6899_ = crate::leanh::lean_ctor_get(v_a_6895_, 1);
                    if crate::leanh::lean_obj_tag(v_tail_6899_) == 0 {
                        v_head_6900_ = crate::leanh::lean_ctor_get(v_a_6895_, 0);
                        crate::leanh::lean_inc(v_head_6900_);
                        crate::leanh::lean_dec_ref_known(v_a_6895_, 2);
                        if v_isShared_6898_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6897_, 0, v_head_6900_);
                            v___x_6902_ = v___x_6897_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_6903_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6903_, 0, v_head_6900_);
                            v___x_6902_ = v_reuseFailAlloc_6903_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_6895_, 2);
                        crate::leanh::lean_del_object(v___x_6897_);
                        v___y_6835_ = v___y_6829_;
                        v___y_6836_ = v___y_6830_;
                        v___y_6837_ = v___y_6831_;
                        v___y_6838_ = v___y_6832_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6897_);
                    crate::leanh::lean_dec(v_a_6895_);
                    v___y_6835_ = v___y_6829_;
                    v___y_6836_ = v___y_6830_;
                    v___y_6837_ = v___y_6831_;
                    v___y_6838_ = v___y_6832_;
                    state = 1;
                    continue;
                }
            }
            6 => {
                return v___x_6902_;
            }
            7 => {
                if v_isShared_6908_ == 0 {
                    v___x_6910_ = v___x_6907_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6911_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6911_, 0, v_a_6905_);
                    v___x_6910_ = v_reuseFailAlloc_6911_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6910_;
            }
            9 => {
                if v_isShared_6925_ == 0 {
                    v___x_6927_ = v___x_6924_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6928_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6928_, 0, v_a_6922_);
                    v___x_6927_ = v_reuseFailAlloc_6928_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6927_;
            }
            11 => {
                if v_isShared_6933_ == 0 {
                    v___x_6935_ = v___x_6932_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6936_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6936_, 0, v_a_6930_);
                    v___x_6935_ = v_reuseFailAlloc_6936_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6935_;
            }
            13 => {
                if v_isShared_6941_ == 0 {
                    v___x_6943_ = v___x_6940_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_6944_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6944_, 0, v_a_6938_);
                    v___x_6943_ = v_reuseFailAlloc_6944_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_6943_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_propext___lam__0___boxed(
    mut v___x_6948_: *mut crate::leanh::LeanObject,
    mut v_mvarId_6949_: *mut crate::leanh::LeanObject,
    mut v___y_6950_: *mut crate::leanh::LeanObject,
    mut v___y_6951_: *mut crate::leanh::LeanObject,
    mut v___y_6952_: *mut crate::leanh::LeanObject,
    mut v___y_6953_: *mut crate::leanh::LeanObject,
    mut v___y_6954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2435__boxed_6955_: u8 = 0;
    let mut v_res_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2435__boxed_6955_ = (crate::leanh::lean_unbox(v___x_6948_) as u8);
    v_res_6956_ = l_Lean_MVarId_propext___lam__0(
        v___x_2435__boxed_6955_,
        v_mvarId_6949_,
        v___y_6950_,
        v___y_6951_,
        v___y_6952_,
        v___y_6953_,
    );
    crate::leanh::lean_dec(v___y_6953_);
    crate::leanh::lean_dec_ref(v___y_6952_);
    crate::leanh::lean_dec(v___y_6951_);
    crate::leanh::lean_dec_ref(v___y_6950_);
    return v_res_6956_;
}
pub unsafe fn l_Lean_MVarId_propext(
    mut v_mvarId_6957_: *mut crate::leanh::LeanObject,
    mut v_a_6958_: *mut crate::leanh::LeanObject,
    mut v_a_6959_: *mut crate::leanh::LeanObject,
    mut v_a_6960_: *mut crate::leanh::LeanObject,
    mut v_a_6961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6963_: u8 = 0;
    let mut v___x_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6970_: u8 = 0;
    let mut v___x_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6978_: u8 = 0;
    let mut v_a_6979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6982_: u8 = 0;
    let mut v___x_6984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6986_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6963_ = 2;
                v___x_6964_ = crate::leanh::lean_box((v___x_6963_) as usize);
                crate::leanh::lean_inc(v_mvarId_6957_);
                v___f_6965_ = crate::leanh::lean_alloc_closure(
                    l_Lean_MVarId_propext___lam__0___boxed as *mut core::ffi::c_void,
                    7,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_6965_, 0, v___x_6964_);
                crate::leanh::lean_closure_set(v___f_6965_, 1, v_mvarId_6957_);
                v___x_6966_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(
                    v___f_6965_,
                    v_a_6958_,
                    v_a_6959_,
                    v_a_6960_,
                    v_a_6961_,
                );
                if crate::leanh::lean_obj_tag(v___x_6966_) == 0 {
                    v_a_6967_ = crate::leanh::lean_ctor_get(v___x_6966_, 0);
                    v_isSharedCheck_6978_ = (!crate::leanh::lean_is_exclusive(v___x_6966_)) as u8;
                    if v_isSharedCheck_6978_ == 0 {
                        v___x_6969_ = v___x_6966_;
                        v_isShared_6970_ = v_isSharedCheck_6978_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6967_);
                        crate::leanh::lean_dec(v___x_6966_);
                        v___x_6969_ = crate::leanh::lean_box(0);
                        v_isShared_6970_ = v_isSharedCheck_6978_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_6957_);
                    v_a_6979_ = crate::leanh::lean_ctor_get(v___x_6966_, 0);
                    v_isSharedCheck_6986_ = (!crate::leanh::lean_is_exclusive(v___x_6966_)) as u8;
                    if v_isSharedCheck_6986_ == 0 {
                        v___x_6981_ = v___x_6966_;
                        v_isShared_6982_ = v_isSharedCheck_6986_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6979_);
                        crate::leanh::lean_dec(v___x_6966_);
                        v___x_6981_ = crate::leanh::lean_box(0);
                        v_isShared_6982_ = v_isSharedCheck_6986_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_6967_) == 0 {
                    if v_isShared_6970_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6969_, 0, v_mvarId_6957_);
                        v___x_6972_ = v___x_6969_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6973_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6973_, 0, v_mvarId_6957_);
                        v___x_6972_ = v_reuseFailAlloc_6973_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_6957_);
                    v_val_6974_ = crate::leanh::lean_ctor_get(v_a_6967_, 0);
                    crate::leanh::lean_inc(v_val_6974_);
                    crate::leanh::lean_dec_ref_known(v_a_6967_, 1);
                    if v_isShared_6970_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6969_, 0, v_val_6974_);
                        v___x_6976_ = v___x_6969_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6977_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6977_, 0, v_val_6974_);
                        v___x_6976_ = v_reuseFailAlloc_6977_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6972_;
            }
            3 => {
                return v___x_6976_;
            }
            4 => {
                if v_isShared_6982_ == 0 {
                    v___x_6984_ = v___x_6981_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6985_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6985_, 0, v_a_6979_);
                    v___x_6984_ = v_reuseFailAlloc_6985_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6984_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_propext___boxed(
    mut v_mvarId_6987_: *mut crate::leanh::LeanObject,
    mut v_a_6988_: *mut crate::leanh::LeanObject,
    mut v_a_6989_: *mut crate::leanh::LeanObject,
    mut v_a_6990_: *mut crate::leanh::LeanObject,
    mut v_a_6991_: *mut crate::leanh::LeanObject,
    mut v_a_6992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6993_ = l_Lean_MVarId_propext(v_mvarId_6987_, v_a_6988_, v_a_6989_, v_a_6990_, v_a_6991_);
    crate::leanh::lean_dec(v_a_6991_);
    crate::leanh::lean_dec_ref(v_a_6990_);
    crate::leanh::lean_dec(v_a_6989_);
    crate::leanh::lean_dec_ref(v_a_6988_);
    return v_res_6993_;
}
pub unsafe fn _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0() -> u64 {
    let mut v___x_6994_: u8 = 0;
    let mut v___x_6995_: u64 = 0;
    v___x_6994_ = 2;
    v___x_6995_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_6994_);
    return v___x_6995_;
}
pub unsafe fn l_Lean_MVarId_proofIrrelHeq___lam__0(
    mut v_mvarId_7002_: *mut crate::leanh::LeanObject,
    mut v___x_7003_: *mut crate::leanh::LeanObject,
    mut v___y_7004_: *mut crate::leanh::LeanObject,
    mut v___y_7005_: *mut crate::leanh::LeanObject,
    mut v___y_7006_: *mut crate::leanh::LeanObject,
    mut v___y_7007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_7011_: u8 = 0;
    let mut v_ctxApprox_7012_: u8 = 0;
    let mut v_quasiPatternApprox_7013_: u8 = 0;
    let mut v_constApprox_7014_: u8 = 0;
    let mut v_isDefEqStuckEx_7015_: u8 = 0;
    let mut v_unificationHints_7016_: u8 = 0;
    let mut v_proofIrrelevance_7017_: u8 = 0;
    let mut v_assignSyntheticOpaque_7018_: u8 = 0;
    let mut v_offsetCnstrs_7019_: u8 = 0;
    let mut v_etaStruct_7020_: u8 = 0;
    let mut v_univApprox_7021_: u8 = 0;
    let mut v_iota_7022_: u8 = 0;
    let mut v_beta_7023_: u8 = 0;
    let mut v_proj_7024_: u8 = 0;
    let mut v_zeta_7025_: u8 = 0;
    let mut v_zetaDelta_7026_: u8 = 0;
    let mut v_zetaUnused_7027_: u8 = 0;
    let mut v_zetaHave_7028_: u8 = 0;
    let mut v___x_7030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7031_: u8 = 0;
    let mut v_trackZetaDelta_7032_: u8 = 0;
    let mut v_zetaDeltaSet_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_7034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_7035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_7036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_7037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_7038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_7039_: u8 = 0;
    let mut v_inTypeClassResolution_7040_: u8 = 0;
    let mut v_cacheInferType_7041_: u8 = 0;
    let mut v___x_7042_: u8 = 0;
    let mut v_config_7044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7045_: u64 = 0;
    let mut v___x_7046_: u64 = 0;
    let mut v___x_7047_: u64 = 0;
    let mut v___x_7048_: u64 = 0;
    let mut v___x_7049_: u64 = 0;
    let mut v_key_7050_: u64 = 0;
    let mut v___x_7051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: u8 = 0;
    let mut v___x_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7074_: u8 = 0;
    let mut v___x_7075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7079_: u8 = 0;
    let mut v_unused_7080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7084_: u8 = 0;
    let mut v___x_7086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7088_: u8 = 0;
    let mut v_a_7089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7092_: u8 = 0;
    let mut v___x_7094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7096_: u8 = 0;
    let mut v_reuseFailAlloc_7097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7098_: u8 = 0;
    let mut v_a_7099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7102_: u8 = 0;
    let mut v___x_7104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_7002_);
                v___x_7009_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_7002_,
                    v___x_7003_,
                    v___y_7004_,
                    v___y_7005_,
                    v___y_7006_,
                    v___y_7007_,
                );
                if crate::leanh::lean_obj_tag(v___x_7009_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_7009_, 1);
                    v___x_7010_ = l_Lean_Meta_Context_config(v___y_7004_);
                    v_foApprox_7011_ = crate::leanh::lean_ctor_get_uint8(v___x_7010_, 0 as u32);
                    v_ctxApprox_7012_ = crate::leanh::lean_ctor_get_uint8(v___x_7010_, 1 as u32);
                    v_quasiPatternApprox_7013_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_7010_, 2 as u32);
                    v_constApprox_7014_ = crate::leanh::lean_ctor_get_uint8(v___x_7010_, 3 as u32);
                    v_isDefEqStuckEx_7015_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_7010_, 4 as u32);
                    v_unificationHints_7016_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_7010_, 5 as u32);
                    v_proofIrrelevance_7017_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_7010_, 6 as u32);
                    v_assignSyntheticOpaque_7018_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_7010_, 7 as u32);
                    v_offsetCnstrs_7019_ = crate::leanh::lean_ctor_get_uint8(v___x_7010_, 8 as u32);
                    v_etaStruct_7020_ = crate::leanh::lean_ctor_get_uint8(v___x_7010_, 10 as u32);
                    v_univApprox_7021_ = crate::leanh::lean_ctor_get_uint8(v___x_7010_, 11 as u32);
                    v_iota_7022_ = crate::leanh::lean_ctor_get_uint8(v___x_7010_, 12 as u32);
                    v_beta_7023_ = crate::leanh::lean_ctor_get_uint8(v___x_7010_, 13 as u32);
                    v_proj_7024_ = crate::leanh::lean_ctor_get_uint8(v___x_7010_, 14 as u32);
                    v_zeta_7025_ = crate::leanh::lean_ctor_get_uint8(v___x_7010_, 15 as u32);
                    v_zetaDelta_7026_ = crate::leanh::lean_ctor_get_uint8(v___x_7010_, 16 as u32);
                    v_zetaUnused_7027_ = crate::leanh::lean_ctor_get_uint8(v___x_7010_, 17 as u32);
                    v_zetaHave_7028_ = crate::leanh::lean_ctor_get_uint8(v___x_7010_, 18 as u32);
                    v_isSharedCheck_7098_ = (!crate::leanh::lean_is_exclusive(v___x_7010_)) as u8;
                    if v_isSharedCheck_7098_ == 0 {
                        v___x_7030_ = v___x_7010_;
                        v_isShared_7031_ = v_isSharedCheck_7098_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_7010_);
                        v___x_7030_ = crate::leanh::lean_box(0);
                        v_isShared_7031_ = v_isSharedCheck_7098_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_7002_);
                    v_a_7099_ = crate::leanh::lean_ctor_get(v___x_7009_, 0);
                    v_isSharedCheck_7106_ = (!crate::leanh::lean_is_exclusive(v___x_7009_)) as u8;
                    if v_isSharedCheck_7106_ == 0 {
                        v___x_7101_ = v___x_7009_;
                        v_isShared_7102_ = v_isSharedCheck_7106_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7099_);
                        crate::leanh::lean_dec(v___x_7009_);
                        v___x_7101_ = crate::leanh::lean_box(0);
                        v_isShared_7102_ = v_isSharedCheck_7106_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_trackZetaDelta_7032_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_7004_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_7033_ = crate::leanh::lean_ctor_get(v___y_7004_, 1);
                v_lctx_7034_ = crate::leanh::lean_ctor_get(v___y_7004_, 2);
                v_localInstances_7035_ = crate::leanh::lean_ctor_get(v___y_7004_, 3);
                v_defEqCtx_x3f_7036_ = crate::leanh::lean_ctor_get(v___y_7004_, 4);
                v_synthPendingDepth_7037_ = crate::leanh::lean_ctor_get(v___y_7004_, 5);
                v_canUnfold_x3f_7038_ = crate::leanh::lean_ctor_get(v___y_7004_, 6);
                v_univApprox_7039_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_7004_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_7040_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_7004_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_7041_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_7004_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_7042_ = 2;
                if v_isShared_7031_ == 0 {
                    v_config_7044_ = v___x_7030_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7097_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7097_,
                        0 as u32,
                        v_foApprox_7011_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7097_,
                        1 as u32,
                        v_ctxApprox_7012_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7097_,
                        2 as u32,
                        v_quasiPatternApprox_7013_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7097_,
                        3 as u32,
                        v_constApprox_7014_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7097_,
                        4 as u32,
                        v_isDefEqStuckEx_7015_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7097_,
                        5 as u32,
                        v_unificationHints_7016_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7097_,
                        6 as u32,
                        v_proofIrrelevance_7017_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7097_,
                        7 as u32,
                        v_assignSyntheticOpaque_7018_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7097_,
                        8 as u32,
                        v_offsetCnstrs_7019_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7097_,
                        10 as u32,
                        v_etaStruct_7020_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7097_,
                        11 as u32,
                        v_univApprox_7021_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7097_,
                        12 as u32,
                        v_iota_7022_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7097_,
                        13 as u32,
                        v_beta_7023_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7097_,
                        14 as u32,
                        v_proj_7024_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7097_,
                        15 as u32,
                        v_zeta_7025_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7097_,
                        16 as u32,
                        v_zetaDelta_7026_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7097_,
                        17 as u32,
                        v_zetaUnused_7027_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7097_,
                        18 as u32,
                        v_zetaHave_7028_,
                    );
                    v_config_7044_ = v_reuseFailAlloc_7097_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(v_config_7044_, 9 as u32, v___x_7042_);
                v___x_7045_ = l_Lean_Meta_Context_configKey(v___y_7004_);
                v___x_7046_ = 3u64;
                v___x_7047_ = lean_uint64_shift_right(v___x_7045_, v___x_7046_);
                v___x_7048_ = lean_uint64_shift_left(v___x_7047_, v___x_7046_);
                v___x_7049_ = crate::leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_once),
                    _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0,
                );
                v_key_7050_ = lean_uint64_lor(v___x_7048_, v___x_7049_);
                v___x_7051_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_7051_, 0, v_config_7044_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_7051_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_7050_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_7038_);
                crate::leanh::lean_inc(v_synthPendingDepth_7037_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_7036_);
                crate::leanh::lean_inc_ref(v_localInstances_7035_);
                crate::leanh::lean_inc_ref(v_lctx_7034_);
                crate::leanh::lean_inc(v_zetaDeltaSet_7033_);
                v___x_7052_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_7052_, 0, v___x_7051_);
                crate::leanh::lean_ctor_set(v___x_7052_, 1, v_zetaDeltaSet_7033_);
                crate::leanh::lean_ctor_set(v___x_7052_, 2, v_lctx_7034_);
                crate::leanh::lean_ctor_set(v___x_7052_, 3, v_localInstances_7035_);
                crate::leanh::lean_ctor_set(v___x_7052_, 4, v_defEqCtx_x3f_7036_);
                crate::leanh::lean_ctor_set(v___x_7052_, 5, v_synthPendingDepth_7037_);
                crate::leanh::lean_ctor_set(v___x_7052_, 6, v_canUnfold_x3f_7038_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7052_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_7032_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7052_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_7039_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7052_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_7040_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7052_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_7041_,
                );
                crate::leanh::lean_inc(v_mvarId_7002_);
                v___x_7053_ = l_Lean_MVarId_getType_x27(
                    v_mvarId_7002_,
                    v___x_7052_,
                    v___y_7005_,
                    v___y_7006_,
                    v___y_7007_,
                );
                crate::leanh::lean_dec_ref_known(v___x_7052_, 7);
                if crate::leanh::lean_obj_tag(v___x_7053_) == 0 {
                    v_a_7054_ = crate::leanh::lean_ctor_get(v___x_7053_, 0);
                    crate::leanh::lean_inc(v_a_7054_);
                    crate::leanh::lean_dec_ref_known(v___x_7053_, 1);
                    v___x_7055_ = l_Lean_MVarId_proofIrrelHeq___lam__0___closed__2;
                    v___x_7056_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_7057_ = l_Lean_Expr_isAppOfArity(v_a_7054_, v___x_7055_, v___x_7056_);
                    if v___x_7057_ == 0 {
                        crate::leanh::lean_dec(v_a_7054_);
                        crate::leanh::lean_dec(v_mvarId_7002_);
                        v___x_7058_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_iffOfEq___lam__0___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_MVarId_iffOfEq___lam__0___closed__1_once
                            ),
                            _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1,
                        );
                        v___x_7059_ =
                            l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(
                                v___x_7058_,
                                v___y_7004_,
                                v___y_7005_,
                                v___y_7006_,
                                v___y_7007_,
                            );
                        return v___x_7059_;
                    } else {
                        v___x_7060_ = l_Lean_Expr_appFn_x21(v_a_7054_);
                        v___x_7061_ = l_Lean_Expr_appFn_x21(v___x_7060_);
                        crate::leanh::lean_dec_ref(v___x_7060_);
                        v___x_7062_ = l_Lean_Expr_appArg_x21(v___x_7061_);
                        crate::leanh::lean_dec_ref(v___x_7061_);
                        v___x_7063_ = l_Lean_Expr_appArg_x21(v_a_7054_);
                        crate::leanh::lean_dec(v_a_7054_);
                        v___x_7064_ = l_Lean_MVarId_proofIrrelHeq___lam__0___closed__4;
                        v___x_7065_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_7066_ = lean_mk_empty_array_with_capacity(v___x_7065_);
                        v___x_7067_ = lean_array_push(v___x_7066_, v___x_7062_);
                        v___x_7068_ = lean_array_push(v___x_7067_, v___x_7063_);
                        v___x_7069_ = l_Lean_Meta_mkAppM(
                            v___x_7064_,
                            v___x_7068_,
                            v___y_7004_,
                            v___y_7005_,
                            v___y_7006_,
                            v___y_7007_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_7069_) == 0 {
                            v_a_7070_ = crate::leanh::lean_ctor_get(v___x_7069_, 0);
                            crate::leanh::lean_inc(v_a_7070_);
                            crate::leanh::lean_dec_ref_known(v___x_7069_, 1);
                            v___x_7071_ =
                                l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(
                                    v_mvarId_7002_,
                                    v_a_7070_,
                                    v___y_7005_,
                                );
                            v_isSharedCheck_7079_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7071_)) as u8;
                            if v_isSharedCheck_7079_ == 0 {
                                v_unused_7080_ = crate::leanh::lean_ctor_get(v___x_7071_, 0);
                                crate::leanh::lean_dec(v_unused_7080_);
                                v___x_7073_ = v___x_7071_;
                                v_isShared_7074_ = v_isSharedCheck_7079_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_7071_);
                                v___x_7073_ = crate::leanh::lean_box(0);
                                v_isShared_7074_ = v_isSharedCheck_7079_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_mvarId_7002_);
                            v_a_7081_ = crate::leanh::lean_ctor_get(v___x_7069_, 0);
                            v_isSharedCheck_7088_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7069_)) as u8;
                            if v_isSharedCheck_7088_ == 0 {
                                v___x_7083_ = v___x_7069_;
                                v_isShared_7084_ = v_isSharedCheck_7088_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7081_);
                                crate::leanh::lean_dec(v___x_7069_);
                                v___x_7083_ = crate::leanh::lean_box(0);
                                v_isShared_7084_ = v_isSharedCheck_7088_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_7002_);
                    v_a_7089_ = crate::leanh::lean_ctor_get(v___x_7053_, 0);
                    v_isSharedCheck_7096_ = (!crate::leanh::lean_is_exclusive(v___x_7053_)) as u8;
                    if v_isSharedCheck_7096_ == 0 {
                        v___x_7091_ = v___x_7053_;
                        v_isShared_7092_ = v_isSharedCheck_7096_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7089_);
                        crate::leanh::lean_dec(v___x_7053_);
                        v___x_7091_ = crate::leanh::lean_box(0);
                        v_isShared_7092_ = v_isSharedCheck_7096_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_7075_ = crate::leanh::lean_box((v___x_7057_) as usize);
                if v_isShared_7074_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7073_, 0, v___x_7075_);
                    v___x_7077_ = v___x_7073_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7078_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7078_, 0, v___x_7075_);
                    v___x_7077_ = v_reuseFailAlloc_7078_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7077_;
            }
            5 => {
                if v_isShared_7084_ == 0 {
                    v___x_7086_ = v___x_7083_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7087_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7087_, 0, v_a_7081_);
                    v___x_7086_ = v_reuseFailAlloc_7087_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7086_;
            }
            7 => {
                if v_isShared_7092_ == 0 {
                    v___x_7094_ = v___x_7091_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7095_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7095_, 0, v_a_7089_);
                    v___x_7094_ = v_reuseFailAlloc_7095_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7094_;
            }
            9 => {
                if v_isShared_7102_ == 0 {
                    v___x_7104_ = v___x_7101_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7105_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7105_, 0, v_a_7099_);
                    v___x_7104_ = v_reuseFailAlloc_7105_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_proofIrrelHeq___lam__0___boxed(
    mut v_mvarId_7107_: *mut crate::leanh::LeanObject,
    mut v___x_7108_: *mut crate::leanh::LeanObject,
    mut v___y_7109_: *mut crate::leanh::LeanObject,
    mut v___y_7110_: *mut crate::leanh::LeanObject,
    mut v___y_7111_: *mut crate::leanh::LeanObject,
    mut v___y_7112_: *mut crate::leanh::LeanObject,
    mut v___y_7113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7114_ = l_Lean_MVarId_proofIrrelHeq___lam__0(
        v_mvarId_7107_,
        v___x_7108_,
        v___y_7109_,
        v___y_7110_,
        v___y_7111_,
        v___y_7112_,
    );
    crate::leanh::lean_dec(v___y_7112_);
    crate::leanh::lean_dec_ref(v___y_7111_);
    crate::leanh::lean_dec(v___y_7110_);
    crate::leanh::lean_dec_ref(v___y_7109_);
    return v_res_7114_;
}
pub unsafe fn l_Lean_MVarId_proofIrrelHeq___lam__1(
    mut v___f_7115_: *mut crate::leanh::LeanObject,
    mut v___y_7116_: *mut crate::leanh::LeanObject,
    mut v___y_7117_: *mut crate::leanh::LeanObject,
    mut v___y_7118_: *mut crate::leanh::LeanObject,
    mut v___y_7119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7125_: u8 = 0;
    let mut v___x_7126_: u8 = 0;
    let mut v___x_7127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7135_: u8 = 0;
    let mut v_a_7136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7139_: u8 = 0;
    let mut v___x_7141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7143_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7121_ = l_Lean_observing_x3f___at___00Lean_MVarId_iffOfEq_spec__0___redArg(
                    v___f_7115_,
                    v___y_7116_,
                    v___y_7117_,
                    v___y_7118_,
                    v___y_7119_,
                );
                if crate::leanh::lean_obj_tag(v___x_7121_) == 0 {
                    v_a_7122_ = crate::leanh::lean_ctor_get(v___x_7121_, 0);
                    v_isSharedCheck_7135_ = (!crate::leanh::lean_is_exclusive(v___x_7121_)) as u8;
                    if v_isSharedCheck_7135_ == 0 {
                        v___x_7124_ = v___x_7121_;
                        v_isShared_7125_ = v_isSharedCheck_7135_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7122_);
                        crate::leanh::lean_dec(v___x_7121_);
                        v___x_7124_ = crate::leanh::lean_box(0);
                        v_isShared_7125_ = v_isSharedCheck_7135_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7136_ = crate::leanh::lean_ctor_get(v___x_7121_, 0);
                    v_isSharedCheck_7143_ = (!crate::leanh::lean_is_exclusive(v___x_7121_)) as u8;
                    if v_isSharedCheck_7143_ == 0 {
                        v___x_7138_ = v___x_7121_;
                        v_isShared_7139_ = v_isSharedCheck_7143_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7136_);
                        crate::leanh::lean_dec(v___x_7121_);
                        v___x_7138_ = crate::leanh::lean_box(0);
                        v_isShared_7139_ = v_isSharedCheck_7143_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_7122_) == 0 {
                    v___x_7126_ = 0;
                    v___x_7127_ = crate::leanh::lean_box((v___x_7126_) as usize);
                    if v_isShared_7125_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7124_, 0, v___x_7127_);
                        v___x_7129_ = v___x_7124_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7130_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7130_, 0, v___x_7127_);
                        v___x_7129_ = v_reuseFailAlloc_7130_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_7131_ = crate::leanh::lean_ctor_get(v_a_7122_, 0);
                    crate::leanh::lean_inc(v_val_7131_);
                    crate::leanh::lean_dec_ref_known(v_a_7122_, 1);
                    if v_isShared_7125_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_7124_, 0, v_val_7131_);
                        v___x_7133_ = v___x_7124_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7134_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_7134_, 0, v_val_7131_);
                        v___x_7133_ = v_reuseFailAlloc_7134_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7129_;
            }
            3 => {
                return v___x_7133_;
            }
            4 => {
                if v_isShared_7139_ == 0 {
                    v___x_7141_ = v___x_7138_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7142_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7142_, 0, v_a_7136_);
                    v___x_7141_ = v_reuseFailAlloc_7142_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7141_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_proofIrrelHeq___lam__1___boxed(
    mut v___f_7144_: *mut crate::leanh::LeanObject,
    mut v___y_7145_: *mut crate::leanh::LeanObject,
    mut v___y_7146_: *mut crate::leanh::LeanObject,
    mut v___y_7147_: *mut crate::leanh::LeanObject,
    mut v___y_7148_: *mut crate::leanh::LeanObject,
    mut v___y_7149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7150_ = l_Lean_MVarId_proofIrrelHeq___lam__1(
        v___f_7144_,
        v___y_7145_,
        v___y_7146_,
        v___y_7147_,
        v___y_7148_,
    );
    crate::leanh::lean_dec(v___y_7148_);
    crate::leanh::lean_dec_ref(v___y_7147_);
    crate::leanh::lean_dec(v___y_7146_);
    crate::leanh::lean_dec_ref(v___y_7145_);
    return v_res_7150_;
}
pub unsafe fn l_Lean_MVarId_proofIrrelHeq(
    mut v_mvarId_7154_: *mut crate::leanh::LeanObject,
    mut v_a_7155_: *mut crate::leanh::LeanObject,
    mut v_a_7156_: *mut crate::leanh::LeanObject,
    mut v_a_7157_: *mut crate::leanh::LeanObject,
    mut v_a_7158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7160_ = l_Lean_MVarId_proofIrrelHeq___closed__1;
    crate::leanh::lean_inc(v_mvarId_7154_);
    v___f_7161_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_proofIrrelHeq___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_7161_, 0, v_mvarId_7154_);
    crate::leanh::lean_closure_set(v___f_7161_, 1, v___x_7160_);
    v___f_7162_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_proofIrrelHeq___lam__1___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7162_, 0, v___f_7161_);
    v___x_7163_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(
        v_mvarId_7154_,
        v___f_7162_,
        v_a_7155_,
        v_a_7156_,
        v_a_7157_,
        v_a_7158_,
    );
    return v___x_7163_;
}
pub unsafe fn l_Lean_MVarId_proofIrrelHeq___boxed(
    mut v_mvarId_7164_: *mut crate::leanh::LeanObject,
    mut v_a_7165_: *mut crate::leanh::LeanObject,
    mut v_a_7166_: *mut crate::leanh::LeanObject,
    mut v_a_7167_: *mut crate::leanh::LeanObject,
    mut v_a_7168_: *mut crate::leanh::LeanObject,
    mut v_a_7169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7170_ =
        l_Lean_MVarId_proofIrrelHeq(v_mvarId_7164_, v_a_7165_, v_a_7166_, v_a_7167_, v_a_7168_);
    crate::leanh::lean_dec(v_a_7168_);
    crate::leanh::lean_dec_ref(v_a_7167_);
    crate::leanh::lean_dec(v_a_7166_);
    crate::leanh::lean_dec_ref(v_a_7165_);
    return v_res_7170_;
}
pub unsafe fn l_Lean_MVarId_subsingletonElim___lam__0(
    mut v_mvarId_7175_: *mut crate::leanh::LeanObject,
    mut v___x_7176_: *mut crate::leanh::LeanObject,
    mut v___y_7177_: *mut crate::leanh::LeanObject,
    mut v___y_7178_: *mut crate::leanh::LeanObject,
    mut v___y_7179_: *mut crate::leanh::LeanObject,
    mut v___y_7180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_7184_: u8 = 0;
    let mut v_ctxApprox_7185_: u8 = 0;
    let mut v_quasiPatternApprox_7186_: u8 = 0;
    let mut v_constApprox_7187_: u8 = 0;
    let mut v_isDefEqStuckEx_7188_: u8 = 0;
    let mut v_unificationHints_7189_: u8 = 0;
    let mut v_proofIrrelevance_7190_: u8 = 0;
    let mut v_assignSyntheticOpaque_7191_: u8 = 0;
    let mut v_offsetCnstrs_7192_: u8 = 0;
    let mut v_etaStruct_7193_: u8 = 0;
    let mut v_univApprox_7194_: u8 = 0;
    let mut v_iota_7195_: u8 = 0;
    let mut v_beta_7196_: u8 = 0;
    let mut v_proj_7197_: u8 = 0;
    let mut v_zeta_7198_: u8 = 0;
    let mut v_zetaDelta_7199_: u8 = 0;
    let mut v_zetaUnused_7200_: u8 = 0;
    let mut v_zetaHave_7201_: u8 = 0;
    let mut v___x_7203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7204_: u8 = 0;
    let mut v_trackZetaDelta_7205_: u8 = 0;
    let mut v_zetaDeltaSet_7206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_7207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_7208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_7209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_7210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_7211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_7212_: u8 = 0;
    let mut v_inTypeClassResolution_7213_: u8 = 0;
    let mut v_cacheInferType_7214_: u8 = 0;
    let mut v___x_7215_: u8 = 0;
    let mut v_config_7217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7218_: u64 = 0;
    let mut v___x_7219_: u64 = 0;
    let mut v___x_7220_: u64 = 0;
    let mut v___x_7221_: u64 = 0;
    let mut v___x_7222_: u64 = 0;
    let mut v_key_7223_: u64 = 0;
    let mut v___x_7224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7230_: u8 = 0;
    let mut v___x_7231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7246_: u8 = 0;
    let mut v___x_7247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7251_: u8 = 0;
    let mut v_unused_7252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7256_: u8 = 0;
    let mut v___x_7258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7260_: u8 = 0;
    let mut v_a_7261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7264_: u8 = 0;
    let mut v___x_7266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7268_: u8 = 0;
    let mut v_reuseFailAlloc_7269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7270_: u8 = 0;
    let mut v_a_7271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7274_: u8 = 0;
    let mut v___x_7276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7278_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_7175_);
                v___x_7182_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_7175_,
                    v___x_7176_,
                    v___y_7177_,
                    v___y_7178_,
                    v___y_7179_,
                    v___y_7180_,
                );
                if crate::leanh::lean_obj_tag(v___x_7182_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_7182_, 1);
                    v___x_7183_ = l_Lean_Meta_Context_config(v___y_7177_);
                    v_foApprox_7184_ = crate::leanh::lean_ctor_get_uint8(v___x_7183_, 0 as u32);
                    v_ctxApprox_7185_ = crate::leanh::lean_ctor_get_uint8(v___x_7183_, 1 as u32);
                    v_quasiPatternApprox_7186_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_7183_, 2 as u32);
                    v_constApprox_7187_ = crate::leanh::lean_ctor_get_uint8(v___x_7183_, 3 as u32);
                    v_isDefEqStuckEx_7188_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_7183_, 4 as u32);
                    v_unificationHints_7189_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_7183_, 5 as u32);
                    v_proofIrrelevance_7190_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_7183_, 6 as u32);
                    v_assignSyntheticOpaque_7191_ =
                        crate::leanh::lean_ctor_get_uint8(v___x_7183_, 7 as u32);
                    v_offsetCnstrs_7192_ = crate::leanh::lean_ctor_get_uint8(v___x_7183_, 8 as u32);
                    v_etaStruct_7193_ = crate::leanh::lean_ctor_get_uint8(v___x_7183_, 10 as u32);
                    v_univApprox_7194_ = crate::leanh::lean_ctor_get_uint8(v___x_7183_, 11 as u32);
                    v_iota_7195_ = crate::leanh::lean_ctor_get_uint8(v___x_7183_, 12 as u32);
                    v_beta_7196_ = crate::leanh::lean_ctor_get_uint8(v___x_7183_, 13 as u32);
                    v_proj_7197_ = crate::leanh::lean_ctor_get_uint8(v___x_7183_, 14 as u32);
                    v_zeta_7198_ = crate::leanh::lean_ctor_get_uint8(v___x_7183_, 15 as u32);
                    v_zetaDelta_7199_ = crate::leanh::lean_ctor_get_uint8(v___x_7183_, 16 as u32);
                    v_zetaUnused_7200_ = crate::leanh::lean_ctor_get_uint8(v___x_7183_, 17 as u32);
                    v_zetaHave_7201_ = crate::leanh::lean_ctor_get_uint8(v___x_7183_, 18 as u32);
                    v_isSharedCheck_7270_ = (!crate::leanh::lean_is_exclusive(v___x_7183_)) as u8;
                    if v_isSharedCheck_7270_ == 0 {
                        v___x_7203_ = v___x_7183_;
                        v_isShared_7204_ = v_isSharedCheck_7270_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_7183_);
                        v___x_7203_ = crate::leanh::lean_box(0);
                        v_isShared_7204_ = v_isSharedCheck_7270_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_7175_);
                    v_a_7271_ = crate::leanh::lean_ctor_get(v___x_7182_, 0);
                    v_isSharedCheck_7278_ = (!crate::leanh::lean_is_exclusive(v___x_7182_)) as u8;
                    if v_isSharedCheck_7278_ == 0 {
                        v___x_7273_ = v___x_7182_;
                        v_isShared_7274_ = v_isSharedCheck_7278_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7271_);
                        crate::leanh::lean_dec(v___x_7182_);
                        v___x_7273_ = crate::leanh::lean_box(0);
                        v_isShared_7274_ = v_isSharedCheck_7278_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_trackZetaDelta_7205_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_7177_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_7206_ = crate::leanh::lean_ctor_get(v___y_7177_, 1);
                v_lctx_7207_ = crate::leanh::lean_ctor_get(v___y_7177_, 2);
                v_localInstances_7208_ = crate::leanh::lean_ctor_get(v___y_7177_, 3);
                v_defEqCtx_x3f_7209_ = crate::leanh::lean_ctor_get(v___y_7177_, 4);
                v_synthPendingDepth_7210_ = crate::leanh::lean_ctor_get(v___y_7177_, 5);
                v_canUnfold_x3f_7211_ = crate::leanh::lean_ctor_get(v___y_7177_, 6);
                v_univApprox_7212_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_7177_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_7213_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_7177_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_7214_ = crate::leanh::lean_ctor_get_uint8(
                    v___y_7177_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_7215_ = 2;
                if v_isShared_7204_ == 0 {
                    v_config_7217_ = v___x_7203_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7269_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7269_,
                        0 as u32,
                        v_foApprox_7184_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7269_,
                        1 as u32,
                        v_ctxApprox_7185_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7269_,
                        2 as u32,
                        v_quasiPatternApprox_7186_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7269_,
                        3 as u32,
                        v_constApprox_7187_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7269_,
                        4 as u32,
                        v_isDefEqStuckEx_7188_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7269_,
                        5 as u32,
                        v_unificationHints_7189_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7269_,
                        6 as u32,
                        v_proofIrrelevance_7190_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7269_,
                        7 as u32,
                        v_assignSyntheticOpaque_7191_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7269_,
                        8 as u32,
                        v_offsetCnstrs_7192_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7269_,
                        10 as u32,
                        v_etaStruct_7193_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7269_,
                        11 as u32,
                        v_univApprox_7194_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7269_,
                        12 as u32,
                        v_iota_7195_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7269_,
                        13 as u32,
                        v_beta_7196_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7269_,
                        14 as u32,
                        v_proj_7197_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7269_,
                        15 as u32,
                        v_zeta_7198_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7269_,
                        16 as u32,
                        v_zetaDelta_7199_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7269_,
                        17 as u32,
                        v_zetaUnused_7200_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_7269_,
                        18 as u32,
                        v_zetaHave_7201_,
                    );
                    v_config_7217_ = v_reuseFailAlloc_7269_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(v_config_7217_, 9 as u32, v___x_7215_);
                v___x_7218_ = l_Lean_Meta_Context_configKey(v___y_7177_);
                v___x_7219_ = 3u64;
                v___x_7220_ = lean_uint64_shift_right(v___x_7218_, v___x_7219_);
                v___x_7221_ = lean_uint64_shift_left(v___x_7220_, v___x_7219_);
                v___x_7222_ = crate::leanh::lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0_once),
                    _init_l_Lean_MVarId_proofIrrelHeq___lam__0___closed__0,
                );
                v_key_7223_ = lean_uint64_lor(v___x_7221_, v___x_7222_);
                v___x_7224_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_7224_, 0, v_config_7217_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_7224_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_7223_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_7211_);
                crate::leanh::lean_inc(v_synthPendingDepth_7210_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_7209_);
                crate::leanh::lean_inc_ref(v_localInstances_7208_);
                crate::leanh::lean_inc_ref(v_lctx_7207_);
                crate::leanh::lean_inc(v_zetaDeltaSet_7206_);
                v___x_7225_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_7225_, 0, v___x_7224_);
                crate::leanh::lean_ctor_set(v___x_7225_, 1, v_zetaDeltaSet_7206_);
                crate::leanh::lean_ctor_set(v___x_7225_, 2, v_lctx_7207_);
                crate::leanh::lean_ctor_set(v___x_7225_, 3, v_localInstances_7208_);
                crate::leanh::lean_ctor_set(v___x_7225_, 4, v_defEqCtx_x3f_7209_);
                crate::leanh::lean_ctor_set(v___x_7225_, 5, v_synthPendingDepth_7210_);
                crate::leanh::lean_ctor_set(v___x_7225_, 6, v_canUnfold_x3f_7211_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7225_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_7205_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7225_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_7212_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7225_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_7213_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_7225_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_7214_,
                );
                crate::leanh::lean_inc(v_mvarId_7175_);
                v___x_7226_ = l_Lean_MVarId_getType_x27(
                    v_mvarId_7175_,
                    v___x_7225_,
                    v___y_7178_,
                    v___y_7179_,
                    v___y_7180_,
                );
                crate::leanh::lean_dec_ref_known(v___x_7225_, 7);
                if crate::leanh::lean_obj_tag(v___x_7226_) == 0 {
                    v_a_7227_ = crate::leanh::lean_ctor_get(v___x_7226_, 0);
                    crate::leanh::lean_inc(v_a_7227_);
                    crate::leanh::lean_dec_ref_known(v___x_7226_, 1);
                    v___x_7228_ = l_Lean_MVarId_propext___lam__0___closed__1;
                    v___x_7229_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_7230_ = l_Lean_Expr_isAppOfArity(v_a_7227_, v___x_7228_, v___x_7229_);
                    if v___x_7230_ == 0 {
                        crate::leanh::lean_dec(v_a_7227_);
                        crate::leanh::lean_dec(v_mvarId_7175_);
                        v___x_7231_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_MVarId_iffOfEq___lam__0___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_MVarId_iffOfEq___lam__0___closed__1_once
                            ),
                            _init_l_Lean_MVarId_iffOfEq___lam__0___closed__1,
                        );
                        v___x_7232_ =
                            l_Lean_throwError___at___00Lean_MVarId_applyN_spec__1___redArg(
                                v___x_7231_,
                                v___y_7177_,
                                v___y_7178_,
                                v___y_7179_,
                                v___y_7180_,
                            );
                        return v___x_7232_;
                    } else {
                        v___x_7233_ = l_Lean_Expr_appFn_x21(v_a_7227_);
                        v___x_7234_ = l_Lean_Expr_appArg_x21(v___x_7233_);
                        crate::leanh::lean_dec_ref(v___x_7233_);
                        v___x_7235_ = l_Lean_Expr_appArg_x21(v_a_7227_);
                        crate::leanh::lean_dec(v_a_7227_);
                        v___x_7236_ = l_Lean_MVarId_subsingletonElim___lam__0___closed__1;
                        v___x_7237_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_7238_ = lean_mk_empty_array_with_capacity(v___x_7237_);
                        v___x_7239_ = lean_array_push(v___x_7238_, v___x_7234_);
                        v___x_7240_ = lean_array_push(v___x_7239_, v___x_7235_);
                        v___x_7241_ = l_Lean_Meta_mkAppM(
                            v___x_7236_,
                            v___x_7240_,
                            v___y_7177_,
                            v___y_7178_,
                            v___y_7179_,
                            v___y_7180_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_7241_) == 0 {
                            v_a_7242_ = crate::leanh::lean_ctor_get(v___x_7241_, 0);
                            crate::leanh::lean_inc(v_a_7242_);
                            crate::leanh::lean_dec_ref_known(v___x_7241_, 1);
                            v___x_7243_ =
                                l_Lean_MVarId_assign___at___00Lean_MVarId_apply_spec__1___redArg(
                                    v_mvarId_7175_,
                                    v_a_7242_,
                                    v___y_7178_,
                                );
                            v_isSharedCheck_7251_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7243_)) as u8;
                            if v_isSharedCheck_7251_ == 0 {
                                v_unused_7252_ = crate::leanh::lean_ctor_get(v___x_7243_, 0);
                                crate::leanh::lean_dec(v_unused_7252_);
                                v___x_7245_ = v___x_7243_;
                                v_isShared_7246_ = v_isSharedCheck_7251_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_7243_);
                                v___x_7245_ = crate::leanh::lean_box(0);
                                v_isShared_7246_ = v_isSharedCheck_7251_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_mvarId_7175_);
                            v_a_7253_ = crate::leanh::lean_ctor_get(v___x_7241_, 0);
                            v_isSharedCheck_7260_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7241_)) as u8;
                            if v_isSharedCheck_7260_ == 0 {
                                v___x_7255_ = v___x_7241_;
                                v_isShared_7256_ = v_isSharedCheck_7260_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7253_);
                                crate::leanh::lean_dec(v___x_7241_);
                                v___x_7255_ = crate::leanh::lean_box(0);
                                v_isShared_7256_ = v_isSharedCheck_7260_;
                                state = 5;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_7175_);
                    v_a_7261_ = crate::leanh::lean_ctor_get(v___x_7226_, 0);
                    v_isSharedCheck_7268_ = (!crate::leanh::lean_is_exclusive(v___x_7226_)) as u8;
                    if v_isSharedCheck_7268_ == 0 {
                        v___x_7263_ = v___x_7226_;
                        v_isShared_7264_ = v_isSharedCheck_7268_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7261_);
                        crate::leanh::lean_dec(v___x_7226_);
                        v___x_7263_ = crate::leanh::lean_box(0);
                        v_isShared_7264_ = v_isSharedCheck_7268_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_7247_ = crate::leanh::lean_box((v___x_7230_) as usize);
                if v_isShared_7246_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7245_, 0, v___x_7247_);
                    v___x_7249_ = v___x_7245_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7250_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7250_, 0, v___x_7247_);
                    v___x_7249_ = v_reuseFailAlloc_7250_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7249_;
            }
            5 => {
                if v_isShared_7256_ == 0 {
                    v___x_7258_ = v___x_7255_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7259_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7259_, 0, v_a_7253_);
                    v___x_7258_ = v_reuseFailAlloc_7259_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7258_;
            }
            7 => {
                if v_isShared_7264_ == 0 {
                    v___x_7266_ = v___x_7263_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7267_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7267_, 0, v_a_7261_);
                    v___x_7266_ = v_reuseFailAlloc_7267_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7266_;
            }
            9 => {
                if v_isShared_7274_ == 0 {
                    v___x_7276_ = v___x_7273_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7277_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7277_, 0, v_a_7271_);
                    v___x_7276_ = v_reuseFailAlloc_7277_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7276_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_subsingletonElim___lam__0___boxed(
    mut v_mvarId_7279_: *mut crate::leanh::LeanObject,
    mut v___x_7280_: *mut crate::leanh::LeanObject,
    mut v___y_7281_: *mut crate::leanh::LeanObject,
    mut v___y_7282_: *mut crate::leanh::LeanObject,
    mut v___y_7283_: *mut crate::leanh::LeanObject,
    mut v___y_7284_: *mut crate::leanh::LeanObject,
    mut v___y_7285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7286_ = l_Lean_MVarId_subsingletonElim___lam__0(
        v_mvarId_7279_,
        v___x_7280_,
        v___y_7281_,
        v___y_7282_,
        v___y_7283_,
        v___y_7284_,
    );
    crate::leanh::lean_dec(v___y_7284_);
    crate::leanh::lean_dec_ref(v___y_7283_);
    crate::leanh::lean_dec(v___y_7282_);
    crate::leanh::lean_dec_ref(v___y_7281_);
    return v_res_7286_;
}
pub unsafe fn l_Lean_MVarId_subsingletonElim(
    mut v_mvarId_7290_: *mut crate::leanh::LeanObject,
    mut v_a_7291_: *mut crate::leanh::LeanObject,
    mut v_a_7292_: *mut crate::leanh::LeanObject,
    mut v_a_7293_: *mut crate::leanh::LeanObject,
    mut v_a_7294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7296_ = l_Lean_MVarId_subsingletonElim___closed__1;
    crate::leanh::lean_inc(v_mvarId_7290_);
    v___f_7297_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_subsingletonElim___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_7297_, 0, v_mvarId_7290_);
    crate::leanh::lean_closure_set(v___f_7297_, 1, v___x_7296_);
    v___f_7298_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_proofIrrelHeq___lam__1___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_7298_, 0, v___f_7297_);
    v___x_7299_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_apply_spec__6___redArg(
        v_mvarId_7290_,
        v___f_7298_,
        v_a_7291_,
        v_a_7292_,
        v_a_7293_,
        v_a_7294_,
    );
    return v___x_7299_;
}
pub unsafe fn l_Lean_MVarId_subsingletonElim___boxed(
    mut v_mvarId_7300_: *mut crate::leanh::LeanObject,
    mut v_a_7301_: *mut crate::leanh::LeanObject,
    mut v_a_7302_: *mut crate::leanh::LeanObject,
    mut v_a_7303_: *mut crate::leanh::LeanObject,
    mut v_a_7304_: *mut crate::leanh::LeanObject,
    mut v_a_7305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7306_ =
        l_Lean_MVarId_subsingletonElim(v_mvarId_7300_, v_a_7301_, v_a_7302_, v_a_7303_, v_a_7304_);
    crate::leanh::lean_dec(v_a_7304_);
    crate::leanh::lean_dec_ref(v_a_7303_);
    crate::leanh::lean_dec(v_a_7302_);
    crate::leanh::lean_dec_ref(v_a_7301_);
    return v_res_7306_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Apply(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Apply(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Apply(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_PrettyPrinter(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Apply(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Apply(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Apply(builtin);
}

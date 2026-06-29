// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv.CbvEvalExt
// Imports: Lean.Data.NameMap Lean.ScopedEnvExtension Lean.Elab.InfoTree Lean.Meta.Sym.Simp.Theorems Lean.Meta.Tactic.AuxLemma Lean.Meta.AppBuilder
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Meta::Defs::l_Lean_Syntax_isNone;
use crate::r#gen::Init::Prelude::{
    l_Lean_Syntax_getArg, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Attributes::l_Lean_registerBuiltinAttribute;
use crate::r#gen::Lean::Data::Name::{
    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl, l_Lean_Name_isAnonymous,
};
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::NameMap::{
    initialize_Lean_Data_NameMap, runtime_initialize_Lean_Data_NameMap,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::InfoTree::{
    initialize_Lean_Elab_InfoTree, runtime_initialize_Lean_Elab_InfoTree,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_constName_x3f, l_Lean_Expr_getAppFn,
    l_Lean_Expr_isAppOfArity, l_Lean_mkAppN, l_Lean_mkConst,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_note,
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofName,
    l_Lean_MessageLog_add, l_Lean_instBEqMessageSeverity_beq, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkEq, l_Lean_Meta_mkEqSymm,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::Sym::Simp::Theorems::{
    initialize_Lean_Meta_Sym_Simp_Theorems, l_Lean_Meta_Sym_Simp_Theorems_insert,
    l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default, l_Lean_Meta_Sym_Simp_mkTheoremFromDecl,
    runtime_initialize_Lean_Meta_Sym_Simp_Theorems,
};
use crate::r#gen::Lean::Meta::Tactic::AuxLemma::{
    initialize_Lean_Meta_Tactic_AuxLemma, l_Lean_Meta_mkAuxLemma,
    runtime_initialize_Lean_Meta_Tactic_AuxLemma,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ScopedEnvExtension::{
    initialize_Lean_ScopedEnvExtension, l_Lean_ScopedEnvExtension_addCore___redArg,
    l_Lean_ScopedEnvExtension_getState___redArg, l_Lean_ScopedEnvExtension_modifyState___redArg,
    l_Lean_registerSimpleScopedEnvExtension___redArg, runtime_initialize_Lean_ScopedEnvExtension,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Operations::{
    l_Std_DTreeMap_Internal_Impl_maxView___redArg, l_Std_DTreeMap_Internal_Impl_minView___redArg,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_array_uget_borrowed;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_of_nat};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul,
    lean_string_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_infer_type;
pub static l_Lean_Meta_Tactic_Cbv_instBEqCbvEvalEntry___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Tactic_Cbv_instBEqCbvEvalEntry_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_Cbv_instBEqCbvEvalEntry___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instBEqCbvEvalEntry___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_Cbv_instBEqCbvEvalEntry: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instBEqCbvEvalEntry___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__0_value:
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
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__0_value)
            as *mut crate::leanh::LeanObject,
        16122875713692181903 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
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
        84, 104, 101, 32, 99, 111, 110, 99, 108, 117, 115, 105, 111, 110, 32, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__4_value:
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
    m_data: [32, 111, 102, 32, 116, 104, 101, 111, 114, 101, 109, 32, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__5_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__6_value:
    crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 101, 113, 117, 97, 108, 105, 116, 121, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__6:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__6_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__8_value:
    crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [95, 99, 98, 118, 95, 101, 118, 97, 108, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__8:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__9_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__8_value)
            as *mut crate::leanh::LeanObject,
        4717274133169104646 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__9:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__10_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__9_value
    ) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__10:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__11_value:
    crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        84, 104, 101, 32, 114, 101, 119, 114, 105, 116, 101, 32, 115, 105, 100, 101, 32, 111, 102,
        32, 116, 104, 101, 111, 114, 101, 109, 32, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__11:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__13_value:
    crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32, 97, 112, 112, 108, 105, 99, 97, 116, 105,
        111, 110, 32, 111, 102, 32, 97, 32, 99, 111, 110, 115, 116, 97, 110, 116, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__13:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__14_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__6_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__8_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__12_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__18_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___closed__0_value:
    crate::leanh::LeanStringObject<70> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 70,
    m_capacity: 70,
    m_length: 69,
    m_data: [
        32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 116, 104, 101, 111, 114, 101, 109, 32, 97,
        110, 100, 32, 116, 104, 117, 115, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 109, 97,
        114, 107, 101, 100, 32, 119, 105, 116, 104, 32, 96, 99, 98, 118, 95, 101, 118, 97, 108, 96,
        32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalState_default___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalState_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalState_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalState_default:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalState_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalState: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalState_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [99, 98, 118, 69, 118, 97, 108, 69, 120, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,16939926138027044706 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<5> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*5 + 0) as u16, other: 5, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalState_default___closed__0_value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_Cbv_cbvEvalExt: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0 + 24) as u16, other: 0, tag: 0 }, m_objs: [282574488338432 as *mut crate::leanh::LeanObject,72621647814721793 as *mut crate::leanh::LeanObject,65793 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: u64 = 0;
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<43> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32, 116, 104, 101, 32, 96, 91, 99, 98, 118, 95, 101, 118, 97, 108, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 1, m_objs: [((( 1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: crate::leanh::LeanClosureObject<1> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalState_default___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [99, 98, 118, 69, 118, 97, 108, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1932357725600152060 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [99, 98, 118, 95, 101, 118, 97, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7347478309838019632 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<81> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 81, m_capacity: 81, m_length: 80, m_data: [82, 101, 103, 105, 115, 116, 101, 114, 32, 97, 32, 116, 104, 101, 111, 114, 101, 109, 32, 97, 115, 32, 97, 32, 114, 101, 119, 114, 105, 116, 101, 32, 114, 117, 108, 101, 32, 102, 111, 114, 32, 96, 99, 98, 118, 96, 32, 101, 118, 97, 108, 117, 97, 116, 105, 111, 110, 32, 111, 102, 32, 97, 32, 103, 105, 118, 101, 110, 32, 100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 46, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<4> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Sym_Simp_Theorem_declName(
    mut v_thm_2235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_expr_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_expr_2236_ = crate::leanh::lean_ctor_get(v_thm_2235_, 0);
    v___x_2237_ = l_Lean_Expr_getAppFn(v_expr_2236_);
    v___x_2238_ = l_Lean_Expr_constName_x3f(v___x_2237_);
    crate::leanh::lean_dec_ref(v___x_2237_);
    return v___x_2238_;
}
pub unsafe fn l_Lean_Meta_Sym_Simp_Theorem_declName___boxed(
    mut v_thm_2239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2240_ = l_Lean_Meta_Sym_Simp_Theorem_declName(v_thm_2239_);
    crate::leanh::lean_dec_ref(v_thm_2239_);
    return v_res_2240_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_instBEqCbvEvalEntry_beq(
    mut v_x_2241_: *mut crate::leanh::LeanObject,
    mut v_x_2242_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_origin_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_appFn_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_thm_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_origin_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_appFn_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_thm_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: u8 = 0;
    v_origin_2243_ = crate::leanh::lean_ctor_get(v_x_2241_, 0);
    v_appFn_2244_ = crate::leanh::lean_ctor_get(v_x_2241_, 1);
    v_thm_2245_ = crate::leanh::lean_ctor_get(v_x_2241_, 2);
    v_origin_2246_ = crate::leanh::lean_ctor_get(v_x_2242_, 0);
    v_appFn_2247_ = crate::leanh::lean_ctor_get(v_x_2242_, 1);
    v_thm_2248_ = crate::leanh::lean_ctor_get(v_x_2242_, 2);
    v___x_2249_ = lean_name_eq(v_origin_2243_, v_origin_2246_);
    if v___x_2249_ == 0 {
        return v___x_2249_;
    } else {
        let mut v___x_2250_: u8 = 0;
        v___x_2250_ = lean_name_eq(v_appFn_2244_, v_appFn_2247_);
        if v___x_2250_ == 0 {
            return v___x_2250_;
        } else {
            let mut v_expr_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_expr_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2253_: u8 = 0;
            v_expr_2251_ = crate::leanh::lean_ctor_get(v_thm_2245_, 0);
            v_expr_2252_ = crate::leanh::lean_ctor_get(v_thm_2248_, 0);
            v___x_2253_ = lean_expr_eqv(v_expr_2251_, v_expr_2252_);
            return v___x_2253_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_instBEqCbvEvalEntry_beq___boxed(
    mut v_x_2254_: *mut crate::leanh::LeanObject,
    mut v_x_2255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2256_: u8 = 0;
    let mut v_r_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2256_ = l_Lean_Meta_Tactic_Cbv_instBEqCbvEvalEntry_beq(v_x_2254_, v_x_2255_);
    crate::leanh::lean_dec_ref(v_x_2255_);
    crate::leanh::lean_dec_ref(v_x_2254_);
    v_r_2257_ = crate::leanh::lean_box((v_res_2256_) as usize);
    return v_r_2257_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2260_ = l_Lean_Meta_Sym_Simp_instInhabitedTheorem_default;
    v___x_2261_ = crate::leanh::lean_box(0);
    v___x_2262_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2262_, 0, v___x_2261_);
    crate::leanh::lean_ctor_set(v___x_2262_, 1, v___x_2261_);
    crate::leanh::lean_ctor_set(v___x_2262_, 2, v___x_2260_);
    return v___x_2262_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2263_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default___closed__0_once
        ),
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default___closed__0,
    );
    return v___x_2263_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2264_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default;
    return v___x_2264_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3___redArg___lam__0(
    mut v_k_2265_: *mut crate::leanh::LeanObject,
    mut v_b_2266_: *mut crate::leanh::LeanObject,
    mut v_c_2267_: *mut crate::leanh::LeanObject,
    mut v___y_2268_: *mut crate::leanh::LeanObject,
    mut v___y_2269_: *mut crate::leanh::LeanObject,
    mut v___y_2270_: *mut crate::leanh::LeanObject,
    mut v___y_2271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_2271_);
    crate::leanh::lean_inc_ref(v___y_2270_);
    crate::leanh::lean_inc(v___y_2269_);
    crate::leanh::lean_inc_ref(v___y_2268_);
    v___x_2273_ = crate::leanh::lean_apply_7(
        v_k_2265_,
        v_b_2266_,
        v_c_2267_,
        v___y_2268_,
        v___y_2269_,
        v___y_2270_,
        v___y_2271_,
        crate::leanh::lean_box(0),
    );
    return v___x_2273_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3___redArg___lam__0___boxed(
    mut v_k_2274_: *mut crate::leanh::LeanObject,
    mut v_b_2275_: *mut crate::leanh::LeanObject,
    mut v_c_2276_: *mut crate::leanh::LeanObject,
    mut v___y_2277_: *mut crate::leanh::LeanObject,
    mut v___y_2278_: *mut crate::leanh::LeanObject,
    mut v___y_2279_: *mut crate::leanh::LeanObject,
    mut v___y_2280_: *mut crate::leanh::LeanObject,
    mut v___y_2281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2282_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3___redArg___lam__0(v_k_2274_, v_b_2275_, v_c_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
    crate::leanh::lean_dec(v___y_2280_);
    crate::leanh::lean_dec_ref(v___y_2279_);
    crate::leanh::lean_dec(v___y_2278_);
    crate::leanh::lean_dec_ref(v___y_2277_);
    return v_res_2282_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3___redArg(
    mut v_type_2283_: *mut crate::leanh::LeanObject,
    mut v_k_2284_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2285_: u8,
    mut v___y_2286_: *mut crate::leanh::LeanObject,
    mut v___y_2287_: *mut crate::leanh::LeanObject,
    mut v___y_2288_: *mut crate::leanh::LeanObject,
    mut v___y_2289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: u8 = 0;
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2298_: u8 = 0;
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2302_: u8 = 0;
    let mut v_a_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2306_: u8 = 0;
    let mut v___x_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2291_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_2291_, 0, v_k_2284_);
                v___x_2292_ = 0;
                v___x_2293_ = crate::leanh::lean_box(0);
                v___x_2294_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        crate::leanh::lean_box(0),
                        v___x_2292_,
                        v___x_2293_,
                        v_type_2283_,
                        v___f_2291_,
                        v_cleanupAnnotations_2285_,
                        v___x_2292_,
                        v___y_2286_,
                        v___y_2287_,
                        v___y_2288_,
                        v___y_2289_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2294_) == 0 {
                    v_a_2295_ = crate::leanh::lean_ctor_get(v___x_2294_, 0);
                    v_isSharedCheck_2302_ = (!crate::leanh::lean_is_exclusive(v___x_2294_)) as u8;
                    if v_isSharedCheck_2302_ == 0 {
                        v___x_2297_ = v___x_2294_;
                        v_isShared_2298_ = v_isSharedCheck_2302_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2295_);
                        crate::leanh::lean_dec(v___x_2294_);
                        v___x_2297_ = crate::leanh::lean_box(0);
                        v_isShared_2298_ = v_isSharedCheck_2302_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2303_ = crate::leanh::lean_ctor_get(v___x_2294_, 0);
                    v_isSharedCheck_2310_ = (!crate::leanh::lean_is_exclusive(v___x_2294_)) as u8;
                    if v_isSharedCheck_2310_ == 0 {
                        v___x_2305_ = v___x_2294_;
                        v_isShared_2306_ = v_isSharedCheck_2310_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2303_);
                        crate::leanh::lean_dec(v___x_2294_);
                        v___x_2305_ = crate::leanh::lean_box(0);
                        v_isShared_2306_ = v_isSharedCheck_2310_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2298_ == 0 {
                    v___x_2300_ = v___x_2297_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2301_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_a_2295_);
                    v___x_2300_ = v_reuseFailAlloc_2301_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2300_;
            }
            3 => {
                if v_isShared_2306_ == 0 {
                    v___x_2308_ = v___x_2305_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2309_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
                    v___x_2308_ = v_reuseFailAlloc_2309_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3___redArg___boxed(
    mut v_type_2311_: *mut crate::leanh::LeanObject,
    mut v_k_2312_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2313_: *mut crate::leanh::LeanObject,
    mut v___y_2314_: *mut crate::leanh::LeanObject,
    mut v___y_2315_: *mut crate::leanh::LeanObject,
    mut v___y_2316_: *mut crate::leanh::LeanObject,
    mut v___y_2317_: *mut crate::leanh::LeanObject,
    mut v___y_2318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2319_: u8 = 0;
    let mut v_res_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2319_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_2313_) as u8);
    v_res_2320_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3___redArg(v_type_2311_, v_k_2312_, v_cleanupAnnotations_boxed_2319_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
    crate::leanh::lean_dec(v___y_2317_);
    crate::leanh::lean_dec_ref(v___y_2316_);
    crate::leanh::lean_dec(v___y_2315_);
    crate::leanh::lean_dec_ref(v___y_2314_);
    return v_res_2320_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3(
    mut v_00_u03b1_2321_: *mut crate::leanh::LeanObject,
    mut v_type_2322_: *mut crate::leanh::LeanObject,
    mut v_k_2323_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2324_: u8,
    mut v___y_2325_: *mut crate::leanh::LeanObject,
    mut v___y_2326_: *mut crate::leanh::LeanObject,
    mut v___y_2327_: *mut crate::leanh::LeanObject,
    mut v___y_2328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2330_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3___redArg(v_type_2322_, v_k_2323_, v_cleanupAnnotations_2324_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
    return v___x_2330_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3___boxed(
    mut v_00_u03b1_2331_: *mut crate::leanh::LeanObject,
    mut v_type_2332_: *mut crate::leanh::LeanObject,
    mut v_k_2333_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2334_: *mut crate::leanh::LeanObject,
    mut v___y_2335_: *mut crate::leanh::LeanObject,
    mut v___y_2336_: *mut crate::leanh::LeanObject,
    mut v___y_2337_: *mut crate::leanh::LeanObject,
    mut v___y_2338_: *mut crate::leanh::LeanObject,
    mut v___y_2339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2340_: u8 = 0;
    let mut v_res_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2340_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_2334_) as u8);
    v_res_2341_ =
        l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3(
            v_00_u03b1_2331_,
            v_type_2332_,
            v_k_2333_,
            v_cleanupAnnotations_boxed_2340_,
            v___y_2335_,
            v___y_2336_,
            v___y_2337_,
            v___y_2338_,
        );
    crate::leanh::lean_dec(v___y_2338_);
    crate::leanh::lean_dec_ref(v___y_2337_);
    crate::leanh::lean_dec(v___y_2336_);
    crate::leanh::lean_dec_ref(v___y_2335_);
    return v_res_2341_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2_spec__3(
    mut v_msgData_2342_: *mut crate::leanh::LeanObject,
    mut v___y_2343_: *mut crate::leanh::LeanObject,
    mut v___y_2344_: *mut crate::leanh::LeanObject,
    mut v___y_2345_: *mut crate::leanh::LeanObject,
    mut v___y_2346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2348_ = lean_st_ref_get(v___y_2346_);
    v_env_2349_ = crate::leanh::lean_ctor_get(v___x_2348_, 0);
    crate::leanh::lean_inc_ref(v_env_2349_);
    crate::leanh::lean_dec(v___x_2348_);
    v___x_2350_ = lean_st_ref_get(v___y_2344_);
    v_mctx_2351_ = crate::leanh::lean_ctor_get(v___x_2350_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2351_);
    crate::leanh::lean_dec(v___x_2350_);
    v_lctx_2352_ = crate::leanh::lean_ctor_get(v___y_2343_, 2);
    v_options_2353_ = crate::leanh::lean_ctor_get(v___y_2345_, 2);
    crate::leanh::lean_inc_ref(v_options_2353_);
    crate::leanh::lean_inc_ref(v_lctx_2352_);
    v___x_2354_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2354_, 0, v_env_2349_);
    crate::leanh::lean_ctor_set(v___x_2354_, 1, v_mctx_2351_);
    crate::leanh::lean_ctor_set(v___x_2354_, 2, v_lctx_2352_);
    crate::leanh::lean_ctor_set(v___x_2354_, 3, v_options_2353_);
    v___x_2355_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2355_, 0, v___x_2354_);
    crate::leanh::lean_ctor_set(v___x_2355_, 1, v_msgData_2342_);
    v___x_2356_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2356_, 0, v___x_2355_);
    return v___x_2356_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2_spec__3___boxed(
    mut v_msgData_2357_: *mut crate::leanh::LeanObject,
    mut v___y_2358_: *mut crate::leanh::LeanObject,
    mut v___y_2359_: *mut crate::leanh::LeanObject,
    mut v___y_2360_: *mut crate::leanh::LeanObject,
    mut v___y_2361_: *mut crate::leanh::LeanObject,
    mut v___y_2362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2363_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2_spec__3(v_msgData_2357_, v___y_2358_, v___y_2359_, v___y_2360_, v___y_2361_);
    crate::leanh::lean_dec(v___y_2361_);
    crate::leanh::lean_dec_ref(v___y_2360_);
    crate::leanh::lean_dec(v___y_2359_);
    crate::leanh::lean_dec_ref(v___y_2358_);
    return v_res_2363_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2___redArg(
    mut v_msg_2364_: *mut crate::leanh::LeanObject,
    mut v___y_2365_: *mut crate::leanh::LeanObject,
    mut v___y_2366_: *mut crate::leanh::LeanObject,
    mut v___y_2367_: *mut crate::leanh::LeanObject,
    mut v___y_2368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2375_: u8 = 0;
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2380_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2370_ = crate::leanh::lean_ctor_get(v___y_2367_, 5);
                v___x_2371_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2_spec__3(v_msg_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_);
                v_a_2372_ = crate::leanh::lean_ctor_get(v___x_2371_, 0);
                v_isSharedCheck_2380_ = (!crate::leanh::lean_is_exclusive(v___x_2371_)) as u8;
                if v_isSharedCheck_2380_ == 0 {
                    v___x_2374_ = v___x_2371_;
                    v_isShared_2375_ = v_isSharedCheck_2380_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2372_);
                    crate::leanh::lean_dec(v___x_2371_);
                    v___x_2374_ = crate::leanh::lean_box(0);
                    v_isShared_2375_ = v_isSharedCheck_2380_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_2370_);
                v___x_2376_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2376_, 0, v_ref_2370_);
                crate::leanh::lean_ctor_set(v___x_2376_, 1, v_a_2372_);
                if v_isShared_2375_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2374_, 1);
                    crate::leanh::lean_ctor_set(v___x_2374_, 0, v___x_2376_);
                    v___x_2378_ = v___x_2374_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2379_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2376_);
                    v___x_2378_ = v_reuseFailAlloc_2379_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2378_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2___redArg___boxed(
    mut v_msg_2381_: *mut crate::leanh::LeanObject,
    mut v___y_2382_: *mut crate::leanh::LeanObject,
    mut v___y_2383_: *mut crate::leanh::LeanObject,
    mut v___y_2384_: *mut crate::leanh::LeanObject,
    mut v___y_2385_: *mut crate::leanh::LeanObject,
    mut v___y_2386_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2387_ =
        l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2___redArg(
            v_msg_2381_,
            v___y_2382_,
            v___y_2383_,
            v___y_2384_,
            v___y_2385_,
        );
    crate::leanh::lean_dec(v___y_2385_);
    crate::leanh::lean_dec_ref(v___y_2384_);
    crate::leanh::lean_dec(v___y_2383_);
    crate::leanh::lean_dec_ref(v___y_2382_);
    return v_res_2387_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2392_ = l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__2;
    v___x_2393_ = l_Lean_stringToMessageData(v___x_2392_);
    return v___x_2393_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2395_ = l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__4;
    v___x_2396_ = l_Lean_stringToMessageData(v___x_2395_);
    return v___x_2396_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2398_ = l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__6;
    v___x_2399_ = l_Lean_stringToMessageData(v___x_2398_);
    return v___x_2399_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2406_ = l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__11;
    v___x_2407_ = l_Lean_stringToMessageData(v___x_2406_);
    return v___x_2407_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2409_ = l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__13;
    v___x_2410_ = l_Lean_stringToMessageData(v___x_2409_);
    return v___x_2410_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0(
    mut v_a_2411_: *mut crate::leanh::LeanObject,
    mut v___x_2412_: *mut crate::leanh::LeanObject,
    mut v_inv_2413_: u8,
    mut v_declName_2414_: *mut crate::leanh::LeanObject,
    mut v_levelParams_2415_: *mut crate::leanh::LeanObject,
    mut v_xs_2416_: *mut crate::leanh::LeanObject,
    mut v_body_2417_: *mut crate::leanh::LeanObject,
    mut v___y_2418_: *mut crate::leanh::LeanObject,
    mut v___y_2419_: *mut crate::leanh::LeanObject,
    mut v___y_2420_: *mut crate::leanh::LeanObject,
    mut v___y_2421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_thmDeclName_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: u8 = 0;
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: u8 = 0;
    let mut v___x_2453_: u8 = 0;
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2467_: u8 = 0;
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2471_: u8 = 0;
    let mut v_a_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2475_: u8 = 0;
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2479_: u8 = 0;
    let mut v_a_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2483_: u8 = 0;
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2487_: u8 = 0;
    let mut v_a_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2491_: u8 = 0;
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2495_: u8 = 0;
    let mut v_a_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2499_: u8 = 0;
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2503_: u8 = 0;
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2428_ = l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__1;
                v___x_2429_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2430_ = l_Lean_Expr_isAppOfArity(v_body_2417_, v___x_2428_, v___x_2429_);
                if v___x_2430_ == 0 {
                    crate::leanh::lean_dec(v_levelParams_2415_);
                    crate::leanh::lean_dec(v_declName_2414_);
                    v___x_2431_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__3_once
                        ),
                        _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__3,
                    );
                    v___x_2432_ = l_Lean_MessageData_ofExpr(v_a_2411_);
                    v___x_2433_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2433_, 0, v___x_2431_);
                    crate::leanh::lean_ctor_set(v___x_2433_, 1, v___x_2432_);
                    v___x_2434_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__5_once
                        ),
                        _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__5,
                    );
                    v___x_2435_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2435_, 0, v___x_2433_);
                    crate::leanh::lean_ctor_set(v___x_2435_, 1, v___x_2434_);
                    v___x_2436_ = l_Lean_MessageData_ofExpr(v___x_2412_);
                    v___x_2437_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2437_, 0, v___x_2435_);
                    crate::leanh::lean_ctor_set(v___x_2437_, 1, v___x_2436_);
                    v___x_2438_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__7_once
                        ),
                        _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__7,
                    );
                    v___x_2439_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2439_, 0, v___x_2437_);
                    crate::leanh::lean_ctor_set(v___x_2439_, 1, v___x_2438_);
                    v___x_2440_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2___redArg(v___x_2439_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
                    return v___x_2440_;
                } else {
                    crate::leanh::lean_dec_ref(v_a_2411_);
                    v___x_2441_ = l_Lean_Expr_appFn_x21(v_body_2417_);
                    v___x_2442_ = l_Lean_Expr_appArg_x21(v___x_2441_);
                    crate::leanh::lean_dec_ref(v___x_2441_);
                    v___x_2443_ = l_Lean_Expr_appArg_x21(v_body_2417_);
                    if v_inv_2413_ == 0 {
                        crate::leanh::lean_inc_ref(v___x_2442_);
                        v___y_2445_ = v___x_2442_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc_ref(v___x_2443_);
                        v___y_2445_ = v___x_2443_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2426_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2426_, 0, v___y_2424_);
                crate::leanh::lean_ctor_set(v___x_2426_, 1, v_thmDeclName_2425_);
                v___x_2427_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2427_, 0, v___x_2426_);
                return v___x_2427_;
            }
            2 => {
                v___x_2446_ = l_Lean_Expr_getAppFn(v___y_2445_);
                crate::leanh::lean_dec_ref(v___y_2445_);
                v___x_2447_ = l_Lean_Expr_constName_x3f(v___x_2446_);
                crate::leanh::lean_dec_ref(v___x_2446_);
                if crate::leanh::lean_obj_tag(v___x_2447_) == 1 {
                    if v_inv_2413_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2443_);
                        crate::leanh::lean_dec_ref(v___x_2442_);
                        crate::leanh::lean_dec(v_levelParams_2415_);
                        crate::leanh::lean_dec_ref(v___x_2412_);
                        v_val_2448_ = crate::leanh::lean_ctor_get(v___x_2447_, 0);
                        crate::leanh::lean_inc(v_val_2448_);
                        crate::leanh::lean_dec_ref_known(v___x_2447_, 1);
                        v___y_2424_ = v_val_2448_;
                        v_thmDeclName_2425_ = v_declName_2414_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_declName_2414_);
                        v_val_2449_ = crate::leanh::lean_ctor_get(v___x_2447_, 0);
                        crate::leanh::lean_inc(v_val_2449_);
                        crate::leanh::lean_dec_ref_known(v___x_2447_, 1);
                        v___x_2450_ = l_Lean_Meta_mkEq(
                            v___x_2443_,
                            v___x_2442_,
                            v___y_2418_,
                            v___y_2419_,
                            v___y_2420_,
                            v___y_2421_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2450_) == 0 {
                            v_a_2451_ = crate::leanh::lean_ctor_get(v___x_2450_, 0);
                            crate::leanh::lean_inc(v_a_2451_);
                            crate::leanh::lean_dec_ref_known(v___x_2450_, 1);
                            v___x_2452_ = 0;
                            v___x_2453_ = 1;
                            v___x_2454_ = l_Lean_Meta_mkForallFVars(
                                v_xs_2416_,
                                v_a_2451_,
                                v___x_2452_,
                                v___x_2430_,
                                v___x_2430_,
                                v___x_2453_,
                                v___y_2418_,
                                v___y_2419_,
                                v___y_2420_,
                                v___y_2421_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2454_) == 0 {
                                v_a_2455_ = crate::leanh::lean_ctor_get(v___x_2454_, 0);
                                crate::leanh::lean_inc(v_a_2455_);
                                crate::leanh::lean_dec_ref_known(v___x_2454_, 1);
                                v___x_2456_ = l_Lean_mkAppN(v___x_2412_, v_xs_2416_);
                                v___x_2457_ = l_Lean_Meta_mkEqSymm(
                                    v___x_2456_,
                                    v___y_2418_,
                                    v___y_2419_,
                                    v___y_2420_,
                                    v___y_2421_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2457_) == 0 {
                                    v_a_2458_ = crate::leanh::lean_ctor_get(v___x_2457_, 0);
                                    crate::leanh::lean_inc(v_a_2458_);
                                    crate::leanh::lean_dec_ref_known(v___x_2457_, 1);
                                    v___x_2459_ = l_Lean_Meta_mkLambdaFVars(
                                        v_xs_2416_,
                                        v_a_2458_,
                                        v___x_2452_,
                                        v___x_2430_,
                                        v___x_2452_,
                                        v___x_2430_,
                                        v___x_2453_,
                                        v___y_2418_,
                                        v___y_2419_,
                                        v___y_2420_,
                                        v___y_2421_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2459_) == 0 {
                                        v_a_2460_ = crate::leanh::lean_ctor_get(v___x_2459_, 0);
                                        crate::leanh::lean_inc(v_a_2460_);
                                        crate::leanh::lean_dec_ref_known(v___x_2459_, 1);
                                        v___x_2461_ = l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__10;
                                        v___x_2462_ = l_Lean_Meta_mkAuxLemma(
                                            v_levelParams_2415_,
                                            v_a_2455_,
                                            v_a_2460_,
                                            v___x_2461_,
                                            v___x_2430_,
                                            v___x_2452_,
                                            v___x_2452_,
                                            v___x_2452_,
                                            v___y_2418_,
                                            v___y_2419_,
                                            v___y_2420_,
                                            v___y_2421_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_2462_) == 0 {
                                            v_a_2463_ = crate::leanh::lean_ctor_get(v___x_2462_, 0);
                                            crate::leanh::lean_inc(v_a_2463_);
                                            crate::leanh::lean_dec_ref_known(v___x_2462_, 1);
                                            v___y_2424_ = v_val_2449_;
                                            v_thmDeclName_2425_ = v_a_2463_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v_val_2449_);
                                            v_a_2464_ = crate::leanh::lean_ctor_get(v___x_2462_, 0);
                                            v_isSharedCheck_2471_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_2462_))
                                                    as u8;
                                            if v_isSharedCheck_2471_ == 0 {
                                                v___x_2466_ = v___x_2462_;
                                                v_isShared_2467_ = v_isSharedCheck_2471_;
                                                state = 3;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_2464_);
                                                crate::leanh::lean_dec(v___x_2462_);
                                                v___x_2466_ = crate::leanh::lean_box(0);
                                                v_isShared_2467_ = v_isSharedCheck_2471_;
                                                state = 3;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_2455_);
                                        crate::leanh::lean_dec(v_val_2449_);
                                        crate::leanh::lean_dec(v_levelParams_2415_);
                                        v_a_2472_ = crate::leanh::lean_ctor_get(v___x_2459_, 0);
                                        v_isSharedCheck_2479_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2459_)) as u8;
                                        if v_isSharedCheck_2479_ == 0 {
                                            v___x_2474_ = v___x_2459_;
                                            v_isShared_2475_ = v_isSharedCheck_2479_;
                                            state = 5;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2472_);
                                            crate::leanh::lean_dec(v___x_2459_);
                                            v___x_2474_ = crate::leanh::lean_box(0);
                                            v_isShared_2475_ = v_isSharedCheck_2479_;
                                            state = 5;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_2455_);
                                    crate::leanh::lean_dec(v_val_2449_);
                                    crate::leanh::lean_dec(v_levelParams_2415_);
                                    v_a_2480_ = crate::leanh::lean_ctor_get(v___x_2457_, 0);
                                    v_isSharedCheck_2487_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2457_)) as u8;
                                    if v_isSharedCheck_2487_ == 0 {
                                        v___x_2482_ = v___x_2457_;
                                        v_isShared_2483_ = v_isSharedCheck_2487_;
                                        state = 7;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2480_);
                                        crate::leanh::lean_dec(v___x_2457_);
                                        v___x_2482_ = crate::leanh::lean_box(0);
                                        v_isShared_2483_ = v_isSharedCheck_2487_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_val_2449_);
                                crate::leanh::lean_dec(v_levelParams_2415_);
                                crate::leanh::lean_dec_ref(v___x_2412_);
                                v_a_2488_ = crate::leanh::lean_ctor_get(v___x_2454_, 0);
                                v_isSharedCheck_2495_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2454_)) as u8;
                                if v_isSharedCheck_2495_ == 0 {
                                    v___x_2490_ = v___x_2454_;
                                    v_isShared_2491_ = v_isSharedCheck_2495_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2488_);
                                    crate::leanh::lean_dec(v___x_2454_);
                                    v___x_2490_ = crate::leanh::lean_box(0);
                                    v_isShared_2491_ = v_isSharedCheck_2495_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_2449_);
                            crate::leanh::lean_dec(v_levelParams_2415_);
                            crate::leanh::lean_dec_ref(v___x_2412_);
                            v_a_2496_ = crate::leanh::lean_ctor_get(v___x_2450_, 0);
                            v_isSharedCheck_2503_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2450_)) as u8;
                            if v_isSharedCheck_2503_ == 0 {
                                v___x_2498_ = v___x_2450_;
                                v_isShared_2499_ = v_isSharedCheck_2503_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2496_);
                                crate::leanh::lean_dec(v___x_2450_);
                                v___x_2498_ = crate::leanh::lean_box(0);
                                v_isShared_2499_ = v_isSharedCheck_2503_;
                                state = 11;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2447_);
                    crate::leanh::lean_dec_ref(v___x_2443_);
                    crate::leanh::lean_dec_ref(v___x_2442_);
                    crate::leanh::lean_dec(v_levelParams_2415_);
                    crate::leanh::lean_dec(v_declName_2414_);
                    v___x_2504_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__12
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__12_once
                        ),
                        _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__12,
                    );
                    v___x_2505_ = l_Lean_MessageData_ofExpr(v___x_2412_);
                    v___x_2506_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2506_, 0, v___x_2504_);
                    crate::leanh::lean_ctor_set(v___x_2506_, 1, v___x_2505_);
                    v___x_2507_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__14
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__14_once
                        ),
                        _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___closed__14,
                    );
                    v___x_2508_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2508_, 0, v___x_2506_);
                    crate::leanh::lean_ctor_set(v___x_2508_, 1, v___x_2507_);
                    v___x_2509_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2___redArg(v___x_2508_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
                    return v___x_2509_;
                }
            }
            3 => {
                if v_isShared_2467_ == 0 {
                    v___x_2469_ = v___x_2466_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2470_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2470_, 0, v_a_2464_);
                    v___x_2469_ = v_reuseFailAlloc_2470_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2469_;
            }
            5 => {
                if v_isShared_2475_ == 0 {
                    v___x_2477_ = v___x_2474_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2478_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
                    v___x_2477_ = v_reuseFailAlloc_2478_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2477_;
            }
            7 => {
                if v_isShared_2483_ == 0 {
                    v___x_2485_ = v___x_2482_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2486_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
                    v___x_2485_ = v_reuseFailAlloc_2486_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2485_;
            }
            9 => {
                if v_isShared_2491_ == 0 {
                    v___x_2493_ = v___x_2490_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2494_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
                    v___x_2493_ = v_reuseFailAlloc_2494_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2493_;
            }
            11 => {
                if v_isShared_2499_ == 0 {
                    v___x_2501_ = v___x_2498_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2502_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
                    v___x_2501_ = v_reuseFailAlloc_2502_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2501_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___boxed(
    mut v_a_2510_: *mut crate::leanh::LeanObject,
    mut v___x_2511_: *mut crate::leanh::LeanObject,
    mut v_inv_2512_: *mut crate::leanh::LeanObject,
    mut v_declName_2513_: *mut crate::leanh::LeanObject,
    mut v_levelParams_2514_: *mut crate::leanh::LeanObject,
    mut v_xs_2515_: *mut crate::leanh::LeanObject,
    mut v_body_2516_: *mut crate::leanh::LeanObject,
    mut v___y_2517_: *mut crate::leanh::LeanObject,
    mut v___y_2518_: *mut crate::leanh::LeanObject,
    mut v___y_2519_: *mut crate::leanh::LeanObject,
    mut v___y_2520_: *mut crate::leanh::LeanObject,
    mut v___y_2521_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inv_boxed_2522_: u8 = 0;
    let mut v_res_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inv_boxed_2522_ = (crate::leanh::lean_unbox(v_inv_2512_) as u8);
    v_res_2523_ = l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0(
        v_a_2510_,
        v___x_2511_,
        v_inv_boxed_2522_,
        v_declName_2513_,
        v_levelParams_2514_,
        v_xs_2515_,
        v_body_2516_,
        v___y_2517_,
        v___y_2518_,
        v___y_2519_,
        v___y_2520_,
    );
    crate::leanh::lean_dec(v___y_2520_);
    crate::leanh::lean_dec_ref(v___y_2519_);
    crate::leanh::lean_dec(v___y_2518_);
    crate::leanh::lean_dec_ref(v___y_2517_);
    crate::leanh::lean_dec_ref(v_body_2516_);
    crate::leanh::lean_dec_ref(v_xs_2515_);
    return v_res_2523_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2524_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2524_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2525_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__0);
    v___x_2526_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2526_, 0, v___x_2525_);
    return v___x_2526_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2527_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__1);
    v___x_2528_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2529_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2529_, 0, v___x_2528_);
    crate::leanh::lean_ctor_set(v___x_2529_, 1, v___x_2528_);
    crate::leanh::lean_ctor_set(v___x_2529_, 2, v___x_2528_);
    crate::leanh::lean_ctor_set(v___x_2529_, 3, v___x_2528_);
    crate::leanh::lean_ctor_set(v___x_2529_, 4, v___x_2527_);
    crate::leanh::lean_ctor_set(v___x_2529_, 5, v___x_2527_);
    crate::leanh::lean_ctor_set(v___x_2529_, 6, v___x_2527_);
    crate::leanh::lean_ctor_set(v___x_2529_, 7, v___x_2527_);
    crate::leanh::lean_ctor_set(v___x_2529_, 8, v___x_2527_);
    crate::leanh::lean_ctor_set(v___x_2529_, 9, v___x_2527_);
    return v___x_2529_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2530_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2531_ = lean_mk_empty_array_with_capacity(v___x_2530_);
    v___x_2532_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2532_, 0, v___x_2531_);
    return v___x_2532_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2533_: usize = 0;
    let mut v___x_2534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2533_ = 5usize;
    v___x_2534_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2535_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_2536_ = lean_mk_empty_array_with_capacity(v___x_2535_);
    v___x_2537_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__3);
    v___x_2538_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_2538_, 0, v___x_2537_);
    crate::leanh::lean_ctor_set(v___x_2538_, 1, v___x_2536_);
    crate::leanh::lean_ctor_set(v___x_2538_, 2, v___x_2534_);
    crate::leanh::lean_ctor_set(v___x_2538_, 3, v___x_2534_);
    crate::leanh::lean_ctor_set_usize(v___x_2538_, 4, v___x_2533_);
    return v___x_2538_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2539_ = crate::leanh::lean_box(1);
    v___x_2540_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4);
    v___x_2541_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__1);
    v___x_2542_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2542_, 0, v___x_2541_);
    crate::leanh::lean_ctor_set(v___x_2542_, 1, v___x_2540_);
    crate::leanh::lean_ctor_set(v___x_2542_, 2, v___x_2539_);
    return v___x_2542_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2544_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__6;
    v___x_2545_ = l_Lean_stringToMessageData(v___x_2544_);
    return v___x_2545_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2547_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__8;
    v___x_2548_ = l_Lean_stringToMessageData(v___x_2547_);
    return v___x_2548_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2550_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__10;
    v___x_2551_ = l_Lean_stringToMessageData(v___x_2550_);
    return v___x_2551_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2553_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__12;
    v___x_2554_ = l_Lean_stringToMessageData(v___x_2553_);
    return v___x_2554_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2556_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__14;
    v___x_2557_ = l_Lean_stringToMessageData(v___x_2556_);
    return v___x_2557_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2559_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__16;
    v___x_2560_ = l_Lean_stringToMessageData(v___x_2559_);
    return v___x_2560_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2562_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__18;
    v___x_2563_ = l_Lean_stringToMessageData(v___x_2562_);
    return v___x_2563_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg(
    mut v_msg_2564_: *mut crate::leanh::LeanObject,
    mut v_declHint_2565_: *mut crate::leanh::LeanObject,
    mut v___y_2566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: u8 = 0;
    let mut v_isExporting_2571_: u8 = 0;
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: u8 = 0;
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2593_: u8 = 0;
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: u8 = 0;
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2625_: u8 = 0;
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2568_ = lean_st_ref_get(v___y_2566_);
                v_env_2569_ = crate::leanh::lean_ctor_get(v___x_2568_, 0);
                crate::leanh::lean_inc_ref(v_env_2569_);
                crate::leanh::lean_dec(v___x_2568_);
                v___x_2570_ = l_Lean_Name_isAnonymous(v_declHint_2565_);
                if v___x_2570_ == 0 {
                    v_isExporting_2571_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_2569_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_2571_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_2569_);
                        crate::leanh::lean_dec(v_declHint_2565_);
                        v___x_2572_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2572_, 0, v_msg_2564_);
                        return v___x_2572_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_2569_);
                        v___x_2573_ = l_Lean_Environment_setExporting(v_env_2569_, v___x_2570_);
                        crate::leanh::lean_inc(v_declHint_2565_);
                        crate::leanh::lean_inc_ref(v___x_2573_);
                        v___x_2574_ = l_Lean_Environment_contains(
                            v___x_2573_,
                            v_declHint_2565_,
                            v_isExporting_2571_,
                        );
                        if v___x_2574_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_2573_);
                            crate::leanh::lean_dec_ref(v_env_2569_);
                            crate::leanh::lean_dec(v_declHint_2565_);
                            v___x_2575_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2575_, 0, v_msg_2564_);
                            return v___x_2575_;
                        } else {
                            v___x_2576_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__2);
                            v___x_2577_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__5);
                            v___x_2578_ = l_Lean_Options_empty;
                            v___x_2579_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2579_, 0, v___x_2573_);
                            crate::leanh::lean_ctor_set(v___x_2579_, 1, v___x_2576_);
                            crate::leanh::lean_ctor_set(v___x_2579_, 2, v___x_2577_);
                            crate::leanh::lean_ctor_set(v___x_2579_, 3, v___x_2578_);
                            crate::leanh::lean_inc(v_declHint_2565_);
                            v___x_2580_ =
                                l_Lean_MessageData_ofConstName(v_declHint_2565_, v___x_2570_);
                            v_c_2581_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_2581_, 0, v___x_2579_);
                            crate::leanh::lean_ctor_set(v_c_2581_, 1, v___x_2580_);
                            v___x_2582_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_2569_,
                                v_declHint_2565_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2582_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_2569_);
                                crate::leanh::lean_dec(v_declHint_2565_);
                                v___x_2583_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__7);
                                v___x_2584_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2584_, 0, v___x_2583_);
                                crate::leanh::lean_ctor_set(v___x_2584_, 1, v_c_2581_);
                                v___x_2585_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__9);
                                v___x_2586_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2586_, 0, v___x_2584_);
                                crate::leanh::lean_ctor_set(v___x_2586_, 1, v___x_2585_);
                                v___x_2587_ = l_Lean_MessageData_note(v___x_2586_);
                                v___x_2588_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2588_, 0, v_msg_2564_);
                                crate::leanh::lean_ctor_set(v___x_2588_, 1, v___x_2587_);
                                v___x_2589_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2589_, 0, v___x_2588_);
                                return v___x_2589_;
                            } else {
                                v_val_2590_ = crate::leanh::lean_ctor_get(v___x_2582_, 0);
                                v_isSharedCheck_2625_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2582_)) as u8;
                                if v_isSharedCheck_2625_ == 0 {
                                    v___x_2592_ = v___x_2582_;
                                    v_isShared_2593_ = v_isSharedCheck_2625_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_2590_);
                                    crate::leanh::lean_dec(v___x_2582_);
                                    v___x_2592_ = crate::leanh::lean_box(0);
                                    v_isShared_2593_ = v_isSharedCheck_2625_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_2569_);
                    crate::leanh::lean_dec(v_declHint_2565_);
                    v___x_2626_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2626_, 0, v_msg_2564_);
                    return v___x_2626_;
                }
            }
            1 => {
                v___x_2594_ = crate::leanh::lean_box(0);
                v___x_2595_ = l_Lean_Environment_header(v_env_2569_);
                crate::leanh::lean_dec_ref(v_env_2569_);
                v___x_2596_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2595_);
                v_mod_2597_ = lean_array_get(v___x_2594_, v___x_2596_, v_val_2590_);
                crate::leanh::lean_dec(v_val_2590_);
                crate::leanh::lean_dec_ref(v___x_2596_);
                v___x_2598_ = l_Lean_isPrivateName(v_declHint_2565_);
                crate::leanh::lean_dec(v_declHint_2565_);
                if v___x_2598_ == 0 {
                    v___x_2599_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__11);
                    v___x_2600_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2600_, 0, v___x_2599_);
                    crate::leanh::lean_ctor_set(v___x_2600_, 1, v_c_2581_);
                    v___x_2601_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__13);
                    v___x_2602_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2602_, 0, v___x_2600_);
                    crate::leanh::lean_ctor_set(v___x_2602_, 1, v___x_2601_);
                    v___x_2603_ = l_Lean_MessageData_ofName(v_mod_2597_);
                    v___x_2604_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2604_, 0, v___x_2602_);
                    crate::leanh::lean_ctor_set(v___x_2604_, 1, v___x_2603_);
                    v___x_2605_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__15);
                    v___x_2606_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2606_, 0, v___x_2604_);
                    crate::leanh::lean_ctor_set(v___x_2606_, 1, v___x_2605_);
                    v___x_2607_ = l_Lean_MessageData_note(v___x_2606_);
                    v___x_2608_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2608_, 0, v_msg_2564_);
                    crate::leanh::lean_ctor_set(v___x_2608_, 1, v___x_2607_);
                    if v_isShared_2593_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2592_, 0);
                        crate::leanh::lean_ctor_set(v___x_2592_, 0, v___x_2608_);
                        v___x_2610_ = v___x_2592_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2611_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2608_);
                        v___x_2610_ = v_reuseFailAlloc_2611_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2612_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__7);
                    v___x_2613_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2613_, 0, v___x_2612_);
                    crate::leanh::lean_ctor_set(v___x_2613_, 1, v_c_2581_);
                    v___x_2614_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__17);
                    v___x_2615_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2615_, 0, v___x_2613_);
                    crate::leanh::lean_ctor_set(v___x_2615_, 1, v___x_2614_);
                    v___x_2616_ = l_Lean_MessageData_ofName(v_mod_2597_);
                    v___x_2617_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2617_, 0, v___x_2615_);
                    crate::leanh::lean_ctor_set(v___x_2617_, 1, v___x_2616_);
                    v___x_2618_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__19);
                    v___x_2619_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2619_, 0, v___x_2617_);
                    crate::leanh::lean_ctor_set(v___x_2619_, 1, v___x_2618_);
                    v___x_2620_ = l_Lean_MessageData_note(v___x_2619_);
                    v___x_2621_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2621_, 0, v_msg_2564_);
                    crate::leanh::lean_ctor_set(v___x_2621_, 1, v___x_2620_);
                    if v_isShared_2593_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_2592_, 0);
                        crate::leanh::lean_ctor_set(v___x_2592_, 0, v___x_2621_);
                        v___x_2623_ = v___x_2592_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2624_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2621_);
                        v___x_2623_ = v_reuseFailAlloc_2624_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2610_;
            }
            3 => {
                return v___x_2623_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___boxed(
    mut v_msg_2627_: *mut crate::leanh::LeanObject,
    mut v_declHint_2628_: *mut crate::leanh::LeanObject,
    mut v___y_2629_: *mut crate::leanh::LeanObject,
    mut v___y_2630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2631_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg(v_msg_2627_, v_declHint_2628_, v___y_2629_);
    crate::leanh::lean_dec(v___y_2629_);
    return v_res_2631_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7(
    mut v_msg_2632_: *mut crate::leanh::LeanObject,
    mut v_declHint_2633_: *mut crate::leanh::LeanObject,
    mut v___y_2634_: *mut crate::leanh::LeanObject,
    mut v___y_2635_: *mut crate::leanh::LeanObject,
    mut v___y_2636_: *mut crate::leanh::LeanObject,
    mut v___y_2637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2643_: u8 = 0;
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2649_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2639_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg(v_msg_2632_, v_declHint_2633_, v___y_2637_);
                v_a_2640_ = crate::leanh::lean_ctor_get(v___x_2639_, 0);
                v_isSharedCheck_2649_ = (!crate::leanh::lean_is_exclusive(v___x_2639_)) as u8;
                if v_isSharedCheck_2649_ == 0 {
                    v___x_2642_ = v___x_2639_;
                    v_isShared_2643_ = v_isSharedCheck_2649_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2640_);
                    crate::leanh::lean_dec(v___x_2639_);
                    v___x_2642_ = crate::leanh::lean_box(0);
                    v_isShared_2643_ = v_isSharedCheck_2649_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2644_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2645_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2645_, 0, v___x_2644_);
                crate::leanh::lean_ctor_set(v___x_2645_, 1, v_a_2640_);
                if v_isShared_2643_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2642_, 0, v___x_2645_);
                    v___x_2647_ = v___x_2642_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2648_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2648_, 0, v___x_2645_);
                    v___x_2647_ = v_reuseFailAlloc_2648_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2647_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7___boxed(
    mut v_msg_2650_: *mut crate::leanh::LeanObject,
    mut v_declHint_2651_: *mut crate::leanh::LeanObject,
    mut v___y_2652_: *mut crate::leanh::LeanObject,
    mut v___y_2653_: *mut crate::leanh::LeanObject,
    mut v___y_2654_: *mut crate::leanh::LeanObject,
    mut v___y_2655_: *mut crate::leanh::LeanObject,
    mut v___y_2656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2657_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7(v_msg_2650_, v_declHint_2651_, v___y_2652_, v___y_2653_, v___y_2654_, v___y_2655_);
    crate::leanh::lean_dec(v___y_2655_);
    crate::leanh::lean_dec_ref(v___y_2654_);
    crate::leanh::lean_dec(v___y_2653_);
    crate::leanh::lean_dec_ref(v___y_2652_);
    return v_res_2657_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__8___redArg(
    mut v_ref_2658_: *mut crate::leanh::LeanObject,
    mut v_msg_2659_: *mut crate::leanh::LeanObject,
    mut v___y_2660_: *mut crate::leanh::LeanObject,
    mut v___y_2661_: *mut crate::leanh::LeanObject,
    mut v___y_2662_: *mut crate::leanh::LeanObject,
    mut v___y_2663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2677_: u8 = 0;
    let mut v_cancelTk_x3f_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2679_: u8 = 0;
    let mut v_inheritedTraceOptions_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_2665_ = crate::leanh::lean_ctor_get(v___y_2662_, 0);
    v_fileMap_2666_ = crate::leanh::lean_ctor_get(v___y_2662_, 1);
    v_options_2667_ = crate::leanh::lean_ctor_get(v___y_2662_, 2);
    v_currRecDepth_2668_ = crate::leanh::lean_ctor_get(v___y_2662_, 3);
    v_maxRecDepth_2669_ = crate::leanh::lean_ctor_get(v___y_2662_, 4);
    v_ref_2670_ = crate::leanh::lean_ctor_get(v___y_2662_, 5);
    v_currNamespace_2671_ = crate::leanh::lean_ctor_get(v___y_2662_, 6);
    v_openDecls_2672_ = crate::leanh::lean_ctor_get(v___y_2662_, 7);
    v_initHeartbeats_2673_ = crate::leanh::lean_ctor_get(v___y_2662_, 8);
    v_maxHeartbeats_2674_ = crate::leanh::lean_ctor_get(v___y_2662_, 9);
    v_quotContext_2675_ = crate::leanh::lean_ctor_get(v___y_2662_, 10);
    v_currMacroScope_2676_ = crate::leanh::lean_ctor_get(v___y_2662_, 11);
    v_diag_2677_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2662_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2678_ = crate::leanh::lean_ctor_get(v___y_2662_, 12);
    v_suppressElabErrors_2679_ = crate::leanh::lean_ctor_get_uint8(
        v___y_2662_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2680_ = crate::leanh::lean_ctor_get(v___y_2662_, 13);
    v_ref_2681_ = l_Lean_replaceRef(v_ref_2658_, v_ref_2670_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_2680_);
    crate::leanh::lean_inc(v_cancelTk_x3f_2678_);
    crate::leanh::lean_inc(v_currMacroScope_2676_);
    crate::leanh::lean_inc(v_quotContext_2675_);
    crate::leanh::lean_inc(v_maxHeartbeats_2674_);
    crate::leanh::lean_inc(v_initHeartbeats_2673_);
    crate::leanh::lean_inc(v_openDecls_2672_);
    crate::leanh::lean_inc(v_currNamespace_2671_);
    crate::leanh::lean_inc(v_maxRecDepth_2669_);
    crate::leanh::lean_inc(v_currRecDepth_2668_);
    crate::leanh::lean_inc_ref(v_options_2667_);
    crate::leanh::lean_inc_ref(v_fileMap_2666_);
    crate::leanh::lean_inc_ref(v_fileName_2665_);
    v___x_2682_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_2682_, 0, v_fileName_2665_);
    crate::leanh::lean_ctor_set(v___x_2682_, 1, v_fileMap_2666_);
    crate::leanh::lean_ctor_set(v___x_2682_, 2, v_options_2667_);
    crate::leanh::lean_ctor_set(v___x_2682_, 3, v_currRecDepth_2668_);
    crate::leanh::lean_ctor_set(v___x_2682_, 4, v_maxRecDepth_2669_);
    crate::leanh::lean_ctor_set(v___x_2682_, 5, v_ref_2681_);
    crate::leanh::lean_ctor_set(v___x_2682_, 6, v_currNamespace_2671_);
    crate::leanh::lean_ctor_set(v___x_2682_, 7, v_openDecls_2672_);
    crate::leanh::lean_ctor_set(v___x_2682_, 8, v_initHeartbeats_2673_);
    crate::leanh::lean_ctor_set(v___x_2682_, 9, v_maxHeartbeats_2674_);
    crate::leanh::lean_ctor_set(v___x_2682_, 10, v_quotContext_2675_);
    crate::leanh::lean_ctor_set(v___x_2682_, 11, v_currMacroScope_2676_);
    crate::leanh::lean_ctor_set(v___x_2682_, 12, v_cancelTk_x3f_2678_);
    crate::leanh::lean_ctor_set(v___x_2682_, 13, v_inheritedTraceOptions_2680_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_2682_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_2677_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_2682_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2679_,
    );
    v___x_2683_ =
        l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2___redArg(
            v_msg_2659_,
            v___y_2660_,
            v___y_2661_,
            v___x_2682_,
            v___y_2663_,
        );
    crate::leanh::lean_dec_ref_known(v___x_2682_, 14);
    return v___x_2683_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__8___redArg___boxed(
    mut v_ref_2684_: *mut crate::leanh::LeanObject,
    mut v_msg_2685_: *mut crate::leanh::LeanObject,
    mut v___y_2686_: *mut crate::leanh::LeanObject,
    mut v___y_2687_: *mut crate::leanh::LeanObject,
    mut v___y_2688_: *mut crate::leanh::LeanObject,
    mut v___y_2689_: *mut crate::leanh::LeanObject,
    mut v___y_2690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2691_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__8___redArg(v_ref_2684_, v_msg_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
    crate::leanh::lean_dec(v___y_2689_);
    crate::leanh::lean_dec_ref(v___y_2688_);
    crate::leanh::lean_dec(v___y_2687_);
    crate::leanh::lean_dec_ref(v___y_2686_);
    crate::leanh::lean_dec(v_ref_2684_);
    return v_res_2691_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6___redArg(
    mut v_ref_2692_: *mut crate::leanh::LeanObject,
    mut v_msg_2693_: *mut crate::leanh::LeanObject,
    mut v_declHint_2694_: *mut crate::leanh::LeanObject,
    mut v___y_2695_: *mut crate::leanh::LeanObject,
    mut v___y_2696_: *mut crate::leanh::LeanObject,
    mut v___y_2697_: *mut crate::leanh::LeanObject,
    mut v___y_2698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2700_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7(v_msg_2693_, v_declHint_2694_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
    v_a_2701_ = crate::leanh::lean_ctor_get(v___x_2700_, 0);
    crate::leanh::lean_inc(v_a_2701_);
    crate::leanh::lean_dec_ref(v___x_2700_);
    v___x_2702_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__8___redArg(v_ref_2692_, v_a_2701_, v___y_2695_, v___y_2696_, v___y_2697_, v___y_2698_);
    return v___x_2702_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6___redArg___boxed(
    mut v_ref_2703_: *mut crate::leanh::LeanObject,
    mut v_msg_2704_: *mut crate::leanh::LeanObject,
    mut v_declHint_2705_: *mut crate::leanh::LeanObject,
    mut v___y_2706_: *mut crate::leanh::LeanObject,
    mut v___y_2707_: *mut crate::leanh::LeanObject,
    mut v___y_2708_: *mut crate::leanh::LeanObject,
    mut v___y_2709_: *mut crate::leanh::LeanObject,
    mut v___y_2710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2711_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6___redArg(v_ref_2703_, v_msg_2704_, v_declHint_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
    crate::leanh::lean_dec(v___y_2709_);
    crate::leanh::lean_dec_ref(v___y_2708_);
    crate::leanh::lean_dec(v___y_2707_);
    crate::leanh::lean_dec_ref(v___y_2706_);
    crate::leanh::lean_dec(v_ref_2703_);
    return v_res_2711_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2713_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__0;
    v___x_2714_ = l_Lean_stringToMessageData(v___x_2713_);
    return v___x_2714_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2716_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__2;
    v___x_2717_ = l_Lean_stringToMessageData(v___x_2716_);
    return v___x_2717_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg(
    mut v_ref_2718_: *mut crate::leanh::LeanObject,
    mut v_constName_2719_: *mut crate::leanh::LeanObject,
    mut v___y_2720_: *mut crate::leanh::LeanObject,
    mut v___y_2721_: *mut crate::leanh::LeanObject,
    mut v___y_2722_: *mut crate::leanh::LeanObject,
    mut v___y_2723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: u8 = 0;
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2725_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__1);
    v___x_2726_ = 0;
    crate::leanh::lean_inc(v_constName_2719_);
    v___x_2727_ = l_Lean_MessageData_ofConstName(v_constName_2719_, v___x_2726_);
    v___x_2728_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2728_, 0, v___x_2725_);
    crate::leanh::lean_ctor_set(v___x_2728_, 1, v___x_2727_);
    v___x_2729_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__3);
    v___x_2730_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2730_, 0, v___x_2728_);
    crate::leanh::lean_ctor_set(v___x_2730_, 1, v___x_2729_);
    v___x_2731_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6___redArg(v_ref_2718_, v___x_2730_, v_constName_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
    return v___x_2731_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_ref_2732_: *mut crate::leanh::LeanObject,
    mut v_constName_2733_: *mut crate::leanh::LeanObject,
    mut v___y_2734_: *mut crate::leanh::LeanObject,
    mut v___y_2735_: *mut crate::leanh::LeanObject,
    mut v___y_2736_: *mut crate::leanh::LeanObject,
    mut v___y_2737_: *mut crate::leanh::LeanObject,
    mut v___y_2738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2739_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg(v_ref_2732_, v_constName_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
    crate::leanh::lean_dec(v___y_2737_);
    crate::leanh::lean_dec_ref(v___y_2736_);
    crate::leanh::lean_dec(v___y_2735_);
    crate::leanh::lean_dec_ref(v___y_2734_);
    crate::leanh::lean_dec(v_ref_2732_);
    return v_res_2739_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0___redArg(
    mut v_constName_2740_: *mut crate::leanh::LeanObject,
    mut v___y_2741_: *mut crate::leanh::LeanObject,
    mut v___y_2742_: *mut crate::leanh::LeanObject,
    mut v___y_2743_: *mut crate::leanh::LeanObject,
    mut v___y_2744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_2746_ = crate::leanh::lean_ctor_get(v___y_2743_, 5);
    v___x_2747_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg(v_ref_2746_, v_constName_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
    return v___x_2747_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0___redArg___boxed(
    mut v_constName_2748_: *mut crate::leanh::LeanObject,
    mut v___y_2749_: *mut crate::leanh::LeanObject,
    mut v___y_2750_: *mut crate::leanh::LeanObject,
    mut v___y_2751_: *mut crate::leanh::LeanObject,
    mut v___y_2752_: *mut crate::leanh::LeanObject,
    mut v___y_2753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2754_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0___redArg(v_constName_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
    crate::leanh::lean_dec(v___y_2752_);
    crate::leanh::lean_dec_ref(v___y_2751_);
    crate::leanh::lean_dec(v___y_2750_);
    crate::leanh::lean_dec_ref(v___y_2749_);
    return v_res_2754_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0(
    mut v_constName_2755_: *mut crate::leanh::LeanObject,
    mut v___y_2756_: *mut crate::leanh::LeanObject,
    mut v___y_2757_: *mut crate::leanh::LeanObject,
    mut v___y_2758_: *mut crate::leanh::LeanObject,
    mut v___y_2759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: u8 = 0;
    let mut v___x_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2769_: u8 = 0;
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2773_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2761_ = lean_st_ref_get(v___y_2759_);
                v_env_2762_ = crate::leanh::lean_ctor_get(v___x_2761_, 0);
                crate::leanh::lean_inc_ref(v_env_2762_);
                crate::leanh::lean_dec(v___x_2761_);
                v___x_2763_ = 0;
                crate::leanh::lean_inc(v_constName_2755_);
                v___x_2764_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_2762_,
                    v_constName_2755_,
                    v___x_2763_,
                );
                if crate::leanh::lean_obj_tag(v___x_2764_) == 0 {
                    v___x_2765_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0___redArg(v_constName_2755_, v___y_2756_, v___y_2757_, v___y_2758_, v___y_2759_);
                    return v___x_2765_;
                } else {
                    crate::leanh::lean_dec(v_constName_2755_);
                    v_val_2766_ = crate::leanh::lean_ctor_get(v___x_2764_, 0);
                    v_isSharedCheck_2773_ = (!crate::leanh::lean_is_exclusive(v___x_2764_)) as u8;
                    if v_isSharedCheck_2773_ == 0 {
                        v___x_2768_ = v___x_2764_;
                        v_isShared_2769_ = v_isSharedCheck_2773_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2766_);
                        crate::leanh::lean_dec(v___x_2764_);
                        v___x_2768_ = crate::leanh::lean_box(0);
                        v_isShared_2769_ = v_isSharedCheck_2773_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2769_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2768_, 0);
                    v___x_2771_ = v___x_2768_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2772_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2772_, 0, v_val_2766_);
                    v___x_2771_ = v_reuseFailAlloc_2772_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2771_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0___boxed(
    mut v_constName_2774_: *mut crate::leanh::LeanObject,
    mut v___y_2775_: *mut crate::leanh::LeanObject,
    mut v___y_2776_: *mut crate::leanh::LeanObject,
    mut v___y_2777_: *mut crate::leanh::LeanObject,
    mut v___y_2778_: *mut crate::leanh::LeanObject,
    mut v___y_2779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2780_ = l_Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0(
        v_constName_2774_,
        v___y_2775_,
        v___y_2776_,
        v___y_2777_,
        v___y_2778_,
    );
    crate::leanh::lean_dec(v___y_2778_);
    crate::leanh::lean_dec_ref(v___y_2777_);
    crate::leanh::lean_dec(v___y_2776_);
    crate::leanh::lean_dec_ref(v___y_2775_);
    return v_res_2780_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__1(
    mut v_a_2781_: *mut crate::leanh::LeanObject,
    mut v_a_2782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2788_: u8 = 0;
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2794_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_2781_) == 0 {
                    v___x_2783_ = l_List_reverse___redArg(v_a_2782_);
                    return v___x_2783_;
                } else {
                    v_head_2784_ = crate::leanh::lean_ctor_get(v_a_2781_, 0);
                    v_tail_2785_ = crate::leanh::lean_ctor_get(v_a_2781_, 1);
                    v_isSharedCheck_2794_ = (!crate::leanh::lean_is_exclusive(v_a_2781_)) as u8;
                    if v_isSharedCheck_2794_ == 0 {
                        v___x_2787_ = v_a_2781_;
                        v_isShared_2788_ = v_isSharedCheck_2794_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2785_);
                        crate::leanh::lean_inc(v_head_2784_);
                        crate::leanh::lean_dec(v_a_2781_);
                        v___x_2787_ = crate::leanh::lean_box(0);
                        v_isShared_2788_ = v_isSharedCheck_2794_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2789_ = l_Lean_mkLevelParam(v_head_2784_);
                if v_isShared_2788_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2787_, 1, v_a_2782_);
                    crate::leanh::lean_ctor_set(v___x_2787_, 0, v___x_2789_);
                    v___x_2791_ = v___x_2787_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2793_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2789_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2793_, 1, v_a_2782_);
                    v___x_2791_ = v_reuseFailAlloc_2793_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_2781_ = v_tail_2785_;
                v_a_2782_ = v___x_2791_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2796_ = l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___closed__0;
    v___x_2797_ = l_Lean_stringToMessageData(v___x_2796_);
    return v___x_2797_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst(
    mut v_declName_2798_: *mut crate::leanh::LeanObject,
    mut v_inv_2799_: u8,
    mut v_a_2800_: *mut crate::leanh::LeanObject,
    mut v_a_2801_: *mut crate::leanh::LeanObject,
    mut v_a_2802_: *mut crate::leanh::LeanObject,
    mut v_a_2803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2810_: u8 = 0;
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: u8 = 0;
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2834_: u8 = 0;
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2841_: u8 = 0;
    let mut v_a_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2845_: u8 = 0;
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2849_: u8 = 0;
    let mut v_a_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2853_: u8 = 0;
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2857_: u8 = 0;
    let mut v___x_2858_: u8 = 0;
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2866_: u8 = 0;
    let mut v___x_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2870_: u8 = 0;
    let mut v_a_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2874_: u8 = 0;
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2878_: u8 = 0;
    let mut v_a_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2882_: u8 = 0;
    let mut v___x_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2886_: u8 = 0;
    let mut v_isSharedCheck_2887_: u8 = 0;
    let mut v_unused_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2893_: u8 = 0;
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2897_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_declName_2798_);
                v___x_2805_ =
                    l_Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0(
                        v_declName_2798_,
                        v_a_2800_,
                        v_a_2801_,
                        v_a_2802_,
                        v_a_2803_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2805_) == 0 {
                    v_a_2806_ = crate::leanh::lean_ctor_get(v___x_2805_, 0);
                    crate::leanh::lean_inc(v_a_2806_);
                    crate::leanh::lean_dec_ref_known(v___x_2805_, 1);
                    v_levelParams_2807_ = crate::leanh::lean_ctor_get(v_a_2806_, 1);
                    v_isSharedCheck_2887_ = (!crate::leanh::lean_is_exclusive(v_a_2806_)) as u8;
                    if v_isSharedCheck_2887_ == 0 {
                        v_unused_2888_ = crate::leanh::lean_ctor_get(v_a_2806_, 2);
                        crate::leanh::lean_dec(v_unused_2888_);
                        v_unused_2889_ = crate::leanh::lean_ctor_get(v_a_2806_, 0);
                        crate::leanh::lean_dec(v_unused_2889_);
                        v___x_2809_ = v_a_2806_;
                        v_isShared_2810_ = v_isSharedCheck_2887_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_levelParams_2807_);
                        crate::leanh::lean_dec(v_a_2806_);
                        v___x_2809_ = crate::leanh::lean_box(0);
                        v_isShared_2810_ = v_isSharedCheck_2887_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_2798_);
                    v_a_2890_ = crate::leanh::lean_ctor_get(v___x_2805_, 0);
                    v_isSharedCheck_2897_ = (!crate::leanh::lean_is_exclusive(v___x_2805_)) as u8;
                    if v_isSharedCheck_2897_ == 0 {
                        v___x_2892_ = v___x_2805_;
                        v_isShared_2893_ = v_isSharedCheck_2897_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2890_);
                        crate::leanh::lean_dec(v___x_2805_);
                        v___x_2892_ = crate::leanh::lean_box(0);
                        v_isShared_2893_ = v_isSharedCheck_2897_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2811_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v_levelParams_2807_);
                v___x_2812_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__1(
                        v_levelParams_2807_,
                        v___x_2811_,
                    );
                crate::leanh::lean_inc(v_declName_2798_);
                v___x_2813_ = l_Lean_mkConst(v_declName_2798_, v___x_2812_);
                crate::leanh::lean_inc(v_a_2803_);
                crate::leanh::lean_inc_ref(v_a_2802_);
                crate::leanh::lean_inc(v_a_2801_);
                crate::leanh::lean_inc_ref(v_a_2800_);
                crate::leanh::lean_inc_ref(v___x_2813_);
                v___x_2814_ =
                    lean_infer_type(v___x_2813_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
                if crate::leanh::lean_obj_tag(v___x_2814_) == 0 {
                    v_a_2815_ = crate::leanh::lean_ctor_get(v___x_2814_, 0);
                    crate::leanh::lean_inc_n(v_a_2815_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2814_, 1);
                    v___x_2816_ =
                        l_Lean_Meta_isProp(v_a_2815_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
                    if crate::leanh::lean_obj_tag(v___x_2816_) == 0 {
                        v_a_2817_ = crate::leanh::lean_ctor_get(v___x_2816_, 0);
                        crate::leanh::lean_inc(v_a_2817_);
                        crate::leanh::lean_dec_ref_known(v___x_2816_, 1);
                        v___x_2818_ = crate::leanh::lean_box((v_inv_2799_) as usize);
                        crate::leanh::lean_inc(v_declName_2798_);
                        crate::leanh::lean_inc_ref(v___x_2813_);
                        crate::leanh::lean_inc(v_a_2815_);
                        v___f_2819_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___lam__0___boxed
                                as *mut core::ffi::c_void,
                            12,
                            5,
                        );
                        crate::leanh::lean_closure_set(v___f_2819_, 0, v_a_2815_);
                        crate::leanh::lean_closure_set(v___f_2819_, 1, v___x_2813_);
                        crate::leanh::lean_closure_set(v___f_2819_, 2, v___x_2818_);
                        crate::leanh::lean_closure_set(v___f_2819_, 3, v_declName_2798_);
                        crate::leanh::lean_closure_set(v___f_2819_, 4, v_levelParams_2807_);
                        v___x_2858_ = (crate::leanh::lean_unbox(v_a_2817_) as u8);
                        crate::leanh::lean_dec(v_a_2817_);
                        if v___x_2858_ == 0 {
                            crate::leanh::lean_dec_ref(v___f_2819_);
                            crate::leanh::lean_dec(v_a_2815_);
                            crate::leanh::lean_del_object(v___x_2809_);
                            crate::leanh::lean_dec(v_declName_2798_);
                            v___x_2859_ = l_Lean_MessageData_ofExpr(v___x_2813_);
                            v___x_2860_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___closed__1
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___closed__1_once
                                ),
                                _init_l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___closed__1,
                            );
                            v___x_2861_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2861_, 0, v___x_2859_);
                            crate::leanh::lean_ctor_set(v___x_2861_, 1, v___x_2860_);
                            v___x_2862_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2___redArg(v___x_2861_, v_a_2800_, v_a_2801_, v_a_2802_, v_a_2803_);
                            v_a_2863_ = crate::leanh::lean_ctor_get(v___x_2862_, 0);
                            v_isSharedCheck_2870_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2862_)) as u8;
                            if v_isSharedCheck_2870_ == 0 {
                                v___x_2865_ = v___x_2862_;
                                v_isShared_2866_ = v_isSharedCheck_2870_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2863_);
                                crate::leanh::lean_dec(v___x_2862_);
                                v___x_2865_ = crate::leanh::lean_box(0);
                                v_isShared_2866_ = v_isSharedCheck_2870_;
                                state = 10;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2813_);
                            v___y_2821_ = v_a_2800_;
                            v___y_2822_ = v_a_2801_;
                            v___y_2823_ = v_a_2802_;
                            v___y_2824_ = v_a_2803_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2815_);
                        crate::leanh::lean_dec_ref(v___x_2813_);
                        crate::leanh::lean_del_object(v___x_2809_);
                        crate::leanh::lean_dec(v_levelParams_2807_);
                        crate::leanh::lean_dec(v_declName_2798_);
                        v_a_2871_ = crate::leanh::lean_ctor_get(v___x_2816_, 0);
                        v_isSharedCheck_2878_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2816_)) as u8;
                        if v_isSharedCheck_2878_ == 0 {
                            v___x_2873_ = v___x_2816_;
                            v_isShared_2874_ = v_isSharedCheck_2878_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2871_);
                            crate::leanh::lean_dec(v___x_2816_);
                            v___x_2873_ = crate::leanh::lean_box(0);
                            v_isShared_2874_ = v_isSharedCheck_2878_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2813_);
                    crate::leanh::lean_del_object(v___x_2809_);
                    crate::leanh::lean_dec(v_levelParams_2807_);
                    crate::leanh::lean_dec(v_declName_2798_);
                    v_a_2879_ = crate::leanh::lean_ctor_get(v___x_2814_, 0);
                    v_isSharedCheck_2886_ = (!crate::leanh::lean_is_exclusive(v___x_2814_)) as u8;
                    if v_isSharedCheck_2886_ == 0 {
                        v___x_2881_ = v___x_2814_;
                        v_isShared_2882_ = v_isSharedCheck_2886_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2879_);
                        crate::leanh::lean_dec(v___x_2814_);
                        v___x_2881_ = crate::leanh::lean_box(0);
                        v_isShared_2882_ = v_isSharedCheck_2886_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2825_ = 0;
                v___x_2826_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__3___redArg(v_a_2815_, v___f_2819_, v___x_2825_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_);
                if crate::leanh::lean_obj_tag(v___x_2826_) == 0 {
                    v_a_2827_ = crate::leanh::lean_ctor_get(v___x_2826_, 0);
                    crate::leanh::lean_inc(v_a_2827_);
                    crate::leanh::lean_dec_ref_known(v___x_2826_, 1);
                    v_fst_2828_ = crate::leanh::lean_ctor_get(v_a_2827_, 0);
                    crate::leanh::lean_inc(v_fst_2828_);
                    v_snd_2829_ = crate::leanh::lean_ctor_get(v_a_2827_, 1);
                    crate::leanh::lean_inc(v_snd_2829_);
                    crate::leanh::lean_dec(v_a_2827_);
                    v___x_2830_ = l_Lean_Meta_Sym_Simp_mkTheoremFromDecl(
                        v_snd_2829_,
                        v___y_2821_,
                        v___y_2822_,
                        v___y_2823_,
                        v___y_2824_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2830_) == 0 {
                        v_a_2831_ = crate::leanh::lean_ctor_get(v___x_2830_, 0);
                        v_isSharedCheck_2841_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2830_)) as u8;
                        if v_isSharedCheck_2841_ == 0 {
                            v___x_2833_ = v___x_2830_;
                            v_isShared_2834_ = v_isSharedCheck_2841_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2831_);
                            crate::leanh::lean_dec(v___x_2830_);
                            v___x_2833_ = crate::leanh::lean_box(0);
                            v_isShared_2834_ = v_isSharedCheck_2841_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fst_2828_);
                        crate::leanh::lean_del_object(v___x_2809_);
                        crate::leanh::lean_dec(v_declName_2798_);
                        v_a_2842_ = crate::leanh::lean_ctor_get(v___x_2830_, 0);
                        v_isSharedCheck_2849_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2830_)) as u8;
                        if v_isSharedCheck_2849_ == 0 {
                            v___x_2844_ = v___x_2830_;
                            v_isShared_2845_ = v_isSharedCheck_2849_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2842_);
                            crate::leanh::lean_dec(v___x_2830_);
                            v___x_2844_ = crate::leanh::lean_box(0);
                            v_isShared_2845_ = v_isSharedCheck_2849_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2809_);
                    crate::leanh::lean_dec(v_declName_2798_);
                    v_a_2850_ = crate::leanh::lean_ctor_get(v___x_2826_, 0);
                    v_isSharedCheck_2857_ = (!crate::leanh::lean_is_exclusive(v___x_2826_)) as u8;
                    if v_isSharedCheck_2857_ == 0 {
                        v___x_2852_ = v___x_2826_;
                        v_isShared_2853_ = v_isSharedCheck_2857_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2850_);
                        crate::leanh::lean_dec(v___x_2826_);
                        v___x_2852_ = crate::leanh::lean_box(0);
                        v_isShared_2853_ = v_isSharedCheck_2857_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2810_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2809_, 2, v_a_2831_);
                    crate::leanh::lean_ctor_set(v___x_2809_, 1, v_fst_2828_);
                    crate::leanh::lean_ctor_set(v___x_2809_, 0, v_declName_2798_);
                    v___x_2836_ = v___x_2809_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2840_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_declName_2798_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 1, v_fst_2828_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2840_, 2, v_a_2831_);
                    v___x_2836_ = v_reuseFailAlloc_2840_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2834_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2833_, 0, v___x_2836_);
                    v___x_2838_ = v___x_2833_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2839_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2836_);
                    v___x_2838_ = v_reuseFailAlloc_2839_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2838_;
            }
            6 => {
                if v_isShared_2845_ == 0 {
                    v___x_2847_ = v___x_2844_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2848_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
                    v___x_2847_ = v_reuseFailAlloc_2848_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2847_;
            }
            8 => {
                if v_isShared_2853_ == 0 {
                    v___x_2855_ = v___x_2852_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2856_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
                    v___x_2855_ = v_reuseFailAlloc_2856_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2855_;
            }
            10 => {
                if v_isShared_2866_ == 0 {
                    v___x_2868_ = v___x_2865_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2869_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
                    v___x_2868_ = v_reuseFailAlloc_2869_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2868_;
            }
            12 => {
                if v_isShared_2874_ == 0 {
                    v___x_2876_ = v___x_2873_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2877_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
                    v___x_2876_ = v_reuseFailAlloc_2877_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2876_;
            }
            14 => {
                if v_isShared_2882_ == 0 {
                    v___x_2884_ = v___x_2881_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2885_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
                    v___x_2884_ = v_reuseFailAlloc_2885_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2884_;
            }
            16 => {
                if v_isShared_2893_ == 0 {
                    v___x_2895_ = v___x_2892_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_2896_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2890_);
                    v___x_2895_ = v_reuseFailAlloc_2896_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_2895_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst___boxed(
    mut v_declName_2898_: *mut crate::leanh::LeanObject,
    mut v_inv_2899_: *mut crate::leanh::LeanObject,
    mut v_a_2900_: *mut crate::leanh::LeanObject,
    mut v_a_2901_: *mut crate::leanh::LeanObject,
    mut v_a_2902_: *mut crate::leanh::LeanObject,
    mut v_a_2903_: *mut crate::leanh::LeanObject,
    mut v_a_2904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_inv_boxed_2905_: u8 = 0;
    let mut v_res_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_inv_boxed_2905_ = (crate::leanh::lean_unbox(v_inv_2899_) as u8);
    v_res_2906_ = l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst(
        v_declName_2898_,
        v_inv_boxed_2905_,
        v_a_2900_,
        v_a_2901_,
        v_a_2902_,
        v_a_2903_,
    );
    crate::leanh::lean_dec(v_a_2903_);
    crate::leanh::lean_dec_ref(v_a_2902_);
    crate::leanh::lean_dec(v_a_2901_);
    crate::leanh::lean_dec_ref(v_a_2900_);
    return v_res_2906_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2(
    mut v_00_u03b1_2907_: *mut crate::leanh::LeanObject,
    mut v_msg_2908_: *mut crate::leanh::LeanObject,
    mut v___y_2909_: *mut crate::leanh::LeanObject,
    mut v___y_2910_: *mut crate::leanh::LeanObject,
    mut v___y_2911_: *mut crate::leanh::LeanObject,
    mut v___y_2912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2914_ =
        l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2___redArg(
            v_msg_2908_,
            v___y_2909_,
            v___y_2910_,
            v___y_2911_,
            v___y_2912_,
        );
    return v___x_2914_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2___boxed(
    mut v_00_u03b1_2915_: *mut crate::leanh::LeanObject,
    mut v_msg_2916_: *mut crate::leanh::LeanObject,
    mut v___y_2917_: *mut crate::leanh::LeanObject,
    mut v___y_2918_: *mut crate::leanh::LeanObject,
    mut v___y_2919_: *mut crate::leanh::LeanObject,
    mut v___y_2920_: *mut crate::leanh::LeanObject,
    mut v___y_2921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2922_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__2(
        v_00_u03b1_2915_,
        v_msg_2916_,
        v___y_2917_,
        v___y_2918_,
        v___y_2919_,
        v___y_2920_,
    );
    crate::leanh::lean_dec(v___y_2920_);
    crate::leanh::lean_dec_ref(v___y_2919_);
    crate::leanh::lean_dec(v___y_2918_);
    crate::leanh::lean_dec_ref(v___y_2917_);
    return v_res_2922_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0(
    mut v_00_u03b1_2923_: *mut crate::leanh::LeanObject,
    mut v_constName_2924_: *mut crate::leanh::LeanObject,
    mut v___y_2925_: *mut crate::leanh::LeanObject,
    mut v___y_2926_: *mut crate::leanh::LeanObject,
    mut v___y_2927_: *mut crate::leanh::LeanObject,
    mut v___y_2928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2930_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0___redArg(v_constName_2924_, v___y_2925_, v___y_2926_, v___y_2927_, v___y_2928_);
    return v___x_2930_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0___boxed(
    mut v_00_u03b1_2931_: *mut crate::leanh::LeanObject,
    mut v_constName_2932_: *mut crate::leanh::LeanObject,
    mut v___y_2933_: *mut crate::leanh::LeanObject,
    mut v___y_2934_: *mut crate::leanh::LeanObject,
    mut v___y_2935_: *mut crate::leanh::LeanObject,
    mut v___y_2936_: *mut crate::leanh::LeanObject,
    mut v___y_2937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2938_ = l_Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0(v_00_u03b1_2931_, v_constName_2932_, v___y_2933_, v___y_2934_, v___y_2935_, v___y_2936_);
    crate::leanh::lean_dec(v___y_2936_);
    crate::leanh::lean_dec_ref(v___y_2935_);
    crate::leanh::lean_dec(v___y_2934_);
    crate::leanh::lean_dec_ref(v___y_2933_);
    return v_res_2938_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2(
    mut v_00_u03b1_2939_: *mut crate::leanh::LeanObject,
    mut v_ref_2940_: *mut crate::leanh::LeanObject,
    mut v_constName_2941_: *mut crate::leanh::LeanObject,
    mut v___y_2942_: *mut crate::leanh::LeanObject,
    mut v___y_2943_: *mut crate::leanh::LeanObject,
    mut v___y_2944_: *mut crate::leanh::LeanObject,
    mut v___y_2945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2947_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg(v_ref_2940_, v_constName_2941_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
    return v___x_2947_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b1_2948_: *mut crate::leanh::LeanObject,
    mut v_ref_2949_: *mut crate::leanh::LeanObject,
    mut v_constName_2950_: *mut crate::leanh::LeanObject,
    mut v___y_2951_: *mut crate::leanh::LeanObject,
    mut v___y_2952_: *mut crate::leanh::LeanObject,
    mut v___y_2953_: *mut crate::leanh::LeanObject,
    mut v___y_2954_: *mut crate::leanh::LeanObject,
    mut v___y_2955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2956_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2(v_00_u03b1_2948_, v_ref_2949_, v_constName_2950_, v___y_2951_, v___y_2952_, v___y_2953_, v___y_2954_);
    crate::leanh::lean_dec(v___y_2954_);
    crate::leanh::lean_dec_ref(v___y_2953_);
    crate::leanh::lean_dec(v___y_2952_);
    crate::leanh::lean_dec_ref(v___y_2951_);
    crate::leanh::lean_dec(v_ref_2949_);
    return v_res_2956_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6(
    mut v_00_u03b1_2957_: *mut crate::leanh::LeanObject,
    mut v_ref_2958_: *mut crate::leanh::LeanObject,
    mut v_msg_2959_: *mut crate::leanh::LeanObject,
    mut v_declHint_2960_: *mut crate::leanh::LeanObject,
    mut v___y_2961_: *mut crate::leanh::LeanObject,
    mut v___y_2962_: *mut crate::leanh::LeanObject,
    mut v___y_2963_: *mut crate::leanh::LeanObject,
    mut v___y_2964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2966_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6___redArg(v_ref_2958_, v_msg_2959_, v_declHint_2960_, v___y_2961_, v___y_2962_, v___y_2963_, v___y_2964_);
    return v___x_2966_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6___boxed(
    mut v_00_u03b1_2967_: *mut crate::leanh::LeanObject,
    mut v_ref_2968_: *mut crate::leanh::LeanObject,
    mut v_msg_2969_: *mut crate::leanh::LeanObject,
    mut v_declHint_2970_: *mut crate::leanh::LeanObject,
    mut v___y_2971_: *mut crate::leanh::LeanObject,
    mut v___y_2972_: *mut crate::leanh::LeanObject,
    mut v___y_2973_: *mut crate::leanh::LeanObject,
    mut v___y_2974_: *mut crate::leanh::LeanObject,
    mut v___y_2975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2976_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6(v_00_u03b1_2967_, v_ref_2968_, v_msg_2969_, v_declHint_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_);
    crate::leanh::lean_dec(v___y_2974_);
    crate::leanh::lean_dec_ref(v___y_2973_);
    crate::leanh::lean_dec(v___y_2972_);
    crate::leanh::lean_dec_ref(v___y_2971_);
    crate::leanh::lean_dec(v_ref_2968_);
    return v_res_2976_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8(
    mut v_msg_2977_: *mut crate::leanh::LeanObject,
    mut v_declHint_2978_: *mut crate::leanh::LeanObject,
    mut v___y_2979_: *mut crate::leanh::LeanObject,
    mut v___y_2980_: *mut crate::leanh::LeanObject,
    mut v___y_2981_: *mut crate::leanh::LeanObject,
    mut v___y_2982_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2984_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg(v_msg_2977_, v_declHint_2978_, v___y_2982_);
    return v___x_2984_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___boxed(
    mut v_msg_2985_: *mut crate::leanh::LeanObject,
    mut v_declHint_2986_: *mut crate::leanh::LeanObject,
    mut v___y_2987_: *mut crate::leanh::LeanObject,
    mut v___y_2988_: *mut crate::leanh::LeanObject,
    mut v___y_2989_: *mut crate::leanh::LeanObject,
    mut v___y_2990_: *mut crate::leanh::LeanObject,
    mut v___y_2991_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2992_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8(v_msg_2985_, v_declHint_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
    crate::leanh::lean_dec(v___y_2990_);
    crate::leanh::lean_dec_ref(v___y_2989_);
    crate::leanh::lean_dec(v___y_2988_);
    crate::leanh::lean_dec_ref(v___y_2987_);
    return v_res_2992_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__8(
    mut v_00_u03b1_2993_: *mut crate::leanh::LeanObject,
    mut v_ref_2994_: *mut crate::leanh::LeanObject,
    mut v_msg_2995_: *mut crate::leanh::LeanObject,
    mut v___y_2996_: *mut crate::leanh::LeanObject,
    mut v___y_2997_: *mut crate::leanh::LeanObject,
    mut v___y_2998_: *mut crate::leanh::LeanObject,
    mut v___y_2999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3001_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__8___redArg(v_ref_2994_, v_msg_2995_, v___y_2996_, v___y_2997_, v___y_2998_, v___y_2999_);
    return v___x_3001_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__8___boxed(
    mut v_00_u03b1_3002_: *mut crate::leanh::LeanObject,
    mut v_ref_3003_: *mut crate::leanh::LeanObject,
    mut v_msg_3004_: *mut crate::leanh::LeanObject,
    mut v___y_3005_: *mut crate::leanh::LeanObject,
    mut v___y_3006_: *mut crate::leanh::LeanObject,
    mut v___y_3007_: *mut crate::leanh::LeanObject,
    mut v___y_3008_: *mut crate::leanh::LeanObject,
    mut v___y_3009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3010_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__8(v_00_u03b1_3002_, v_ref_3003_, v_msg_3004_, v___y_3005_, v___y_3006_, v___y_3007_, v___y_3008_);
    crate::leanh::lean_dec(v___y_3008_);
    crate::leanh::lean_dec_ref(v___y_3007_);
    crate::leanh::lean_dec(v___y_3006_);
    crate::leanh::lean_dec_ref(v___y_3005_);
    crate::leanh::lean_dec(v_ref_3003_);
    return v_res_3010_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3017_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3017_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3018_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__1_once),
        _init_l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__1,
    );
    v___x_3019_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3019_, 0, v___x_3018_);
    return v___x_3019_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry(
    mut v_s_3020_: *mut crate::leanh::LeanObject,
    mut v_e_3021_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lemmas_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3026_: u8 = 0;
    let mut v_appFn_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_thm_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3047_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lemmas_3022_ = crate::leanh::lean_ctor_get(v_s_3020_, 0);
                v_entries_3023_ = crate::leanh::lean_ctor_get(v_s_3020_, 1);
                v_isSharedCheck_3047_ = (!crate::leanh::lean_is_exclusive(v_s_3020_)) as u8;
                if v_isSharedCheck_3047_ == 0 {
                    v___x_3025_ = v_s_3020_;
                    v_isShared_3026_ = v_isSharedCheck_3047_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_entries_3023_);
                    crate::leanh::lean_inc(v_lemmas_3022_);
                    crate::leanh::lean_dec(v_s_3020_);
                    v___x_3025_ = crate::leanh::lean_box(0);
                    v_isShared_3026_ = v_isSharedCheck_3047_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_appFn_3027_ = crate::leanh::lean_ctor_get(v_e_3021_, 1);
                crate::leanh::lean_inc(v_appFn_3027_);
                v_thm_3028_ = crate::leanh::lean_ctor_get(v_e_3021_, 2);
                v___x_3044_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_lemmas_3022_, v_appFn_3027_);
                if crate::leanh::lean_obj_tag(v___x_3044_) == 0 {
                    v___x_3045_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__2_once
                        ),
                        _init_l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__2,
                    );
                    v___y_3040_ = v___x_3045_;
                    state = 4;
                    continue;
                } else {
                    v_val_3046_ = crate::leanh::lean_ctor_get(v___x_3044_, 0);
                    crate::leanh::lean_inc(v_val_3046_);
                    crate::leanh::lean_dec_ref_known(v___x_3044_, 1);
                    v___y_3040_ = v_val_3046_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_thm_3028_);
                v___x_3032_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v___y_3030_, v_thm_3028_);
                crate::leanh::lean_inc(v_appFn_3027_);
                v___x_3033_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_appFn_3027_, v___x_3032_, v_lemmas_3022_);
                v___x_3034_ = lean_array_push(v___y_3031_, v_e_3021_);
                v___x_3035_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_appFn_3027_, v___x_3034_, v_entries_3023_);
                if v_isShared_3026_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3025_, 1, v___x_3035_);
                    crate::leanh::lean_ctor_set(v___x_3025_, 0, v___x_3033_);
                    v___x_3037_ = v___x_3025_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3038_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3033_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3038_, 1, v___x_3035_);
                    v___x_3037_ = v_reuseFailAlloc_3038_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3037_;
            }
            4 => {
                v___x_3041_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_entries_3023_, v_appFn_3027_);
                if crate::leanh::lean_obj_tag(v___x_3041_) == 0 {
                    v___x_3042_ = l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__0;
                    v___y_3030_ = v___y_3040_;
                    v___y_3031_ = v___x_3042_;
                    state = 2;
                    continue;
                } else {
                    v_val_3043_ = crate::leanh::lean_ctor_get(v___x_3041_, 0);
                    crate::leanh::lean_inc(v_val_3043_);
                    crate::leanh::lean_dec_ref_known(v___x_3041_, 1);
                    v___y_3030_ = v___y_3040_;
                    v___y_3031_ = v_val_3043_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__0___redArg(
    mut v_t_3048_: *mut crate::leanh::LeanObject,
    mut v_k_3049_: *mut crate::leanh::LeanObject,
    mut v_fallback_3050_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_3048_) == 0 {
                    v_k_3051_ = crate::leanh::lean_ctor_get(v_t_3048_, 1);
                    v_v_3052_ = crate::leanh::lean_ctor_get(v_t_3048_, 2);
                    v_l_3053_ = crate::leanh::lean_ctor_get(v_t_3048_, 3);
                    v_r_3054_ = crate::leanh::lean_ctor_get(v_t_3048_, 4);
                    v___x_3055_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3049_, v_k_3051_);
                    match v___x_3055_ {
                        0 => {
                            v_t_3048_ = v_l_3053_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            crate::leanh::lean_inc(v_v_3052_);
                            return v_v_3052_;
                        }
                        _ => {
                            v_t_3048_ = v_r_3054_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_fallback_3050_);
                    return v_fallback_3050_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__0___redArg___boxed(
    mut v_t_3058_: *mut crate::leanh::LeanObject,
    mut v_k_3059_: *mut crate::leanh::LeanObject,
    mut v_fallback_3060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3061_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__0___redArg(v_t_3058_, v_k_3059_, v_fallback_3060_);
    crate::leanh::lean_dec(v_fallback_3060_);
    crate::leanh::lean_dec(v_k_3059_);
    crate::leanh::lean_dec(v_t_3058_);
    return v_res_3061_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__2___redArg(
    mut v_k_3062_: *mut crate::leanh::LeanObject,
    mut v_t_3063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3070_: u8 = 0;
    let mut v___x_3071_: u8 = 0;
    let mut v_impl_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: u8 = 0;
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3090_: u8 = 0;
    let mut v_size_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: u8 = 0;
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3102_: u8 = 0;
    let mut v___x_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3127_: u8 = 0;
    let mut v_unused_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3140_: u8 = 0;
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3144_: u8 = 0;
    let mut v_unused_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3151_: u8 = 0;
    let mut v_unused_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3169_: u8 = 0;
    let mut v_size_3170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3179_: u8 = 0;
    let mut v_unused_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3186_: u8 = 0;
    let mut v_k_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3191_: u8 = 0;
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3202_: u8 = 0;
    let mut v_unused_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3206_: u8 = 0;
    let mut v_unused_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3215_: u8 = 0;
    let mut v___x_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3223_: u8 = 0;
    let mut v_unused_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3232_: u8 = 0;
    let mut v___x_3234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3240_: u8 = 0;
    let mut v_unused_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: u8 = 0;
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3260_: u8 = 0;
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: u8 = 0;
    let mut v___x_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3276_: u8 = 0;
    let mut v_size_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: u8 = 0;
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3288_: u8 = 0;
    let mut v___x_3289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3313_: u8 = 0;
    let mut v_unused_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3328_: u8 = 0;
    let mut v_unused_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3336_: u8 = 0;
    let mut v_k_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3354_: u8 = 0;
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3365_: u8 = 0;
    let mut v_unused_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3387_: u8 = 0;
    let mut v_unused_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3393_: u8 = 0;
    let mut v_unused_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3401_: u8 = 0;
    let mut v___x_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tree_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: u8 = 0;
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3417_: u8 = 0;
    let mut v_size_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: u8 = 0;
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3429_: u8 = 0;
    let mut v___x_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3441_: u8 = 0;
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3445_: u8 = 0;
    let mut v_unused_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3464_: u8 = 0;
    let mut v_unused_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3480_: u8 = 0;
    let mut v_unused_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3488_: u8 = 0;
    let mut v_k_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3509_: u8 = 0;
    let mut v_unused_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3517_: u8 = 0;
    let mut v_k_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3524_: u8 = 0;
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3535_: u8 = 0;
    let mut v_unused_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3539_: u8 = 0;
    let mut v_unused_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3551_: u8 = 0;
    let mut v_unused_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: u8 = 0;
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3575_: u8 = 0;
    let mut v_size_3576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: u8 = 0;
    let mut v___x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3587_: u8 = 0;
    let mut v___x_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3613_: u8 = 0;
    let mut v_unused_3614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3627_: u8 = 0;
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3631_: u8 = 0;
    let mut v_unused_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3638_: u8 = 0;
    let mut v_unused_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3656_: u8 = 0;
    let mut v_size_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3666_: u8 = 0;
    let mut v_unused_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3673_: u8 = 0;
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3681_: u8 = 0;
    let mut v_unused_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3690_: u8 = 0;
    let mut v_k_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3695_: u8 = 0;
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3706_: u8 = 0;
    let mut v_unused_3707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3710_: u8 = 0;
    let mut v_unused_3711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3721_: u8 = 0;
    let mut v_unused_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_3063_) == 0 {
                    v_k_3064_ = crate::leanh::lean_ctor_get(v_t_3063_, 1);
                    v_v_3065_ = crate::leanh::lean_ctor_get(v_t_3063_, 2);
                    v_l_3066_ = crate::leanh::lean_ctor_get(v_t_3063_, 3);
                    v_r_3067_ = crate::leanh::lean_ctor_get(v_t_3063_, 4);
                    v_isSharedCheck_3721_ = (!crate::leanh::lean_is_exclusive(v_t_3063_)) as u8;
                    if v_isSharedCheck_3721_ == 0 {
                        v_unused_3722_ = crate::leanh::lean_ctor_get(v_t_3063_, 0);
                        crate::leanh::lean_dec(v_unused_3722_);
                        v___x_3069_ = v_t_3063_;
                        v_isShared_3070_ = v_isSharedCheck_3721_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_3067_);
                        crate::leanh::lean_inc(v_l_3066_);
                        crate::leanh::lean_inc(v_v_3065_);
                        crate::leanh::lean_inc(v_k_3064_);
                        crate::leanh::lean_dec(v_t_3063_);
                        v___x_3069_ = crate::leanh::lean_box(0);
                        v_isShared_3070_ = v_isSharedCheck_3721_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_t_3063_;
                }
            }
            1 => {
                v___x_3071_ =
                    l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3062_, v_k_3064_);
                match v___x_3071_ {
                    0 => {
                        v_impl_3072_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__2___redArg(v_k_3062_, v_l_3066_);
                        v___x_3073_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_impl_3072_) == 0 {
                            if crate::leanh::lean_obj_tag(v_r_3067_) == 0 {
                                v_size_3074_ = crate::leanh::lean_ctor_get(v_impl_3072_, 0);
                                crate::leanh::lean_inc(v_size_3074_);
                                v_size_3075_ = crate::leanh::lean_ctor_get(v_r_3067_, 0);
                                v_k_3076_ = crate::leanh::lean_ctor_get(v_r_3067_, 1);
                                v_v_3077_ = crate::leanh::lean_ctor_get(v_r_3067_, 2);
                                v_l_3078_ = crate::leanh::lean_ctor_get(v_r_3067_, 3);
                                crate::leanh::lean_inc(v_l_3078_);
                                v_r_3079_ = crate::leanh::lean_ctor_get(v_r_3067_, 4);
                                v___x_3080_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_3081_ = lean_nat_mul(v___x_3080_, v_size_3074_);
                                v___x_3082_ = lean_nat_dec_lt(v___x_3081_, v_size_3075_);
                                crate::leanh::lean_dec(v___x_3081_);
                                if v___x_3082_ == 0 {
                                    crate::leanh::lean_dec(v_l_3078_);
                                    v___x_3083_ = lean_nat_add(v___x_3073_, v_size_3074_);
                                    crate::leanh::lean_dec(v_size_3074_);
                                    v___x_3084_ = lean_nat_add(v___x_3083_, v_size_3075_);
                                    crate::leanh::lean_dec(v___x_3083_);
                                    if v_isShared_3070_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_3069_, 3, v_impl_3072_);
                                        crate::leanh::lean_ctor_set(v___x_3069_, 0, v___x_3084_);
                                        v___x_3086_ = v___x_3069_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3087_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3087_,
                                            0,
                                            v___x_3084_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3087_,
                                            1,
                                            v_k_3064_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3087_,
                                            2,
                                            v_v_3065_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3087_,
                                            3,
                                            v_impl_3072_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3087_,
                                            4,
                                            v_r_3067_,
                                        );
                                        v___x_3086_ = v_reuseFailAlloc_3087_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_r_3079_);
                                    crate::leanh::lean_inc(v_v_3077_);
                                    crate::leanh::lean_inc(v_k_3076_);
                                    crate::leanh::lean_inc(v_size_3075_);
                                    v_isSharedCheck_3151_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_3067_)) as u8;
                                    if v_isSharedCheck_3151_ == 0 {
                                        v_unused_3152_ = crate::leanh::lean_ctor_get(v_r_3067_, 4);
                                        crate::leanh::lean_dec(v_unused_3152_);
                                        v_unused_3153_ = crate::leanh::lean_ctor_get(v_r_3067_, 3);
                                        crate::leanh::lean_dec(v_unused_3153_);
                                        v_unused_3154_ = crate::leanh::lean_ctor_get(v_r_3067_, 2);
                                        crate::leanh::lean_dec(v_unused_3154_);
                                        v_unused_3155_ = crate::leanh::lean_ctor_get(v_r_3067_, 1);
                                        crate::leanh::lean_dec(v_unused_3155_);
                                        v_unused_3156_ = crate::leanh::lean_ctor_get(v_r_3067_, 0);
                                        crate::leanh::lean_dec(v_unused_3156_);
                                        v___x_3089_ = v_r_3067_;
                                        v_isShared_3090_ = v_isSharedCheck_3151_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_r_3067_);
                                        v___x_3089_ = crate::leanh::lean_box(0);
                                        v_isShared_3090_ = v_isSharedCheck_3151_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_3157_ = crate::leanh::lean_ctor_get(v_impl_3072_, 0);
                                crate::leanh::lean_inc(v_size_3157_);
                                v___x_3158_ = lean_nat_add(v___x_3073_, v_size_3157_);
                                crate::leanh::lean_dec(v_size_3157_);
                                if v_isShared_3070_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3069_, 3, v_impl_3072_);
                                    crate::leanh::lean_ctor_set(v___x_3069_, 0, v___x_3158_);
                                    v___x_3160_ = v___x_3069_;
                                    state = 13;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3161_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3161_,
                                        0,
                                        v___x_3158_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3161_,
                                        1,
                                        v_k_3064_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3161_,
                                        2,
                                        v_v_3065_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3161_,
                                        3,
                                        v_impl_3072_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3161_,
                                        4,
                                        v_r_3067_,
                                    );
                                    v___x_3160_ = v_reuseFailAlloc_3161_;
                                    state = 13;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v_r_3067_) == 0 {
                                v_l_3162_ = crate::leanh::lean_ctor_get(v_r_3067_, 3);
                                crate::leanh::lean_inc(v_l_3162_);
                                if crate::leanh::lean_obj_tag(v_l_3162_) == 0 {
                                    v_r_3163_ = crate::leanh::lean_ctor_get(v_r_3067_, 4);
                                    crate::leanh::lean_inc(v_r_3163_);
                                    if crate::leanh::lean_obj_tag(v_r_3163_) == 0 {
                                        v_size_3164_ = crate::leanh::lean_ctor_get(v_r_3067_, 0);
                                        v_k_3165_ = crate::leanh::lean_ctor_get(v_r_3067_, 1);
                                        v_v_3166_ = crate::leanh::lean_ctor_get(v_r_3067_, 2);
                                        v_isSharedCheck_3179_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_3067_)) as u8;
                                        if v_isSharedCheck_3179_ == 0 {
                                            v_unused_3180_ =
                                                crate::leanh::lean_ctor_get(v_r_3067_, 4);
                                            crate::leanh::lean_dec(v_unused_3180_);
                                            v_unused_3181_ =
                                                crate::leanh::lean_ctor_get(v_r_3067_, 3);
                                            crate::leanh::lean_dec(v_unused_3181_);
                                            v___x_3168_ = v_r_3067_;
                                            v_isShared_3169_ = v_isSharedCheck_3179_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_3166_);
                                            crate::leanh::lean_inc(v_k_3165_);
                                            crate::leanh::lean_inc(v_size_3164_);
                                            crate::leanh::lean_dec(v_r_3067_);
                                            v___x_3168_ = crate::leanh::lean_box(0);
                                            v_isShared_3169_ = v_isSharedCheck_3179_;
                                            state = 14;
                                            continue;
                                        }
                                    } else {
                                        v_k_3182_ = crate::leanh::lean_ctor_get(v_r_3067_, 1);
                                        v_v_3183_ = crate::leanh::lean_ctor_get(v_r_3067_, 2);
                                        v_isSharedCheck_3206_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_3067_)) as u8;
                                        if v_isSharedCheck_3206_ == 0 {
                                            v_unused_3207_ =
                                                crate::leanh::lean_ctor_get(v_r_3067_, 4);
                                            crate::leanh::lean_dec(v_unused_3207_);
                                            v_unused_3208_ =
                                                crate::leanh::lean_ctor_get(v_r_3067_, 3);
                                            crate::leanh::lean_dec(v_unused_3208_);
                                            v_unused_3209_ =
                                                crate::leanh::lean_ctor_get(v_r_3067_, 0);
                                            crate::leanh::lean_dec(v_unused_3209_);
                                            v___x_3185_ = v_r_3067_;
                                            v_isShared_3186_ = v_isSharedCheck_3206_;
                                            state = 17;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_3183_);
                                            crate::leanh::lean_inc(v_k_3182_);
                                            crate::leanh::lean_dec(v_r_3067_);
                                            v___x_3185_ = crate::leanh::lean_box(0);
                                            v_isShared_3186_ = v_isSharedCheck_3206_;
                                            state = 17;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_3210_ = crate::leanh::lean_ctor_get(v_r_3067_, 4);
                                    crate::leanh::lean_inc(v_r_3210_);
                                    if crate::leanh::lean_obj_tag(v_r_3210_) == 0 {
                                        v_k_3211_ = crate::leanh::lean_ctor_get(v_r_3067_, 1);
                                        v_v_3212_ = crate::leanh::lean_ctor_get(v_r_3067_, 2);
                                        v_isSharedCheck_3223_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_3067_)) as u8;
                                        if v_isSharedCheck_3223_ == 0 {
                                            v_unused_3224_ =
                                                crate::leanh::lean_ctor_get(v_r_3067_, 4);
                                            crate::leanh::lean_dec(v_unused_3224_);
                                            v_unused_3225_ =
                                                crate::leanh::lean_ctor_get(v_r_3067_, 3);
                                            crate::leanh::lean_dec(v_unused_3225_);
                                            v_unused_3226_ =
                                                crate::leanh::lean_ctor_get(v_r_3067_, 0);
                                            crate::leanh::lean_dec(v_unused_3226_);
                                            v___x_3214_ = v_r_3067_;
                                            v_isShared_3215_ = v_isSharedCheck_3223_;
                                            state = 22;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_3212_);
                                            crate::leanh::lean_inc(v_k_3211_);
                                            crate::leanh::lean_dec(v_r_3067_);
                                            v___x_3214_ = crate::leanh::lean_box(0);
                                            v_isShared_3215_ = v_isSharedCheck_3223_;
                                            state = 22;
                                            continue;
                                        }
                                    } else {
                                        v_size_3227_ = crate::leanh::lean_ctor_get(v_r_3067_, 0);
                                        v_k_3228_ = crate::leanh::lean_ctor_get(v_r_3067_, 1);
                                        v_v_3229_ = crate::leanh::lean_ctor_get(v_r_3067_, 2);
                                        v_isSharedCheck_3240_ =
                                            (!crate::leanh::lean_is_exclusive(v_r_3067_)) as u8;
                                        if v_isSharedCheck_3240_ == 0 {
                                            v_unused_3241_ =
                                                crate::leanh::lean_ctor_get(v_r_3067_, 4);
                                            crate::leanh::lean_dec(v_unused_3241_);
                                            v_unused_3242_ =
                                                crate::leanh::lean_ctor_get(v_r_3067_, 3);
                                            crate::leanh::lean_dec(v_unused_3242_);
                                            v___x_3231_ = v_r_3067_;
                                            v_isShared_3232_ = v_isSharedCheck_3240_;
                                            state = 25;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_3229_);
                                            crate::leanh::lean_inc(v_k_3228_);
                                            crate::leanh::lean_inc(v_size_3227_);
                                            crate::leanh::lean_dec(v_r_3067_);
                                            v___x_3231_ = crate::leanh::lean_box(0);
                                            v_isShared_3232_ = v_isSharedCheck_3240_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_3070_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3069_, 3, v_r_3067_);
                                    crate::leanh::lean_ctor_set(v___x_3069_, 0, v___x_3073_);
                                    v___x_3244_ = v___x_3069_;
                                    state = 28;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3245_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3245_,
                                        0,
                                        v___x_3073_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3245_,
                                        1,
                                        v_k_3064_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3245_,
                                        2,
                                        v_v_3065_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3245_,
                                        3,
                                        v_r_3067_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3245_,
                                        4,
                                        v_r_3067_,
                                    );
                                    v___x_3244_ = v_reuseFailAlloc_3245_;
                                    state = 28;
                                    continue;
                                }
                            }
                        }
                    }
                    1 => {
                        crate::leanh::lean_del_object(v___x_3069_);
                        crate::leanh::lean_dec(v_v_3065_);
                        crate::leanh::lean_dec(v_k_3064_);
                        if crate::leanh::lean_obj_tag(v_l_3066_) == 0 {
                            if crate::leanh::lean_obj_tag(v_r_3067_) == 0 {
                                v_size_3246_ = crate::leanh::lean_ctor_get(v_l_3066_, 0);
                                v_k_3247_ = crate::leanh::lean_ctor_get(v_l_3066_, 1);
                                v_v_3248_ = crate::leanh::lean_ctor_get(v_l_3066_, 2);
                                v_l_3249_ = crate::leanh::lean_ctor_get(v_l_3066_, 3);
                                v_r_3250_ = crate::leanh::lean_ctor_get(v_l_3066_, 4);
                                crate::leanh::lean_inc(v_r_3250_);
                                v_size_3251_ = crate::leanh::lean_ctor_get(v_r_3067_, 0);
                                v_k_3252_ = crate::leanh::lean_ctor_get(v_r_3067_, 1);
                                v_v_3253_ = crate::leanh::lean_ctor_get(v_r_3067_, 2);
                                v_l_3254_ = crate::leanh::lean_ctor_get(v_r_3067_, 3);
                                crate::leanh::lean_inc(v_l_3254_);
                                v_r_3255_ = crate::leanh::lean_ctor_get(v_r_3067_, 4);
                                v___x_3256_ = crate::leanh::lean_unsigned_to_nat(1);
                                v___x_3257_ = lean_nat_dec_lt(v_size_3246_, v_size_3251_);
                                if v___x_3257_ == 0 {
                                    crate::leanh::lean_inc(v_l_3249_);
                                    crate::leanh::lean_inc(v_v_3248_);
                                    crate::leanh::lean_inc(v_k_3247_);
                                    v_isSharedCheck_3393_ =
                                        (!crate::leanh::lean_is_exclusive(v_l_3066_)) as u8;
                                    if v_isSharedCheck_3393_ == 0 {
                                        v_unused_3394_ = crate::leanh::lean_ctor_get(v_l_3066_, 4);
                                        crate::leanh::lean_dec(v_unused_3394_);
                                        v_unused_3395_ = crate::leanh::lean_ctor_get(v_l_3066_, 3);
                                        crate::leanh::lean_dec(v_unused_3395_);
                                        v_unused_3396_ = crate::leanh::lean_ctor_get(v_l_3066_, 2);
                                        crate::leanh::lean_dec(v_unused_3396_);
                                        v_unused_3397_ = crate::leanh::lean_ctor_get(v_l_3066_, 1);
                                        crate::leanh::lean_dec(v_unused_3397_);
                                        v_unused_3398_ = crate::leanh::lean_ctor_get(v_l_3066_, 0);
                                        crate::leanh::lean_dec(v_unused_3398_);
                                        v___x_3259_ = v_l_3066_;
                                        v_isShared_3260_ = v_isSharedCheck_3393_;
                                        state = 29;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_l_3066_);
                                        v___x_3259_ = crate::leanh::lean_box(0);
                                        v_isShared_3260_ = v_isSharedCheck_3393_;
                                        state = 29;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_r_3255_);
                                    crate::leanh::lean_inc(v_v_3253_);
                                    crate::leanh::lean_inc(v_k_3252_);
                                    v_isSharedCheck_3551_ =
                                        (!crate::leanh::lean_is_exclusive(v_r_3067_)) as u8;
                                    if v_isSharedCheck_3551_ == 0 {
                                        v_unused_3552_ = crate::leanh::lean_ctor_get(v_r_3067_, 4);
                                        crate::leanh::lean_dec(v_unused_3552_);
                                        v_unused_3553_ = crate::leanh::lean_ctor_get(v_r_3067_, 3);
                                        crate::leanh::lean_dec(v_unused_3553_);
                                        v_unused_3554_ = crate::leanh::lean_ctor_get(v_r_3067_, 2);
                                        crate::leanh::lean_dec(v_unused_3554_);
                                        v_unused_3555_ = crate::leanh::lean_ctor_get(v_r_3067_, 1);
                                        crate::leanh::lean_dec(v_unused_3555_);
                                        v_unused_3556_ = crate::leanh::lean_ctor_get(v_r_3067_, 0);
                                        crate::leanh::lean_dec(v_unused_3556_);
                                        v___x_3400_ = v_r_3067_;
                                        v_isShared_3401_ = v_isSharedCheck_3551_;
                                        state = 51;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_r_3067_);
                                        v___x_3400_ = crate::leanh::lean_box(0);
                                        v_isShared_3401_ = v_isSharedCheck_3551_;
                                        state = 51;
                                        continue;
                                    }
                                }
                            } else {
                                return v_l_3066_;
                            }
                        } else {
                            return v_r_3067_;
                        }
                    }
                    _ => {
                        v_impl_3557_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__2___redArg(v_k_3062_, v_r_3067_);
                        v___x_3558_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_impl_3557_) == 0 {
                            if crate::leanh::lean_obj_tag(v_l_3066_) == 0 {
                                v_size_3559_ = crate::leanh::lean_ctor_get(v_impl_3557_, 0);
                                crate::leanh::lean_inc(v_size_3559_);
                                v_size_3560_ = crate::leanh::lean_ctor_get(v_l_3066_, 0);
                                v_k_3561_ = crate::leanh::lean_ctor_get(v_l_3066_, 1);
                                v_v_3562_ = crate::leanh::lean_ctor_get(v_l_3066_, 2);
                                v_l_3563_ = crate::leanh::lean_ctor_get(v_l_3066_, 3);
                                v_r_3564_ = crate::leanh::lean_ctor_get(v_l_3066_, 4);
                                crate::leanh::lean_inc(v_r_3564_);
                                v___x_3565_ = crate::leanh::lean_unsigned_to_nat(3);
                                v___x_3566_ = lean_nat_mul(v___x_3565_, v_size_3559_);
                                v___x_3567_ = lean_nat_dec_lt(v___x_3566_, v_size_3560_);
                                crate::leanh::lean_dec(v___x_3566_);
                                if v___x_3567_ == 0 {
                                    crate::leanh::lean_dec(v_r_3564_);
                                    v___x_3568_ = lean_nat_add(v___x_3558_, v_size_3560_);
                                    v___x_3569_ = lean_nat_add(v___x_3568_, v_size_3559_);
                                    crate::leanh::lean_dec(v_size_3559_);
                                    crate::leanh::lean_dec(v___x_3568_);
                                    if v_isShared_3070_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_3069_, 4, v_impl_3557_);
                                        crate::leanh::lean_ctor_set(v___x_3069_, 0, v___x_3569_);
                                        v___x_3571_ = v___x_3069_;
                                        state = 74;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3572_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3572_,
                                            0,
                                            v___x_3569_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3572_,
                                            1,
                                            v_k_3064_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3572_,
                                            2,
                                            v_v_3065_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3572_,
                                            3,
                                            v_l_3066_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_3572_,
                                            4,
                                            v_impl_3557_,
                                        );
                                        v___x_3571_ = v_reuseFailAlloc_3572_;
                                        state = 74;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_inc(v_l_3563_);
                                    crate::leanh::lean_inc(v_v_3562_);
                                    crate::leanh::lean_inc(v_k_3561_);
                                    crate::leanh::lean_inc(v_size_3560_);
                                    v_isSharedCheck_3638_ =
                                        (!crate::leanh::lean_is_exclusive(v_l_3066_)) as u8;
                                    if v_isSharedCheck_3638_ == 0 {
                                        v_unused_3639_ = crate::leanh::lean_ctor_get(v_l_3066_, 4);
                                        crate::leanh::lean_dec(v_unused_3639_);
                                        v_unused_3640_ = crate::leanh::lean_ctor_get(v_l_3066_, 3);
                                        crate::leanh::lean_dec(v_unused_3640_);
                                        v_unused_3641_ = crate::leanh::lean_ctor_get(v_l_3066_, 2);
                                        crate::leanh::lean_dec(v_unused_3641_);
                                        v_unused_3642_ = crate::leanh::lean_ctor_get(v_l_3066_, 1);
                                        crate::leanh::lean_dec(v_unused_3642_);
                                        v_unused_3643_ = crate::leanh::lean_ctor_get(v_l_3066_, 0);
                                        crate::leanh::lean_dec(v_unused_3643_);
                                        v___x_3574_ = v_l_3066_;
                                        v_isShared_3575_ = v_isSharedCheck_3638_;
                                        state = 75;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_l_3066_);
                                        v___x_3574_ = crate::leanh::lean_box(0);
                                        v_isShared_3575_ = v_isSharedCheck_3638_;
                                        state = 75;
                                        continue;
                                    }
                                }
                            } else {
                                v_size_3644_ = crate::leanh::lean_ctor_get(v_impl_3557_, 0);
                                crate::leanh::lean_inc(v_size_3644_);
                                v___x_3645_ = lean_nat_add(v___x_3558_, v_size_3644_);
                                crate::leanh::lean_dec(v_size_3644_);
                                if v_isShared_3070_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3069_, 4, v_impl_3557_);
                                    crate::leanh::lean_ctor_set(v___x_3069_, 0, v___x_3645_);
                                    v___x_3647_ = v___x_3069_;
                                    state = 85;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3648_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3648_,
                                        0,
                                        v___x_3645_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3648_,
                                        1,
                                        v_k_3064_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3648_,
                                        2,
                                        v_v_3065_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3648_,
                                        3,
                                        v_l_3066_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3648_,
                                        4,
                                        v_impl_3557_,
                                    );
                                    v___x_3647_ = v_reuseFailAlloc_3648_;
                                    state = 85;
                                    continue;
                                }
                            }
                        } else {
                            if crate::leanh::lean_obj_tag(v_l_3066_) == 0 {
                                v_l_3649_ = crate::leanh::lean_ctor_get(v_l_3066_, 3);
                                if crate::leanh::lean_obj_tag(v_l_3649_) == 0 {
                                    crate::leanh::lean_inc_ref(v_l_3649_);
                                    v_r_3650_ = crate::leanh::lean_ctor_get(v_l_3066_, 4);
                                    crate::leanh::lean_inc(v_r_3650_);
                                    if crate::leanh::lean_obj_tag(v_r_3650_) == 0 {
                                        v_size_3651_ = crate::leanh::lean_ctor_get(v_l_3066_, 0);
                                        v_k_3652_ = crate::leanh::lean_ctor_get(v_l_3066_, 1);
                                        v_v_3653_ = crate::leanh::lean_ctor_get(v_l_3066_, 2);
                                        v_isSharedCheck_3666_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_3066_)) as u8;
                                        if v_isSharedCheck_3666_ == 0 {
                                            v_unused_3667_ =
                                                crate::leanh::lean_ctor_get(v_l_3066_, 4);
                                            crate::leanh::lean_dec(v_unused_3667_);
                                            v_unused_3668_ =
                                                crate::leanh::lean_ctor_get(v_l_3066_, 3);
                                            crate::leanh::lean_dec(v_unused_3668_);
                                            v___x_3655_ = v_l_3066_;
                                            v_isShared_3656_ = v_isSharedCheck_3666_;
                                            state = 86;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_3653_);
                                            crate::leanh::lean_inc(v_k_3652_);
                                            crate::leanh::lean_inc(v_size_3651_);
                                            crate::leanh::lean_dec(v_l_3066_);
                                            v___x_3655_ = crate::leanh::lean_box(0);
                                            v_isShared_3656_ = v_isSharedCheck_3666_;
                                            state = 86;
                                            continue;
                                        }
                                    } else {
                                        v_k_3669_ = crate::leanh::lean_ctor_get(v_l_3066_, 1);
                                        v_v_3670_ = crate::leanh::lean_ctor_get(v_l_3066_, 2);
                                        v_isSharedCheck_3681_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_3066_)) as u8;
                                        if v_isSharedCheck_3681_ == 0 {
                                            v_unused_3682_ =
                                                crate::leanh::lean_ctor_get(v_l_3066_, 4);
                                            crate::leanh::lean_dec(v_unused_3682_);
                                            v_unused_3683_ =
                                                crate::leanh::lean_ctor_get(v_l_3066_, 3);
                                            crate::leanh::lean_dec(v_unused_3683_);
                                            v_unused_3684_ =
                                                crate::leanh::lean_ctor_get(v_l_3066_, 0);
                                            crate::leanh::lean_dec(v_unused_3684_);
                                            v___x_3672_ = v_l_3066_;
                                            v_isShared_3673_ = v_isSharedCheck_3681_;
                                            state = 89;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_3670_);
                                            crate::leanh::lean_inc(v_k_3669_);
                                            crate::leanh::lean_dec(v_l_3066_);
                                            v___x_3672_ = crate::leanh::lean_box(0);
                                            v_isShared_3673_ = v_isSharedCheck_3681_;
                                            state = 89;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_r_3685_ = crate::leanh::lean_ctor_get(v_l_3066_, 4);
                                    crate::leanh::lean_inc(v_r_3685_);
                                    if crate::leanh::lean_obj_tag(v_r_3685_) == 0 {
                                        crate::leanh::lean_inc(v_l_3649_);
                                        v_k_3686_ = crate::leanh::lean_ctor_get(v_l_3066_, 1);
                                        v_v_3687_ = crate::leanh::lean_ctor_get(v_l_3066_, 2);
                                        v_isSharedCheck_3710_ =
                                            (!crate::leanh::lean_is_exclusive(v_l_3066_)) as u8;
                                        if v_isSharedCheck_3710_ == 0 {
                                            v_unused_3711_ =
                                                crate::leanh::lean_ctor_get(v_l_3066_, 4);
                                            crate::leanh::lean_dec(v_unused_3711_);
                                            v_unused_3712_ =
                                                crate::leanh::lean_ctor_get(v_l_3066_, 3);
                                            crate::leanh::lean_dec(v_unused_3712_);
                                            v_unused_3713_ =
                                                crate::leanh::lean_ctor_get(v_l_3066_, 0);
                                            crate::leanh::lean_dec(v_unused_3713_);
                                            v___x_3689_ = v_l_3066_;
                                            v_isShared_3690_ = v_isSharedCheck_3710_;
                                            state = 92;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_v_3687_);
                                            crate::leanh::lean_inc(v_k_3686_);
                                            crate::leanh::lean_dec(v_l_3066_);
                                            v___x_3689_ = crate::leanh::lean_box(0);
                                            v_isShared_3690_ = v_isSharedCheck_3710_;
                                            state = 92;
                                            continue;
                                        }
                                    } else {
                                        v___x_3714_ = crate::leanh::lean_unsigned_to_nat(2);
                                        if v_isShared_3070_ == 0 {
                                            crate::leanh::lean_ctor_set(v___x_3069_, 4, v_r_3685_);
                                            crate::leanh::lean_ctor_set(
                                                v___x_3069_,
                                                0,
                                                v___x_3714_,
                                            );
                                            v___x_3716_ = v___x_3069_;
                                            state = 97;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3717_ =
                                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3717_,
                                                0,
                                                v___x_3714_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3717_,
                                                1,
                                                v_k_3064_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3717_,
                                                2,
                                                v_v_3065_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3717_,
                                                3,
                                                v_l_3066_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v_reuseFailAlloc_3717_,
                                                4,
                                                v_r_3685_,
                                            );
                                            v___x_3716_ = v_reuseFailAlloc_3717_;
                                            state = 97;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                if v_isShared_3070_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3069_, 4, v_l_3066_);
                                    crate::leanh::lean_ctor_set(v___x_3069_, 0, v___x_3558_);
                                    v___x_3719_ = v___x_3069_;
                                    state = 98;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3720_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3720_,
                                        0,
                                        v___x_3558_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3720_,
                                        1,
                                        v_k_3064_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3720_,
                                        2,
                                        v_v_3065_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3720_,
                                        3,
                                        v_l_3066_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3720_,
                                        4,
                                        v_l_3066_,
                                    );
                                    v___x_3719_ = v_reuseFailAlloc_3720_;
                                    state = 98;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_3086_;
            }
            3 => {
                v_size_3091_ = crate::leanh::lean_ctor_get(v_l_3078_, 0);
                v_k_3092_ = crate::leanh::lean_ctor_get(v_l_3078_, 1);
                v_v_3093_ = crate::leanh::lean_ctor_get(v_l_3078_, 2);
                v_l_3094_ = crate::leanh::lean_ctor_get(v_l_3078_, 3);
                v_r_3095_ = crate::leanh::lean_ctor_get(v_l_3078_, 4);
                v_size_3096_ = crate::leanh::lean_ctor_get(v_r_3079_, 0);
                v___x_3097_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3098_ = lean_nat_mul(v___x_3097_, v_size_3096_);
                v___x_3099_ = lean_nat_dec_lt(v_size_3091_, v___x_3098_);
                crate::leanh::lean_dec(v___x_3098_);
                if v___x_3099_ == 0 {
                    crate::leanh::lean_inc(v_r_3095_);
                    crate::leanh::lean_inc(v_l_3094_);
                    crate::leanh::lean_inc(v_v_3093_);
                    crate::leanh::lean_inc(v_k_3092_);
                    v_isSharedCheck_3127_ = (!crate::leanh::lean_is_exclusive(v_l_3078_)) as u8;
                    if v_isSharedCheck_3127_ == 0 {
                        v_unused_3128_ = crate::leanh::lean_ctor_get(v_l_3078_, 4);
                        crate::leanh::lean_dec(v_unused_3128_);
                        v_unused_3129_ = crate::leanh::lean_ctor_get(v_l_3078_, 3);
                        crate::leanh::lean_dec(v_unused_3129_);
                        v_unused_3130_ = crate::leanh::lean_ctor_get(v_l_3078_, 2);
                        crate::leanh::lean_dec(v_unused_3130_);
                        v_unused_3131_ = crate::leanh::lean_ctor_get(v_l_3078_, 1);
                        crate::leanh::lean_dec(v_unused_3131_);
                        v_unused_3132_ = crate::leanh::lean_ctor_get(v_l_3078_, 0);
                        crate::leanh::lean_dec(v_unused_3132_);
                        v___x_3101_ = v_l_3078_;
                        v_isShared_3102_ = v_isSharedCheck_3127_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_3078_);
                        v___x_3101_ = crate::leanh::lean_box(0);
                        v_isShared_3102_ = v_isSharedCheck_3127_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3069_);
                    v___x_3133_ = lean_nat_add(v___x_3073_, v_size_3074_);
                    crate::leanh::lean_dec(v_size_3074_);
                    v___x_3134_ = lean_nat_add(v___x_3133_, v_size_3075_);
                    crate::leanh::lean_dec(v_size_3075_);
                    v___x_3135_ = lean_nat_add(v___x_3133_, v_size_3091_);
                    crate::leanh::lean_dec(v___x_3133_);
                    crate::leanh::lean_inc_ref(v_impl_3072_);
                    if v_isShared_3090_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3089_, 4, v_l_3078_);
                        crate::leanh::lean_ctor_set(v___x_3089_, 3, v_impl_3072_);
                        crate::leanh::lean_ctor_set(v___x_3089_, 2, v_v_3065_);
                        crate::leanh::lean_ctor_set(v___x_3089_, 1, v_k_3064_);
                        crate::leanh::lean_ctor_set(v___x_3089_, 0, v___x_3135_);
                        v___x_3137_ = v___x_3089_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3150_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3135_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 1, v_k_3064_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 2, v_v_3065_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 3, v_impl_3072_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 4, v_l_3078_);
                        v___x_3137_ = v_reuseFailAlloc_3150_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3103_ = lean_nat_add(v___x_3073_, v_size_3074_);
                crate::leanh::lean_dec(v_size_3074_);
                v___x_3104_ = lean_nat_add(v___x_3103_, v_size_3075_);
                crate::leanh::lean_dec(v_size_3075_);
                if crate::leanh::lean_obj_tag(v_l_3094_) == 0 {
                    v_size_3125_ = crate::leanh::lean_ctor_get(v_l_3094_, 0);
                    crate::leanh::lean_inc(v_size_3125_);
                    v___y_3117_ = v_size_3125_;
                    state = 8;
                    continue;
                } else {
                    v___x_3126_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3117_ = v___x_3126_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_3109_ = lean_nat_add(v___y_3107_, v___y_3108_);
                crate::leanh::lean_dec(v___y_3108_);
                crate::leanh::lean_dec(v___y_3107_);
                if v_isShared_3102_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3101_, 4, v_r_3079_);
                    crate::leanh::lean_ctor_set(v___x_3101_, 3, v_r_3095_);
                    crate::leanh::lean_ctor_set(v___x_3101_, 2, v_v_3077_);
                    crate::leanh::lean_ctor_set(v___x_3101_, 1, v_k_3076_);
                    crate::leanh::lean_ctor_set(v___x_3101_, 0, v___x_3109_);
                    v___x_3111_ = v___x_3101_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3115_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3109_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 1, v_k_3076_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 2, v_v_3077_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 3, v_r_3095_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 4, v_r_3079_);
                    v___x_3111_ = v_reuseFailAlloc_3115_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3090_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3089_, 4, v___x_3111_);
                    crate::leanh::lean_ctor_set(v___x_3089_, 3, v___y_3106_);
                    crate::leanh::lean_ctor_set(v___x_3089_, 2, v_v_3093_);
                    crate::leanh::lean_ctor_set(v___x_3089_, 1, v_k_3092_);
                    crate::leanh::lean_ctor_set(v___x_3089_, 0, v___x_3104_);
                    v___x_3113_ = v___x_3089_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3114_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3104_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3114_, 1, v_k_3092_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3114_, 2, v_v_3093_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3114_, 3, v___y_3106_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3114_, 4, v___x_3111_);
                    v___x_3113_ = v_reuseFailAlloc_3114_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3113_;
            }
            8 => {
                v___x_3118_ = lean_nat_add(v___x_3103_, v___y_3117_);
                crate::leanh::lean_dec(v___y_3117_);
                crate::leanh::lean_dec(v___x_3103_);
                if v_isShared_3070_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3069_, 4, v_l_3094_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 3, v_impl_3072_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 0, v___x_3118_);
                    v___x_3120_ = v___x_3069_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3124_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3118_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3124_, 1, v_k_3064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3124_, 2, v_v_3065_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3124_, 3, v_impl_3072_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3124_, 4, v_l_3094_);
                    v___x_3120_ = v_reuseFailAlloc_3124_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3121_ = lean_nat_add(v___x_3073_, v_size_3096_);
                if crate::leanh::lean_obj_tag(v_r_3095_) == 0 {
                    v_size_3122_ = crate::leanh::lean_ctor_get(v_r_3095_, 0);
                    crate::leanh::lean_inc(v_size_3122_);
                    v___y_3106_ = v___x_3120_;
                    v___y_3107_ = v___x_3121_;
                    v___y_3108_ = v_size_3122_;
                    state = 5;
                    continue;
                } else {
                    v___x_3123_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3106_ = v___x_3120_;
                    v___y_3107_ = v___x_3121_;
                    v___y_3108_ = v___x_3123_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_3144_ = (!crate::leanh::lean_is_exclusive(v_impl_3072_)) as u8;
                if v_isSharedCheck_3144_ == 0 {
                    v_unused_3145_ = crate::leanh::lean_ctor_get(v_impl_3072_, 4);
                    crate::leanh::lean_dec(v_unused_3145_);
                    v_unused_3146_ = crate::leanh::lean_ctor_get(v_impl_3072_, 3);
                    crate::leanh::lean_dec(v_unused_3146_);
                    v_unused_3147_ = crate::leanh::lean_ctor_get(v_impl_3072_, 2);
                    crate::leanh::lean_dec(v_unused_3147_);
                    v_unused_3148_ = crate::leanh::lean_ctor_get(v_impl_3072_, 1);
                    crate::leanh::lean_dec(v_unused_3148_);
                    v_unused_3149_ = crate::leanh::lean_ctor_get(v_impl_3072_, 0);
                    crate::leanh::lean_dec(v_unused_3149_);
                    v___x_3139_ = v_impl_3072_;
                    v_isShared_3140_ = v_isSharedCheck_3144_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_impl_3072_);
                    v___x_3139_ = crate::leanh::lean_box(0);
                    v_isShared_3140_ = v_isSharedCheck_3144_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3140_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3139_, 4, v_r_3079_);
                    crate::leanh::lean_ctor_set(v___x_3139_, 3, v___x_3137_);
                    crate::leanh::lean_ctor_set(v___x_3139_, 2, v_v_3077_);
                    crate::leanh::lean_ctor_set(v___x_3139_, 1, v_k_3076_);
                    crate::leanh::lean_ctor_set(v___x_3139_, 0, v___x_3134_);
                    v___x_3142_ = v___x_3139_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3143_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3134_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_k_3076_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3143_, 2, v_v_3077_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3143_, 3, v___x_3137_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3143_, 4, v_r_3079_);
                    v___x_3142_ = v_reuseFailAlloc_3143_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3142_;
            }
            13 => {
                return v___x_3160_;
            }
            14 => {
                v_size_3170_ = crate::leanh::lean_ctor_get(v_l_3162_, 0);
                v___x_3171_ = lean_nat_add(v___x_3073_, v_size_3164_);
                crate::leanh::lean_dec(v_size_3164_);
                v___x_3172_ = lean_nat_add(v___x_3073_, v_size_3170_);
                if v_isShared_3169_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3168_, 4, v_l_3162_);
                    crate::leanh::lean_ctor_set(v___x_3168_, 3, v_impl_3072_);
                    crate::leanh::lean_ctor_set(v___x_3168_, 2, v_v_3065_);
                    crate::leanh::lean_ctor_set(v___x_3168_, 1, v_k_3064_);
                    crate::leanh::lean_ctor_set(v___x_3168_, 0, v___x_3172_);
                    v___x_3174_ = v___x_3168_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3178_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3172_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 1, v_k_3064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 2, v_v_3065_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 3, v_impl_3072_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 4, v_l_3162_);
                    v___x_3174_ = v_reuseFailAlloc_3178_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_3070_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3069_, 4, v_r_3163_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 3, v___x_3174_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 2, v_v_3166_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 1, v_k_3165_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 0, v___x_3171_);
                    v___x_3176_ = v___x_3069_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3177_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3177_, 0, v___x_3171_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3177_, 1, v_k_3165_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3177_, 2, v_v_3166_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3177_, 3, v___x_3174_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3177_, 4, v_r_3163_);
                    v___x_3176_ = v_reuseFailAlloc_3177_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3176_;
            }
            17 => {
                v_k_3187_ = crate::leanh::lean_ctor_get(v_l_3162_, 1);
                v_v_3188_ = crate::leanh::lean_ctor_get(v_l_3162_, 2);
                v_isSharedCheck_3202_ = (!crate::leanh::lean_is_exclusive(v_l_3162_)) as u8;
                if v_isSharedCheck_3202_ == 0 {
                    v_unused_3203_ = crate::leanh::lean_ctor_get(v_l_3162_, 4);
                    crate::leanh::lean_dec(v_unused_3203_);
                    v_unused_3204_ = crate::leanh::lean_ctor_get(v_l_3162_, 3);
                    crate::leanh::lean_dec(v_unused_3204_);
                    v_unused_3205_ = crate::leanh::lean_ctor_get(v_l_3162_, 0);
                    crate::leanh::lean_dec(v_unused_3205_);
                    v___x_3190_ = v_l_3162_;
                    v_isShared_3191_ = v_isSharedCheck_3202_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_3188_);
                    crate::leanh::lean_inc(v_k_3187_);
                    crate::leanh::lean_dec(v_l_3162_);
                    v___x_3190_ = crate::leanh::lean_box(0);
                    v_isShared_3191_ = v_isSharedCheck_3202_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_3192_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_3191_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3190_, 4, v_r_3163_);
                    crate::leanh::lean_ctor_set(v___x_3190_, 3, v_r_3163_);
                    crate::leanh::lean_ctor_set(v___x_3190_, 2, v_v_3065_);
                    crate::leanh::lean_ctor_set(v___x_3190_, 1, v_k_3064_);
                    crate::leanh::lean_ctor_set(v___x_3190_, 0, v___x_3073_);
                    v___x_3194_ = v___x_3190_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3201_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3201_, 0, v___x_3073_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3201_, 1, v_k_3064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3201_, 2, v_v_3065_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3201_, 3, v_r_3163_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3201_, 4, v_r_3163_);
                    v___x_3194_ = v_reuseFailAlloc_3201_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_3186_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3185_, 3, v_r_3163_);
                    crate::leanh::lean_ctor_set(v___x_3185_, 0, v___x_3073_);
                    v___x_3196_ = v___x_3185_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3200_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3200_, 0, v___x_3073_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3200_, 1, v_k_3182_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3200_, 2, v_v_3183_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3200_, 3, v_r_3163_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3200_, 4, v_r_3163_);
                    v___x_3196_ = v_reuseFailAlloc_3200_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_3070_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3069_, 4, v___x_3196_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 3, v___x_3194_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 2, v_v_3188_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 1, v_k_3187_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 0, v___x_3192_);
                    v___x_3198_ = v___x_3069_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3199_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3199_, 0, v___x_3192_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3199_, 1, v_k_3187_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3199_, 2, v_v_3188_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3199_, 3, v___x_3194_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3199_, 4, v___x_3196_);
                    v___x_3198_ = v_reuseFailAlloc_3199_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3198_;
            }
            22 => {
                v___x_3216_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_3215_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3214_, 4, v_l_3162_);
                    crate::leanh::lean_ctor_set(v___x_3214_, 2, v_v_3065_);
                    crate::leanh::lean_ctor_set(v___x_3214_, 1, v_k_3064_);
                    crate::leanh::lean_ctor_set(v___x_3214_, 0, v___x_3073_);
                    v___x_3218_ = v___x_3214_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3222_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3073_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 1, v_k_3064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 2, v_v_3065_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 3, v_l_3162_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 4, v_l_3162_);
                    v___x_3218_ = v_reuseFailAlloc_3222_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                if v_isShared_3070_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3069_, 4, v_r_3210_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 3, v___x_3218_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 2, v_v_3212_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 1, v_k_3211_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 0, v___x_3216_);
                    v___x_3220_ = v___x_3069_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3221_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3216_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 1, v_k_3211_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 2, v_v_3212_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 3, v___x_3218_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3221_, 4, v_r_3210_);
                    v___x_3220_ = v_reuseFailAlloc_3221_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3220_;
            }
            25 => {
                if v_isShared_3232_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3231_, 3, v_r_3210_);
                    v___x_3234_ = v___x_3231_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3239_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_size_3227_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 1, v_k_3228_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 2, v_v_3229_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 3, v_r_3210_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 4, v_r_3210_);
                    v___x_3234_ = v_reuseFailAlloc_3239_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_3235_ = crate::leanh::lean_unsigned_to_nat(2);
                if v_isShared_3070_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3069_, 4, v___x_3234_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 3, v_r_3210_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 0, v___x_3235_);
                    v___x_3237_ = v___x_3069_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_3238_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3238_, 0, v___x_3235_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3238_, 1, v_k_3064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3238_, 2, v_v_3065_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3238_, 3, v_r_3210_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3238_, 4, v___x_3234_);
                    v___x_3237_ = v_reuseFailAlloc_3238_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_3237_;
            }
            28 => {
                return v___x_3244_;
            }
            29 => {
                v___x_3261_ = l_Std_DTreeMap_Internal_Impl_maxView___redArg(
                    v_k_3247_, v_v_3248_, v_l_3249_, v_r_3250_,
                );
                v_tree_3262_ = crate::leanh::lean_ctor_get(v___x_3261_, 2);
                crate::leanh::lean_inc(v_tree_3262_);
                if crate::leanh::lean_obj_tag(v_tree_3262_) == 0 {
                    v_k_3263_ = crate::leanh::lean_ctor_get(v___x_3261_, 0);
                    crate::leanh::lean_inc(v_k_3263_);
                    v_v_3264_ = crate::leanh::lean_ctor_get(v___x_3261_, 1);
                    crate::leanh::lean_inc(v_v_3264_);
                    crate::leanh::lean_dec_ref(v___x_3261_);
                    v_size_3265_ = crate::leanh::lean_ctor_get(v_tree_3262_, 0);
                    v___x_3266_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_3267_ = lean_nat_mul(v___x_3266_, v_size_3265_);
                    v___x_3268_ = lean_nat_dec_lt(v___x_3267_, v_size_3251_);
                    crate::leanh::lean_dec(v___x_3267_);
                    if v___x_3268_ == 0 {
                        crate::leanh::lean_dec(v_l_3254_);
                        v___x_3269_ = lean_nat_add(v___x_3256_, v_size_3265_);
                        v___x_3270_ = lean_nat_add(v___x_3269_, v_size_3251_);
                        crate::leanh::lean_dec(v___x_3269_);
                        if v_isShared_3260_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3259_, 4, v_r_3067_);
                            crate::leanh::lean_ctor_set(v___x_3259_, 3, v_tree_3262_);
                            crate::leanh::lean_ctor_set(v___x_3259_, 2, v_v_3264_);
                            crate::leanh::lean_ctor_set(v___x_3259_, 1, v_k_3263_);
                            crate::leanh::lean_ctor_set(v___x_3259_, 0, v___x_3270_);
                            v___x_3272_ = v___x_3259_;
                            state = 30;
                            continue;
                        } else {
                            v_reuseFailAlloc_3273_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3273_, 0, v___x_3270_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3273_, 1, v_k_3263_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3273_, 2, v_v_3264_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3273_, 3, v_tree_3262_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3273_, 4, v_r_3067_);
                            v___x_3272_ = v_reuseFailAlloc_3273_;
                            state = 30;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_r_3255_);
                        crate::leanh::lean_inc(v_v_3253_);
                        crate::leanh::lean_inc(v_k_3252_);
                        crate::leanh::lean_inc(v_size_3251_);
                        v_isSharedCheck_3328_ = (!crate::leanh::lean_is_exclusive(v_r_3067_)) as u8;
                        if v_isSharedCheck_3328_ == 0 {
                            v_unused_3329_ = crate::leanh::lean_ctor_get(v_r_3067_, 4);
                            crate::leanh::lean_dec(v_unused_3329_);
                            v_unused_3330_ = crate::leanh::lean_ctor_get(v_r_3067_, 3);
                            crate::leanh::lean_dec(v_unused_3330_);
                            v_unused_3331_ = crate::leanh::lean_ctor_get(v_r_3067_, 2);
                            crate::leanh::lean_dec(v_unused_3331_);
                            v_unused_3332_ = crate::leanh::lean_ctor_get(v_r_3067_, 1);
                            crate::leanh::lean_dec(v_unused_3332_);
                            v_unused_3333_ = crate::leanh::lean_ctor_get(v_r_3067_, 0);
                            crate::leanh::lean_dec(v_unused_3333_);
                            v___x_3275_ = v_r_3067_;
                            v_isShared_3276_ = v_isSharedCheck_3328_;
                            state = 31;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_r_3067_);
                            v___x_3275_ = crate::leanh::lean_box(0);
                            v_isShared_3276_ = v_isSharedCheck_3328_;
                            state = 31;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_r_3255_);
                    crate::leanh::lean_inc(v_v_3253_);
                    crate::leanh::lean_inc(v_k_3252_);
                    crate::leanh::lean_inc(v_size_3251_);
                    v_isSharedCheck_3387_ = (!crate::leanh::lean_is_exclusive(v_r_3067_)) as u8;
                    if v_isSharedCheck_3387_ == 0 {
                        v_unused_3388_ = crate::leanh::lean_ctor_get(v_r_3067_, 4);
                        crate::leanh::lean_dec(v_unused_3388_);
                        v_unused_3389_ = crate::leanh::lean_ctor_get(v_r_3067_, 3);
                        crate::leanh::lean_dec(v_unused_3389_);
                        v_unused_3390_ = crate::leanh::lean_ctor_get(v_r_3067_, 2);
                        crate::leanh::lean_dec(v_unused_3390_);
                        v_unused_3391_ = crate::leanh::lean_ctor_get(v_r_3067_, 1);
                        crate::leanh::lean_dec(v_unused_3391_);
                        v_unused_3392_ = crate::leanh::lean_ctor_get(v_r_3067_, 0);
                        crate::leanh::lean_dec(v_unused_3392_);
                        v___x_3335_ = v_r_3067_;
                        v_isShared_3336_ = v_isSharedCheck_3387_;
                        state = 40;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_3067_);
                        v___x_3335_ = crate::leanh::lean_box(0);
                        v_isShared_3336_ = v_isSharedCheck_3387_;
                        state = 40;
                        continue;
                    }
                }
            }
            30 => {
                return v___x_3272_;
            }
            31 => {
                v_size_3277_ = crate::leanh::lean_ctor_get(v_l_3254_, 0);
                v_k_3278_ = crate::leanh::lean_ctor_get(v_l_3254_, 1);
                v_v_3279_ = crate::leanh::lean_ctor_get(v_l_3254_, 2);
                v_l_3280_ = crate::leanh::lean_ctor_get(v_l_3254_, 3);
                v_r_3281_ = crate::leanh::lean_ctor_get(v_l_3254_, 4);
                v_size_3282_ = crate::leanh::lean_ctor_get(v_r_3255_, 0);
                v___x_3283_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3284_ = lean_nat_mul(v___x_3283_, v_size_3282_);
                v___x_3285_ = lean_nat_dec_lt(v_size_3277_, v___x_3284_);
                crate::leanh::lean_dec(v___x_3284_);
                if v___x_3285_ == 0 {
                    crate::leanh::lean_inc(v_r_3281_);
                    crate::leanh::lean_inc(v_l_3280_);
                    crate::leanh::lean_inc(v_v_3279_);
                    crate::leanh::lean_inc(v_k_3278_);
                    v_isSharedCheck_3313_ = (!crate::leanh::lean_is_exclusive(v_l_3254_)) as u8;
                    if v_isSharedCheck_3313_ == 0 {
                        v_unused_3314_ = crate::leanh::lean_ctor_get(v_l_3254_, 4);
                        crate::leanh::lean_dec(v_unused_3314_);
                        v_unused_3315_ = crate::leanh::lean_ctor_get(v_l_3254_, 3);
                        crate::leanh::lean_dec(v_unused_3315_);
                        v_unused_3316_ = crate::leanh::lean_ctor_get(v_l_3254_, 2);
                        crate::leanh::lean_dec(v_unused_3316_);
                        v_unused_3317_ = crate::leanh::lean_ctor_get(v_l_3254_, 1);
                        crate::leanh::lean_dec(v_unused_3317_);
                        v_unused_3318_ = crate::leanh::lean_ctor_get(v_l_3254_, 0);
                        crate::leanh::lean_dec(v_unused_3318_);
                        v___x_3287_ = v_l_3254_;
                        v_isShared_3288_ = v_isSharedCheck_3313_;
                        state = 32;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_3254_);
                        v___x_3287_ = crate::leanh::lean_box(0);
                        v_isShared_3288_ = v_isSharedCheck_3313_;
                        state = 32;
                        continue;
                    }
                } else {
                    v___x_3319_ = lean_nat_add(v___x_3256_, v_size_3265_);
                    v___x_3320_ = lean_nat_add(v___x_3319_, v_size_3251_);
                    crate::leanh::lean_dec(v_size_3251_);
                    v___x_3321_ = lean_nat_add(v___x_3319_, v_size_3277_);
                    crate::leanh::lean_dec(v___x_3319_);
                    if v_isShared_3276_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3275_, 4, v_l_3254_);
                        crate::leanh::lean_ctor_set(v___x_3275_, 3, v_tree_3262_);
                        crate::leanh::lean_ctor_set(v___x_3275_, 2, v_v_3264_);
                        crate::leanh::lean_ctor_set(v___x_3275_, 1, v_k_3263_);
                        crate::leanh::lean_ctor_set(v___x_3275_, 0, v___x_3321_);
                        v___x_3323_ = v___x_3275_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_3327_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3327_, 0, v___x_3321_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3327_, 1, v_k_3263_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3327_, 2, v_v_3264_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3327_, 3, v_tree_3262_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3327_, 4, v_l_3254_);
                        v___x_3323_ = v_reuseFailAlloc_3327_;
                        state = 38;
                        continue;
                    }
                }
            }
            32 => {
                v___x_3289_ = lean_nat_add(v___x_3256_, v_size_3265_);
                v___x_3290_ = lean_nat_add(v___x_3289_, v_size_3251_);
                crate::leanh::lean_dec(v_size_3251_);
                if crate::leanh::lean_obj_tag(v_l_3280_) == 0 {
                    v_size_3311_ = crate::leanh::lean_ctor_get(v_l_3280_, 0);
                    crate::leanh::lean_inc(v_size_3311_);
                    v___y_3303_ = v_size_3311_;
                    state = 36;
                    continue;
                } else {
                    v___x_3312_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3303_ = v___x_3312_;
                    state = 36;
                    continue;
                }
            }
            33 => {
                v___x_3295_ = lean_nat_add(v___y_3292_, v___y_3294_);
                crate::leanh::lean_dec(v___y_3294_);
                crate::leanh::lean_dec(v___y_3292_);
                if v_isShared_3288_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3287_, 4, v_r_3255_);
                    crate::leanh::lean_ctor_set(v___x_3287_, 3, v_r_3281_);
                    crate::leanh::lean_ctor_set(v___x_3287_, 2, v_v_3253_);
                    crate::leanh::lean_ctor_set(v___x_3287_, 1, v_k_3252_);
                    crate::leanh::lean_ctor_set(v___x_3287_, 0, v___x_3295_);
                    v___x_3297_ = v___x_3287_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_3301_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3301_, 0, v___x_3295_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3301_, 1, v_k_3252_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3301_, 2, v_v_3253_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3301_, 3, v_r_3281_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3301_, 4, v_r_3255_);
                    v___x_3297_ = v_reuseFailAlloc_3301_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                if v_isShared_3276_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3275_, 4, v___x_3297_);
                    crate::leanh::lean_ctor_set(v___x_3275_, 3, v___y_3293_);
                    crate::leanh::lean_ctor_set(v___x_3275_, 2, v_v_3279_);
                    crate::leanh::lean_ctor_set(v___x_3275_, 1, v_k_3278_);
                    crate::leanh::lean_ctor_set(v___x_3275_, 0, v___x_3290_);
                    v___x_3299_ = v___x_3275_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3300_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3300_, 0, v___x_3290_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3300_, 1, v_k_3278_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3300_, 2, v_v_3279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3300_, 3, v___y_3293_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3300_, 4, v___x_3297_);
                    v___x_3299_ = v_reuseFailAlloc_3300_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_3299_;
            }
            36 => {
                v___x_3304_ = lean_nat_add(v___x_3289_, v___y_3303_);
                crate::leanh::lean_dec(v___y_3303_);
                crate::leanh::lean_dec(v___x_3289_);
                if v_isShared_3260_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3259_, 4, v_l_3280_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 3, v_tree_3262_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 2, v_v_3264_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 1, v_k_3263_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 0, v___x_3304_);
                    v___x_3306_ = v___x_3259_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3310_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3310_, 0, v___x_3304_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3310_, 1, v_k_3263_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3310_, 2, v_v_3264_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3310_, 3, v_tree_3262_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3310_, 4, v_l_3280_);
                    v___x_3306_ = v_reuseFailAlloc_3310_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                v___x_3307_ = lean_nat_add(v___x_3256_, v_size_3282_);
                if crate::leanh::lean_obj_tag(v_r_3281_) == 0 {
                    v_size_3308_ = crate::leanh::lean_ctor_get(v_r_3281_, 0);
                    crate::leanh::lean_inc(v_size_3308_);
                    v___y_3292_ = v___x_3307_;
                    v___y_3293_ = v___x_3306_;
                    v___y_3294_ = v_size_3308_;
                    state = 33;
                    continue;
                } else {
                    v___x_3309_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3292_ = v___x_3307_;
                    v___y_3293_ = v___x_3306_;
                    v___y_3294_ = v___x_3309_;
                    state = 33;
                    continue;
                }
            }
            38 => {
                if v_isShared_3260_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3259_, 4, v_r_3255_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 3, v___x_3323_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 2, v_v_3253_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 1, v_k_3252_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 0, v___x_3320_);
                    v___x_3325_ = v___x_3259_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_3326_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3326_, 0, v___x_3320_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3326_, 1, v_k_3252_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3326_, 2, v_v_3253_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3326_, 3, v___x_3323_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3326_, 4, v_r_3255_);
                    v___x_3325_ = v_reuseFailAlloc_3326_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_3325_;
            }
            40 => {
                if crate::leanh::lean_obj_tag(v_l_3254_) == 0 {
                    if crate::leanh::lean_obj_tag(v_r_3255_) == 0 {
                        v_k_3337_ = crate::leanh::lean_ctor_get(v___x_3261_, 0);
                        crate::leanh::lean_inc(v_k_3337_);
                        v_v_3338_ = crate::leanh::lean_ctor_get(v___x_3261_, 1);
                        crate::leanh::lean_inc(v_v_3338_);
                        crate::leanh::lean_dec_ref(v___x_3261_);
                        v_size_3339_ = crate::leanh::lean_ctor_get(v_l_3254_, 0);
                        v___x_3340_ = lean_nat_add(v___x_3256_, v_size_3251_);
                        crate::leanh::lean_dec(v_size_3251_);
                        v___x_3341_ = lean_nat_add(v___x_3256_, v_size_3339_);
                        if v_isShared_3336_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3335_, 4, v_l_3254_);
                            crate::leanh::lean_ctor_set(v___x_3335_, 3, v_tree_3262_);
                            crate::leanh::lean_ctor_set(v___x_3335_, 2, v_v_3338_);
                            crate::leanh::lean_ctor_set(v___x_3335_, 1, v_k_3337_);
                            crate::leanh::lean_ctor_set(v___x_3335_, 0, v___x_3341_);
                            v___x_3343_ = v___x_3335_;
                            state = 41;
                            continue;
                        } else {
                            v_reuseFailAlloc_3347_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3347_, 0, v___x_3341_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3347_, 1, v_k_3337_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3347_, 2, v_v_3338_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3347_, 3, v_tree_3262_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3347_, 4, v_l_3254_);
                            v___x_3343_ = v_reuseFailAlloc_3347_;
                            state = 41;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_size_3251_);
                        v_k_3348_ = crate::leanh::lean_ctor_get(v___x_3261_, 0);
                        crate::leanh::lean_inc(v_k_3348_);
                        v_v_3349_ = crate::leanh::lean_ctor_get(v___x_3261_, 1);
                        crate::leanh::lean_inc(v_v_3349_);
                        crate::leanh::lean_dec_ref(v___x_3261_);
                        v_k_3350_ = crate::leanh::lean_ctor_get(v_l_3254_, 1);
                        v_v_3351_ = crate::leanh::lean_ctor_get(v_l_3254_, 2);
                        v_isSharedCheck_3365_ = (!crate::leanh::lean_is_exclusive(v_l_3254_)) as u8;
                        if v_isSharedCheck_3365_ == 0 {
                            v_unused_3366_ = crate::leanh::lean_ctor_get(v_l_3254_, 4);
                            crate::leanh::lean_dec(v_unused_3366_);
                            v_unused_3367_ = crate::leanh::lean_ctor_get(v_l_3254_, 3);
                            crate::leanh::lean_dec(v_unused_3367_);
                            v_unused_3368_ = crate::leanh::lean_ctor_get(v_l_3254_, 0);
                            crate::leanh::lean_dec(v_unused_3368_);
                            v___x_3353_ = v_l_3254_;
                            v_isShared_3354_ = v_isSharedCheck_3365_;
                            state = 43;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_v_3351_);
                            crate::leanh::lean_inc(v_k_3350_);
                            crate::leanh::lean_dec(v_l_3254_);
                            v___x_3353_ = crate::leanh::lean_box(0);
                            v_isShared_3354_ = v_isSharedCheck_3365_;
                            state = 43;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_r_3255_) == 0 {
                        crate::leanh::lean_dec(v_size_3251_);
                        v_k_3369_ = crate::leanh::lean_ctor_get(v___x_3261_, 0);
                        crate::leanh::lean_inc(v_k_3369_);
                        v_v_3370_ = crate::leanh::lean_ctor_get(v___x_3261_, 1);
                        crate::leanh::lean_inc(v_v_3370_);
                        crate::leanh::lean_dec_ref(v___x_3261_);
                        v___x_3371_ = crate::leanh::lean_unsigned_to_nat(3);
                        if v_isShared_3336_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3335_, 4, v_l_3254_);
                            crate::leanh::lean_ctor_set(v___x_3335_, 2, v_v_3370_);
                            crate::leanh::lean_ctor_set(v___x_3335_, 1, v_k_3369_);
                            crate::leanh::lean_ctor_set(v___x_3335_, 0, v___x_3256_);
                            v___x_3373_ = v___x_3335_;
                            state = 47;
                            continue;
                        } else {
                            v_reuseFailAlloc_3377_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3377_, 0, v___x_3256_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3377_, 1, v_k_3369_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3377_, 2, v_v_3370_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3377_, 3, v_l_3254_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3377_, 4, v_l_3254_);
                            v___x_3373_ = v_reuseFailAlloc_3377_;
                            state = 47;
                            continue;
                        }
                    } else {
                        v_k_3378_ = crate::leanh::lean_ctor_get(v___x_3261_, 0);
                        crate::leanh::lean_inc(v_k_3378_);
                        v_v_3379_ = crate::leanh::lean_ctor_get(v___x_3261_, 1);
                        crate::leanh::lean_inc(v_v_3379_);
                        crate::leanh::lean_dec_ref(v___x_3261_);
                        if v_isShared_3336_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3335_, 3, v_r_3255_);
                            v___x_3381_ = v___x_3335_;
                            state = 49;
                            continue;
                        } else {
                            v_reuseFailAlloc_3386_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_size_3251_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3386_, 1, v_k_3252_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3386_, 2, v_v_3253_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3386_, 3, v_r_3255_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3386_, 4, v_r_3255_);
                            v___x_3381_ = v_reuseFailAlloc_3386_;
                            state = 49;
                            continue;
                        }
                    }
                }
            }
            41 => {
                if v_isShared_3260_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3259_, 4, v_r_3255_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 3, v___x_3343_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 2, v_v_3253_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 1, v_k_3252_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 0, v___x_3340_);
                    v___x_3345_ = v___x_3259_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_3346_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3346_, 0, v___x_3340_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3346_, 1, v_k_3252_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3346_, 2, v_v_3253_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3346_, 3, v___x_3343_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3346_, 4, v_r_3255_);
                    v___x_3345_ = v_reuseFailAlloc_3346_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_3345_;
            }
            43 => {
                v___x_3355_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_3354_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3353_, 4, v_r_3255_);
                    crate::leanh::lean_ctor_set(v___x_3353_, 3, v_r_3255_);
                    crate::leanh::lean_ctor_set(v___x_3353_, 2, v_v_3349_);
                    crate::leanh::lean_ctor_set(v___x_3353_, 1, v_k_3348_);
                    crate::leanh::lean_ctor_set(v___x_3353_, 0, v___x_3256_);
                    v___x_3357_ = v___x_3353_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_3364_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3364_, 0, v___x_3256_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3364_, 1, v_k_3348_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3364_, 2, v_v_3349_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3364_, 3, v_r_3255_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3364_, 4, v_r_3255_);
                    v___x_3357_ = v_reuseFailAlloc_3364_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                if v_isShared_3336_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3335_, 3, v_r_3255_);
                    crate::leanh::lean_ctor_set(v___x_3335_, 0, v___x_3256_);
                    v___x_3359_ = v___x_3335_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_3363_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3256_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3363_, 1, v_k_3252_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3363_, 2, v_v_3253_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3363_, 3, v_r_3255_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3363_, 4, v_r_3255_);
                    v___x_3359_ = v_reuseFailAlloc_3363_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                if v_isShared_3260_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3259_, 4, v___x_3359_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 3, v___x_3357_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 2, v_v_3351_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 1, v_k_3350_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 0, v___x_3355_);
                    v___x_3361_ = v___x_3259_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_3362_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3362_, 0, v___x_3355_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3362_, 1, v_k_3350_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3362_, 2, v_v_3351_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3362_, 3, v___x_3357_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3362_, 4, v___x_3359_);
                    v___x_3361_ = v_reuseFailAlloc_3362_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_3361_;
            }
            47 => {
                if v_isShared_3260_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3259_, 4, v_r_3255_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 3, v___x_3373_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 2, v_v_3253_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 1, v_k_3252_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 0, v___x_3371_);
                    v___x_3375_ = v___x_3259_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_3376_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3371_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3376_, 1, v_k_3252_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3376_, 2, v_v_3253_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3376_, 3, v___x_3373_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3376_, 4, v_r_3255_);
                    v___x_3375_ = v_reuseFailAlloc_3376_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_3375_;
            }
            49 => {
                v___x_3382_ = crate::leanh::lean_unsigned_to_nat(2);
                if v_isShared_3260_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3259_, 4, v___x_3381_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 3, v_r_3255_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 2, v_v_3379_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 1, v_k_3378_);
                    crate::leanh::lean_ctor_set(v___x_3259_, 0, v___x_3382_);
                    v___x_3384_ = v___x_3259_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_3385_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3385_, 0, v___x_3382_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3385_, 1, v_k_3378_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3385_, 2, v_v_3379_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3385_, 3, v_r_3255_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3385_, 4, v___x_3381_);
                    v___x_3384_ = v_reuseFailAlloc_3385_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_3384_;
            }
            51 => {
                v___x_3402_ = l_Std_DTreeMap_Internal_Impl_minView___redArg(
                    v_k_3252_, v_v_3253_, v_l_3254_, v_r_3255_,
                );
                v_tree_3403_ = crate::leanh::lean_ctor_get(v___x_3402_, 2);
                crate::leanh::lean_inc(v_tree_3403_);
                if crate::leanh::lean_obj_tag(v_tree_3403_) == 0 {
                    v_k_3404_ = crate::leanh::lean_ctor_get(v___x_3402_, 0);
                    crate::leanh::lean_inc(v_k_3404_);
                    v_v_3405_ = crate::leanh::lean_ctor_get(v___x_3402_, 1);
                    crate::leanh::lean_inc(v_v_3405_);
                    crate::leanh::lean_dec_ref(v___x_3402_);
                    v_size_3406_ = crate::leanh::lean_ctor_get(v_tree_3403_, 0);
                    v___x_3407_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_3408_ = lean_nat_mul(v___x_3407_, v_size_3406_);
                    v___x_3409_ = lean_nat_dec_lt(v___x_3408_, v_size_3246_);
                    crate::leanh::lean_dec(v___x_3408_);
                    if v___x_3409_ == 0 {
                        crate::leanh::lean_dec(v_r_3250_);
                        v___x_3410_ = lean_nat_add(v___x_3256_, v_size_3246_);
                        v___x_3411_ = lean_nat_add(v___x_3410_, v_size_3406_);
                        crate::leanh::lean_dec(v___x_3410_);
                        if v_isShared_3401_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3400_, 4, v_tree_3403_);
                            crate::leanh::lean_ctor_set(v___x_3400_, 3, v_l_3066_);
                            crate::leanh::lean_ctor_set(v___x_3400_, 2, v_v_3405_);
                            crate::leanh::lean_ctor_set(v___x_3400_, 1, v_k_3404_);
                            crate::leanh::lean_ctor_set(v___x_3400_, 0, v___x_3411_);
                            v___x_3413_ = v___x_3400_;
                            state = 52;
                            continue;
                        } else {
                            v_reuseFailAlloc_3414_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3414_, 0, v___x_3411_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3414_, 1, v_k_3404_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3414_, 2, v_v_3405_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3414_, 3, v_l_3066_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3414_, 4, v_tree_3403_);
                            v___x_3413_ = v_reuseFailAlloc_3414_;
                            state = 52;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_inc(v_l_3249_);
                        crate::leanh::lean_inc(v_v_3248_);
                        crate::leanh::lean_inc(v_k_3247_);
                        crate::leanh::lean_inc(v_size_3246_);
                        v_isSharedCheck_3480_ = (!crate::leanh::lean_is_exclusive(v_l_3066_)) as u8;
                        if v_isSharedCheck_3480_ == 0 {
                            v_unused_3481_ = crate::leanh::lean_ctor_get(v_l_3066_, 4);
                            crate::leanh::lean_dec(v_unused_3481_);
                            v_unused_3482_ = crate::leanh::lean_ctor_get(v_l_3066_, 3);
                            crate::leanh::lean_dec(v_unused_3482_);
                            v_unused_3483_ = crate::leanh::lean_ctor_get(v_l_3066_, 2);
                            crate::leanh::lean_dec(v_unused_3483_);
                            v_unused_3484_ = crate::leanh::lean_ctor_get(v_l_3066_, 1);
                            crate::leanh::lean_dec(v_unused_3484_);
                            v_unused_3485_ = crate::leanh::lean_ctor_get(v_l_3066_, 0);
                            crate::leanh::lean_dec(v_unused_3485_);
                            v___x_3416_ = v_l_3066_;
                            v_isShared_3417_ = v_isSharedCheck_3480_;
                            state = 53;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_l_3066_);
                            v___x_3416_ = crate::leanh::lean_box(0);
                            v_isShared_3417_ = v_isSharedCheck_3480_;
                            state = 53;
                            continue;
                        }
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_l_3249_) == 0 {
                        crate::leanh::lean_inc_ref(v_l_3249_);
                        crate::leanh::lean_inc(v_v_3248_);
                        crate::leanh::lean_inc(v_k_3247_);
                        crate::leanh::lean_inc(v_size_3246_);
                        v_isSharedCheck_3509_ = (!crate::leanh::lean_is_exclusive(v_l_3066_)) as u8;
                        if v_isSharedCheck_3509_ == 0 {
                            v_unused_3510_ = crate::leanh::lean_ctor_get(v_l_3066_, 4);
                            crate::leanh::lean_dec(v_unused_3510_);
                            v_unused_3511_ = crate::leanh::lean_ctor_get(v_l_3066_, 3);
                            crate::leanh::lean_dec(v_unused_3511_);
                            v_unused_3512_ = crate::leanh::lean_ctor_get(v_l_3066_, 2);
                            crate::leanh::lean_dec(v_unused_3512_);
                            v_unused_3513_ = crate::leanh::lean_ctor_get(v_l_3066_, 1);
                            crate::leanh::lean_dec(v_unused_3513_);
                            v_unused_3514_ = crate::leanh::lean_ctor_get(v_l_3066_, 0);
                            crate::leanh::lean_dec(v_unused_3514_);
                            v___x_3487_ = v_l_3066_;
                            v_isShared_3488_ = v_isSharedCheck_3509_;
                            state = 63;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_l_3066_);
                            v___x_3487_ = crate::leanh::lean_box(0);
                            v_isShared_3488_ = v_isSharedCheck_3509_;
                            state = 63;
                            continue;
                        }
                    } else {
                        if crate::leanh::lean_obj_tag(v_r_3250_) == 0 {
                            crate::leanh::lean_inc(v_l_3249_);
                            crate::leanh::lean_inc(v_v_3248_);
                            crate::leanh::lean_inc(v_k_3247_);
                            v_isSharedCheck_3539_ =
                                (!crate::leanh::lean_is_exclusive(v_l_3066_)) as u8;
                            if v_isSharedCheck_3539_ == 0 {
                                v_unused_3540_ = crate::leanh::lean_ctor_get(v_l_3066_, 4);
                                crate::leanh::lean_dec(v_unused_3540_);
                                v_unused_3541_ = crate::leanh::lean_ctor_get(v_l_3066_, 3);
                                crate::leanh::lean_dec(v_unused_3541_);
                                v_unused_3542_ = crate::leanh::lean_ctor_get(v_l_3066_, 2);
                                crate::leanh::lean_dec(v_unused_3542_);
                                v_unused_3543_ = crate::leanh::lean_ctor_get(v_l_3066_, 1);
                                crate::leanh::lean_dec(v_unused_3543_);
                                v_unused_3544_ = crate::leanh::lean_ctor_get(v_l_3066_, 0);
                                crate::leanh::lean_dec(v_unused_3544_);
                                v___x_3516_ = v_l_3066_;
                                v_isShared_3517_ = v_isSharedCheck_3539_;
                                state = 68;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_l_3066_);
                                v___x_3516_ = crate::leanh::lean_box(0);
                                v_isShared_3517_ = v_isSharedCheck_3539_;
                                state = 68;
                                continue;
                            }
                        } else {
                            v_k_3545_ = crate::leanh::lean_ctor_get(v___x_3402_, 0);
                            crate::leanh::lean_inc(v_k_3545_);
                            v_v_3546_ = crate::leanh::lean_ctor_get(v___x_3402_, 1);
                            crate::leanh::lean_inc(v_v_3546_);
                            crate::leanh::lean_dec_ref(v___x_3402_);
                            v___x_3547_ = crate::leanh::lean_unsigned_to_nat(2);
                            if v_isShared_3401_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3400_, 4, v_r_3250_);
                                crate::leanh::lean_ctor_set(v___x_3400_, 3, v_l_3066_);
                                crate::leanh::lean_ctor_set(v___x_3400_, 2, v_v_3546_);
                                crate::leanh::lean_ctor_set(v___x_3400_, 1, v_k_3545_);
                                crate::leanh::lean_ctor_set(v___x_3400_, 0, v___x_3547_);
                                v___x_3549_ = v___x_3400_;
                                state = 73;
                                continue;
                            } else {
                                v_reuseFailAlloc_3550_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3550_, 0, v___x_3547_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3550_, 1, v_k_3545_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3550_, 2, v_v_3546_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3550_, 3, v_l_3066_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3550_, 4, v_r_3250_);
                                v___x_3549_ = v_reuseFailAlloc_3550_;
                                state = 73;
                                continue;
                            }
                        }
                    }
                }
            }
            52 => {
                return v___x_3413_;
            }
            53 => {
                v_size_3418_ = crate::leanh::lean_ctor_get(v_l_3249_, 0);
                v_size_3419_ = crate::leanh::lean_ctor_get(v_r_3250_, 0);
                v_k_3420_ = crate::leanh::lean_ctor_get(v_r_3250_, 1);
                v_v_3421_ = crate::leanh::lean_ctor_get(v_r_3250_, 2);
                v_l_3422_ = crate::leanh::lean_ctor_get(v_r_3250_, 3);
                v_r_3423_ = crate::leanh::lean_ctor_get(v_r_3250_, 4);
                v___x_3424_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3425_ = lean_nat_mul(v___x_3424_, v_size_3418_);
                v___x_3426_ = lean_nat_dec_lt(v_size_3419_, v___x_3425_);
                crate::leanh::lean_dec(v___x_3425_);
                if v___x_3426_ == 0 {
                    crate::leanh::lean_inc(v_r_3423_);
                    crate::leanh::lean_inc(v_l_3422_);
                    crate::leanh::lean_inc(v_v_3421_);
                    crate::leanh::lean_inc(v_k_3420_);
                    crate::leanh::lean_del_object(v___x_3416_);
                    v_isSharedCheck_3464_ = (!crate::leanh::lean_is_exclusive(v_r_3250_)) as u8;
                    if v_isSharedCheck_3464_ == 0 {
                        v_unused_3465_ = crate::leanh::lean_ctor_get(v_r_3250_, 4);
                        crate::leanh::lean_dec(v_unused_3465_);
                        v_unused_3466_ = crate::leanh::lean_ctor_get(v_r_3250_, 3);
                        crate::leanh::lean_dec(v_unused_3466_);
                        v_unused_3467_ = crate::leanh::lean_ctor_get(v_r_3250_, 2);
                        crate::leanh::lean_dec(v_unused_3467_);
                        v_unused_3468_ = crate::leanh::lean_ctor_get(v_r_3250_, 1);
                        crate::leanh::lean_dec(v_unused_3468_);
                        v_unused_3469_ = crate::leanh::lean_ctor_get(v_r_3250_, 0);
                        crate::leanh::lean_dec(v_unused_3469_);
                        v___x_3428_ = v_r_3250_;
                        v_isShared_3429_ = v_isSharedCheck_3464_;
                        state = 54;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_3250_);
                        v___x_3428_ = crate::leanh::lean_box(0);
                        v_isShared_3429_ = v_isSharedCheck_3464_;
                        state = 54;
                        continue;
                    }
                } else {
                    v___x_3470_ = lean_nat_add(v___x_3256_, v_size_3246_);
                    crate::leanh::lean_dec(v_size_3246_);
                    v___x_3471_ = lean_nat_add(v___x_3470_, v_size_3406_);
                    crate::leanh::lean_dec(v___x_3470_);
                    v___x_3472_ = lean_nat_add(v___x_3256_, v_size_3406_);
                    v___x_3473_ = lean_nat_add(v___x_3472_, v_size_3419_);
                    crate::leanh::lean_dec(v___x_3472_);
                    if v_isShared_3401_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3400_, 4, v_tree_3403_);
                        crate::leanh::lean_ctor_set(v___x_3400_, 3, v_r_3250_);
                        crate::leanh::lean_ctor_set(v___x_3400_, 2, v_v_3405_);
                        crate::leanh::lean_ctor_set(v___x_3400_, 1, v_k_3404_);
                        crate::leanh::lean_ctor_set(v___x_3400_, 0, v___x_3473_);
                        v___x_3475_ = v___x_3400_;
                        state = 61;
                        continue;
                    } else {
                        v_reuseFailAlloc_3479_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3479_, 0, v___x_3473_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3479_, 1, v_k_3404_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3479_, 2, v_v_3405_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3479_, 3, v_r_3250_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3479_, 4, v_tree_3403_);
                        v___x_3475_ = v_reuseFailAlloc_3479_;
                        state = 61;
                        continue;
                    }
                }
            }
            54 => {
                v___x_3430_ = lean_nat_add(v___x_3256_, v_size_3246_);
                crate::leanh::lean_dec(v_size_3246_);
                v___x_3431_ = lean_nat_add(v___x_3430_, v_size_3406_);
                crate::leanh::lean_dec(v___x_3430_);
                v___x_3452_ = lean_nat_add(v___x_3256_, v_size_3418_);
                if crate::leanh::lean_obj_tag(v_l_3422_) == 0 {
                    v_size_3462_ = crate::leanh::lean_ctor_get(v_l_3422_, 0);
                    crate::leanh::lean_inc(v_size_3462_);
                    v___y_3454_ = v_size_3462_;
                    state = 59;
                    continue;
                } else {
                    v___x_3463_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3454_ = v___x_3463_;
                    state = 59;
                    continue;
                }
            }
            55 => {
                v___x_3436_ = lean_nat_add(v___y_3434_, v___y_3435_);
                crate::leanh::lean_dec(v___y_3435_);
                crate::leanh::lean_dec(v___y_3434_);
                crate::leanh::lean_inc_ref(v_tree_3403_);
                if v_isShared_3429_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3428_, 4, v_tree_3403_);
                    crate::leanh::lean_ctor_set(v___x_3428_, 3, v_r_3423_);
                    crate::leanh::lean_ctor_set(v___x_3428_, 2, v_v_3405_);
                    crate::leanh::lean_ctor_set(v___x_3428_, 1, v_k_3404_);
                    crate::leanh::lean_ctor_set(v___x_3428_, 0, v___x_3436_);
                    v___x_3438_ = v___x_3428_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_3451_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3451_, 0, v___x_3436_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3451_, 1, v_k_3404_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3451_, 2, v_v_3405_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3451_, 3, v_r_3423_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3451_, 4, v_tree_3403_);
                    v___x_3438_ = v_reuseFailAlloc_3451_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                v_isSharedCheck_3445_ = (!crate::leanh::lean_is_exclusive(v_tree_3403_)) as u8;
                if v_isSharedCheck_3445_ == 0 {
                    v_unused_3446_ = crate::leanh::lean_ctor_get(v_tree_3403_, 4);
                    crate::leanh::lean_dec(v_unused_3446_);
                    v_unused_3447_ = crate::leanh::lean_ctor_get(v_tree_3403_, 3);
                    crate::leanh::lean_dec(v_unused_3447_);
                    v_unused_3448_ = crate::leanh::lean_ctor_get(v_tree_3403_, 2);
                    crate::leanh::lean_dec(v_unused_3448_);
                    v_unused_3449_ = crate::leanh::lean_ctor_get(v_tree_3403_, 1);
                    crate::leanh::lean_dec(v_unused_3449_);
                    v_unused_3450_ = crate::leanh::lean_ctor_get(v_tree_3403_, 0);
                    crate::leanh::lean_dec(v_unused_3450_);
                    v___x_3440_ = v_tree_3403_;
                    v_isShared_3441_ = v_isSharedCheck_3445_;
                    state = 57;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_tree_3403_);
                    v___x_3440_ = crate::leanh::lean_box(0);
                    v_isShared_3441_ = v_isSharedCheck_3445_;
                    state = 57;
                    continue;
                }
            }
            57 => {
                if v_isShared_3441_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3440_, 4, v___x_3438_);
                    crate::leanh::lean_ctor_set(v___x_3440_, 3, v___y_3433_);
                    crate::leanh::lean_ctor_set(v___x_3440_, 2, v_v_3421_);
                    crate::leanh::lean_ctor_set(v___x_3440_, 1, v_k_3420_);
                    crate::leanh::lean_ctor_set(v___x_3440_, 0, v___x_3431_);
                    v___x_3443_ = v___x_3440_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_3444_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3431_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3444_, 1, v_k_3420_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3444_, 2, v_v_3421_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3444_, 3, v___y_3433_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3444_, 4, v___x_3438_);
                    v___x_3443_ = v_reuseFailAlloc_3444_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_3443_;
            }
            59 => {
                v___x_3455_ = lean_nat_add(v___x_3452_, v___y_3454_);
                crate::leanh::lean_dec(v___y_3454_);
                crate::leanh::lean_dec(v___x_3452_);
                if v_isShared_3401_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3400_, 4, v_l_3422_);
                    crate::leanh::lean_ctor_set(v___x_3400_, 3, v_l_3249_);
                    crate::leanh::lean_ctor_set(v___x_3400_, 2, v_v_3248_);
                    crate::leanh::lean_ctor_set(v___x_3400_, 1, v_k_3247_);
                    crate::leanh::lean_ctor_set(v___x_3400_, 0, v___x_3455_);
                    v___x_3457_ = v___x_3400_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_3461_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_k_3247_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3461_, 2, v_v_3248_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3461_, 3, v_l_3249_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3461_, 4, v_l_3422_);
                    v___x_3457_ = v_reuseFailAlloc_3461_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                v___x_3458_ = lean_nat_add(v___x_3256_, v_size_3406_);
                if crate::leanh::lean_obj_tag(v_r_3423_) == 0 {
                    v_size_3459_ = crate::leanh::lean_ctor_get(v_r_3423_, 0);
                    crate::leanh::lean_inc(v_size_3459_);
                    v___y_3433_ = v___x_3457_;
                    v___y_3434_ = v___x_3458_;
                    v___y_3435_ = v_size_3459_;
                    state = 55;
                    continue;
                } else {
                    v___x_3460_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3433_ = v___x_3457_;
                    v___y_3434_ = v___x_3458_;
                    v___y_3435_ = v___x_3460_;
                    state = 55;
                    continue;
                }
            }
            61 => {
                if v_isShared_3417_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3416_, 4, v___x_3475_);
                    crate::leanh::lean_ctor_set(v___x_3416_, 0, v___x_3471_);
                    v___x_3477_ = v___x_3416_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_3478_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3478_, 0, v___x_3471_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3478_, 1, v_k_3247_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3478_, 2, v_v_3248_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3478_, 3, v_l_3249_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3478_, 4, v___x_3475_);
                    v___x_3477_ = v_reuseFailAlloc_3478_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_3477_;
            }
            63 => {
                if crate::leanh::lean_obj_tag(v_r_3250_) == 0 {
                    v_k_3489_ = crate::leanh::lean_ctor_get(v___x_3402_, 0);
                    crate::leanh::lean_inc(v_k_3489_);
                    v_v_3490_ = crate::leanh::lean_ctor_get(v___x_3402_, 1);
                    crate::leanh::lean_inc(v_v_3490_);
                    crate::leanh::lean_dec_ref(v___x_3402_);
                    v_size_3491_ = crate::leanh::lean_ctor_get(v_r_3250_, 0);
                    v___x_3492_ = lean_nat_add(v___x_3256_, v_size_3246_);
                    crate::leanh::lean_dec(v_size_3246_);
                    v___x_3493_ = lean_nat_add(v___x_3256_, v_size_3491_);
                    if v_isShared_3401_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3400_, 4, v_tree_3403_);
                        crate::leanh::lean_ctor_set(v___x_3400_, 3, v_r_3250_);
                        crate::leanh::lean_ctor_set(v___x_3400_, 2, v_v_3490_);
                        crate::leanh::lean_ctor_set(v___x_3400_, 1, v_k_3489_);
                        crate::leanh::lean_ctor_set(v___x_3400_, 0, v___x_3493_);
                        v___x_3495_ = v___x_3400_;
                        state = 64;
                        continue;
                    } else {
                        v_reuseFailAlloc_3499_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3499_, 0, v___x_3493_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3499_, 1, v_k_3489_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3499_, 2, v_v_3490_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3499_, 3, v_r_3250_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3499_, 4, v_tree_3403_);
                        v___x_3495_ = v_reuseFailAlloc_3499_;
                        state = 64;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_size_3246_);
                    v_k_3500_ = crate::leanh::lean_ctor_get(v___x_3402_, 0);
                    crate::leanh::lean_inc(v_k_3500_);
                    v_v_3501_ = crate::leanh::lean_ctor_get(v___x_3402_, 1);
                    crate::leanh::lean_inc(v_v_3501_);
                    crate::leanh::lean_dec_ref(v___x_3402_);
                    v___x_3502_ = crate::leanh::lean_unsigned_to_nat(3);
                    if v_isShared_3401_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3400_, 4, v_r_3250_);
                        crate::leanh::lean_ctor_set(v___x_3400_, 3, v_r_3250_);
                        crate::leanh::lean_ctor_set(v___x_3400_, 2, v_v_3501_);
                        crate::leanh::lean_ctor_set(v___x_3400_, 1, v_k_3500_);
                        crate::leanh::lean_ctor_set(v___x_3400_, 0, v___x_3256_);
                        v___x_3504_ = v___x_3400_;
                        state = 66;
                        continue;
                    } else {
                        v_reuseFailAlloc_3508_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3256_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3508_, 1, v_k_3500_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3508_, 2, v_v_3501_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3508_, 3, v_r_3250_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3508_, 4, v_r_3250_);
                        v___x_3504_ = v_reuseFailAlloc_3508_;
                        state = 66;
                        continue;
                    }
                }
            }
            64 => {
                if v_isShared_3488_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3487_, 4, v___x_3495_);
                    crate::leanh::lean_ctor_set(v___x_3487_, 0, v___x_3492_);
                    v___x_3497_ = v___x_3487_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_3498_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3498_, 0, v___x_3492_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3498_, 1, v_k_3247_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3498_, 2, v_v_3248_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3498_, 3, v_l_3249_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3498_, 4, v___x_3495_);
                    v___x_3497_ = v_reuseFailAlloc_3498_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_3497_;
            }
            66 => {
                if v_isShared_3488_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3487_, 4, v___x_3504_);
                    crate::leanh::lean_ctor_set(v___x_3487_, 0, v___x_3502_);
                    v___x_3506_ = v___x_3487_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_3507_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3507_, 0, v___x_3502_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3507_, 1, v_k_3247_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3507_, 2, v_v_3248_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3507_, 3, v_l_3249_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3507_, 4, v___x_3504_);
                    v___x_3506_ = v_reuseFailAlloc_3507_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_3506_;
            }
            68 => {
                v_k_3518_ = crate::leanh::lean_ctor_get(v___x_3402_, 0);
                crate::leanh::lean_inc(v_k_3518_);
                v_v_3519_ = crate::leanh::lean_ctor_get(v___x_3402_, 1);
                crate::leanh::lean_inc(v_v_3519_);
                crate::leanh::lean_dec_ref(v___x_3402_);
                v_k_3520_ = crate::leanh::lean_ctor_get(v_r_3250_, 1);
                v_v_3521_ = crate::leanh::lean_ctor_get(v_r_3250_, 2);
                v_isSharedCheck_3535_ = (!crate::leanh::lean_is_exclusive(v_r_3250_)) as u8;
                if v_isSharedCheck_3535_ == 0 {
                    v_unused_3536_ = crate::leanh::lean_ctor_get(v_r_3250_, 4);
                    crate::leanh::lean_dec(v_unused_3536_);
                    v_unused_3537_ = crate::leanh::lean_ctor_get(v_r_3250_, 3);
                    crate::leanh::lean_dec(v_unused_3537_);
                    v_unused_3538_ = crate::leanh::lean_ctor_get(v_r_3250_, 0);
                    crate::leanh::lean_dec(v_unused_3538_);
                    v___x_3523_ = v_r_3250_;
                    v_isShared_3524_ = v_isSharedCheck_3535_;
                    state = 69;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_3521_);
                    crate::leanh::lean_inc(v_k_3520_);
                    crate::leanh::lean_dec(v_r_3250_);
                    v___x_3523_ = crate::leanh::lean_box(0);
                    v_isShared_3524_ = v_isSharedCheck_3535_;
                    state = 69;
                    continue;
                }
            }
            69 => {
                v___x_3525_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_3524_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3523_, 4, v_l_3249_);
                    crate::leanh::lean_ctor_set(v___x_3523_, 3, v_l_3249_);
                    crate::leanh::lean_ctor_set(v___x_3523_, 2, v_v_3248_);
                    crate::leanh::lean_ctor_set(v___x_3523_, 1, v_k_3247_);
                    crate::leanh::lean_ctor_set(v___x_3523_, 0, v___x_3256_);
                    v___x_3527_ = v___x_3523_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_3534_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3534_, 0, v___x_3256_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3534_, 1, v_k_3247_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3534_, 2, v_v_3248_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3534_, 3, v_l_3249_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3534_, 4, v_l_3249_);
                    v___x_3527_ = v_reuseFailAlloc_3534_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                if v_isShared_3401_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3400_, 4, v_l_3249_);
                    crate::leanh::lean_ctor_set(v___x_3400_, 3, v_l_3249_);
                    crate::leanh::lean_ctor_set(v___x_3400_, 2, v_v_3519_);
                    crate::leanh::lean_ctor_set(v___x_3400_, 1, v_k_3518_);
                    crate::leanh::lean_ctor_set(v___x_3400_, 0, v___x_3256_);
                    v___x_3529_ = v___x_3400_;
                    state = 71;
                    continue;
                } else {
                    v_reuseFailAlloc_3533_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3533_, 0, v___x_3256_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3533_, 1, v_k_3518_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3533_, 2, v_v_3519_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3533_, 3, v_l_3249_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3533_, 4, v_l_3249_);
                    v___x_3529_ = v_reuseFailAlloc_3533_;
                    state = 71;
                    continue;
                }
            }
            71 => {
                if v_isShared_3517_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3516_, 4, v___x_3529_);
                    crate::leanh::lean_ctor_set(v___x_3516_, 3, v___x_3527_);
                    crate::leanh::lean_ctor_set(v___x_3516_, 2, v_v_3521_);
                    crate::leanh::lean_ctor_set(v___x_3516_, 1, v_k_3520_);
                    crate::leanh::lean_ctor_set(v___x_3516_, 0, v___x_3525_);
                    v___x_3531_ = v___x_3516_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_3532_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3525_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3532_, 1, v_k_3520_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3532_, 2, v_v_3521_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3532_, 3, v___x_3527_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3532_, 4, v___x_3529_);
                    v___x_3531_ = v_reuseFailAlloc_3532_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                return v___x_3531_;
            }
            73 => {
                return v___x_3549_;
            }
            74 => {
                return v___x_3571_;
            }
            75 => {
                v_size_3576_ = crate::leanh::lean_ctor_get(v_l_3563_, 0);
                v_size_3577_ = crate::leanh::lean_ctor_get(v_r_3564_, 0);
                v_k_3578_ = crate::leanh::lean_ctor_get(v_r_3564_, 1);
                v_v_3579_ = crate::leanh::lean_ctor_get(v_r_3564_, 2);
                v_l_3580_ = crate::leanh::lean_ctor_get(v_r_3564_, 3);
                v_r_3581_ = crate::leanh::lean_ctor_get(v_r_3564_, 4);
                v___x_3582_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3583_ = lean_nat_mul(v___x_3582_, v_size_3576_);
                v___x_3584_ = lean_nat_dec_lt(v_size_3577_, v___x_3583_);
                crate::leanh::lean_dec(v___x_3583_);
                if v___x_3584_ == 0 {
                    crate::leanh::lean_inc(v_r_3581_);
                    crate::leanh::lean_inc(v_l_3580_);
                    crate::leanh::lean_inc(v_v_3579_);
                    crate::leanh::lean_inc(v_k_3578_);
                    v_isSharedCheck_3613_ = (!crate::leanh::lean_is_exclusive(v_r_3564_)) as u8;
                    if v_isSharedCheck_3613_ == 0 {
                        v_unused_3614_ = crate::leanh::lean_ctor_get(v_r_3564_, 4);
                        crate::leanh::lean_dec(v_unused_3614_);
                        v_unused_3615_ = crate::leanh::lean_ctor_get(v_r_3564_, 3);
                        crate::leanh::lean_dec(v_unused_3615_);
                        v_unused_3616_ = crate::leanh::lean_ctor_get(v_r_3564_, 2);
                        crate::leanh::lean_dec(v_unused_3616_);
                        v_unused_3617_ = crate::leanh::lean_ctor_get(v_r_3564_, 1);
                        crate::leanh::lean_dec(v_unused_3617_);
                        v_unused_3618_ = crate::leanh::lean_ctor_get(v_r_3564_, 0);
                        crate::leanh::lean_dec(v_unused_3618_);
                        v___x_3586_ = v_r_3564_;
                        v_isShared_3587_ = v_isSharedCheck_3613_;
                        state = 76;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_3564_);
                        v___x_3586_ = crate::leanh::lean_box(0);
                        v_isShared_3587_ = v_isSharedCheck_3613_;
                        state = 76;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3069_);
                    v___x_3619_ = lean_nat_add(v___x_3558_, v_size_3560_);
                    crate::leanh::lean_dec(v_size_3560_);
                    v___x_3620_ = lean_nat_add(v___x_3619_, v_size_3559_);
                    crate::leanh::lean_dec(v___x_3619_);
                    v___x_3621_ = lean_nat_add(v___x_3558_, v_size_3559_);
                    crate::leanh::lean_dec(v_size_3559_);
                    v___x_3622_ = lean_nat_add(v___x_3621_, v_size_3577_);
                    crate::leanh::lean_dec(v___x_3621_);
                    crate::leanh::lean_inc_ref(v_impl_3557_);
                    if v_isShared_3575_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3574_, 4, v_impl_3557_);
                        crate::leanh::lean_ctor_set(v___x_3574_, 3, v_r_3564_);
                        crate::leanh::lean_ctor_set(v___x_3574_, 2, v_v_3065_);
                        crate::leanh::lean_ctor_set(v___x_3574_, 1, v_k_3064_);
                        crate::leanh::lean_ctor_set(v___x_3574_, 0, v___x_3622_);
                        v___x_3624_ = v___x_3574_;
                        state = 82;
                        continue;
                    } else {
                        v_reuseFailAlloc_3637_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3637_, 0, v___x_3622_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3637_, 1, v_k_3064_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3637_, 2, v_v_3065_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3637_, 3, v_r_3564_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3637_, 4, v_impl_3557_);
                        v___x_3624_ = v_reuseFailAlloc_3637_;
                        state = 82;
                        continue;
                    }
                }
            }
            76 => {
                v___x_3588_ = lean_nat_add(v___x_3558_, v_size_3560_);
                crate::leanh::lean_dec(v_size_3560_);
                v___x_3589_ = lean_nat_add(v___x_3588_, v_size_3559_);
                crate::leanh::lean_dec(v___x_3588_);
                v___x_3601_ = lean_nat_add(v___x_3558_, v_size_3576_);
                if crate::leanh::lean_obj_tag(v_l_3580_) == 0 {
                    v_size_3611_ = crate::leanh::lean_ctor_get(v_l_3580_, 0);
                    crate::leanh::lean_inc(v_size_3611_);
                    v___y_3603_ = v_size_3611_;
                    state = 80;
                    continue;
                } else {
                    v___x_3612_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3603_ = v___x_3612_;
                    state = 80;
                    continue;
                }
            }
            77 => {
                v___x_3594_ = lean_nat_add(v___y_3592_, v___y_3593_);
                crate::leanh::lean_dec(v___y_3593_);
                crate::leanh::lean_dec(v___y_3592_);
                if v_isShared_3587_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3586_, 4, v_impl_3557_);
                    crate::leanh::lean_ctor_set(v___x_3586_, 3, v_r_3581_);
                    crate::leanh::lean_ctor_set(v___x_3586_, 2, v_v_3065_);
                    crate::leanh::lean_ctor_set(v___x_3586_, 1, v_k_3064_);
                    crate::leanh::lean_ctor_set(v___x_3586_, 0, v___x_3594_);
                    v___x_3596_ = v___x_3586_;
                    state = 78;
                    continue;
                } else {
                    v_reuseFailAlloc_3600_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3594_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 1, v_k_3064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 2, v_v_3065_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 3, v_r_3581_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 4, v_impl_3557_);
                    v___x_3596_ = v_reuseFailAlloc_3600_;
                    state = 78;
                    continue;
                }
            }
            78 => {
                if v_isShared_3575_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3574_, 4, v___x_3596_);
                    crate::leanh::lean_ctor_set(v___x_3574_, 3, v___y_3591_);
                    crate::leanh::lean_ctor_set(v___x_3574_, 2, v_v_3579_);
                    crate::leanh::lean_ctor_set(v___x_3574_, 1, v_k_3578_);
                    crate::leanh::lean_ctor_set(v___x_3574_, 0, v___x_3589_);
                    v___x_3598_ = v___x_3574_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_3599_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3599_, 0, v___x_3589_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3599_, 1, v_k_3578_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3599_, 2, v_v_3579_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3599_, 3, v___y_3591_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3599_, 4, v___x_3596_);
                    v___x_3598_ = v_reuseFailAlloc_3599_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                return v___x_3598_;
            }
            80 => {
                v___x_3604_ = lean_nat_add(v___x_3601_, v___y_3603_);
                crate::leanh::lean_dec(v___y_3603_);
                crate::leanh::lean_dec(v___x_3601_);
                if v_isShared_3070_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3069_, 4, v_l_3580_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 3, v_l_3563_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 2, v_v_3562_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 1, v_k_3561_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 0, v___x_3604_);
                    v___x_3606_ = v___x_3069_;
                    state = 81;
                    continue;
                } else {
                    v_reuseFailAlloc_3610_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3604_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3610_, 1, v_k_3561_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3610_, 2, v_v_3562_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3610_, 3, v_l_3563_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3610_, 4, v_l_3580_);
                    v___x_3606_ = v_reuseFailAlloc_3610_;
                    state = 81;
                    continue;
                }
            }
            81 => {
                v___x_3607_ = lean_nat_add(v___x_3558_, v_size_3559_);
                crate::leanh::lean_dec(v_size_3559_);
                if crate::leanh::lean_obj_tag(v_r_3581_) == 0 {
                    v_size_3608_ = crate::leanh::lean_ctor_get(v_r_3581_, 0);
                    crate::leanh::lean_inc(v_size_3608_);
                    v___y_3591_ = v___x_3606_;
                    v___y_3592_ = v___x_3607_;
                    v___y_3593_ = v_size_3608_;
                    state = 77;
                    continue;
                } else {
                    v___x_3609_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3591_ = v___x_3606_;
                    v___y_3592_ = v___x_3607_;
                    v___y_3593_ = v___x_3609_;
                    state = 77;
                    continue;
                }
            }
            82 => {
                v_isSharedCheck_3631_ = (!crate::leanh::lean_is_exclusive(v_impl_3557_)) as u8;
                if v_isSharedCheck_3631_ == 0 {
                    v_unused_3632_ = crate::leanh::lean_ctor_get(v_impl_3557_, 4);
                    crate::leanh::lean_dec(v_unused_3632_);
                    v_unused_3633_ = crate::leanh::lean_ctor_get(v_impl_3557_, 3);
                    crate::leanh::lean_dec(v_unused_3633_);
                    v_unused_3634_ = crate::leanh::lean_ctor_get(v_impl_3557_, 2);
                    crate::leanh::lean_dec(v_unused_3634_);
                    v_unused_3635_ = crate::leanh::lean_ctor_get(v_impl_3557_, 1);
                    crate::leanh::lean_dec(v_unused_3635_);
                    v_unused_3636_ = crate::leanh::lean_ctor_get(v_impl_3557_, 0);
                    crate::leanh::lean_dec(v_unused_3636_);
                    v___x_3626_ = v_impl_3557_;
                    v_isShared_3627_ = v_isSharedCheck_3631_;
                    state = 83;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_impl_3557_);
                    v___x_3626_ = crate::leanh::lean_box(0);
                    v_isShared_3627_ = v_isSharedCheck_3631_;
                    state = 83;
                    continue;
                }
            }
            83 => {
                if v_isShared_3627_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3626_, 4, v___x_3624_);
                    crate::leanh::lean_ctor_set(v___x_3626_, 3, v_l_3563_);
                    crate::leanh::lean_ctor_set(v___x_3626_, 2, v_v_3562_);
                    crate::leanh::lean_ctor_set(v___x_3626_, 1, v_k_3561_);
                    crate::leanh::lean_ctor_set(v___x_3626_, 0, v___x_3620_);
                    v___x_3629_ = v___x_3626_;
                    state = 84;
                    continue;
                } else {
                    v_reuseFailAlloc_3630_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 0, v___x_3620_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 1, v_k_3561_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 2, v_v_3562_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 3, v_l_3563_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3630_, 4, v___x_3624_);
                    v___x_3629_ = v_reuseFailAlloc_3630_;
                    state = 84;
                    continue;
                }
            }
            84 => {
                return v___x_3629_;
            }
            85 => {
                return v___x_3647_;
            }
            86 => {
                v_size_3657_ = crate::leanh::lean_ctor_get(v_r_3650_, 0);
                v___x_3658_ = lean_nat_add(v___x_3558_, v_size_3651_);
                crate::leanh::lean_dec(v_size_3651_);
                v___x_3659_ = lean_nat_add(v___x_3558_, v_size_3657_);
                if v_isShared_3656_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3655_, 4, v_impl_3557_);
                    crate::leanh::lean_ctor_set(v___x_3655_, 3, v_r_3650_);
                    crate::leanh::lean_ctor_set(v___x_3655_, 2, v_v_3065_);
                    crate::leanh::lean_ctor_set(v___x_3655_, 1, v_k_3064_);
                    crate::leanh::lean_ctor_set(v___x_3655_, 0, v___x_3659_);
                    v___x_3661_ = v___x_3655_;
                    state = 87;
                    continue;
                } else {
                    v_reuseFailAlloc_3665_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3665_, 0, v___x_3659_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3665_, 1, v_k_3064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3665_, 2, v_v_3065_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3665_, 3, v_r_3650_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3665_, 4, v_impl_3557_);
                    v___x_3661_ = v_reuseFailAlloc_3665_;
                    state = 87;
                    continue;
                }
            }
            87 => {
                if v_isShared_3070_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3069_, 4, v___x_3661_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 3, v_l_3649_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 2, v_v_3653_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 1, v_k_3652_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 0, v___x_3658_);
                    v___x_3663_ = v___x_3069_;
                    state = 88;
                    continue;
                } else {
                    v_reuseFailAlloc_3664_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3658_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3664_, 1, v_k_3652_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3664_, 2, v_v_3653_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3664_, 3, v_l_3649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3664_, 4, v___x_3661_);
                    v___x_3663_ = v_reuseFailAlloc_3664_;
                    state = 88;
                    continue;
                }
            }
            88 => {
                return v___x_3663_;
            }
            89 => {
                v___x_3674_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_3673_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3672_, 3, v_r_3650_);
                    crate::leanh::lean_ctor_set(v___x_3672_, 2, v_v_3065_);
                    crate::leanh::lean_ctor_set(v___x_3672_, 1, v_k_3064_);
                    crate::leanh::lean_ctor_set(v___x_3672_, 0, v___x_3558_);
                    v___x_3676_ = v___x_3672_;
                    state = 90;
                    continue;
                } else {
                    v_reuseFailAlloc_3680_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3558_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3680_, 1, v_k_3064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3680_, 2, v_v_3065_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3680_, 3, v_r_3650_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3680_, 4, v_r_3650_);
                    v___x_3676_ = v_reuseFailAlloc_3680_;
                    state = 90;
                    continue;
                }
            }
            90 => {
                if v_isShared_3070_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3069_, 4, v___x_3676_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 3, v_l_3649_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 2, v_v_3670_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 1, v_k_3669_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 0, v___x_3674_);
                    v___x_3678_ = v___x_3069_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_3679_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3674_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3679_, 1, v_k_3669_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3679_, 2, v_v_3670_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3679_, 3, v_l_3649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3679_, 4, v___x_3676_);
                    v___x_3678_ = v_reuseFailAlloc_3679_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_3678_;
            }
            92 => {
                v_k_3691_ = crate::leanh::lean_ctor_get(v_r_3685_, 1);
                v_v_3692_ = crate::leanh::lean_ctor_get(v_r_3685_, 2);
                v_isSharedCheck_3706_ = (!crate::leanh::lean_is_exclusive(v_r_3685_)) as u8;
                if v_isSharedCheck_3706_ == 0 {
                    v_unused_3707_ = crate::leanh::lean_ctor_get(v_r_3685_, 4);
                    crate::leanh::lean_dec(v_unused_3707_);
                    v_unused_3708_ = crate::leanh::lean_ctor_get(v_r_3685_, 3);
                    crate::leanh::lean_dec(v_unused_3708_);
                    v_unused_3709_ = crate::leanh::lean_ctor_get(v_r_3685_, 0);
                    crate::leanh::lean_dec(v_unused_3709_);
                    v___x_3694_ = v_r_3685_;
                    v_isShared_3695_ = v_isSharedCheck_3706_;
                    state = 93;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_3692_);
                    crate::leanh::lean_inc(v_k_3691_);
                    crate::leanh::lean_dec(v_r_3685_);
                    v___x_3694_ = crate::leanh::lean_box(0);
                    v_isShared_3695_ = v_isSharedCheck_3706_;
                    state = 93;
                    continue;
                }
            }
            93 => {
                v___x_3696_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_3695_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3694_, 4, v_l_3649_);
                    crate::leanh::lean_ctor_set(v___x_3694_, 3, v_l_3649_);
                    crate::leanh::lean_ctor_set(v___x_3694_, 2, v_v_3687_);
                    crate::leanh::lean_ctor_set(v___x_3694_, 1, v_k_3686_);
                    crate::leanh::lean_ctor_set(v___x_3694_, 0, v___x_3558_);
                    v___x_3698_ = v___x_3694_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_3705_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3558_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3705_, 1, v_k_3686_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3705_, 2, v_v_3687_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3705_, 3, v_l_3649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3705_, 4, v_l_3649_);
                    v___x_3698_ = v_reuseFailAlloc_3705_;
                    state = 94;
                    continue;
                }
            }
            94 => {
                if v_isShared_3690_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3689_, 4, v_l_3649_);
                    crate::leanh::lean_ctor_set(v___x_3689_, 2, v_v_3065_);
                    crate::leanh::lean_ctor_set(v___x_3689_, 1, v_k_3064_);
                    crate::leanh::lean_ctor_set(v___x_3689_, 0, v___x_3558_);
                    v___x_3700_ = v___x_3689_;
                    state = 95;
                    continue;
                } else {
                    v_reuseFailAlloc_3704_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3704_, 0, v___x_3558_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3704_, 1, v_k_3064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3704_, 2, v_v_3065_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3704_, 3, v_l_3649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3704_, 4, v_l_3649_);
                    v___x_3700_ = v_reuseFailAlloc_3704_;
                    state = 95;
                    continue;
                }
            }
            95 => {
                if v_isShared_3070_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3069_, 4, v___x_3700_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 3, v___x_3698_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 2, v_v_3692_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 1, v_k_3691_);
                    crate::leanh::lean_ctor_set(v___x_3069_, 0, v___x_3696_);
                    v___x_3702_ = v___x_3069_;
                    state = 96;
                    continue;
                } else {
                    v_reuseFailAlloc_3703_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3703_, 0, v___x_3696_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3703_, 1, v_k_3691_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3703_, 2, v_v_3692_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3703_, 3, v___x_3698_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3703_, 4, v___x_3700_);
                    v___x_3702_ = v_reuseFailAlloc_3703_;
                    state = 96;
                    continue;
                }
            }
            96 => {
                return v___x_3702_;
            }
            97 => {
                return v___x_3716_;
            }
            98 => {
                return v___x_3719_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__2___redArg___boxed(
    mut v_k_3723_: *mut crate::leanh::LeanObject,
    mut v_t_3724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3725_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__2___redArg(v_k_3723_, v_t_3724_);
    crate::leanh::lean_dec(v_k_3723_);
    return v_res_3725_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__1(
    mut v_as_3726_: *mut crate::leanh::LeanObject,
    mut v_i_3727_: usize,
    mut v_stop_3728_: usize,
    mut v_b_3729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3730_: u8 = 0;
    let mut v___x_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_thm_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3734_: usize = 0;
    let mut v___x_3735_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3730_ = lean_usize_dec_eq(v_i_3727_, v_stop_3728_);
                if v___x_3730_ == 0 {
                    v___x_3731_ = lean_array_uget_borrowed(v_as_3726_, v_i_3727_);
                    v_thm_3732_ = crate::leanh::lean_ctor_get(v___x_3731_, 2);
                    crate::leanh::lean_inc_ref(v_thm_3732_);
                    v___x_3733_ = l_Lean_Meta_Sym_Simp_Theorems_insert(v_b_3729_, v_thm_3732_);
                    v___x_3734_ = 1usize;
                    v___x_3735_ = lean_usize_add(v_i_3727_, v___x_3734_);
                    v_i_3727_ = v___x_3735_;
                    v_b_3729_ = v___x_3733_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3729_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__1___boxed(
    mut v_as_3737_: *mut crate::leanh::LeanObject,
    mut v_i_3738_: *mut crate::leanh::LeanObject,
    mut v_stop_3739_: *mut crate::leanh::LeanObject,
    mut v_b_3740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3741_: usize = 0;
    let mut v_stop_boxed_3742_: usize = 0;
    let mut v_res_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3741_ = crate::leanh::lean_unbox_usize(v_i_3738_);
    crate::leanh::lean_dec(v_i_3738_);
    v_stop_boxed_3742_ = crate::leanh::lean_unbox_usize(v_stop_3739_);
    crate::leanh::lean_dec(v_stop_3739_);
    v_res_3743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__1(v_as_3737_, v_i_boxed_3741_, v_stop_boxed_3742_, v_b_3740_);
    crate::leanh::lean_dec_ref(v_as_3737_);
    return v_res_3743_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas(
    mut v_entries_3746_: *mut crate::leanh::LeanObject,
    mut v_appFn_3747_: *mut crate::leanh::LeanObject,
    mut v_lemmas_3748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_appFnEntries_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3753_: u8 = 0;
    v___x_3749_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3750_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas___closed__0;
    v_appFnEntries_3751_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__0___redArg(v_entries_3746_, v_appFn_3747_, v___x_3750_);
    v___x_3752_ = lean_array_get_size(v_appFnEntries_3751_);
    v___x_3753_ = lean_nat_dec_eq(v___x_3752_, v___x_3749_);
    if v___x_3753_ == 0 {
        let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3755_: u8 = 0;
        v___x_3754_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__2),
            core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__2_once),
            _init_l_Lean_Meta_Tactic_Cbv_CbvEvalState_addEntry___closed__2,
        );
        v___x_3755_ = lean_nat_dec_lt(v___x_3749_, v___x_3752_);
        if v___x_3755_ == 0 {
            let mut v___x_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_appFnEntries_3751_);
            v___x_3756_ =
                l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(
                    v_appFn_3747_,
                    v___x_3754_,
                    v_lemmas_3748_,
                );
            return v___x_3756_;
        } else {
            let mut v___x_3757_: u8 = 0;
            v___x_3757_ = lean_nat_dec_le(v___x_3752_, v___x_3752_);
            if v___x_3757_ == 0 {
                if v___x_3755_ == 0 {
                    let mut v___x_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec(v_appFnEntries_3751_);
                    v___x_3758_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_appFn_3747_, v___x_3754_, v_lemmas_3748_);
                    return v___x_3758_;
                } else {
                    let mut v___x_3759_: usize = 0;
                    let mut v___x_3760_: usize = 0;
                    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_3759_ = 0usize;
                    v___x_3760_ = lean_usize_of_nat(v___x_3752_);
                    v___x_3761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__1(v_appFnEntries_3751_, v___x_3759_, v___x_3760_, v___x_3754_);
                    crate::leanh::lean_dec(v_appFnEntries_3751_);
                    v___x_3762_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_appFn_3747_, v___x_3761_, v_lemmas_3748_);
                    return v___x_3762_;
                }
            } else {
                let mut v___x_3763_: usize = 0;
                let mut v___x_3764_: usize = 0;
                let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_3763_ = 0usize;
                v___x_3764_ = lean_usize_of_nat(v___x_3752_);
                v___x_3765_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__1(v_appFnEntries_3751_, v___x_3763_, v___x_3764_, v___x_3754_);
                crate::leanh::lean_dec(v_appFnEntries_3751_);
                v___x_3766_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_appFn_3747_, v___x_3765_, v_lemmas_3748_);
                return v___x_3766_;
            }
        }
    } else {
        let mut v___x_3767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_appFnEntries_3751_);
        v___x_3767_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__2___redArg(v_appFn_3747_, v_lemmas_3748_);
        crate::leanh::lean_dec(v_appFn_3747_);
        return v___x_3767_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas___boxed(
    mut v_entries_3768_: *mut crate::leanh::LeanObject,
    mut v_appFn_3769_: *mut crate::leanh::LeanObject,
    mut v_lemmas_3770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3771_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas(v_entries_3768_, v_appFn_3769_, v_lemmas_3770_);
    crate::leanh::lean_dec(v_entries_3768_);
    return v_res_3771_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__0(
    mut v_00_u03b4_3772_: *mut crate::leanh::LeanObject,
    mut v_t_3773_: *mut crate::leanh::LeanObject,
    mut v_k_3774_: *mut crate::leanh::LeanObject,
    mut v_fallback_3775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3776_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__0___redArg(v_t_3773_, v_k_3774_, v_fallback_3775_);
    return v___x_3776_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__0___boxed(
    mut v_00_u03b4_3777_: *mut crate::leanh::LeanObject,
    mut v_t_3778_: *mut crate::leanh::LeanObject,
    mut v_k_3779_: *mut crate::leanh::LeanObject,
    mut v_fallback_3780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3781_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__0(v_00_u03b4_3777_, v_t_3778_, v_k_3779_, v_fallback_3780_);
    crate::leanh::lean_dec(v_fallback_3780_);
    crate::leanh::lean_dec(v_k_3779_);
    crate::leanh::lean_dec(v_t_3778_);
    return v_res_3781_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__2(
    mut v_00_u03b2_3782_: *mut crate::leanh::LeanObject,
    mut v_k_3783_: *mut crate::leanh::LeanObject,
    mut v_t_3784_: *mut crate::leanh::LeanObject,
    mut v_h_3785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3786_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__2___redArg(v_k_3783_, v_t_3784_);
    return v___x_3786_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__2___boxed(
    mut v_00_u03b2_3787_: *mut crate::leanh::LeanObject,
    mut v_k_3788_: *mut crate::leanh::LeanObject,
    mut v_t_3789_: *mut crate::leanh::LeanObject,
    mut v_h_3790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3791_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__2(v_00_u03b2_3787_, v_k_3788_, v_t_3789_, v_h_3790_);
    crate::leanh::lean_dec(v_k_3788_);
    return v_res_3791_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__2(
    mut v_declName_3792_: *mut crate::leanh::LeanObject,
    mut v_as_3793_: *mut crate::leanh::LeanObject,
    mut v_i_3794_: usize,
    mut v_stop_3795_: usize,
    mut v_b_3796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: usize = 0;
    let mut v___x_3800_: usize = 0;
    let mut v___x_3802_: u8 = 0;
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_origin_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: u8 = 0;
    let mut v___x_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3802_ = lean_usize_dec_eq(v_i_3794_, v_stop_3795_);
                if v___x_3802_ == 0 {
                    v___x_3803_ = lean_array_uget_borrowed(v_as_3793_, v_i_3794_);
                    v_origin_3804_ = crate::leanh::lean_ctor_get(v___x_3803_, 0);
                    v___x_3805_ = lean_name_eq(v_origin_3804_, v_declName_3792_);
                    if v___x_3805_ == 0 {
                        crate::leanh::lean_inc(v___x_3803_);
                        v___x_3806_ = lean_array_push(v_b_3796_, v___x_3803_);
                        v___y_3798_ = v___x_3806_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3798_ = v_b_3796_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_3796_;
                }
            }
            1 => {
                v___x_3799_ = 1usize;
                v___x_3800_ = lean_usize_add(v_i_3794_, v___x_3799_);
                v_i_3794_ = v___x_3800_;
                v_b_3796_ = v___y_3798_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__2___boxed(
    mut v_declName_3807_: *mut crate::leanh::LeanObject,
    mut v_as_3808_: *mut crate::leanh::LeanObject,
    mut v_i_3809_: *mut crate::leanh::LeanObject,
    mut v_stop_3810_: *mut crate::leanh::LeanObject,
    mut v_b_3811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3812_: usize = 0;
    let mut v_stop_boxed_3813_: usize = 0;
    let mut v_res_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3812_ = crate::leanh::lean_unbox_usize(v_i_3809_);
    crate::leanh::lean_dec(v_i_3809_);
    v_stop_boxed_3813_ = crate::leanh::lean_unbox_usize(v_stop_3810_);
    crate::leanh::lean_dec(v_stop_3810_);
    v_res_3814_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__2(v_declName_3807_, v_as_3808_, v_i_boxed_3812_, v_stop_boxed_3813_, v_b_3811_);
    crate::leanh::lean_dec_ref(v_as_3808_);
    crate::leanh::lean_dec(v_declName_3807_);
    return v_res_3814_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__0(
    mut v_declName_3815_: *mut crate::leanh::LeanObject,
    mut v_as_3816_: *mut crate::leanh::LeanObject,
    mut v_i_3817_: usize,
    mut v_stop_3818_: usize,
) -> u8 {
    let mut v___x_3819_: u8 = 0;
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_origin_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3822_: u8 = 0;
    let mut v___x_3823_: usize = 0;
    let mut v___x_3824_: usize = 0;
    let mut v___x_3826_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3819_ = lean_usize_dec_eq(v_i_3817_, v_stop_3818_);
                if v___x_3819_ == 0 {
                    v___x_3820_ = lean_array_uget_borrowed(v_as_3816_, v_i_3817_);
                    v_origin_3821_ = crate::leanh::lean_ctor_get(v___x_3820_, 0);
                    v___x_3822_ = lean_name_eq(v_origin_3821_, v_declName_3815_);
                    if v___x_3822_ == 0 {
                        v___x_3823_ = 1usize;
                        v___x_3824_ = lean_usize_add(v_i_3817_, v___x_3823_);
                        v_i_3817_ = v___x_3824_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3822_;
                    }
                } else {
                    v___x_3826_ = 0;
                    return v___x_3826_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__0___boxed(
    mut v_declName_3827_: *mut crate::leanh::LeanObject,
    mut v_as_3828_: *mut crate::leanh::LeanObject,
    mut v_i_3829_: *mut crate::leanh::LeanObject,
    mut v_stop_3830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3831_: usize = 0;
    let mut v_stop_boxed_3832_: usize = 0;
    let mut v_res_3833_: u8 = 0;
    let mut v_r_3834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3831_ = crate::leanh::lean_unbox_usize(v_i_3829_);
    crate::leanh::lean_dec(v_i_3829_);
    v_stop_boxed_3832_ = crate::leanh::lean_unbox_usize(v_stop_3830_);
    crate::leanh::lean_dec(v_stop_3830_);
    v_res_3833_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__0(v_declName_3827_, v_as_3828_, v_i_boxed_3831_, v_stop_boxed_3832_);
    crate::leanh::lean_dec_ref(v_as_3828_);
    crate::leanh::lean_dec(v_declName_3827_);
    v_r_3834_ = crate::leanh::lean_box((v_res_3833_) as usize);
    return v_r_3834_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__1_spec__1(
    mut v_declName_3835_: *mut crate::leanh::LeanObject,
    mut v_init_3836_: *mut crate::leanh::LeanObject,
    mut v_x_3837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: u8 = 0;
    let mut v___x_3848_: usize = 0;
    let mut v___x_3849_: usize = 0;
    let mut v___x_3850_: u8 = 0;
    let mut v___x_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3837_) == 0 {
                    v_k_3838_ = crate::leanh::lean_ctor_get(v_x_3837_, 1);
                    v_v_3839_ = crate::leanh::lean_ctor_get(v_x_3837_, 2);
                    v_l_3840_ = crate::leanh::lean_ctor_get(v_x_3837_, 3);
                    v_r_3841_ = crate::leanh::lean_ctor_get(v_x_3837_, 4);
                    v___x_3842_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__1_spec__1(v_declName_3835_, v_init_3836_, v_l_3840_);
                    if crate::leanh::lean_obj_tag(v___x_3842_) == 0 {
                        v___x_3843_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3844_ = lean_array_get_size(v_v_3839_);
                        v___x_3845_ = lean_nat_dec_lt(v___x_3843_, v___x_3844_);
                        if v___x_3845_ == 0 {
                            v_init_3836_ = v___x_3842_;
                            v_x_3837_ = v_r_3841_;
                            state = 0;
                            continue;
                        } else {
                            if v___x_3845_ == 0 {
                                v_init_3836_ = v___x_3842_;
                                v_x_3837_ = v_r_3841_;
                                state = 0;
                                continue;
                            } else {
                                v___x_3848_ = 0usize;
                                v___x_3849_ = lean_usize_of_nat(v___x_3844_);
                                v___x_3850_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__0(v_declName_3835_, v_v_3839_, v___x_3848_, v___x_3849_);
                                if v___x_3850_ == 0 {
                                    v_init_3836_ = v___x_3842_;
                                    v_x_3837_ = v_r_3841_;
                                    state = 0;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_v_3839_);
                                    crate::leanh::lean_inc(v_k_3838_);
                                    v___x_3852_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3852_, 0, v_k_3838_);
                                    crate::leanh::lean_ctor_set(v___x_3852_, 1, v_v_3839_);
                                    v___x_3853_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_3853_, 0, v___x_3852_);
                                    v_init_3836_ = v___x_3853_;
                                    v_x_3837_ = v_r_3841_;
                                    state = 0;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_init_3836_ = v___x_3842_;
                        v_x_3837_ = v_r_3841_;
                        state = 0;
                        continue;
                    }
                } else {
                    return v_init_3836_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__1_spec__1___boxed(
    mut v_declName_3856_: *mut crate::leanh::LeanObject,
    mut v_init_3857_: *mut crate::leanh::LeanObject,
    mut v_x_3858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3859_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__1_spec__1(v_declName_3856_, v_init_3857_, v_x_3858_);
    crate::leanh::lean_dec(v_x_3858_);
    crate::leanh::lean_dec(v_declName_3856_);
    return v_res_3859_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvEvalState_erase(
    mut v_s_3860_: *mut crate::leanh::LeanObject,
    mut v_declName_3861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lemmas_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_entries_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3866_: u8 = 0;
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3872_: u8 = 0;
    let mut v_fst_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: u8 = 0;
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: u8 = 0;
    let mut v___x_3895_: u8 = 0;
    let mut v___x_3896_: usize = 0;
    let mut v___x_3897_: usize = 0;
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: usize = 0;
    let mut v___x_3900_: usize = 0;
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3902_: u8 = 0;
    let mut v_isSharedCheck_3903_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lemmas_3862_ = crate::leanh::lean_ctor_get(v_s_3860_, 0);
                v_entries_3863_ = crate::leanh::lean_ctor_get(v_s_3860_, 1);
                v_isSharedCheck_3903_ = (!crate::leanh::lean_is_exclusive(v_s_3860_)) as u8;
                if v_isSharedCheck_3903_ == 0 {
                    v___x_3865_ = v_s_3860_;
                    v_isShared_3866_ = v_isSharedCheck_3903_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_entries_3863_);
                    crate::leanh::lean_inc(v_lemmas_3862_);
                    crate::leanh::lean_dec(v_s_3860_);
                    v___x_3865_ = crate::leanh::lean_box(0);
                    v_isShared_3866_ = v_isSharedCheck_3903_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3867_ = crate::leanh::lean_box(0);
                v___x_3868_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__1_spec__1(v_declName_3861_, v___x_3867_, v_entries_3863_);
                if crate::leanh::lean_obj_tag(v___x_3868_) == 0 {
                    crate::leanh::lean_del_object(v___x_3865_);
                    crate::leanh::lean_dec(v_entries_3863_);
                    crate::leanh::lean_dec(v_lemmas_3862_);
                    return v___x_3867_;
                } else {
                    v_val_3869_ = crate::leanh::lean_ctor_get(v___x_3868_, 0);
                    v_isSharedCheck_3902_ = (!crate::leanh::lean_is_exclusive(v___x_3868_)) as u8;
                    if v_isSharedCheck_3902_ == 0 {
                        v___x_3871_ = v___x_3868_;
                        v_isShared_3872_ = v_isSharedCheck_3902_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3869_);
                        crate::leanh::lean_dec(v___x_3868_);
                        v___x_3871_ = crate::leanh::lean_box(0);
                        v_isShared_3872_ = v_isSharedCheck_3902_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_fst_3873_ = crate::leanh::lean_ctor_get(v_val_3869_, 0);
                crate::leanh::lean_inc(v_fst_3873_);
                v_snd_3874_ = crate::leanh::lean_ctor_get(v_val_3869_, 1);
                crate::leanh::lean_inc(v_snd_3874_);
                crate::leanh::lean_dec(v_val_3869_);
                v___x_3891_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3892_ = lean_array_get_size(v_snd_3874_);
                v___x_3893_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas___closed__0;
                v___x_3894_ = lean_nat_dec_lt(v___x_3891_, v___x_3892_);
                if v___x_3894_ == 0 {
                    crate::leanh::lean_dec(v_snd_3874_);
                    v___y_3885_ = v___x_3893_;
                    state = 6;
                    continue;
                } else {
                    v___x_3895_ = lean_nat_dec_le(v___x_3892_, v___x_3892_);
                    if v___x_3895_ == 0 {
                        if v___x_3894_ == 0 {
                            crate::leanh::lean_dec(v_snd_3874_);
                            v___y_3885_ = v___x_3893_;
                            state = 6;
                            continue;
                        } else {
                            v___x_3896_ = 0usize;
                            v___x_3897_ = lean_usize_of_nat(v___x_3892_);
                            v___x_3898_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__2(v_declName_3861_, v_snd_3874_, v___x_3896_, v___x_3897_, v___x_3893_);
                            crate::leanh::lean_dec(v_snd_3874_);
                            v___y_3885_ = v___x_3898_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___x_3899_ = 0usize;
                        v___x_3900_ = lean_usize_of_nat(v___x_3892_);
                        v___x_3901_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__2(v_declName_3861_, v_snd_3874_, v___x_3899_, v___x_3900_, v___x_3893_);
                        crate::leanh::lean_dec(v_snd_3874_);
                        v___y_3885_ = v___x_3901_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3877_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas(v___y_3876_, v_fst_3873_, v_lemmas_3862_);
                if v_isShared_3866_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3865_, 1, v___y_3876_);
                    crate::leanh::lean_ctor_set(v___x_3865_, 0, v___x_3877_);
                    v___x_3879_ = v___x_3865_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3883_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3883_, 1, v___y_3876_);
                    v___x_3879_ = v_reuseFailAlloc_3883_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3872_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3871_, 0, v___x_3879_);
                    v___x_3881_ = v___x_3871_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3882_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3879_);
                    v___x_3881_ = v_reuseFailAlloc_3882_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3881_;
            }
            6 => {
                v___x_3886_ = lean_array_get_size(v___y_3885_);
                v___x_3887_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_3888_ = lean_nat_dec_eq(v___x_3886_, v___x_3887_);
                if v___x_3888_ == 0 {
                    crate::leanh::lean_inc(v_fst_3873_);
                    v___x_3889_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_fst_3873_, v___y_3885_, v_entries_3863_);
                    v___y_3876_ = v___x_3889_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_3885_);
                    v___x_3890_ = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_CbvEvalState_rebuildLemmas_spec__2___redArg(v_fst_3873_, v_entries_3863_);
                    v___y_3876_ = v___x_3890_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvEvalState_erase___boxed(
    mut v_s_3904_: *mut crate::leanh::LeanObject,
    mut v_declName_3905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3906_ = l_Lean_Meta_Tactic_Cbv_CbvEvalState_erase(v_s_3904_, v_declName_3905_);
    crate::leanh::lean_dec(v_declName_3905_);
    return v_res_3906_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__1(
    mut v_declName_3907_: *mut crate::leanh::LeanObject,
    mut v_init_3908_: *mut crate::leanh::LeanObject,
    mut v_t_3909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3910_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__1_spec__1(v_declName_3907_, v_init_3908_, v_t_3909_);
    return v___x_3910_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__1___boxed(
    mut v_declName_3911_: *mut crate::leanh::LeanObject,
    mut v_init_3912_: *mut crate::leanh::LeanObject,
    mut v_t_3913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3914_ =
        l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_Tactic_Cbv_CbvEvalState_erase_spec__1(
            v_declName_3911_,
            v_init_3912_,
            v_t_3913_,
        );
    crate::leanh::lean_dec(v_t_3913_);
    crate::leanh::lean_dec(v_declName_3911_);
    return v_res_3914_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_(
    mut v_x_3917_: *mut crate::leanh::LeanObject,
    mut v_entry_3918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_thm_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3925_: u8 = 0;
    let mut v___x_3926_: u8 = 0;
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3931_: u8 = 0;
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3935_: u8 = 0;
    let mut v_unused_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3945_: u8 = 0;
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3949_: u8 = 0;
    let mut v_unused_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3954_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_thm_3919_ = crate::leanh::lean_ctor_get(v_entry_3918_, 2);
                v___x_3920_ = l_Lean_Meta_Sym_Simp_Theorem_declName(v_thm_3919_);
                if crate::leanh::lean_obj_tag(v___x_3920_) == 0 {
                    crate::leanh::lean_dec_ref(v_entry_3918_);
                    v___x_3921_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_;
                    return v___x_3921_;
                } else {
                    v_val_3922_ = crate::leanh::lean_ctor_get(v___x_3920_, 0);
                    v_isSharedCheck_3954_ = (!crate::leanh::lean_is_exclusive(v___x_3920_)) as u8;
                    if v_isSharedCheck_3954_ == 0 {
                        v___x_3924_ = v___x_3920_;
                        v_isShared_3925_ = v_isSharedCheck_3954_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3922_);
                        crate::leanh::lean_dec(v___x_3920_);
                        v___x_3924_ = crate::leanh::lean_box(0);
                        v_isShared_3925_ = v_isSharedCheck_3954_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3926_ = l_Lean_isPrivateName(v_val_3922_);
                crate::leanh::lean_dec(v_val_3922_);
                if v___x_3926_ == 0 {
                    crate::leanh::lean_inc_ref(v_entry_3918_);
                    if v_isShared_3925_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3924_, 0, v_entry_3918_);
                        v___x_3928_ = v___x_3924_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3939_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_entry_3918_);
                        v___x_3928_ = v_reuseFailAlloc_3939_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3940_ = crate::leanh::lean_box(0);
                    crate::leanh::lean_inc_ref(v_entry_3918_);
                    if v_isShared_3925_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3924_, 0, v_entry_3918_);
                        v___x_3942_ = v___x_3924_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3953_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_entry_3918_);
                        v___x_3942_ = v_reuseFailAlloc_3953_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_isSharedCheck_3935_ = (!crate::leanh::lean_is_exclusive(v_entry_3918_)) as u8;
                if v_isSharedCheck_3935_ == 0 {
                    v_unused_3936_ = crate::leanh::lean_ctor_get(v_entry_3918_, 2);
                    crate::leanh::lean_dec(v_unused_3936_);
                    v_unused_3937_ = crate::leanh::lean_ctor_get(v_entry_3918_, 1);
                    crate::leanh::lean_dec(v_unused_3937_);
                    v_unused_3938_ = crate::leanh::lean_ctor_get(v_entry_3918_, 0);
                    crate::leanh::lean_dec(v_unused_3938_);
                    v___x_3930_ = v_entry_3918_;
                    v_isShared_3931_ = v_isSharedCheck_3935_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_entry_3918_);
                    v___x_3930_ = crate::leanh::lean_box(0);
                    v_isShared_3931_ = v_isSharedCheck_3935_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref_n(v___x_3928_, 2);
                if v_isShared_3931_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3930_, 2, v___x_3928_);
                    crate::leanh::lean_ctor_set(v___x_3930_, 1, v___x_3928_);
                    crate::leanh::lean_ctor_set(v___x_3930_, 0, v___x_3928_);
                    v___x_3933_ = v___x_3930_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3934_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3934_, 0, v___x_3928_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3934_, 1, v___x_3928_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3934_, 2, v___x_3928_);
                    v___x_3933_ = v_reuseFailAlloc_3934_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3933_;
            }
            5 => {
                v_isSharedCheck_3949_ = (!crate::leanh::lean_is_exclusive(v_entry_3918_)) as u8;
                if v_isSharedCheck_3949_ == 0 {
                    v_unused_3950_ = crate::leanh::lean_ctor_get(v_entry_3918_, 2);
                    crate::leanh::lean_dec(v_unused_3950_);
                    v_unused_3951_ = crate::leanh::lean_ctor_get(v_entry_3918_, 1);
                    crate::leanh::lean_dec(v_unused_3951_);
                    v_unused_3952_ = crate::leanh::lean_ctor_get(v_entry_3918_, 0);
                    crate::leanh::lean_dec(v_unused_3952_);
                    v___x_3944_ = v_entry_3918_;
                    v_isShared_3945_ = v_isSharedCheck_3949_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_entry_3918_);
                    v___x_3944_ = crate::leanh::lean_box(0);
                    v_isShared_3945_ = v_isSharedCheck_3949_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3945_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3944_, 2, v___x_3942_);
                    crate::leanh::lean_ctor_set(v___x_3944_, 1, v___x_3940_);
                    crate::leanh::lean_ctor_set(v___x_3944_, 0, v___x_3940_);
                    v___x_3947_ = v___x_3944_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3948_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3940_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3948_, 1, v___x_3940_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3948_, 2, v___x_3942_);
                    v___x_3947_ = v_reuseFailAlloc_3948_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3947_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2____boxed(
    mut v_x_3955_: *mut crate::leanh::LeanObject,
    mut v_entry_3956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3957_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_(v_x_3955_, v_entry_3956_);
    crate::leanh::lean_dec_ref(v_x_3955_);
    return v_res_3957_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_(
    mut v___y_3958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v___y_3958_);
    return v___y_3958_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2____boxed(
    mut v___y_3959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3960_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_(v___y_3959_);
    crate::leanh::lean_dec_ref(v___y_3959_);
    return v_res_3960_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3974_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_;
    v___x_3975_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_3974_);
    return v___x_3975_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2____boxed(
    mut v_a_3976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3977_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_();
    return v_res_3977_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas___redArg(
    mut v_target_3978_: *mut crate::leanh::LeanObject,
    mut v_a_3979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lemmas_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3981_ = lean_st_ref_get(v_a_3979_);
    v_env_3982_ = crate::leanh::lean_ctor_get(v___x_3981_, 0);
    crate::leanh::lean_inc_ref(v_env_3982_);
    crate::leanh::lean_dec(v___x_3981_);
    v___x_3983_ = l_Lean_Meta_Tactic_Cbv_cbvEvalExt;
    v_ext_3984_ = crate::leanh::lean_ctor_get(v___x_3983_, 1);
    v_toEnvExtension_3985_ = crate::leanh::lean_ctor_get(v_ext_3984_, 0);
    v_asyncMode_3986_ = crate::leanh::lean_ctor_get(v_toEnvExtension_3985_, 2);
    v___x_3987_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalState_default;
    v___x_3988_ = l_Lean_ScopedEnvExtension_getState___redArg(
        v___x_3987_,
        v___x_3983_,
        v_env_3982_,
        v_asyncMode_3986_,
    );
    v_lemmas_3989_ = crate::leanh::lean_ctor_get(v___x_3988_, 0);
    crate::leanh::lean_inc(v_lemmas_3989_);
    crate::leanh::lean_dec(v___x_3988_);
    v___x_3990_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_lemmas_3989_,
            v_target_3978_,
        );
    crate::leanh::lean_dec(v_lemmas_3989_);
    v___x_3991_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3991_, 0, v___x_3990_);
    return v___x_3991_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas___redArg___boxed(
    mut v_target_3992_: *mut crate::leanh::LeanObject,
    mut v_a_3993_: *mut crate::leanh::LeanObject,
    mut v_a_3994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3995_ = l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas___redArg(v_target_3992_, v_a_3993_);
    crate::leanh::lean_dec(v_a_3993_);
    crate::leanh::lean_dec(v_target_3992_);
    return v_res_3995_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas(
    mut v_target_3996_: *mut crate::leanh::LeanObject,
    mut v_a_3997_: *mut crate::leanh::LeanObject,
    mut v_a_3998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4000_ = l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas___redArg(v_target_3996_, v_a_3998_);
    return v___x_4000_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas___boxed(
    mut v_target_4001_: *mut crate::leanh::LeanObject,
    mut v_a_4002_: *mut crate::leanh::LeanObject,
    mut v_a_4003_: *mut crate::leanh::LeanObject,
    mut v_a_4004_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4005_ = l_Lean_Meta_Tactic_Cbv_getCbvEvalLemmas(v_target_4001_, v_a_4002_, v_a_4003_);
    crate::leanh::lean_dec(v_a_4003_);
    crate::leanh::lean_dec_ref(v_a_4002_);
    crate::leanh::lean_dec(v_target_4001_);
    return v_res_4005_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4006_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4006_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4007_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__0_once), _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__0);
    v___x_4008_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4008_, 0, v___x_4007_);
    return v___x_4008_;
}
pub unsafe fn _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4009_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__1_once), _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__1);
    v___x_4010_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4010_, 0, v___x_4009_);
    crate::leanh::lean_ctor_set(v___x_4010_, 1, v___x_4009_);
    return v___x_4010_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg(
    mut v_ext_4011_: *mut crate::leanh::LeanObject,
    mut v_b_4012_: *mut crate::leanh::LeanObject,
    mut v_kind_4013_: u8,
    mut v___y_4014_: *mut crate::leanh::LeanObject,
    mut v___y_4015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_currNamespace_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4029_: u8 = 0;
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4038_: u8 = 0;
    let mut v_unused_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_currNamespace_4017_ = crate::leanh::lean_ctor_get(v___y_4014_, 6);
                v___x_4018_ = lean_st_ref_take(v___y_4015_);
                v_env_4019_ = crate::leanh::lean_ctor_get(v___x_4018_, 0);
                v_nextMacroScope_4020_ = crate::leanh::lean_ctor_get(v___x_4018_, 1);
                v_ngen_4021_ = crate::leanh::lean_ctor_get(v___x_4018_, 2);
                v_auxDeclNGen_4022_ = crate::leanh::lean_ctor_get(v___x_4018_, 3);
                v_traceState_4023_ = crate::leanh::lean_ctor_get(v___x_4018_, 4);
                v_messages_4024_ = crate::leanh::lean_ctor_get(v___x_4018_, 6);
                v_infoState_4025_ = crate::leanh::lean_ctor_get(v___x_4018_, 7);
                v_snapshotTasks_4026_ = crate::leanh::lean_ctor_get(v___x_4018_, 8);
                v_isSharedCheck_4038_ = (!crate::leanh::lean_is_exclusive(v___x_4018_)) as u8;
                if v_isSharedCheck_4038_ == 0 {
                    v_unused_4039_ = crate::leanh::lean_ctor_get(v___x_4018_, 5);
                    crate::leanh::lean_dec(v_unused_4039_);
                    v___x_4028_ = v___x_4018_;
                    v_isShared_4029_ = v_isSharedCheck_4038_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4026_);
                    crate::leanh::lean_inc(v_infoState_4025_);
                    crate::leanh::lean_inc(v_messages_4024_);
                    crate::leanh::lean_inc(v_traceState_4023_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4022_);
                    crate::leanh::lean_inc(v_ngen_4021_);
                    crate::leanh::lean_inc(v_nextMacroScope_4020_);
                    crate::leanh::lean_inc(v_env_4019_);
                    crate::leanh::lean_dec(v___x_4018_);
                    v___x_4028_ = crate::leanh::lean_box(0);
                    v_isShared_4029_ = v_isSharedCheck_4038_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_currNamespace_4017_);
                v___x_4030_ = l_Lean_ScopedEnvExtension_addCore___redArg(
                    v_env_4019_,
                    v_ext_4011_,
                    v_b_4012_,
                    v_kind_4013_,
                    v_currNamespace_4017_,
                );
                v___x_4031_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__2);
                if v_isShared_4029_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4028_, 5, v___x_4031_);
                    crate::leanh::lean_ctor_set(v___x_4028_, 0, v___x_4030_);
                    v___x_4033_ = v___x_4028_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4037_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4037_, 0, v___x_4030_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4037_, 1, v_nextMacroScope_4020_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4037_, 2, v_ngen_4021_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4037_, 3, v_auxDeclNGen_4022_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4037_, 4, v_traceState_4023_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4037_, 5, v___x_4031_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4037_, 6, v_messages_4024_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4037_, 7, v_infoState_4025_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4037_, 8, v_snapshotTasks_4026_);
                    v___x_4033_ = v_reuseFailAlloc_4037_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4034_ = lean_st_ref_set(v___y_4015_, v___x_4033_);
                v___x_4035_ = crate::leanh::lean_box(0);
                v___x_4036_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4036_, 0, v___x_4035_);
                return v___x_4036_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_ext_4040_: *mut crate::leanh::LeanObject,
    mut v_b_4041_: *mut crate::leanh::LeanObject,
    mut v_kind_4042_: *mut crate::leanh::LeanObject,
    mut v___y_4043_: *mut crate::leanh::LeanObject,
    mut v___y_4044_: *mut crate::leanh::LeanObject,
    mut v___y_4045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_4046_: u8 = 0;
    let mut v_res_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4046_ = (crate::leanh::lean_unbox(v_kind_4042_) as u8);
    v_res_4047_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg(v_ext_4040_, v_b_4041_, v_kind_boxed_4046_, v___y_4043_, v___y_4044_);
    crate::leanh::lean_dec(v___y_4044_);
    crate::leanh::lean_dec_ref(v___y_4043_);
    return v_res_4047_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_4048_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4049_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4050_: *mut crate::leanh::LeanObject,
    mut v_ext_4051_: *mut crate::leanh::LeanObject,
    mut v_b_4052_: *mut crate::leanh::LeanObject,
    mut v_kind_4053_: u8,
    mut v___y_4054_: *mut crate::leanh::LeanObject,
    mut v___y_4055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4057_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg(v_ext_4051_, v_b_4052_, v_kind_4053_, v___y_4054_, v___y_4055_);
    return v___x_4057_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_4058_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_4059_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_4060_: *mut crate::leanh::LeanObject,
    mut v_ext_4061_: *mut crate::leanh::LeanObject,
    mut v_b_4062_: *mut crate::leanh::LeanObject,
    mut v_kind_4063_: *mut crate::leanh::LeanObject,
    mut v___y_4064_: *mut crate::leanh::LeanObject,
    mut v___y_4065_: *mut crate::leanh::LeanObject,
    mut v___y_4066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_4067_: u8 = 0;
    let mut v_res_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4067_ = (crate::leanh::lean_unbox(v_kind_4063_) as u8);
    v_res_4068_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0(v_00_u03b1_4058_, v_00_u03b2_4059_, v_00_u03c3_4060_, v_ext_4061_, v_b_4062_, v_kind_boxed_4067_, v___y_4064_, v___y_4065_);
    crate::leanh::lean_dec(v___y_4065_);
    crate::leanh::lean_dec_ref(v___y_4064_);
    return v_res_4068_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_()
-> u64 {
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: u64 = 0;
    v___x_4075_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_;
    v___x_4076_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4075_);
    return v___x_4076_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4077_: u64 = 0;
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4077_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
    v___x_4078_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_;
    v___x_4079_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
    crate::leanh::lean_ctor_set(v___x_4079_, 0, v___x_4078_);
    crate::leanh::lean_ctor_set_uint64(
        v___x_4079_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
        v___x_4077_,
    );
    return v___x_4079_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4080_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4080_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4081_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
    v___x_4082_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4082_, 0, v___x_4081_);
    return v___x_4082_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4083_ = crate::leanh::lean_box(1);
    v___x_4084_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4);
    v___x_4085_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
    v___x_4086_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4086_, 0, v___x_4085_);
    crate::leanh::lean_ctor_set(v___x_4086_, 1, v___x_4084_);
    crate::leanh::lean_ctor_set(v___x_4086_, 2, v___x_4083_);
    return v___x_4086_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4089_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
    v___x_4090_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4091_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4091_, 0, v___x_4090_);
    crate::leanh::lean_ctor_set(v___x_4091_, 1, v___x_4090_);
    crate::leanh::lean_ctor_set(v___x_4091_, 2, v___x_4090_);
    crate::leanh::lean_ctor_set(v___x_4091_, 3, v___x_4090_);
    crate::leanh::lean_ctor_set(v___x_4091_, 4, v___x_4089_);
    crate::leanh::lean_ctor_set(v___x_4091_, 5, v___x_4089_);
    crate::leanh::lean_ctor_set(v___x_4091_, 6, v___x_4089_);
    crate::leanh::lean_ctor_set(v___x_4091_, 7, v___x_4089_);
    crate::leanh::lean_ctor_set(v___x_4091_, 8, v___x_4089_);
    crate::leanh::lean_ctor_set(v___x_4091_, 9, v___x_4089_);
    return v___x_4091_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4092_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
    v___x_4093_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4093_, 0, v___x_4092_);
    crate::leanh::lean_ctor_set(v___x_4093_, 1, v___x_4092_);
    crate::leanh::lean_ctor_set(v___x_4093_, 2, v___x_4092_);
    crate::leanh::lean_ctor_set(v___x_4093_, 3, v___x_4092_);
    crate::leanh::lean_ctor_set(v___x_4093_, 4, v___x_4092_);
    crate::leanh::lean_ctor_set(v___x_4093_, 5, v___x_4092_);
    return v___x_4093_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4094_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
    v___x_4095_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4095_, 0, v___x_4094_);
    crate::leanh::lean_ctor_set(v___x_4095_, 1, v___x_4094_);
    crate::leanh::lean_ctor_set(v___x_4095_, 2, v___x_4094_);
    crate::leanh::lean_ctor_set(v___x_4095_, 3, v___x_4094_);
    crate::leanh::lean_ctor_set(v___x_4095_, 4, v___x_4094_);
    return v___x_4095_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_(
    mut v___x_4096_: *mut crate::leanh::LeanObject,
    mut v_lemmaName_4097_: *mut crate::leanh::LeanObject,
    mut v_stx_4098_: *mut crate::leanh::LeanObject,
    mut v_kind_4099_: u8,
    mut v___y_4100_: *mut crate::leanh::LeanObject,
    mut v___y_4101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4104_: u8 = 0;
    let mut v___x_4105_: u8 = 0;
    let mut v___x_4106_: u8 = 0;
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4127_: u8 = 0;
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4131_: u8 = 0;
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4134_: u8 = 0;
    let mut v___x_4135_: u8 = 0;
    let mut v___x_4136_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4132_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4133_ = l_Lean_Syntax_getArg(v_stx_4098_, v___x_4132_);
                v___x_4134_ = l_Lean_Syntax_isNone(v___x_4133_);
                crate::leanh::lean_dec(v___x_4133_);
                if v___x_4134_ == 0 {
                    v___x_4135_ = 1;
                    v___y_4104_ = v___x_4135_;
                    state = 1;
                    continue;
                } else {
                    v___x_4136_ = 0;
                    v___y_4104_ = v___x_4136_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4105_ = 0;
                v___x_4106_ = 1;
                v___x_4107_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
                v___x_4108_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4109_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__4);
                v___x_4110_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
                v___x_4111_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_;
                v___x_4112_ = crate::leanh::lean_box(0);
                crate::leanh::lean_inc(v___x_4096_);
                v___x_4113_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_4113_, 0, v___x_4107_);
                crate::leanh::lean_ctor_set(v___x_4113_, 1, v___x_4096_);
                crate::leanh::lean_ctor_set(v___x_4113_, 2, v___x_4110_);
                crate::leanh::lean_ctor_set(v___x_4113_, 3, v___x_4111_);
                crate::leanh::lean_ctor_set(v___x_4113_, 4, v___x_4112_);
                crate::leanh::lean_ctor_set(v___x_4113_, 5, v___x_4108_);
                crate::leanh::lean_ctor_set(v___x_4113_, 6, v___x_4112_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4113_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v___x_4105_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4113_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v___x_4105_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4113_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v___x_4105_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4113_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v___x_4106_,
                );
                v___x_4114_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
                v___x_4115_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
                v___x_4116_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
                v___x_4117_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4117_, 0, v___x_4114_);
                crate::leanh::lean_ctor_set(v___x_4117_, 1, v___x_4115_);
                crate::leanh::lean_ctor_set(v___x_4117_, 2, v___x_4096_);
                crate::leanh::lean_ctor_set(v___x_4117_, 3, v___x_4109_);
                crate::leanh::lean_ctor_set(v___x_4117_, 4, v___x_4116_);
                v___x_4118_ = lean_st_mk_ref(v___x_4117_);
                v___x_4119_ = l_Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst(
                    v_lemmaName_4097_,
                    v___y_4104_,
                    v___x_4113_,
                    v___x_4118_,
                    v___y_4100_,
                    v___y_4101_,
                );
                crate::leanh::lean_dec_ref_known(v___x_4113_, 7);
                if crate::leanh::lean_obj_tag(v___x_4119_) == 0 {
                    v_a_4120_ = crate::leanh::lean_ctor_get(v___x_4119_, 0);
                    crate::leanh::lean_inc(v_a_4120_);
                    crate::leanh::lean_dec_ref_known(v___x_4119_, 1);
                    v___x_4121_ = lean_st_ref_get(v___x_4118_);
                    crate::leanh::lean_dec(v___x_4118_);
                    crate::leanh::lean_dec(v___x_4121_);
                    v___x_4122_ = l_Lean_Meta_Tactic_Cbv_cbvEvalExt;
                    v___x_4123_ = l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg(v___x_4122_, v_a_4120_, v_kind_4099_, v___y_4100_, v___y_4101_);
                    return v___x_4123_;
                } else {
                    crate::leanh::lean_dec(v___x_4118_);
                    v_a_4124_ = crate::leanh::lean_ctor_get(v___x_4119_, 0);
                    v_isSharedCheck_4131_ = (!crate::leanh::lean_is_exclusive(v___x_4119_)) as u8;
                    if v_isSharedCheck_4131_ == 0 {
                        v___x_4126_ = v___x_4119_;
                        v_isShared_4127_ = v_isSharedCheck_4131_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4124_);
                        crate::leanh::lean_dec(v___x_4119_);
                        v___x_4126_ = crate::leanh::lean_box(0);
                        v_isShared_4127_ = v_isSharedCheck_4131_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4127_ == 0 {
                    v___x_4129_ = v___x_4126_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4130_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4130_, 0, v_a_4124_);
                    v___x_4129_ = v_reuseFailAlloc_4130_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4129_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2____boxed(
    mut v___x_4137_: *mut crate::leanh::LeanObject,
    mut v_lemmaName_4138_: *mut crate::leanh::LeanObject,
    mut v_stx_4139_: *mut crate::leanh::LeanObject,
    mut v_kind_4140_: *mut crate::leanh::LeanObject,
    mut v___y_4141_: *mut crate::leanh::LeanObject,
    mut v___y_4142_: *mut crate::leanh::LeanObject,
    mut v___y_4143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_4144_: u8 = 0;
    let mut v_res_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_4144_ = (crate::leanh::lean_unbox(v_kind_4140_) as u8);
    v_res_4145_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_(v___x_4137_, v_lemmaName_4138_, v_stx_4139_, v_kind_boxed_4144_, v___y_4141_, v___y_4142_);
    crate::leanh::lean_dec(v___y_4142_);
    crate::leanh::lean_dec_ref(v___y_4141_);
    crate::leanh::lean_dec(v_stx_4139_);
    return v_res_4145_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_(
    mut v_val_4146_: *mut crate::leanh::LeanObject,
    mut v_x_4147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_val_4146_);
    return v_val_4146_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2____boxed(
    mut v_val_4148_: *mut crate::leanh::LeanObject,
    mut v_x_4149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4150_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_(v_val_4148_, v_x_4149_);
    crate::leanh::lean_dec_ref(v_x_4149_);
    crate::leanh::lean_dec_ref(v_val_4148_);
    return v_res_4150_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3(
    mut v_msgData_4151_: *mut crate::leanh::LeanObject,
    mut v___y_4152_: *mut crate::leanh::LeanObject,
    mut v___y_4153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4155_ = lean_st_ref_get(v___y_4153_);
    v_env_4156_ = crate::leanh::lean_ctor_get(v___x_4155_, 0);
    crate::leanh::lean_inc_ref(v_env_4156_);
    crate::leanh::lean_dec(v___x_4155_);
    v_options_4157_ = crate::leanh::lean_ctor_get(v___y_4152_, 2);
    v___x_4158_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__2);
    v___x_4159_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_4160_ = lean_mk_empty_array_with_capacity(v___x_4159_);
    crate::leanh::lean_dec_ref(v___x_4160_);
    v___x_4161_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2_spec__6_spec__7_spec__8___redArg___closed__5);
    crate::leanh::lean_inc_ref(v_options_4157_);
    v___x_4162_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4162_, 0, v_env_4156_);
    crate::leanh::lean_ctor_set(v___x_4162_, 1, v___x_4158_);
    crate::leanh::lean_ctor_set(v___x_4162_, 2, v___x_4161_);
    crate::leanh::lean_ctor_set(v___x_4162_, 3, v_options_4157_);
    v___x_4163_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4163_, 0, v___x_4162_);
    crate::leanh::lean_ctor_set(v___x_4163_, 1, v_msgData_4151_);
    v___x_4164_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4164_, 0, v___x_4163_);
    return v___x_4164_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3___boxed(
    mut v_msgData_4165_: *mut crate::leanh::LeanObject,
    mut v___y_4166_: *mut crate::leanh::LeanObject,
    mut v___y_4167_: *mut crate::leanh::LeanObject,
    mut v___y_4168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4169_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3(v_msgData_4165_, v___y_4166_, v___y_4167_);
    crate::leanh::lean_dec(v___y_4167_);
    crate::leanh::lean_dec_ref(v___y_4166_);
    return v_res_4169_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0(
    mut v___y_4178_: u8,
    mut v_suppressElabErrors_4179_: u8,
    mut v_x_4180_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_4180_) == 1 {
        let mut v_pre_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_4181_ = crate::leanh::lean_ctor_get(v_x_4180_, 0);
        match crate::leanh::lean_obj_tag(v_pre_4181_) {
            1 => {
                let mut v_pre_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_4182_ = crate::leanh::lean_ctor_get(v_pre_4181_, 0);
                match crate::leanh::lean_obj_tag(v_pre_4182_) {
                    0 => {
                        let mut v_str_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_4186_: u8 = 0;
                        v_str_4183_ = crate::leanh::lean_ctor_get(v_x_4180_, 1);
                        v_str_4184_ = crate::leanh::lean_ctor_get(v_pre_4181_, 1);
                        v___x_4185_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__0;
                        v___x_4186_ = lean_string_dec_eq(v_str_4184_, v___x_4185_);
                        if v___x_4186_ == 0 {
                            let mut v___x_4187_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4188_: u8 = 0;
                            v___x_4187_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__1;
                            v___x_4188_ = lean_string_dec_eq(v_str_4184_, v___x_4187_);
                            if v___x_4188_ == 0 {
                                return v___y_4178_;
                            } else {
                                let mut v___x_4189_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_4190_: u8 = 0;
                                v___x_4189_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__2;
                                v___x_4190_ = lean_string_dec_eq(v_str_4183_, v___x_4189_);
                                if v___x_4190_ == 0 {
                                    return v___y_4178_;
                                } else {
                                    return v_suppressElabErrors_4179_;
                                }
                            }
                        } else {
                            let mut v___x_4191_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4192_: u8 = 0;
                            v___x_4191_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__3;
                            v___x_4192_ = lean_string_dec_eq(v_str_4183_, v___x_4191_);
                            if v___x_4192_ == 0 {
                                return v___y_4178_;
                            } else {
                                return v_suppressElabErrors_4179_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_4193_ = crate::leanh::lean_ctor_get(v_pre_4182_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_4193_) == 0 {
                            let mut v_str_4194_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_4195_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_4196_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4197_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4198_: u8 = 0;
                            v_str_4194_ = crate::leanh::lean_ctor_get(v_x_4180_, 1);
                            v_str_4195_ = crate::leanh::lean_ctor_get(v_pre_4181_, 1);
                            v_str_4196_ = crate::leanh::lean_ctor_get(v_pre_4182_, 1);
                            v___x_4197_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__4;
                            v___x_4198_ = lean_string_dec_eq(v_str_4196_, v___x_4197_);
                            if v___x_4198_ == 0 {
                                return v___y_4178_;
                            } else {
                                let mut v___x_4199_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_4200_: u8 = 0;
                                v___x_4199_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__5;
                                v___x_4200_ = lean_string_dec_eq(v_str_4195_, v___x_4199_);
                                if v___x_4200_ == 0 {
                                    return v___y_4178_;
                                } else {
                                    let mut v___x_4201_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_4202_: u8 = 0;
                                    v___x_4201_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__6;
                                    v___x_4202_ = lean_string_dec_eq(v_str_4194_, v___x_4201_);
                                    if v___x_4202_ == 0 {
                                        return v___y_4178_;
                                    } else {
                                        return v_suppressElabErrors_4179_;
                                    }
                                }
                            }
                        } else {
                            return v___y_4178_;
                        }
                    }
                    _ => {
                        return v___y_4178_;
                    }
                }
            }
            0 => {
                let mut v_str_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4205_: u8 = 0;
                v_str_4203_ = crate::leanh::lean_ctor_get(v_x_4180_, 1);
                v___x_4204_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___closed__7;
                v___x_4205_ = lean_string_dec_eq(v_str_4203_, v___x_4204_);
                if v___x_4205_ == 0 {
                    return v___y_4178_;
                } else {
                    return v_suppressElabErrors_4179_;
                }
            }
            _ => {
                return v___y_4178_;
            }
        }
    } else {
        return v___y_4178_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___boxed(
    mut v___y_4206_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_4207_: *mut crate::leanh::LeanObject,
    mut v_x_4208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3876__boxed_4209_: u8 = 0;
    let mut v_suppressElabErrors_boxed_4210_: u8 = 0;
    let mut v_res_4211_: u8 = 0;
    let mut v_r_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_3876__boxed_4209_ = (crate::leanh::lean_unbox(v___y_4206_) as u8);
    v_suppressElabErrors_boxed_4210_ = (crate::leanh::lean_unbox(v_suppressElabErrors_4207_) as u8);
    v_res_4211_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0(v___y_3876__boxed_4209_, v_suppressElabErrors_boxed_4210_, v_x_4208_);
    crate::leanh::lean_dec(v_x_4208_);
    v_r_4212_ = crate::leanh::lean_box((v_res_4211_) as usize);
    return v_r_4212_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(
    mut v_opts_4213_: *mut crate::leanh::LeanObject,
    mut v_opt_4214_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_4215_ = crate::leanh::lean_ctor_get(v_opt_4214_, 0);
    v_defValue_4216_ = crate::leanh::lean_ctor_get(v_opt_4214_, 1);
    v_map_4217_ = crate::leanh::lean_ctor_get(v_opts_4213_, 0);
    v___x_4218_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_4217_,
            v_name_4215_,
        );
    if crate::leanh::lean_obj_tag(v___x_4218_) == 0 {
        let mut v___x_4219_: u8 = 0;
        v___x_4219_ = (crate::leanh::lean_unbox(v_defValue_4216_) as u8);
        return v___x_4219_;
    } else {
        let mut v_val_4220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_4220_ = crate::leanh::lean_ctor_get(v___x_4218_, 0);
        crate::leanh::lean_inc(v_val_4220_);
        crate::leanh::lean_dec_ref_known(v___x_4218_, 1);
        if crate::leanh::lean_obj_tag(v_val_4220_) == 1 {
            let mut v_v_4221_: u8 = 0;
            v_v_4221_ = crate::leanh::lean_ctor_get_uint8(v_val_4220_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_4220_, 0);
            return v_v_4221_;
        } else {
            let mut v___x_4222_: u8 = 0;
            crate::leanh::lean_dec(v_val_4220_);
            v___x_4222_ = (crate::leanh::lean_unbox(v_defValue_4216_) as u8);
            return v___x_4222_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4___boxed(
    mut v_opts_4223_: *mut crate::leanh::LeanObject,
    mut v_opt_4224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4225_: u8 = 0;
    let mut v_r_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4225_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(v_opts_4223_, v_opt_4224_);
    crate::leanh::lean_dec_ref(v_opt_4224_);
    crate::leanh::lean_dec_ref(v_opts_4223_);
    v_r_4226_ = crate::leanh::lean_box((v_res_4225_) as usize);
    return v_r_4226_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2(
    mut v_ref_4228_: *mut crate::leanh::LeanObject,
    mut v_msgData_4229_: *mut crate::leanh::LeanObject,
    mut v_severity_4230_: u8,
    mut v_isSilent_4231_: u8,
    mut v___y_4232_: *mut crate::leanh::LeanObject,
    mut v___y_4233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_4236_: u8 = 0;
    let mut v___y_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4239_: u8 = 0;
    let mut v___y_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4259_: u8 = 0;
    let mut v___x_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4270_: u8 = 0;
    let mut v___y_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4273_: u8 = 0;
    let mut v___y_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4276_: u8 = 0;
    let mut v___y_4277_: u8 = 0;
    let mut v___y_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4285_: u8 = 0;
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: u8 = 0;
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4295_: u8 = 0;
    let mut v___y_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4299_: u8 = 0;
    let mut v___y_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4301_: u8 = 0;
    let mut v___y_4302_: u8 = 0;
    let mut v___y_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4309_: u8 = 0;
    let mut v___y_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4311_: u8 = 0;
    let mut v___y_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4314_: u8 = 0;
    let mut v_ref_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: u8 = 0;
    let mut v___y_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4323_: u8 = 0;
    let mut v___y_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4326_: u8 = 0;
    let mut v___y_4327_: u8 = 0;
    let mut v___y_4329_: u8 = 0;
    let mut v_fileName_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_4334_: u8 = 0;
    let mut v___x_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: u8 = 0;
    let mut v___x_4339_: u8 = 0;
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: u8 = 0;
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: u8 = 0;
    let mut v___x_4345_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4319_ = 2;
                v___x_4344_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4230_, v___x_4319_);
                if v___x_4344_ == 0 {
                    v___y_4329_ = v___x_4344_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_4229_);
                    v___x_4345_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_4229_);
                    v___y_4329_ = v___x_4345_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_4245_ = lean_st_ref_take(v___y_4244_);
                v_currNamespace_4246_ = crate::leanh::lean_ctor_get(v___y_4243_, 6);
                v_openDecls_4247_ = crate::leanh::lean_ctor_get(v___y_4243_, 7);
                v_env_4248_ = crate::leanh::lean_ctor_get(v___x_4245_, 0);
                v_nextMacroScope_4249_ = crate::leanh::lean_ctor_get(v___x_4245_, 1);
                v_ngen_4250_ = crate::leanh::lean_ctor_get(v___x_4245_, 2);
                v_auxDeclNGen_4251_ = crate::leanh::lean_ctor_get(v___x_4245_, 3);
                v_traceState_4252_ = crate::leanh::lean_ctor_get(v___x_4245_, 4);
                v_cache_4253_ = crate::leanh::lean_ctor_get(v___x_4245_, 5);
                v_messages_4254_ = crate::leanh::lean_ctor_get(v___x_4245_, 6);
                v_infoState_4255_ = crate::leanh::lean_ctor_get(v___x_4245_, 7);
                v_snapshotTasks_4256_ = crate::leanh::lean_ctor_get(v___x_4245_, 8);
                v_isSharedCheck_4270_ = (!crate::leanh::lean_is_exclusive(v___x_4245_)) as u8;
                if v_isSharedCheck_4270_ == 0 {
                    v___x_4258_ = v___x_4245_;
                    v_isShared_4259_ = v_isSharedCheck_4270_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4256_);
                    crate::leanh::lean_inc(v_infoState_4255_);
                    crate::leanh::lean_inc(v_messages_4254_);
                    crate::leanh::lean_inc(v_cache_4253_);
                    crate::leanh::lean_inc(v_traceState_4252_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4251_);
                    crate::leanh::lean_inc(v_ngen_4250_);
                    crate::leanh::lean_inc(v_nextMacroScope_4249_);
                    crate::leanh::lean_inc(v_env_4248_);
                    crate::leanh::lean_dec(v___x_4245_);
                    v___x_4258_ = crate::leanh::lean_box(0);
                    v_isShared_4259_ = v_isSharedCheck_4270_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_4247_);
                crate::leanh::lean_inc(v_currNamespace_4246_);
                v___x_4260_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4260_, 0, v_currNamespace_4246_);
                crate::leanh::lean_ctor_set(v___x_4260_, 1, v_openDecls_4247_);
                v___x_4261_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4261_, 0, v___x_4260_);
                crate::leanh::lean_ctor_set(v___x_4261_, 1, v___y_4242_);
                crate::leanh::lean_inc_ref(v___y_4238_);
                crate::leanh::lean_inc_ref(v___y_4241_);
                v___x_4262_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_4262_, 0, v___y_4241_);
                crate::leanh::lean_ctor_set(v___x_4262_, 1, v___y_4240_);
                crate::leanh::lean_ctor_set(v___x_4262_, 2, v___y_4237_);
                crate::leanh::lean_ctor_set(v___x_4262_, 3, v___y_4238_);
                crate::leanh::lean_ctor_set(v___x_4262_, 4, v___x_4261_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4262_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_4236_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4262_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_4239_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4262_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_4231_,
                );
                v___x_4263_ = l_Lean_MessageLog_add(v___x_4262_, v_messages_4254_);
                if v_isShared_4259_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4258_, 6, v___x_4263_);
                    v___x_4265_ = v___x_4258_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4269_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_env_4248_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 1, v_nextMacroScope_4249_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 2, v_ngen_4250_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 3, v_auxDeclNGen_4251_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 4, v_traceState_4252_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 5, v_cache_4253_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 6, v___x_4263_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 7, v_infoState_4255_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4269_, 8, v_snapshotTasks_4256_);
                    v___x_4265_ = v_reuseFailAlloc_4269_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4266_ = lean_st_ref_set(v___y_4244_, v___x_4265_);
                v___x_4267_ = crate::leanh::lean_box(0);
                v___x_4268_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4268_, 0, v___x_4267_);
                return v___x_4268_;
            }
            4 => {
                v___x_4280_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_4229_,
                    );
                v___x_4281_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__3(v___x_4280_, v___y_4232_, v___y_4233_);
                v_a_4282_ = crate::leanh::lean_ctor_get(v___x_4281_, 0);
                v_isSharedCheck_4295_ = (!crate::leanh::lean_is_exclusive(v___x_4281_)) as u8;
                if v_isSharedCheck_4295_ == 0 {
                    v___x_4284_ = v___x_4281_;
                    v_isShared_4285_ = v_isSharedCheck_4295_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4282_);
                    crate::leanh::lean_dec(v___x_4281_);
                    v___x_4284_ = crate::leanh::lean_box(0);
                    v_isShared_4285_ = v_isSharedCheck_4295_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_4274_, 2);
                v___x_4286_ = l_Lean_FileMap_toPosition(v___y_4274_, v___y_4275_);
                crate::leanh::lean_dec(v___y_4275_);
                v___x_4287_ = l_Lean_FileMap_toPosition(v___y_4274_, v___y_4279_);
                crate::leanh::lean_dec(v___y_4279_);
                v___x_4288_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4288_, 0, v___x_4287_);
                v___x_4289_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___closed__0;
                if v___y_4277_ == 0 {
                    crate::leanh::lean_del_object(v___x_4284_);
                    crate::leanh::lean_dec_ref(v___y_4272_);
                    v___y_4236_ = v___y_4273_;
                    v___y_4237_ = v___x_4288_;
                    v___y_4238_ = v___x_4289_;
                    v___y_4239_ = v___y_4276_;
                    v___y_4240_ = v___x_4286_;
                    v___y_4241_ = v___y_4278_;
                    v___y_4242_ = v_a_4282_;
                    v___y_4243_ = v___y_4232_;
                    v___y_4244_ = v___y_4233_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_4282_);
                    v___x_4290_ = l_Lean_MessageData_hasTag(v___y_4272_, v_a_4282_);
                    if v___x_4290_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4288_, 1);
                        crate::leanh::lean_dec_ref(v___x_4286_);
                        crate::leanh::lean_dec(v_a_4282_);
                        v___x_4291_ = crate::leanh::lean_box(0);
                        if v_isShared_4285_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4284_, 0, v___x_4291_);
                            v___x_4293_ = v___x_4284_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_4294_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4294_, 0, v___x_4291_);
                            v___x_4293_ = v_reuseFailAlloc_4294_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4284_);
                        v___y_4236_ = v___y_4273_;
                        v___y_4237_ = v___x_4288_;
                        v___y_4238_ = v___x_4289_;
                        v___y_4239_ = v___y_4276_;
                        v___y_4240_ = v___x_4286_;
                        v___y_4241_ = v___y_4278_;
                        v___y_4242_ = v_a_4282_;
                        v___y_4243_ = v___y_4232_;
                        v___y_4244_ = v___y_4233_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_4293_;
            }
            7 => {
                v___x_4305_ = l_Lean_Syntax_getTailPos_x3f(v___y_4298_, v___y_4299_);
                crate::leanh::lean_dec(v___y_4298_);
                if crate::leanh::lean_obj_tag(v___x_4305_) == 0 {
                    crate::leanh::lean_inc(v___y_4304_);
                    v___y_4272_ = v___y_4297_;
                    v___y_4273_ = v___y_4299_;
                    v___y_4274_ = v___y_4300_;
                    v___y_4275_ = v___y_4304_;
                    v___y_4276_ = v___y_4301_;
                    v___y_4277_ = v___y_4302_;
                    v___y_4278_ = v___y_4303_;
                    v___y_4279_ = v___y_4304_;
                    state = 4;
                    continue;
                } else {
                    v_val_4306_ = crate::leanh::lean_ctor_get(v___x_4305_, 0);
                    crate::leanh::lean_inc(v_val_4306_);
                    crate::leanh::lean_dec_ref_known(v___x_4305_, 1);
                    v___y_4272_ = v___y_4297_;
                    v___y_4273_ = v___y_4299_;
                    v___y_4274_ = v___y_4300_;
                    v___y_4275_ = v___y_4304_;
                    v___y_4276_ = v___y_4301_;
                    v___y_4277_ = v___y_4302_;
                    v___y_4278_ = v___y_4303_;
                    v___y_4279_ = v_val_4306_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_4315_ = l_Lean_replaceRef(v_ref_4228_, v___y_4313_);
                v___x_4316_ = l_Lean_Syntax_getPos_x3f(v_ref_4315_, v___y_4309_);
                if crate::leanh::lean_obj_tag(v___x_4316_) == 0 {
                    v___x_4317_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_4297_ = v___y_4308_;
                    v___y_4298_ = v_ref_4315_;
                    v___y_4299_ = v___y_4309_;
                    v___y_4300_ = v___y_4310_;
                    v___y_4301_ = v___y_4314_;
                    v___y_4302_ = v___y_4311_;
                    v___y_4303_ = v___y_4312_;
                    v___y_4304_ = v___x_4317_;
                    state = 7;
                    continue;
                } else {
                    v_val_4318_ = crate::leanh::lean_ctor_get(v___x_4316_, 0);
                    crate::leanh::lean_inc(v_val_4318_);
                    crate::leanh::lean_dec_ref_known(v___x_4316_, 1);
                    v___y_4297_ = v___y_4308_;
                    v___y_4298_ = v_ref_4315_;
                    v___y_4299_ = v___y_4309_;
                    v___y_4300_ = v___y_4310_;
                    v___y_4301_ = v___y_4314_;
                    v___y_4302_ = v___y_4311_;
                    v___y_4303_ = v___y_4312_;
                    v___y_4304_ = v_val_4318_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_4327_ == 0 {
                    v___y_4308_ = v___y_4321_;
                    v___y_4309_ = v___y_4326_;
                    v___y_4310_ = v___y_4322_;
                    v___y_4311_ = v___y_4323_;
                    v___y_4312_ = v___y_4324_;
                    v___y_4313_ = v___y_4325_;
                    v___y_4314_ = v_severity_4230_;
                    state = 8;
                    continue;
                } else {
                    v___y_4308_ = v___y_4321_;
                    v___y_4309_ = v___y_4326_;
                    v___y_4310_ = v___y_4322_;
                    v___y_4311_ = v___y_4323_;
                    v___y_4312_ = v___y_4324_;
                    v___y_4313_ = v___y_4325_;
                    v___y_4314_ = v___x_4319_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_4329_ == 0 {
                    v_fileName_4330_ = crate::leanh::lean_ctor_get(v___y_4232_, 0);
                    v_fileMap_4331_ = crate::leanh::lean_ctor_get(v___y_4232_, 1);
                    v_options_4332_ = crate::leanh::lean_ctor_get(v___y_4232_, 2);
                    v_ref_4333_ = crate::leanh::lean_ctor_get(v___y_4232_, 5);
                    v_suppressElabErrors_4334_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_4232_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_4335_ = crate::leanh::lean_box((v___y_4329_) as usize);
                    v___x_4336_ = crate::leanh::lean_box((v_suppressElabErrors_4334_) as usize);
                    v___f_4337_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_4337_, 0, v___x_4335_);
                    crate::leanh::lean_closure_set(v___f_4337_, 1, v___x_4336_);
                    v___x_4338_ = 1;
                    v___x_4339_ = l_Lean_instBEqMessageSeverity_beq(v_severity_4230_, v___x_4338_);
                    if v___x_4339_ == 0 {
                        v___y_4321_ = v___f_4337_;
                        v___y_4322_ = v_fileMap_4331_;
                        v___y_4323_ = v_suppressElabErrors_4334_;
                        v___y_4324_ = v_fileName_4330_;
                        v___y_4325_ = v_ref_4333_;
                        v___y_4326_ = v___y_4329_;
                        v___y_4327_ = v___x_4339_;
                        state = 9;
                        continue;
                    } else {
                        v___x_4340_ = l_Lean_warningAsError;
                        v___x_4341_ = l_Lean_Option_get___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2_spec__4(v_options_4332_, v___x_4340_);
                        v___y_4321_ = v___f_4337_;
                        v___y_4322_ = v_fileMap_4331_;
                        v___y_4323_ = v_suppressElabErrors_4334_;
                        v___y_4324_ = v_fileName_4330_;
                        v___y_4325_ = v_ref_4333_;
                        v___y_4326_ = v___y_4329_;
                        v___y_4327_ = v___x_4341_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_4229_);
                    v___x_4342_ = crate::leanh::lean_box(0);
                    v___x_4343_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4343_, 0, v___x_4342_);
                    return v___x_4343_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2___boxed(
    mut v_ref_4346_: *mut crate::leanh::LeanObject,
    mut v_msgData_4347_: *mut crate::leanh::LeanObject,
    mut v_severity_4348_: *mut crate::leanh::LeanObject,
    mut v_isSilent_4349_: *mut crate::leanh::LeanObject,
    mut v___y_4350_: *mut crate::leanh::LeanObject,
    mut v___y_4351_: *mut crate::leanh::LeanObject,
    mut v___y_4352_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_4353_: u8 = 0;
    let mut v_isSilent_boxed_4354_: u8 = 0;
    let mut v_res_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_4353_ = (crate::leanh::lean_unbox(v_severity_4348_) as u8);
    v_isSilent_boxed_4354_ = (crate::leanh::lean_unbox(v_isSilent_4349_) as u8);
    v_res_4355_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_ref_4346_, v_msgData_4347_, v_severity_boxed_4353_, v_isSilent_boxed_4354_, v___y_4350_, v___y_4351_);
    crate::leanh::lean_dec(v___y_4351_);
    crate::leanh::lean_dec_ref(v___y_4350_);
    crate::leanh::lean_dec(v_ref_4346_);
    return v_res_4355_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1(
    mut v_msgData_4356_: *mut crate::leanh::LeanObject,
    mut v_severity_4357_: u8,
    mut v_isSilent_4358_: u8,
    mut v___y_4359_: *mut crate::leanh::LeanObject,
    mut v___y_4360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_4362_ = crate::leanh::lean_ctor_get(v___y_4359_, 5);
    v___x_4363_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1_spec__2(v_ref_4362_, v_msgData_4356_, v_severity_4357_, v_isSilent_4358_, v___y_4359_, v___y_4360_);
    return v___x_4363_;
}
pub unsafe fn l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1___boxed(
    mut v_msgData_4364_: *mut crate::leanh::LeanObject,
    mut v_severity_4365_: *mut crate::leanh::LeanObject,
    mut v_isSilent_4366_: *mut crate::leanh::LeanObject,
    mut v___y_4367_: *mut crate::leanh::LeanObject,
    mut v___y_4368_: *mut crate::leanh::LeanObject,
    mut v___y_4369_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_4370_: u8 = 0;
    let mut v_isSilent_boxed_4371_: u8 = 0;
    let mut v_res_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_4370_ = (crate::leanh::lean_unbox(v_severity_4365_) as u8);
    v_isSilent_boxed_4371_ = (crate::leanh::lean_unbox(v_isSilent_4366_) as u8);
    v_res_4372_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1(v_msgData_4364_, v_severity_boxed_4370_, v_isSilent_boxed_4371_, v___y_4367_, v___y_4368_);
    crate::leanh::lean_dec(v___y_4368_);
    crate::leanh::lean_dec_ref(v___y_4367_);
    return v_res_4372_;
}
pub unsafe fn l_Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1(
    mut v_msgData_4373_: *mut crate::leanh::LeanObject,
    mut v___y_4374_: *mut crate::leanh::LeanObject,
    mut v___y_4375_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4377_: u8 = 0;
    let mut v___x_4378_: u8 = 0;
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4377_ = 1;
    v___x_4378_ = 0;
    v___x_4379_ = l_Lean_log___at___00Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1_spec__1(v_msgData_4373_, v___x_4377_, v___x_4378_, v___y_4374_, v___y_4375_);
    return v___x_4379_;
}
pub unsafe fn l_Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1___boxed(
    mut v_msgData_4380_: *mut crate::leanh::LeanObject,
    mut v___y_4381_: *mut crate::leanh::LeanObject,
    mut v___y_4382_: *mut crate::leanh::LeanObject,
    mut v___y_4383_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4384_ = l_Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1(v_msgData_4380_, v___y_4381_, v___y_4382_);
    crate::leanh::lean_dec(v___y_4382_);
    crate::leanh::lean_dec_ref(v___y_4381_);
    return v_res_4384_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4386_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_;
    v___x_4387_ = l_Lean_stringToMessageData(v___x_4386_);
    return v___x_4387_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_(
    mut v___x_4388_: *mut crate::leanh::LeanObject,
    mut v_declName_4389_: *mut crate::leanh::LeanObject,
    mut v___y_4390_: *mut crate::leanh::LeanObject,
    mut v___y_4391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: u8 = 0;
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4411_: u8 = 0;
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4423_: u8 = 0;
    let mut v___f_4424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4435_: u8 = 0;
    let mut v_unused_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4437_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4393_ = lean_st_ref_get(v___y_4391_);
                v_env_4394_ = crate::leanh::lean_ctor_get(v___x_4393_, 0);
                crate::leanh::lean_inc_ref(v_env_4394_);
                crate::leanh::lean_dec(v___x_4393_);
                v___x_4395_ = l_Lean_Meta_Tactic_Cbv_cbvEvalExt;
                v_ext_4396_ = crate::leanh::lean_ctor_get(v___x_4395_, 1);
                v_toEnvExtension_4397_ = crate::leanh::lean_ctor_get(v_ext_4396_, 0);
                v_asyncMode_4398_ = crate::leanh::lean_ctor_get(v_toEnvExtension_4397_, 2);
                v___x_4399_ = l_Lean_ScopedEnvExtension_getState___redArg(
                    v___x_4388_,
                    v___x_4395_,
                    v_env_4394_,
                    v_asyncMode_4398_,
                );
                v___x_4400_ =
                    l_Lean_Meta_Tactic_Cbv_CbvEvalState_erase(v___x_4399_, v_declName_4389_);
                if crate::leanh::lean_obj_tag(v___x_4400_) == 0 {
                    v___x_4401_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstVal___at___00Lean_Meta_Tactic_Cbv_mkCbvTheoremFromConst_spec__0_spec__0_spec__2___redArg___closed__3);
                    v___x_4402_ = 0;
                    v___x_4403_ = l_Lean_MessageData_ofConstName(v_declName_4389_, v___x_4402_);
                    v___x_4404_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4404_, 0, v___x_4401_);
                    crate::leanh::lean_ctor_set(v___x_4404_, 1, v___x_4403_);
                    v___x_4405_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_);
                    v___x_4406_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4406_, 0, v___x_4404_);
                    crate::leanh::lean_ctor_set(v___x_4406_, 1, v___x_4405_);
                    v___x_4407_ = l_Lean_logWarning___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__1(v___x_4406_, v___y_4390_, v___y_4391_);
                    return v___x_4407_;
                } else {
                    crate::leanh::lean_dec(v_declName_4389_);
                    v_val_4408_ = crate::leanh::lean_ctor_get(v___x_4400_, 0);
                    v_isSharedCheck_4437_ = (!crate::leanh::lean_is_exclusive(v___x_4400_)) as u8;
                    if v_isSharedCheck_4437_ == 0 {
                        v___x_4410_ = v___x_4400_;
                        v_isShared_4411_ = v_isSharedCheck_4437_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4408_);
                        crate::leanh::lean_dec(v___x_4400_);
                        v___x_4410_ = crate::leanh::lean_box(0);
                        v_isShared_4411_ = v_isSharedCheck_4437_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4412_ = lean_st_ref_take(v___y_4391_);
                v_env_4413_ = crate::leanh::lean_ctor_get(v___x_4412_, 0);
                v_nextMacroScope_4414_ = crate::leanh::lean_ctor_get(v___x_4412_, 1);
                v_ngen_4415_ = crate::leanh::lean_ctor_get(v___x_4412_, 2);
                v_auxDeclNGen_4416_ = crate::leanh::lean_ctor_get(v___x_4412_, 3);
                v_traceState_4417_ = crate::leanh::lean_ctor_get(v___x_4412_, 4);
                v_messages_4418_ = crate::leanh::lean_ctor_get(v___x_4412_, 6);
                v_infoState_4419_ = crate::leanh::lean_ctor_get(v___x_4412_, 7);
                v_snapshotTasks_4420_ = crate::leanh::lean_ctor_get(v___x_4412_, 8);
                v_isSharedCheck_4435_ = (!crate::leanh::lean_is_exclusive(v___x_4412_)) as u8;
                if v_isSharedCheck_4435_ == 0 {
                    v_unused_4436_ = crate::leanh::lean_ctor_get(v___x_4412_, 5);
                    crate::leanh::lean_dec(v_unused_4436_);
                    v___x_4422_ = v___x_4412_;
                    v_isShared_4423_ = v_isSharedCheck_4435_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4420_);
                    crate::leanh::lean_inc(v_infoState_4419_);
                    crate::leanh::lean_inc(v_messages_4418_);
                    crate::leanh::lean_inc(v_traceState_4417_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4416_);
                    crate::leanh::lean_inc(v_ngen_4415_);
                    crate::leanh::lean_inc(v_nextMacroScope_4414_);
                    crate::leanh::lean_inc(v_env_4413_);
                    crate::leanh::lean_dec(v___x_4412_);
                    v___x_4422_ = crate::leanh::lean_box(0);
                    v_isShared_4423_ = v_isSharedCheck_4435_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_4424_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_4424_, 0, v_val_4408_);
                v___x_4425_ = l_Lean_ScopedEnvExtension_modifyState___redArg(
                    v___x_4395_,
                    v_env_4413_,
                    v___f_4424_,
                );
                v___x_4426_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__2_once), _init_l_Lean_ScopedEnvExtension_add___at___00__private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2__spec__0___redArg___closed__2);
                if v_isShared_4423_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4422_, 5, v___x_4426_);
                    crate::leanh::lean_ctor_set(v___x_4422_, 0, v___x_4425_);
                    v___x_4428_ = v___x_4422_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4434_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4434_, 0, v___x_4425_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4434_, 1, v_nextMacroScope_4414_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4434_, 2, v_ngen_4415_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4434_, 3, v_auxDeclNGen_4416_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4434_, 4, v_traceState_4417_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4434_, 5, v___x_4426_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4434_, 6, v_messages_4418_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4434_, 7, v_infoState_4419_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4434_, 8, v_snapshotTasks_4420_);
                    v___x_4428_ = v_reuseFailAlloc_4434_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4429_ = lean_st_ref_set(v___y_4391_, v___x_4428_);
                v___x_4430_ = crate::leanh::lean_box(0);
                if v_isShared_4411_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4410_, 0);
                    crate::leanh::lean_ctor_set(v___x_4410_, 0, v___x_4430_);
                    v___x_4432_ = v___x_4410_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4433_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4433_, 0, v___x_4430_);
                    v___x_4432_ = v_reuseFailAlloc_4433_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4432_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2____boxed(
    mut v___x_4438_: *mut crate::leanh::LeanObject,
    mut v_declName_4439_: *mut crate::leanh::LeanObject,
    mut v___y_4440_: *mut crate::leanh::LeanObject,
    mut v___y_4441_: *mut crate::leanh::LeanObject,
    mut v___y_4442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4443_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_(v___x_4438_, v_declName_4439_, v___y_4440_, v___y_4441_);
    crate::leanh::lean_dec(v___y_4441_);
    crate::leanh::lean_dec_ref(v___y_4440_);
    crate::leanh::lean_dec_ref(v___x_4438_);
    return v_res_4443_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4465_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_;
    v___x_4466_ = l_Lean_registerBuiltinAttribute(v___x_4465_);
    return v___x_4466_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2____boxed(
    mut v_a_4467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4468_ = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_();
    return v_res_4468_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_NameMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ScopedEnvExtension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_InfoTree(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_AuxLemma(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default =
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry_default);
    l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry =
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvEvalEntry);
    res = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2896192001____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Tactic_Cbv_cbvEvalExt = crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_cbvEvalExt);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_CbvEvalExt_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvEvalExt_2146700013____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_NameMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_ScopedEnvExtension(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_InfoTree(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Theorems(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_AuxLemma(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Cbv_CbvEvalExt(builtin);
}

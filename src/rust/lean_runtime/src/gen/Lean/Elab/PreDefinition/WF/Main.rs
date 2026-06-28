// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Main
// Imports: Lean.Elab.PreDefinition.WF.PackMutual Lean.Elab.PreDefinition.WF.FloatRecApp Lean.Elab.PreDefinition.WF.Rel Lean.Elab.PreDefinition.WF.Fix Lean.Elab.PreDefinition.WF.Unfold Lean.Elab.PreDefinition.WF.Preprocess Lean.Elab.PreDefinition.WF.GuessLex
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_Lean_Syntax_getPos_x3f, l_Lean_Syntax_getTailPos_x3f,
    l_Lean_replaceRef,
};
use crate::r#gen::Lean::CoreM::l_Lean_enableRealizationsForConst;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Data::Position::l_Lean_FileMap_toPosition;
use crate::r#gen::Lean::Elab::DefView::l_Lean_Elab_DefKind_isTheorem;
use crate::r#gen::Lean::Elab::PreDefinition::Basic::{
    l_Lean_Elab_addAndCompilePartialRec, l_Lean_Elab_addAsAxiom___redArg,
    l_Lean_Elab_eraseRecAppSyntaxExpr, l_Lean_Elab_instInhabitedPreDefinition_default,
};
use crate::r#gen::Lean::Elab::PreDefinition::FixedParams::l_Lean_Elab_getFixedParamPerms;
use crate::r#gen::Lean::Elab::PreDefinition::Mutual::{
    l_Lean_Elab_Mutual_addPreDefAttributes, l_Lean_Elab_Mutual_addPreDefsFromUnary,
    l_Lean_Elab_Mutual_cleanPreDef,
};
use crate::r#gen::Lean::Elab::PreDefinition::WF::Eqns::l_Lean_Elab_WF_registerEqnsInfo;
use crate::r#gen::Lean::Elab::PreDefinition::WF::Fix::{
    initialize_Lean_Elab_PreDefinition_WF_Fix, l_Lean_Elab_WF_isNatLtWF, l_Lean_Elab_WF_mkFix,
    runtime_initialize_Lean_Elab_PreDefinition_WF_Fix,
};
use crate::r#gen::Lean::Elab::PreDefinition::WF::FloatRecApp::{
    initialize_Lean_Elab_PreDefinition_WF_FloatRecApp, l_Lean_Elab_WF_floatRecApp,
    runtime_initialize_Lean_Elab_PreDefinition_WF_FloatRecApp,
};
use crate::r#gen::Lean::Elab::PreDefinition::WF::GuessLex::{
    initialize_Lean_Elab_PreDefinition_WF_GuessLex, l_Lean_Elab_WF_guessLex,
    runtime_initialize_Lean_Elab_PreDefinition_WF_GuessLex,
};
use crate::r#gen::Lean::Elab::PreDefinition::WF::PackMutual::{
    initialize_Lean_Elab_PreDefinition_WF_PackMutual, l_Lean_Elab_WF_packMutual,
    l_Lean_Elab_WF_preDefsFromUnaryNonRec, l_Lean_Elab_WF_varyingVarNames,
    runtime_initialize_Lean_Elab_PreDefinition_WF_PackMutual,
};
use crate::r#gen::Lean::Elab::PreDefinition::WF::Preprocess::{
    initialize_Lean_Elab_PreDefinition_WF_Preprocess, l_Lean_Elab_WF_preprocess,
    runtime_initialize_Lean_Elab_PreDefinition_WF_Preprocess,
};
use crate::r#gen::Lean::Elab::PreDefinition::WF::Rel::{
    initialize_Lean_Elab_PreDefinition_WF_Rel, l_Lean_Elab_WF_elabWFRel___redArg,
    runtime_initialize_Lean_Elab_PreDefinition_WF_Rel,
};
use crate::r#gen::Lean::Elab::PreDefinition::WF::Unfold::{
    initialize_Lean_Elab_PreDefinition_WF_Unfold, l_Lean_Elab_WF_mkBinaryUnfoldEq,
    l_Lean_Elab_WF_mkUnfoldEq, runtime_initialize_Lean_Elab_PreDefinition_WF_Unfold,
};
use crate::r#gen::Lean::Elab::Util::{l_Lean_Elab_getBetterRef, l_Lean_Elab_pp_macroStack};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_setExporting, l_Lean_Environment_unlockAsync,
};
use crate::r#gen::Lean::Expr::{l_Lean_Expr_bindingDomain_x21, l_Lean_Expr_isForall};
use crate::r#gen::Lean::ExtraModUses::l_Lean_copyExtraModUses;
use crate::r#gen::Lean::Log::{
    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed, l_Lean_warningAsError,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_hasSyntheticSorry, l_Lean_MessageData_hasTag, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_MessageData_ofSyntax,
    l_Lean_MessageLog_add, l_Lean_indentD, l_Lean_instBEqMessageSeverity_beq,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux, l_Lean_Meta_whnfForall,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::RecExt::l_Lean_Meta_markAsRecursive___redArg;
use crate::r#gen::Lean::Meta::Transform::{
    l_Lean_Meta_unfoldDeclsFrom, l_Lean_Meta_unfoldIfArgIsAppOf,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
};
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_string_dec_eq,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__1_value: crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 16, m_capacity: 16, m_length: 15, m_data: [119, 104, 105, 108, 101, 32, 101, 120, 112, 97, 110, 100, 105, 110, 103, 0]};
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__2_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__1_value) as *mut crate::leanh::LeanObject] };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [119, 105, 116, 104, 32, 114, 101, 115, 117, 108, 116, 105, 110, 103, 32, 101, 120, 112, 97, 110, 115, 105, 111, 110, 0]};
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__1_value: crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject] };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__0_value: crate::leanh::LeanStringObject<41> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [119, 101, 108, 108, 45, 102, 111, 117, 110, 100, 101, 100, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 117, 115, 101, 100, 44, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__2_value: crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 116, 97, 107, 101, 32, 97, 110, 121, 32, 40, 110, 111, 110, 45, 102, 105, 120, 101, 100, 41, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_wfRecursion___lam__1___closed__0_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Elab_wfRecursion___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_wfRecursion___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_wfRecursion___lam__1___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_wfRecursion___lam__1___closed__0_value)
                as *mut crate::leanh::LeanObject,
            14231257465488249300 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_wfRecursion___lam__1___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_wfRecursion___lam__1___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__1_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [117, 110, 115, 111, 108, 118, 101, 100, 71, 111, 97, 108, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__3_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [115, 121, 110, 116, 104, 80, 108, 97, 99, 101, 104, 111, 108, 100, 101, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [108, 101, 97, 110, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__5_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [105, 110, 100, 117, 99, 116, 105, 111, 110, 87, 105, 116, 104, 78, 111, 65, 108, 116, 115, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__6_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [95, 110, 97, 109, 101, 100, 69, 114, 114, 111, 114, 0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__0_value: crate::leanh::LeanStringObject<57> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 57, m_capacity: 57, m_length: 56, m_data: [109, 97, 114, 107, 105, 110, 103, 32, 102, 117, 110, 99, 116, 105, 111, 110, 115, 32, 100, 101, 102, 105, 110, 101, 100, 32, 98, 121, 32, 119, 101, 108, 108, 45, 102, 111, 117, 110, 100, 101, 100, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 32, 97, 115, 32, 96, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__1_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [96, 32, 105, 115, 32, 110, 111, 116, 32, 101, 102, 102, 101, 99, 116, 105, 118, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__2_value) as *mut crate::leanh::LeanObject,7045040058828669725 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__4_value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [115, 101, 109, 105, 114, 101, 100, 117, 99, 105, 98, 108, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__4_value) as *mut crate::leanh::LeanObject,2616510057874194026 as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__1_value:
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
static mut l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_wfRecursion___lam__3___closed__0_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [119, 102, 82, 101, 108, 58, 32, 0],
    };
static mut l_Lean_Elab_wfRecursion___lam__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_wfRecursion___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_wfRecursion___lam__3___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_wfRecursion___lam__3___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_wfRecursion___lam__4___closed__0_value: crate::leanh::LeanStringObject<44> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 44,
        m_capacity: 44,
        m_length: 43,
        m_data: [
            119, 102, 82, 101, 99, 117, 114, 115, 105, 111, 110, 58, 32, 101, 120, 112, 101, 99,
            116, 101, 100, 32, 117, 110, 97, 114, 121, 32, 102, 117, 110, 99, 116, 105, 111, 110,
            32, 116, 121, 112, 101, 58, 32, 0,
        ],
    };
static mut l_Lean_Elab_wfRecursion___lam__4___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_wfRecursion___lam__4___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_wfRecursion___lam__4___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_wfRecursion___lam__4___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_wfRecursion___closed__0_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0],
    };
static mut l_Lean_Elab_wfRecursion___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_wfRecursion___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_wfRecursion___closed__1_value: crate::leanh::LeanStringObject<3> =
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
        m_data: [119, 102, 0],
    };
static mut l_Lean_Elab_wfRecursion___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_wfRecursion___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_wfRecursion___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,12843180897352504333 as *mut crate::leanh::LeanObject] };
static l_Lean_Elab_wfRecursion___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_wfRecursion___closed__2_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_wfRecursion___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6897119537390546559 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_wfRecursion___closed__2_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_wfRecursion___closed__2_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_wfRecursion___closed__1_value)
                as *mut crate::leanh::LeanObject,
            16378770904461102315 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_wfRecursion___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_wfRecursion___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_wfRecursion___closed__3_value: crate::leanh::LeanStringObject<4> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [62, 62, 32, 0],
    };
static mut l_Lean_Elab_wfRecursion___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_wfRecursion___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_wfRecursion___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_wfRecursion___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_wfRecursion___closed__5_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [32, 58, 61, 10, 0],
    };
static mut l_Lean_Elab_wfRecursion___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_wfRecursion___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_wfRecursion___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_wfRecursion___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_wfRecursion___closed__7_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
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
            117, 110, 97, 114, 121, 80, 114, 101, 68, 101, 102, 80, 114, 111, 99, 101, 115, 115,
            101, 100, 58, 0,
        ],
    };
static mut l_Lean_Elab_wfRecursion___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_wfRecursion___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_wfRecursion___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_wfRecursion___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_wfRecursion___closed__9_value: crate::leanh::LeanStringObject<13> =
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
        m_data: [117, 110, 97, 114, 121, 80, 114, 101, 68, 101, 102, 58, 0],
    };
static mut l_Lean_Elab_wfRecursion___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_wfRecursion___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_wfRecursion___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_wfRecursion___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_wfRecursion___boxed__const__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + core::mem::size_of::<usize>() * 1) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(0 as *mut crate::leanh::LeanObject)],
    };
pub static mut l_Lean_Elab_wfRecursion___boxed__const__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_wfRecursion___boxed__const__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,5444244426488757208 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<14> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [80, 114, 101, 68, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13137517462150097927 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [87, 70, 0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3605452190871862503 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 97, 105, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__8_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11527647570593103758 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__10_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,16681038731969867959 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__11_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10081066737318281290 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__12_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,16584419178443049096 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__13_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__14_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17110484281458795685 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__15_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__16_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,138514765357503512 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__17_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17752538390258892945 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__18_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,12392621330832324399 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__19_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,17886144840214276108 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__20_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__7_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,2199936252580437888 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__21_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__9_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1881709542014824965 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__22_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 1197449596 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,2761134277730256498 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__23_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__24_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1679577236075163133 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__25_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__26_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,3565243550472261469 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__27_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,8887678442999467056 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2447_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2447_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2448_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0_once
        ),
        _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__0,
    );
    v___x_2449_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2449_, 0, v___x_2448_);
    return v___x_2449_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2450_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1_once
        ),
        _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1,
    );
    v___x_2451_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2451_, 0, v___x_2450_);
    crate::leanh::lean_ctor_set(v___x_2451_, 1, v___x_2450_);
    return v___x_2451_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2452_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1_once
        ),
        _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__1,
    );
    v___x_2453_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2453_, 0, v___x_2452_);
    crate::leanh::lean_ctor_set(v___x_2453_, 1, v___x_2452_);
    crate::leanh::lean_ctor_set(v___x_2453_, 2, v___x_2452_);
    crate::leanh::lean_ctor_set(v___x_2453_, 3, v___x_2452_);
    crate::leanh::lean_ctor_set(v___x_2453_, 4, v___x_2452_);
    crate::leanh::lean_ctor_set(v___x_2453_, 5, v___x_2452_);
    return v___x_2453_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(
    mut v_env_2454_: *mut crate::leanh::LeanObject,
    mut v___y_2455_: *mut crate::leanh::LeanObject,
    mut v___y_2456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2468_: u8 = 0;
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2480_: u8 = 0;
    let mut v___x_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2488_: u8 = 0;
    let mut v_unused_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2491_: u8 = 0;
    let mut v_unused_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2458_ = lean_st_ref_take(v___y_2456_);
                v_nextMacroScope_2459_ = crate::leanh::lean_ctor_get(v___x_2458_, 1);
                v_ngen_2460_ = crate::leanh::lean_ctor_get(v___x_2458_, 2);
                v_auxDeclNGen_2461_ = crate::leanh::lean_ctor_get(v___x_2458_, 3);
                v_traceState_2462_ = crate::leanh::lean_ctor_get(v___x_2458_, 4);
                v_messages_2463_ = crate::leanh::lean_ctor_get(v___x_2458_, 6);
                v_infoState_2464_ = crate::leanh::lean_ctor_get(v___x_2458_, 7);
                v_snapshotTasks_2465_ = crate::leanh::lean_ctor_get(v___x_2458_, 8);
                v_isSharedCheck_2491_ = (!crate::leanh::lean_is_exclusive(v___x_2458_)) as u8;
                if v_isSharedCheck_2491_ == 0 {
                    v_unused_2492_ = crate::leanh::lean_ctor_get(v___x_2458_, 5);
                    crate::leanh::lean_dec(v_unused_2492_);
                    v_unused_2493_ = crate::leanh::lean_ctor_get(v___x_2458_, 0);
                    crate::leanh::lean_dec(v_unused_2493_);
                    v___x_2467_ = v___x_2458_;
                    v_isShared_2468_ = v_isSharedCheck_2491_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_2465_);
                    crate::leanh::lean_inc(v_infoState_2464_);
                    crate::leanh::lean_inc(v_messages_2463_);
                    crate::leanh::lean_inc(v_traceState_2462_);
                    crate::leanh::lean_inc(v_auxDeclNGen_2461_);
                    crate::leanh::lean_inc(v_ngen_2460_);
                    crate::leanh::lean_inc(v_nextMacroScope_2459_);
                    crate::leanh::lean_dec(v___x_2458_);
                    v___x_2467_ = crate::leanh::lean_box(0);
                    v_isShared_2468_ = v_isSharedCheck_2491_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2469_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
                if v_isShared_2468_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2467_, 5, v___x_2469_);
                    crate::leanh::lean_ctor_set(v___x_2467_, 0, v_env_2454_);
                    v___x_2471_ = v___x_2467_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2490_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_env_2454_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 1, v_nextMacroScope_2459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 2, v_ngen_2460_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 3, v_auxDeclNGen_2461_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 4, v_traceState_2462_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 5, v___x_2469_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 6, v_messages_2463_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 7, v_infoState_2464_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 8, v_snapshotTasks_2465_);
                    v___x_2471_ = v_reuseFailAlloc_2490_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2472_ = lean_st_ref_set(v___y_2456_, v___x_2471_);
                v___x_2473_ = lean_st_ref_take(v___y_2455_);
                v_mctx_2474_ = crate::leanh::lean_ctor_get(v___x_2473_, 0);
                v_zetaDeltaFVarIds_2475_ = crate::leanh::lean_ctor_get(v___x_2473_, 2);
                v_postponed_2476_ = crate::leanh::lean_ctor_get(v___x_2473_, 3);
                v_diag_2477_ = crate::leanh::lean_ctor_get(v___x_2473_, 4);
                v_isSharedCheck_2488_ = (!crate::leanh::lean_is_exclusive(v___x_2473_)) as u8;
                if v_isSharedCheck_2488_ == 0 {
                    v_unused_2489_ = crate::leanh::lean_ctor_get(v___x_2473_, 1);
                    crate::leanh::lean_dec(v_unused_2489_);
                    v___x_2479_ = v___x_2473_;
                    v_isShared_2480_ = v_isSharedCheck_2488_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2477_);
                    crate::leanh::lean_inc(v_postponed_2476_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2475_);
                    crate::leanh::lean_inc(v_mctx_2474_);
                    crate::leanh::lean_dec(v___x_2473_);
                    v___x_2479_ = crate::leanh::lean_box(0);
                    v_isShared_2480_ = v_isSharedCheck_2488_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2481_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once), _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
                if v_isShared_2480_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2479_, 1, v___x_2481_);
                    v___x_2483_ = v___x_2479_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2487_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_mctx_2474_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2487_, 1, v___x_2481_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2487_,
                        2,
                        v_zetaDeltaFVarIds_2475_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2487_, 3, v_postponed_2476_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2487_, 4, v_diag_2477_);
                    v___x_2483_ = v_reuseFailAlloc_2487_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2484_ = lean_st_ref_set(v___y_2455_, v___x_2483_);
                v___x_2485_ = crate::leanh::lean_box(0);
                v___x_2486_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2486_, 0, v___x_2485_);
                return v___x_2486_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___boxed(
    mut v_env_2494_: *mut crate::leanh::LeanObject,
    mut v___y_2495_: *mut crate::leanh::LeanObject,
    mut v___y_2496_: *mut crate::leanh::LeanObject,
    mut v___y_2497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2498_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(
        v_env_2494_,
        v___y_2495_,
        v___y_2496_,
    );
    crate::leanh::lean_dec(v___y_2496_);
    crate::leanh::lean_dec(v___y_2495_);
    return v_res_2498_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9(
    mut v_env_2499_: *mut crate::leanh::LeanObject,
    mut v___y_2500_: *mut crate::leanh::LeanObject,
    mut v___y_2501_: *mut crate::leanh::LeanObject,
    mut v___y_2502_: *mut crate::leanh::LeanObject,
    mut v___y_2503_: *mut crate::leanh::LeanObject,
    mut v___y_2504_: *mut crate::leanh::LeanObject,
    mut v___y_2505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2507_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(
        v_env_2499_,
        v___y_2503_,
        v___y_2505_,
    );
    return v___x_2507_;
}
pub unsafe fn l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___boxed(
    mut v_env_2508_: *mut crate::leanh::LeanObject,
    mut v___y_2509_: *mut crate::leanh::LeanObject,
    mut v___y_2510_: *mut crate::leanh::LeanObject,
    mut v___y_2511_: *mut crate::leanh::LeanObject,
    mut v___y_2512_: *mut crate::leanh::LeanObject,
    mut v___y_2513_: *mut crate::leanh::LeanObject,
    mut v___y_2514_: *mut crate::leanh::LeanObject,
    mut v___y_2515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2516_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9(
        v_env_2508_,
        v___y_2509_,
        v___y_2510_,
        v___y_2511_,
        v___y_2512_,
        v___y_2513_,
        v___y_2514_,
    );
    crate::leanh::lean_dec(v___y_2514_);
    crate::leanh::lean_dec_ref(v___y_2513_);
    crate::leanh::lean_dec(v___y_2512_);
    crate::leanh::lean_dec_ref(v___y_2511_);
    crate::leanh::lean_dec(v___y_2510_);
    crate::leanh::lean_dec_ref(v___y_2509_);
    return v_res_2516_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0(
    mut v_k_2517_: *mut crate::leanh::LeanObject,
    mut v___y_2518_: *mut crate::leanh::LeanObject,
    mut v___y_2519_: *mut crate::leanh::LeanObject,
    mut v_b_2520_: *mut crate::leanh::LeanObject,
    mut v_c_2521_: *mut crate::leanh::LeanObject,
    mut v___y_2522_: *mut crate::leanh::LeanObject,
    mut v___y_2523_: *mut crate::leanh::LeanObject,
    mut v___y_2524_: *mut crate::leanh::LeanObject,
    mut v___y_2525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_2525_);
    crate::leanh::lean_inc_ref(v___y_2524_);
    crate::leanh::lean_inc(v___y_2523_);
    crate::leanh::lean_inc_ref(v___y_2522_);
    crate::leanh::lean_inc(v___y_2519_);
    crate::leanh::lean_inc_ref(v___y_2518_);
    v___x_2527_ = crate::leanh::lean_apply_9(
        v_k_2517_,
        v_b_2520_,
        v_c_2521_,
        v___y_2518_,
        v___y_2519_,
        v___y_2522_,
        v___y_2523_,
        v___y_2524_,
        v___y_2525_,
        crate::leanh::lean_box(0),
    );
    return v___x_2527_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0___boxed(
    mut v_k_2528_: *mut crate::leanh::LeanObject,
    mut v___y_2529_: *mut crate::leanh::LeanObject,
    mut v___y_2530_: *mut crate::leanh::LeanObject,
    mut v_b_2531_: *mut crate::leanh::LeanObject,
    mut v_c_2532_: *mut crate::leanh::LeanObject,
    mut v___y_2533_: *mut crate::leanh::LeanObject,
    mut v___y_2534_: *mut crate::leanh::LeanObject,
    mut v___y_2535_: *mut crate::leanh::LeanObject,
    mut v___y_2536_: *mut crate::leanh::LeanObject,
    mut v___y_2537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2538_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0(v_k_2528_, v___y_2529_, v___y_2530_, v_b_2531_, v_c_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
    crate::leanh::lean_dec(v___y_2536_);
    crate::leanh::lean_dec_ref(v___y_2535_);
    crate::leanh::lean_dec(v___y_2534_);
    crate::leanh::lean_dec_ref(v___y_2533_);
    crate::leanh::lean_dec(v___y_2530_);
    crate::leanh::lean_dec_ref(v___y_2529_);
    return v_res_2538_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(
    mut v_type_2539_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_2540_: *mut crate::leanh::LeanObject,
    mut v_k_2541_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2542_: u8,
    mut v_whnfType_2543_: u8,
    mut v___y_2544_: *mut crate::leanh::LeanObject,
    mut v___y_2545_: *mut crate::leanh::LeanObject,
    mut v___y_2546_: *mut crate::leanh::LeanObject,
    mut v___y_2547_: *mut crate::leanh::LeanObject,
    mut v___y_2548_: *mut crate::leanh::LeanObject,
    mut v___y_2549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2556_: u8 = 0;
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2560_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_2545_);
                crate::leanh::lean_inc_ref(v___y_2544_);
                v___f_2551_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 3);
                crate::leanh::lean_closure_set(v___f_2551_, 0, v_k_2541_);
                crate::leanh::lean_closure_set(v___f_2551_, 1, v___y_2544_);
                crate::leanh::lean_closure_set(v___f_2551_, 2, v___y_2545_);
                v___x_2552_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    crate::leanh::lean_box(0),
                    v_type_2539_,
                    v_maxFVars_x3f_2540_,
                    v___f_2551_,
                    v_cleanupAnnotations_2542_,
                    v_whnfType_2543_,
                    v___y_2546_,
                    v___y_2547_,
                    v___y_2548_,
                    v___y_2549_,
                );
                if crate::leanh::lean_obj_tag(v___x_2552_) == 0 {
                    return v___x_2552_;
                } else {
                    v_a_2553_ = crate::leanh::lean_ctor_get(v___x_2552_, 0);
                    v_isSharedCheck_2560_ = (!crate::leanh::lean_is_exclusive(v___x_2552_)) as u8;
                    if v_isSharedCheck_2560_ == 0 {
                        v___x_2555_ = v___x_2552_;
                        v_isShared_2556_ = v_isSharedCheck_2560_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2553_);
                        crate::leanh::lean_dec(v___x_2552_);
                        v___x_2555_ = crate::leanh::lean_box(0);
                        v_isShared_2556_ = v_isSharedCheck_2560_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2556_ == 0 {
                    v___x_2558_ = v___x_2555_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2559_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2553_);
                    v___x_2558_ = v_reuseFailAlloc_2559_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2558_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg___boxed(
    mut v_type_2561_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_2562_: *mut crate::leanh::LeanObject,
    mut v_k_2563_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2564_: *mut crate::leanh::LeanObject,
    mut v_whnfType_2565_: *mut crate::leanh::LeanObject,
    mut v___y_2566_: *mut crate::leanh::LeanObject,
    mut v___y_2567_: *mut crate::leanh::LeanObject,
    mut v___y_2568_: *mut crate::leanh::LeanObject,
    mut v___y_2569_: *mut crate::leanh::LeanObject,
    mut v___y_2570_: *mut crate::leanh::LeanObject,
    mut v___y_2571_: *mut crate::leanh::LeanObject,
    mut v___y_2572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2573_: u8 = 0;
    let mut v_whnfType_boxed_2574_: u8 = 0;
    let mut v_res_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2573_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_2564_) as u8);
    v_whnfType_boxed_2574_ = (crate::leanh::lean_unbox(v_whnfType_2565_) as u8);
    v_res_2575_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(
            v_type_2561_,
            v_maxFVars_x3f_2562_,
            v_k_2563_,
            v_cleanupAnnotations_boxed_2573_,
            v_whnfType_boxed_2574_,
            v___y_2566_,
            v___y_2567_,
            v___y_2568_,
            v___y_2569_,
            v___y_2570_,
            v___y_2571_,
        );
    crate::leanh::lean_dec(v___y_2571_);
    crate::leanh::lean_dec_ref(v___y_2570_);
    crate::leanh::lean_dec(v___y_2569_);
    crate::leanh::lean_dec_ref(v___y_2568_);
    crate::leanh::lean_dec(v___y_2567_);
    crate::leanh::lean_dec_ref(v___y_2566_);
    return v_res_2575_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15(
    mut v_00_u03b1_2576_: *mut crate::leanh::LeanObject,
    mut v_type_2577_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_2578_: *mut crate::leanh::LeanObject,
    mut v_k_2579_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2580_: u8,
    mut v_whnfType_2581_: u8,
    mut v___y_2582_: *mut crate::leanh::LeanObject,
    mut v___y_2583_: *mut crate::leanh::LeanObject,
    mut v___y_2584_: *mut crate::leanh::LeanObject,
    mut v___y_2585_: *mut crate::leanh::LeanObject,
    mut v___y_2586_: *mut crate::leanh::LeanObject,
    mut v___y_2587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2589_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(
            v_type_2577_,
            v_maxFVars_x3f_2578_,
            v_k_2579_,
            v_cleanupAnnotations_2580_,
            v_whnfType_2581_,
            v___y_2582_,
            v___y_2583_,
            v___y_2584_,
            v___y_2585_,
            v___y_2586_,
            v___y_2587_,
        );
    return v___x_2589_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___boxed(
    mut v_00_u03b1_2590_: *mut crate::leanh::LeanObject,
    mut v_type_2591_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_2592_: *mut crate::leanh::LeanObject,
    mut v_k_2593_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_2594_: *mut crate::leanh::LeanObject,
    mut v_whnfType_2595_: *mut crate::leanh::LeanObject,
    mut v___y_2596_: *mut crate::leanh::LeanObject,
    mut v___y_2597_: *mut crate::leanh::LeanObject,
    mut v___y_2598_: *mut crate::leanh::LeanObject,
    mut v___y_2599_: *mut crate::leanh::LeanObject,
    mut v___y_2600_: *mut crate::leanh::LeanObject,
    mut v___y_2601_: *mut crate::leanh::LeanObject,
    mut v___y_2602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_2603_: u8 = 0;
    let mut v_whnfType_boxed_2604_: u8 = 0;
    let mut v_res_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_2603_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_2594_) as u8);
    v_whnfType_boxed_2604_ = (crate::leanh::lean_unbox(v_whnfType_2595_) as u8);
    v_res_2605_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15(
        v_00_u03b1_2590_,
        v_type_2591_,
        v_maxFVars_x3f_2592_,
        v_k_2593_,
        v_cleanupAnnotations_boxed_2603_,
        v_whnfType_boxed_2604_,
        v___y_2596_,
        v___y_2597_,
        v___y_2598_,
        v___y_2599_,
        v___y_2600_,
        v___y_2601_,
    );
    crate::leanh::lean_dec(v___y_2601_);
    crate::leanh::lean_dec_ref(v___y_2600_);
    crate::leanh::lean_dec(v___y_2599_);
    crate::leanh::lean_dec_ref(v___y_2598_);
    crate::leanh::lean_dec(v___y_2597_);
    crate::leanh::lean_dec_ref(v___y_2596_);
    return v_res_2605_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2606_ = crate::leanh::lean_box(1);
    v___x_2607_ = l_Lean_MessageData_ofFormat(v___x_2606_);
    return v___x_2607_;
}
pub unsafe fn _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2611_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__2;
    v___x_2612_ = l_Lean_MessageData_ofFormat(v___x_2611_);
    return v___x_2612_;
}
pub unsafe fn l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(
    mut v_x_2613_: *mut crate::leanh::LeanObject,
    mut v_x_2614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2619_: u8 = 0;
    let mut v_before_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2623_: u8 = 0;
    let mut v___x_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2636_: u8 = 0;
    let mut v_unused_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2638_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2614_) == 0 {
                    return v_x_2613_;
                } else {
                    v_head_2615_ = crate::leanh::lean_ctor_get(v_x_2614_, 0);
                    v_tail_2616_ = crate::leanh::lean_ctor_get(v_x_2614_, 1);
                    v_isSharedCheck_2638_ = (!crate::leanh::lean_is_exclusive(v_x_2614_)) as u8;
                    if v_isSharedCheck_2638_ == 0 {
                        v___x_2618_ = v_x_2614_;
                        v_isShared_2619_ = v_isSharedCheck_2638_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2616_);
                        crate::leanh::lean_inc(v_head_2615_);
                        crate::leanh::lean_dec(v_x_2614_);
                        v___x_2618_ = crate::leanh::lean_box(0);
                        v_isShared_2619_ = v_isSharedCheck_2638_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_before_2620_ = crate::leanh::lean_ctor_get(v_head_2615_, 0);
                v_isSharedCheck_2636_ = (!crate::leanh::lean_is_exclusive(v_head_2615_)) as u8;
                if v_isSharedCheck_2636_ == 0 {
                    v_unused_2637_ = crate::leanh::lean_ctor_get(v_head_2615_, 1);
                    crate::leanh::lean_dec(v_unused_2637_);
                    v___x_2622_ = v_head_2615_;
                    v_isShared_2623_ = v_isSharedCheck_2636_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_before_2620_);
                    crate::leanh::lean_dec(v_head_2615_);
                    v___x_2622_ = crate::leanh::lean_box(0);
                    v_isShared_2623_ = v_isSharedCheck_2636_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2624_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0);
                if v_isShared_2623_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2622_, 7);
                    crate::leanh::lean_ctor_set(v___x_2622_, 1, v___x_2624_);
                    crate::leanh::lean_ctor_set(v___x_2622_, 0, v_x_2613_);
                    v___x_2626_ = v___x_2622_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2635_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_x_2613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2635_, 1, v___x_2624_);
                    v___x_2626_ = v_reuseFailAlloc_2635_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2627_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__3);
                if v_isShared_2619_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2618_, 7);
                    crate::leanh::lean_ctor_set(v___x_2618_, 1, v___x_2627_);
                    crate::leanh::lean_ctor_set(v___x_2618_, 0, v___x_2626_);
                    v___x_2629_ = v___x_2618_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2634_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2634_, 0, v___x_2626_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2634_, 1, v___x_2627_);
                    v___x_2629_ = v_reuseFailAlloc_2634_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2630_ = l_Lean_MessageData_ofSyntax(v_before_2620_);
                v___x_2631_ = l_Lean_indentD(v___x_2630_);
                v___x_2632_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2632_, 0, v___x_2629_);
                crate::leanh::lean_ctor_set(v___x_2632_, 1, v___x_2631_);
                v_x_2613_ = v___x_2632_;
                v_x_2614_ = v_tail_2616_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(
    mut v_opts_2639_: *mut crate::leanh::LeanObject,
    mut v_opt_2640_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_name_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_name_2641_ = crate::leanh::lean_ctor_get(v_opt_2640_, 0);
    v_defValue_2642_ = crate::leanh::lean_ctor_get(v_opt_2640_, 1);
    v_map_2643_ = crate::leanh::lean_ctor_get(v_opts_2639_, 0);
    v___x_2644_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_2643_,
            v_name_2641_,
        );
    if crate::leanh::lean_obj_tag(v___x_2644_) == 0 {
        let mut v___x_2645_: u8 = 0;
        v___x_2645_ = (crate::leanh::lean_unbox(v_defValue_2642_) as u8);
        return v___x_2645_;
    } else {
        let mut v_val_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_2646_ = crate::leanh::lean_ctor_get(v___x_2644_, 0);
        crate::leanh::lean_inc(v_val_2646_);
        crate::leanh::lean_dec_ref_known(v___x_2644_, 1);
        if crate::leanh::lean_obj_tag(v_val_2646_) == 1 {
            let mut v_v_2647_: u8 = 0;
            v_v_2647_ = crate::leanh::lean_ctor_get_uint8(v_val_2646_, 0 as u32);
            crate::leanh::lean_dec_ref_known(v_val_2646_, 0);
            return v_v_2647_;
        } else {
            let mut v___x_2648_: u8 = 0;
            crate::leanh::lean_dec(v_val_2646_);
            v___x_2648_ = (crate::leanh::lean_unbox(v_defValue_2642_) as u8);
            return v___x_2648_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4___boxed(
    mut v_opts_2649_: *mut crate::leanh::LeanObject,
    mut v_opt_2650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2651_: u8 = 0;
    let mut v_r_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2651_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v_opts_2649_, v_opt_2650_);
    crate::leanh::lean_dec_ref(v_opt_2650_);
    crate::leanh::lean_dec_ref(v_opts_2649_);
    v_r_2652_ = crate::leanh::lean_box((v_res_2651_) as usize);
    return v_r_2652_;
}
pub unsafe fn _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2656_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__1;
    v___x_2657_ = l_Lean_MessageData_ofFormat(v___x_2656_);
    return v___x_2657_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(
    mut v_msgData_2658_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2659_: *mut crate::leanh::LeanObject,
    mut v___y_2660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: u8 = 0;
    let mut v___x_2665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_after_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2671_: u8 = 0;
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_msgData_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2683_: u8 = 0;
    let mut v_unused_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_2662_ = crate::leanh::lean_ctor_get(v___y_2660_, 2);
                v___x_2663_ = l_Lean_Elab_pp_macroStack;
                v___x_2664_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v_options_2662_, v___x_2663_);
                if v___x_2664_ == 0 {
                    crate::leanh::lean_dec(v_macroStack_2659_);
                    v___x_2665_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2665_, 0, v_msgData_2658_);
                    return v___x_2665_;
                } else {
                    if crate::leanh::lean_obj_tag(v_macroStack_2659_) == 0 {
                        v___x_2666_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2666_, 0, v_msgData_2658_);
                        return v___x_2666_;
                    } else {
                        v_head_2667_ = crate::leanh::lean_ctor_get(v_macroStack_2659_, 0);
                        crate::leanh::lean_inc(v_head_2667_);
                        v_after_2668_ = crate::leanh::lean_ctor_get(v_head_2667_, 1);
                        v_isSharedCheck_2683_ =
                            (!crate::leanh::lean_is_exclusive(v_head_2667_)) as u8;
                        if v_isSharedCheck_2683_ == 0 {
                            v_unused_2684_ = crate::leanh::lean_ctor_get(v_head_2667_, 0);
                            crate::leanh::lean_dec(v_unused_2684_);
                            v___x_2670_ = v_head_2667_;
                            v_isShared_2671_ = v_isSharedCheck_2683_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_after_2668_);
                            crate::leanh::lean_dec(v_head_2667_);
                            v___x_2670_ = crate::leanh::lean_box(0);
                            v_isShared_2671_ = v_isSharedCheck_2683_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2672_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0), core::ptr::addr_of_mut!(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0_once), _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5___closed__0);
                if v_isShared_2671_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2670_, 7);
                    crate::leanh::lean_ctor_set(v___x_2670_, 1, v___x_2672_);
                    crate::leanh::lean_ctor_set(v___x_2670_, 0, v_msgData_2658_);
                    v___x_2674_ = v___x_2670_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2682_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_msgData_2658_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2682_, 1, v___x_2672_);
                    v___x_2674_ = v_reuseFailAlloc_2682_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2675_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2_once), _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___closed__2);
                v___x_2676_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2676_, 0, v___x_2674_);
                crate::leanh::lean_ctor_set(v___x_2676_, 1, v___x_2675_);
                v___x_2677_ = l_Lean_MessageData_ofSyntax(v_after_2668_);
                v___x_2678_ = l_Lean_indentD(v___x_2677_);
                v_msgData_2679_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_msgData_2679_, 0, v___x_2676_);
                crate::leanh::lean_ctor_set(v_msgData_2679_, 1, v___x_2678_);
                v___x_2680_ = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__5(v_msgData_2679_, v_macroStack_2659_);
                v___x_2681_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2681_, 0, v___x_2680_);
                return v___x_2681_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg___boxed(
    mut v_msgData_2685_: *mut crate::leanh::LeanObject,
    mut v_macroStack_2686_: *mut crate::leanh::LeanObject,
    mut v___y_2687_: *mut crate::leanh::LeanObject,
    mut v___y_2688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2689_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_msgData_2685_, v_macroStack_2686_, v___y_2687_);
    crate::leanh::lean_dec_ref(v___y_2687_);
    return v_res_2689_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(
    mut v_msgData_2690_: *mut crate::leanh::LeanObject,
    mut v___y_2691_: *mut crate::leanh::LeanObject,
    mut v___y_2692_: *mut crate::leanh::LeanObject,
    mut v___y_2693_: *mut crate::leanh::LeanObject,
    mut v___y_2694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2696_ = lean_st_ref_get(v___y_2694_);
    v_env_2697_ = crate::leanh::lean_ctor_get(v___x_2696_, 0);
    crate::leanh::lean_inc_ref(v_env_2697_);
    crate::leanh::lean_dec(v___x_2696_);
    v___x_2698_ = lean_st_ref_get(v___y_2692_);
    v_mctx_2699_ = crate::leanh::lean_ctor_get(v___x_2698_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2699_);
    crate::leanh::lean_dec(v___x_2698_);
    v_lctx_2700_ = crate::leanh::lean_ctor_get(v___y_2691_, 2);
    v_options_2701_ = crate::leanh::lean_ctor_get(v___y_2693_, 2);
    crate::leanh::lean_inc_ref(v_options_2701_);
    crate::leanh::lean_inc_ref(v_lctx_2700_);
    v___x_2702_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2702_, 0, v_env_2697_);
    crate::leanh::lean_ctor_set(v___x_2702_, 1, v_mctx_2699_);
    crate::leanh::lean_ctor_set(v___x_2702_, 2, v_lctx_2700_);
    crate::leanh::lean_ctor_set(v___x_2702_, 3, v_options_2701_);
    v___x_2703_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2703_, 0, v___x_2702_);
    crate::leanh::lean_ctor_set(v___x_2703_, 1, v_msgData_2690_);
    v___x_2704_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2704_, 0, v___x_2703_);
    return v___x_2704_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0___boxed(
    mut v_msgData_2705_: *mut crate::leanh::LeanObject,
    mut v___y_2706_: *mut crate::leanh::LeanObject,
    mut v___y_2707_: *mut crate::leanh::LeanObject,
    mut v___y_2708_: *mut crate::leanh::LeanObject,
    mut v___y_2709_: *mut crate::leanh::LeanObject,
    mut v___y_2710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2711_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msgData_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
    crate::leanh::lean_dec(v___y_2709_);
    crate::leanh::lean_dec_ref(v___y_2708_);
    crate::leanh::lean_dec(v___y_2707_);
    crate::leanh::lean_dec_ref(v___y_2706_);
    return v_res_2711_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(
    mut v_msg_2712_: *mut crate::leanh::LeanObject,
    mut v___y_2713_: *mut crate::leanh::LeanObject,
    mut v___y_2714_: *mut crate::leanh::LeanObject,
    mut v___y_2715_: *mut crate::leanh::LeanObject,
    mut v___y_2716_: *mut crate::leanh::LeanObject,
    mut v___y_2717_: *mut crate::leanh::LeanObject,
    mut v___y_2718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_macroStack_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2729_: u8 = 0;
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2734_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2720_ = crate::leanh::lean_ctor_get(v___y_2717_, 5);
                v___x_2721_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_2712_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
                v_a_2722_ = crate::leanh::lean_ctor_get(v___x_2721_, 0);
                crate::leanh::lean_inc(v_a_2722_);
                crate::leanh::lean_dec_ref(v___x_2721_);
                v_macroStack_2723_ = crate::leanh::lean_ctor_get(v___y_2713_, 1);
                v___x_2724_ = l_Lean_Elab_getBetterRef(v_ref_2720_, v_macroStack_2723_);
                crate::leanh::lean_inc(v_macroStack_2723_);
                v___x_2725_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_a_2722_, v_macroStack_2723_, v___y_2717_);
                v_a_2726_ = crate::leanh::lean_ctor_get(v___x_2725_, 0);
                v_isSharedCheck_2734_ = (!crate::leanh::lean_is_exclusive(v___x_2725_)) as u8;
                if v_isSharedCheck_2734_ == 0 {
                    v___x_2728_ = v___x_2725_;
                    v_isShared_2729_ = v_isSharedCheck_2734_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2726_);
                    crate::leanh::lean_dec(v___x_2725_);
                    v___x_2728_ = crate::leanh::lean_box(0);
                    v_isShared_2729_ = v_isSharedCheck_2734_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2730_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2730_, 0, v___x_2724_);
                crate::leanh::lean_ctor_set(v___x_2730_, 1, v_a_2726_);
                if v_isShared_2729_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2728_, 1);
                    crate::leanh::lean_ctor_set(v___x_2728_, 0, v___x_2730_);
                    v___x_2732_ = v___x_2728_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2733_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2733_, 0, v___x_2730_);
                    v___x_2732_ = v_reuseFailAlloc_2733_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2732_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg___boxed(
    mut v_msg_2735_: *mut crate::leanh::LeanObject,
    mut v___y_2736_: *mut crate::leanh::LeanObject,
    mut v___y_2737_: *mut crate::leanh::LeanObject,
    mut v___y_2738_: *mut crate::leanh::LeanObject,
    mut v___y_2739_: *mut crate::leanh::LeanObject,
    mut v___y_2740_: *mut crate::leanh::LeanObject,
    mut v___y_2741_: *mut crate::leanh::LeanObject,
    mut v___y_2742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2743_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(
        v_msg_2735_,
        v___y_2736_,
        v___y_2737_,
        v___y_2738_,
        v___y_2739_,
        v___y_2740_,
        v___y_2741_,
    );
    crate::leanh::lean_dec(v___y_2741_);
    crate::leanh::lean_dec_ref(v___y_2740_);
    crate::leanh::lean_dec(v___y_2739_);
    crate::leanh::lean_dec_ref(v___y_2738_);
    crate::leanh::lean_dec(v___y_2737_);
    crate::leanh::lean_dec_ref(v___y_2736_);
    return v_res_2743_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__0;
    v___x_2746_ = l_Lean_stringToMessageData(v___x_2745_);
    return v___x_2746_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__2;
    v___x_2749_ = l_Lean_stringToMessageData(v___x_2748_);
    return v___x_2749_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4(
    mut v_as_2750_: *mut crate::leanh::LeanObject,
    mut v_sz_2751_: usize,
    mut v_i_2752_: usize,
    mut v_b_2753_: *mut crate::leanh::LeanObject,
    mut v___y_2754_: *mut crate::leanh::LeanObject,
    mut v___y_2755_: *mut crate::leanh::LeanObject,
    mut v___y_2756_: *mut crate::leanh::LeanObject,
    mut v___y_2757_: *mut crate::leanh::LeanObject,
    mut v___y_2758_: *mut crate::leanh::LeanObject,
    mut v___y_2759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: usize = 0;
    let mut v___x_2764_: usize = 0;
    let mut v___x_2766_: u8 = 0;
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: u8 = 0;
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v_a_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: u8 = 0;
    let mut v_declName_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2795_: u8 = 0;
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2799_: u8 = 0;
    let mut v_reuseFailAlloc_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2801_: u8 = 0;
    let mut v_unused_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2766_ = lean_usize_dec_lt(v_i_2752_, v_sz_2751_);
                if v___x_2766_ == 0 {
                    v___x_2767_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2767_, 0, v_b_2753_);
                    return v___x_2767_;
                } else {
                    v_array_2768_ = crate::leanh::lean_ctor_get(v_b_2753_, 0);
                    v_start_2769_ = crate::leanh::lean_ctor_get(v_b_2753_, 1);
                    v_stop_2770_ = crate::leanh::lean_ctor_get(v_b_2753_, 2);
                    v___x_2771_ = lean_nat_dec_lt(v_start_2769_, v_stop_2770_);
                    if v___x_2771_ == 0 {
                        v___x_2772_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2772_, 0, v_b_2753_);
                        return v___x_2772_;
                    } else {
                        crate::leanh::lean_inc(v_stop_2770_);
                        crate::leanh::lean_inc(v_start_2769_);
                        crate::leanh::lean_inc_ref(v_array_2768_);
                        v_isSharedCheck_2801_ = (!crate::leanh::lean_is_exclusive(v_b_2753_)) as u8;
                        if v_isSharedCheck_2801_ == 0 {
                            v_unused_2802_ = crate::leanh::lean_ctor_get(v_b_2753_, 2);
                            crate::leanh::lean_dec(v_unused_2802_);
                            v_unused_2803_ = crate::leanh::lean_ctor_get(v_b_2753_, 1);
                            crate::leanh::lean_dec(v_unused_2803_);
                            v_unused_2804_ = crate::leanh::lean_ctor_get(v_b_2753_, 0);
                            crate::leanh::lean_dec(v_unused_2804_);
                            v___x_2774_ = v_b_2753_;
                            v_isShared_2775_ = v_isSharedCheck_2801_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_b_2753_);
                            v___x_2774_ = crate::leanh::lean_box(0);
                            v_isShared_2775_ = v_isSharedCheck_2801_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2763_ = 1usize;
                v___x_2764_ = lean_usize_add(v_i_2752_, v___x_2763_);
                v_i_2752_ = v___x_2764_;
                v_b_2753_ = v_a_2762_;
                state = 0;
                continue;
            }
            2 => {
                v_a_2776_ = lean_array_uget_borrowed(v_as_2750_, v_i_2752_);
                v___x_2777_ = lean_array_fget(v_array_2768_, v_start_2769_);
                v___x_2778_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2779_ = lean_nat_add(v_start_2769_, v___x_2778_);
                crate::leanh::lean_dec(v_start_2769_);
                if v_isShared_2775_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2774_, 1, v___x_2779_);
                    v___x_2781_ = v___x_2774_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2800_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_array_2768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2800_, 1, v___x_2779_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2800_, 2, v_stop_2770_);
                    v___x_2781_ = v_reuseFailAlloc_2800_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2782_ = lean_array_get_size(v_a_2776_);
                v___x_2783_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2784_ = lean_nat_dec_eq(v___x_2782_, v___x_2783_);
                if v___x_2784_ == 0 {
                    crate::leanh::lean_dec(v___x_2777_);
                    v_a_2762_ = v___x_2781_;
                    state = 1;
                    continue;
                } else {
                    v_declName_2785_ = crate::leanh::lean_ctor_get(v___x_2777_, 3);
                    crate::leanh::lean_inc(v_declName_2785_);
                    crate::leanh::lean_dec(v___x_2777_);
                    v___x_2786_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__1);
                    v___x_2787_ = l_Lean_MessageData_ofName(v_declName_2785_);
                    v___x_2788_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2788_, 0, v___x_2786_);
                    crate::leanh::lean_ctor_set(v___x_2788_, 1, v___x_2787_);
                    v___x_2789_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___closed__3);
                    v___x_2790_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2790_, 0, v___x_2788_);
                    crate::leanh::lean_ctor_set(v___x_2790_, 1, v___x_2789_);
                    v___x_2791_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(
                        v___x_2790_,
                        v___y_2754_,
                        v___y_2755_,
                        v___y_2756_,
                        v___y_2757_,
                        v___y_2758_,
                        v___y_2759_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2791_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2791_, 1);
                        v_a_2762_ = v___x_2781_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2781_);
                        v_a_2792_ = crate::leanh::lean_ctor_get(v___x_2791_, 0);
                        v_isSharedCheck_2799_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2791_)) as u8;
                        if v_isSharedCheck_2799_ == 0 {
                            v___x_2794_ = v___x_2791_;
                            v_isShared_2795_ = v_isSharedCheck_2799_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2792_);
                            crate::leanh::lean_dec(v___x_2791_);
                            v___x_2794_ = crate::leanh::lean_box(0);
                            v_isShared_2795_ = v_isSharedCheck_2799_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_2795_ == 0 {
                    v___x_2797_ = v___x_2794_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2798_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
                    v___x_2797_ = v_reuseFailAlloc_2798_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2797_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4___boxed(
    mut v_as_2805_: *mut crate::leanh::LeanObject,
    mut v_sz_2806_: *mut crate::leanh::LeanObject,
    mut v_i_2807_: *mut crate::leanh::LeanObject,
    mut v_b_2808_: *mut crate::leanh::LeanObject,
    mut v___y_2809_: *mut crate::leanh::LeanObject,
    mut v___y_2810_: *mut crate::leanh::LeanObject,
    mut v___y_2811_: *mut crate::leanh::LeanObject,
    mut v___y_2812_: *mut crate::leanh::LeanObject,
    mut v___y_2813_: *mut crate::leanh::LeanObject,
    mut v___y_2814_: *mut crate::leanh::LeanObject,
    mut v___y_2815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2816_: usize = 0;
    let mut v_i_boxed_2817_: usize = 0;
    let mut v_res_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2816_ = crate::leanh::lean_unbox_usize(v_sz_2806_);
    crate::leanh::lean_dec(v_sz_2806_);
    v_i_boxed_2817_ = crate::leanh::lean_unbox_usize(v_i_2807_);
    crate::leanh::lean_dec(v_i_2807_);
    v_res_2818_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4(v_as_2805_, v_sz_boxed_2816_, v_i_boxed_2817_, v_b_2808_, v___y_2809_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
    crate::leanh::lean_dec(v___y_2814_);
    crate::leanh::lean_dec_ref(v___y_2813_);
    crate::leanh::lean_dec(v___y_2812_);
    crate::leanh::lean_dec_ref(v___y_2811_);
    crate::leanh::lean_dec(v___y_2810_);
    crate::leanh::lean_dec_ref(v___y_2809_);
    crate::leanh::lean_dec_ref(v_as_2805_);
    return v_res_2818_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(
    mut v_a_2819_: *mut crate::leanh::LeanObject,
    mut v_as_2820_: *mut crate::leanh::LeanObject,
    mut v_i_2821_: *mut crate::leanh::LeanObject,
    mut v_j_2822_: *mut crate::leanh::LeanObject,
    mut v_bs_2823_: *mut crate::leanh::LeanObject,
    mut v___y_2824_: *mut crate::leanh::LeanObject,
    mut v___y_2825_: *mut crate::leanh::LeanObject,
    mut v___y_2826_: *mut crate::leanh::LeanObject,
    mut v___y_2827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2830_: u8 = 0;
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2843_: u8 = 0;
    let mut v___x_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2847_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2829_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_2830_ = lean_nat_dec_eq(v_i_2821_, v_zero_2829_);
                if v_isZero_2830_ == 1 {
                    crate::leanh::lean_dec(v_j_2822_);
                    crate::leanh::lean_dec(v_i_2821_);
                    crate::leanh::lean_dec_ref(v_a_2819_);
                    v___x_2831_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2831_, 0, v_bs_2823_);
                    return v___x_2831_;
                } else {
                    v___x_2832_ = lean_array_fget_borrowed(v_as_2820_, v_j_2822_);
                    crate::leanh::lean_inc(v___x_2832_);
                    crate::leanh::lean_inc(v_j_2822_);
                    crate::leanh::lean_inc_ref(v_a_2819_);
                    v___x_2833_ = l_Lean_Elab_WF_varyingVarNames(
                        v_a_2819_,
                        v_j_2822_,
                        v___x_2832_,
                        v___y_2824_,
                        v___y_2825_,
                        v___y_2826_,
                        v___y_2827_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2833_) == 0 {
                        v_a_2834_ = crate::leanh::lean_ctor_get(v___x_2833_, 0);
                        crate::leanh::lean_inc(v_a_2834_);
                        crate::leanh::lean_dec_ref_known(v___x_2833_, 1);
                        v_one_2835_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_n_2836_ = lean_nat_sub(v_i_2821_, v_one_2835_);
                        crate::leanh::lean_dec(v_i_2821_);
                        v___x_2837_ = lean_nat_add(v_j_2822_, v_one_2835_);
                        crate::leanh::lean_dec(v_j_2822_);
                        v___x_2838_ = lean_array_push(v_bs_2823_, v_a_2834_);
                        v_i_2821_ = v_n_2836_;
                        v_j_2822_ = v___x_2837_;
                        v_bs_2823_ = v___x_2838_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_2823_);
                        crate::leanh::lean_dec(v_j_2822_);
                        crate::leanh::lean_dec(v_i_2821_);
                        crate::leanh::lean_dec_ref(v_a_2819_);
                        v_a_2840_ = crate::leanh::lean_ctor_get(v___x_2833_, 0);
                        v_isSharedCheck_2847_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2833_)) as u8;
                        if v_isSharedCheck_2847_ == 0 {
                            v___x_2842_ = v___x_2833_;
                            v_isShared_2843_ = v_isSharedCheck_2847_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2840_);
                            crate::leanh::lean_dec(v___x_2833_);
                            v___x_2842_ = crate::leanh::lean_box(0);
                            v_isShared_2843_ = v_isSharedCheck_2847_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2843_ == 0 {
                    v___x_2845_ = v___x_2842_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2846_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
                    v___x_2845_ = v_reuseFailAlloc_2846_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2845_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg___boxed(
    mut v_a_2848_: *mut crate::leanh::LeanObject,
    mut v_as_2849_: *mut crate::leanh::LeanObject,
    mut v_i_2850_: *mut crate::leanh::LeanObject,
    mut v_j_2851_: *mut crate::leanh::LeanObject,
    mut v_bs_2852_: *mut crate::leanh::LeanObject,
    mut v___y_2853_: *mut crate::leanh::LeanObject,
    mut v___y_2854_: *mut crate::leanh::LeanObject,
    mut v___y_2855_: *mut crate::leanh::LeanObject,
    mut v___y_2856_: *mut crate::leanh::LeanObject,
    mut v___y_2857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2858_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(
        v_a_2848_,
        v_as_2849_,
        v_i_2850_,
        v_j_2851_,
        v_bs_2852_,
        v___y_2853_,
        v___y_2854_,
        v___y_2855_,
        v___y_2856_,
    );
    crate::leanh::lean_dec(v___y_2856_);
    crate::leanh::lean_dec_ref(v___y_2855_);
    crate::leanh::lean_dec(v___y_2854_);
    crate::leanh::lean_dec_ref(v___y_2853_);
    crate::leanh::lean_dec_ref(v_as_2849_);
    return v_res_2858_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(
    mut v_as_2859_: *mut crate::leanh::LeanObject,
    mut v_sz_2860_: usize,
    mut v_i_2861_: usize,
    mut v_b_2862_: *mut crate::leanh::LeanObject,
    mut v___y_2863_: *mut crate::leanh::LeanObject,
    mut v___y_2864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2866_: u8 = 0;
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: usize = 0;
    let mut v___x_2872_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2866_ = lean_usize_dec_lt(v_i_2861_, v_sz_2860_);
                if v___x_2866_ == 0 {
                    v___x_2867_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2867_, 0, v_b_2862_);
                    return v___x_2867_;
                } else {
                    v_a_2868_ = lean_array_uget_borrowed(v_as_2859_, v_i_2861_);
                    v___x_2869_ =
                        l_Lean_Elab_addAsAxiom___redArg(v_a_2868_, v___y_2863_, v___y_2864_);
                    if crate::leanh::lean_obj_tag(v___x_2869_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2869_, 1);
                        v___x_2870_ = crate::leanh::lean_box(0);
                        v___x_2871_ = 1usize;
                        v___x_2872_ = lean_usize_add(v_i_2861_, v___x_2871_);
                        v_i_2861_ = v___x_2872_;
                        v_b_2862_ = v___x_2870_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2869_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg___boxed(
    mut v_as_2874_: *mut crate::leanh::LeanObject,
    mut v_sz_2875_: *mut crate::leanh::LeanObject,
    mut v_i_2876_: *mut crate::leanh::LeanObject,
    mut v_b_2877_: *mut crate::leanh::LeanObject,
    mut v___y_2878_: *mut crate::leanh::LeanObject,
    mut v___y_2879_: *mut crate::leanh::LeanObject,
    mut v___y_2880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2881_: usize = 0;
    let mut v_i_boxed_2882_: usize = 0;
    let mut v_res_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2881_ = crate::leanh::lean_unbox_usize(v_sz_2875_);
    crate::leanh::lean_dec(v_sz_2875_);
    v_i_boxed_2882_ = crate::leanh::lean_unbox_usize(v_i_2876_);
    crate::leanh::lean_dec(v_i_2876_);
    v_res_2883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_as_2874_, v_sz_boxed_2881_, v_i_boxed_2882_, v_b_2877_, v___y_2878_, v___y_2879_);
    crate::leanh::lean_dec(v___y_2879_);
    crate::leanh::lean_dec_ref(v___y_2878_);
    crate::leanh::lean_dec_ref(v_as_2874_);
    return v_res_2883_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(
    mut v_sz_2884_: usize,
    mut v_i_2885_: usize,
    mut v_bs_2886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2887_: u8 = 0;
    let mut v_v_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: usize = 0;
    let mut v___x_2893_: usize = 0;
    let mut v___x_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2887_ = lean_usize_dec_lt(v_i_2885_, v_sz_2884_);
                if v___x_2887_ == 0 {
                    return v_bs_2886_;
                } else {
                    v_v_2888_ = lean_array_uget_borrowed(v_bs_2886_, v_i_2885_);
                    v_declName_2889_ = crate::leanh::lean_ctor_get(v_v_2888_, 3);
                    crate::leanh::lean_inc(v_declName_2889_);
                    v___x_2890_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2891_ = lean_array_uset(v_bs_2886_, v_i_2885_, v___x_2890_);
                    v___x_2892_ = 1usize;
                    v___x_2893_ = lean_usize_add(v_i_2885_, v___x_2892_);
                    v___x_2894_ = lean_array_uset(v_bs_x27_2891_, v_i_2885_, v_declName_2889_);
                    v_i_2885_ = v___x_2893_;
                    v_bs_2886_ = v___x_2894_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5___boxed(
    mut v_sz_2896_: *mut crate::leanh::LeanObject,
    mut v_i_2897_: *mut crate::leanh::LeanObject,
    mut v_bs_2898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2899_: usize = 0;
    let mut v_i_boxed_2900_: usize = 0;
    let mut v_res_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2899_ = crate::leanh::lean_unbox_usize(v_sz_2896_);
    crate::leanh::lean_dec(v_sz_2896_);
    v_i_boxed_2900_ = crate::leanh::lean_unbox_usize(v_i_2897_);
    crate::leanh::lean_dec(v_i_2897_);
    v_res_2901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(v_sz_boxed_2899_, v_i_boxed_2900_, v_bs_2898_);
    return v_res_2901_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(
    mut v_a_2902_: *mut crate::leanh::LeanObject,
    mut v___x_2903_: *mut crate::leanh::LeanObject,
    mut v_sz_2904_: usize,
    mut v_i_2905_: usize,
    mut v_bs_2906_: *mut crate::leanh::LeanObject,
    mut v___y_2907_: *mut crate::leanh::LeanObject,
    mut v___y_2908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2910_: u8 = 0;
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_2914_: u8 = 0;
    let mut v_levelParams_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifiers_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binders_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSectionVars_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_termination_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2925_: u8 = 0;
    let mut v_sz_2926_: usize = 0;
    let mut v___x_2927_: usize = 0;
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: usize = 0;
    let mut v___x_2936_: usize = 0;
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2943_: u8 = 0;
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2947_: u8 = 0;
    let mut v_isSharedCheck_2948_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2910_ = lean_usize_dec_lt(v_i_2905_, v_sz_2904_);
                if v___x_2910_ == 0 {
                    crate::leanh::lean_dec(v___x_2903_);
                    crate::leanh::lean_dec_ref(v_a_2902_);
                    v___x_2911_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2911_, 0, v_bs_2906_);
                    return v___x_2911_;
                } else {
                    v_v_2912_ = lean_array_uget(v_bs_2906_, v_i_2905_);
                    v_ref_2913_ = crate::leanh::lean_ctor_get(v_v_2912_, 0);
                    v_kind_2914_ = crate::leanh::lean_ctor_get_uint8(
                        v_v_2912_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                    );
                    v_levelParams_2915_ = crate::leanh::lean_ctor_get(v_v_2912_, 1);
                    v_modifiers_2916_ = crate::leanh::lean_ctor_get(v_v_2912_, 2);
                    v_declName_2917_ = crate::leanh::lean_ctor_get(v_v_2912_, 3);
                    v_binders_2918_ = crate::leanh::lean_ctor_get(v_v_2912_, 4);
                    v_numSectionVars_2919_ = crate::leanh::lean_ctor_get(v_v_2912_, 5);
                    v_type_2920_ = crate::leanh::lean_ctor_get(v_v_2912_, 6);
                    v_value_2921_ = crate::leanh::lean_ctor_get(v_v_2912_, 7);
                    v_termination_2922_ = crate::leanh::lean_ctor_get(v_v_2912_, 8);
                    v_isSharedCheck_2948_ = (!crate::leanh::lean_is_exclusive(v_v_2912_)) as u8;
                    if v_isSharedCheck_2948_ == 0 {
                        v___x_2924_ = v_v_2912_;
                        v_isShared_2925_ = v_isSharedCheck_2948_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_termination_2922_);
                        crate::leanh::lean_inc(v_value_2921_);
                        crate::leanh::lean_inc(v_type_2920_);
                        crate::leanh::lean_inc(v_numSectionVars_2919_);
                        crate::leanh::lean_inc(v_binders_2918_);
                        crate::leanh::lean_inc(v_declName_2917_);
                        crate::leanh::lean_inc(v_modifiers_2916_);
                        crate::leanh::lean_inc(v_levelParams_2915_);
                        crate::leanh::lean_inc(v_ref_2913_);
                        crate::leanh::lean_dec(v_v_2912_);
                        v___x_2924_ = crate::leanh::lean_box(0);
                        v_isShared_2925_ = v_isSharedCheck_2948_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_2926_ = lean_array_size(v_a_2902_);
                v___x_2927_ = 0usize;
                crate::leanh::lean_inc_ref(v_a_2902_);
                v___x_2928_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(v_sz_2926_, v___x_2927_, v_a_2902_);
                crate::leanh::lean_inc(v___x_2903_);
                v___x_2929_ = l_Lean_Meta_unfoldIfArgIsAppOf(
                    v___x_2928_,
                    v___x_2903_,
                    v_value_2921_,
                    v___y_2907_,
                    v___y_2908_,
                );
                if crate::leanh::lean_obj_tag(v___x_2929_) == 0 {
                    v_a_2930_ = crate::leanh::lean_ctor_get(v___x_2929_, 0);
                    crate::leanh::lean_inc(v_a_2930_);
                    crate::leanh::lean_dec_ref_known(v___x_2929_, 1);
                    v___x_2931_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2932_ = lean_array_uset(v_bs_2906_, v_i_2905_, v___x_2931_);
                    if v_isShared_2925_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2924_, 7, v_a_2930_);
                        v___x_2934_ = v___x_2924_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2939_ = crate::leanh::lean_alloc_ctor(0, 9, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_ref_2913_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2939_, 1, v_levelParams_2915_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2939_, 2, v_modifiers_2916_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2939_, 3, v_declName_2917_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2939_, 4, v_binders_2918_);
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_2939_,
                            5,
                            v_numSectionVars_2919_,
                        );
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2939_, 6, v_type_2920_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2939_, 7, v_a_2930_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2939_, 8, v_termination_2922_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_2939_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                            v_kind_2914_,
                        );
                        v___x_2934_ = v_reuseFailAlloc_2939_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2924_);
                    crate::leanh::lean_dec_ref(v_termination_2922_);
                    crate::leanh::lean_dec_ref(v_type_2920_);
                    crate::leanh::lean_dec(v_numSectionVars_2919_);
                    crate::leanh::lean_dec(v_binders_2918_);
                    crate::leanh::lean_dec(v_declName_2917_);
                    crate::leanh::lean_dec_ref(v_modifiers_2916_);
                    crate::leanh::lean_dec(v_levelParams_2915_);
                    crate::leanh::lean_dec(v_ref_2913_);
                    crate::leanh::lean_dec_ref(v_bs_2906_);
                    crate::leanh::lean_dec(v___x_2903_);
                    crate::leanh::lean_dec_ref(v_a_2902_);
                    v_a_2940_ = crate::leanh::lean_ctor_get(v___x_2929_, 0);
                    v_isSharedCheck_2947_ = (!crate::leanh::lean_is_exclusive(v___x_2929_)) as u8;
                    if v_isSharedCheck_2947_ == 0 {
                        v___x_2942_ = v___x_2929_;
                        v_isShared_2943_ = v_isSharedCheck_2947_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2940_);
                        crate::leanh::lean_dec(v___x_2929_);
                        v___x_2942_ = crate::leanh::lean_box(0);
                        v_isShared_2943_ = v_isSharedCheck_2947_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2935_ = 1usize;
                v___x_2936_ = lean_usize_add(v_i_2905_, v___x_2935_);
                v___x_2937_ = lean_array_uset(v_bs_x27_2932_, v_i_2905_, v___x_2934_);
                v_i_2905_ = v___x_2936_;
                v_bs_2906_ = v___x_2937_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_2943_ == 0 {
                    v___x_2945_ = v___x_2942_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2946_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2940_);
                    v___x_2945_ = v_reuseFailAlloc_2946_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2945_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg___boxed(
    mut v_a_2949_: *mut crate::leanh::LeanObject,
    mut v___x_2950_: *mut crate::leanh::LeanObject,
    mut v_sz_2951_: *mut crate::leanh::LeanObject,
    mut v_i_2952_: *mut crate::leanh::LeanObject,
    mut v_bs_2953_: *mut crate::leanh::LeanObject,
    mut v___y_2954_: *mut crate::leanh::LeanObject,
    mut v___y_2955_: *mut crate::leanh::LeanObject,
    mut v___y_2956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2957_: usize = 0;
    let mut v_i_boxed_2958_: usize = 0;
    let mut v_res_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2957_ = crate::leanh::lean_unbox_usize(v_sz_2951_);
    crate::leanh::lean_dec(v_sz_2951_);
    v_i_boxed_2958_ = crate::leanh::lean_unbox_usize(v_i_2952_);
    crate::leanh::lean_dec(v_i_2952_);
    v_res_2959_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(v_a_2949_, v___x_2950_, v_sz_boxed_2957_, v_i_boxed_2958_, v_bs_2953_, v___y_2954_, v___y_2955_);
    crate::leanh::lean_dec(v___y_2955_);
    crate::leanh::lean_dec_ref(v___y_2954_);
    return v_res_2959_;
}
pub unsafe fn l_Lean_Elab_wfRecursion___lam__0(
    mut v_a_2960_: *mut crate::leanh::LeanObject,
    mut v_sz_2961_: usize,
    mut v___x_2962_: usize,
    mut v___x_2963_: *mut crate::leanh::LeanObject,
    mut v___x_2964_: *mut crate::leanh::LeanObject,
    mut v___y_2965_: *mut crate::leanh::LeanObject,
    mut v___y_2966_: *mut crate::leanh::LeanObject,
    mut v___y_2967_: *mut crate::leanh::LeanObject,
    mut v___y_2968_: *mut crate::leanh::LeanObject,
    mut v___y_2969_: *mut crate::leanh::LeanObject,
    mut v___y_2970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2981_: usize = 0;
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSectionVars_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2991_: u8 = 0;
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2997_: u8 = 0;
    let mut v_a_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3001_: u8 = 0;
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3005_: u8 = 0;
    let mut v_a_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3009_: u8 = 0;
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3013_: u8 = 0;
    let mut v_a_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3017_: u8 = 0;
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3021_: u8 = 0;
    let mut v_a_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3025_: u8 = 0;
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3029_: u8 = 0;
    let mut v_a_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3033_: u8 = 0;
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3037_: u8 = 0;
    let mut v_a_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3041_: u8 = 0;
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3045_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2972_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_a_2960_, v_sz_2961_, v___x_2962_, v___x_2963_, v___y_2969_, v___y_2970_);
                if crate::leanh::lean_obj_tag(v___x_2972_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2972_, 1);
                    crate::leanh::lean_inc_ref(v_a_2960_);
                    v___x_2973_ = l_Lean_Elab_getFixedParamPerms(
                        v_a_2960_,
                        v___y_2967_,
                        v___y_2968_,
                        v___y_2969_,
                        v___y_2970_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2973_) == 0 {
                        v_a_2974_ = crate::leanh::lean_ctor_get(v___x_2973_, 0);
                        crate::leanh::lean_inc_n(v_a_2974_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_2973_, 1);
                        v___x_2975_ = lean_array_get_size(v_a_2960_);
                        v___x_2976_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2977_ = lean_mk_empty_array_with_capacity(v___x_2975_);
                        v___x_2978_ =
                            l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(
                                v_a_2974_,
                                v_a_2960_,
                                v___x_2975_,
                                v___x_2976_,
                                v___x_2977_,
                                v___y_2967_,
                                v___y_2968_,
                                v___y_2969_,
                                v___y_2970_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_2978_) == 0 {
                            v_a_2979_ = crate::leanh::lean_ctor_get(v___x_2978_, 0);
                            crate::leanh::lean_inc(v_a_2979_);
                            crate::leanh::lean_dec_ref_known(v___x_2978_, 1);
                            crate::leanh::lean_inc_ref(v_a_2960_);
                            v___x_2980_ =
                                l_Array_toSubarray___redArg(v_a_2960_, v___x_2976_, v___x_2975_);
                            v_sz_2981_ = lean_array_size(v_a_2979_);
                            v___x_2982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__4(v_a_2979_, v_sz_2981_, v___x_2962_, v___x_2980_, v___y_2965_, v___y_2966_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
                            if crate::leanh::lean_obj_tag(v___x_2982_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_2982_, 1);
                                v___x_2983_ =
                                    lean_array_get_borrowed(v___x_2964_, v_a_2960_, v___x_2976_);
                                v_numSectionVars_2984_ =
                                    crate::leanh::lean_ctor_get(v___x_2983_, 5);
                                crate::leanh::lean_inc(v_numSectionVars_2984_);
                                crate::leanh::lean_inc_ref(v_a_2960_);
                                v___x_2985_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(v_a_2960_, v_numSectionVars_2984_, v_sz_2961_, v___x_2962_, v_a_2960_, v___y_2969_, v___y_2970_);
                                if crate::leanh::lean_obj_tag(v___x_2985_) == 0 {
                                    v_a_2986_ = crate::leanh::lean_ctor_get(v___x_2985_, 0);
                                    crate::leanh::lean_inc(v_a_2986_);
                                    crate::leanh::lean_dec_ref_known(v___x_2985_, 1);
                                    crate::leanh::lean_inc(v_a_2979_);
                                    crate::leanh::lean_inc(v_a_2974_);
                                    v___x_2987_ = l_Lean_Elab_WF_packMutual(
                                        v_a_2974_,
                                        v_a_2979_,
                                        v_a_2986_,
                                        v___y_2967_,
                                        v___y_2968_,
                                        v___y_2969_,
                                        v___y_2970_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2987_) == 0 {
                                        v_a_2988_ = crate::leanh::lean_ctor_get(v___x_2987_, 0);
                                        v_isSharedCheck_2997_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2987_)) as u8;
                                        if v_isSharedCheck_2997_ == 0 {
                                            v___x_2990_ = v___x_2987_;
                                            v_isShared_2991_ = v_isSharedCheck_2997_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2988_);
                                            crate::leanh::lean_dec(v___x_2987_);
                                            v___x_2990_ = crate::leanh::lean_box(0);
                                            v_isShared_2991_ = v_isSharedCheck_2997_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_2979_);
                                        crate::leanh::lean_dec(v_a_2974_);
                                        v_a_2998_ = crate::leanh::lean_ctor_get(v___x_2987_, 0);
                                        v_isSharedCheck_3005_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2987_)) as u8;
                                        if v_isSharedCheck_3005_ == 0 {
                                            v___x_3000_ = v___x_2987_;
                                            v_isShared_3001_ = v_isSharedCheck_3005_;
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2998_);
                                            crate::leanh::lean_dec(v___x_2987_);
                                            v___x_3000_ = crate::leanh::lean_box(0);
                                            v_isShared_3001_ = v_isSharedCheck_3005_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_2979_);
                                    crate::leanh::lean_dec(v_a_2974_);
                                    v_a_3006_ = crate::leanh::lean_ctor_get(v___x_2985_, 0);
                                    v_isSharedCheck_3013_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2985_)) as u8;
                                    if v_isSharedCheck_3013_ == 0 {
                                        v___x_3008_ = v___x_2985_;
                                        v_isShared_3009_ = v_isSharedCheck_3013_;
                                        state = 5;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3006_);
                                        crate::leanh::lean_dec(v___x_2985_);
                                        v___x_3008_ = crate::leanh::lean_box(0);
                                        v_isShared_3009_ = v_isSharedCheck_3013_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2979_);
                                crate::leanh::lean_dec(v_a_2974_);
                                crate::leanh::lean_dec_ref(v_a_2960_);
                                v_a_3014_ = crate::leanh::lean_ctor_get(v___x_2982_, 0);
                                v_isSharedCheck_3021_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2982_)) as u8;
                                if v_isSharedCheck_3021_ == 0 {
                                    v___x_3016_ = v___x_2982_;
                                    v_isShared_3017_ = v_isSharedCheck_3021_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3014_);
                                    crate::leanh::lean_dec(v___x_2982_);
                                    v___x_3016_ = crate::leanh::lean_box(0);
                                    v_isShared_3017_ = v_isSharedCheck_3021_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2974_);
                            crate::leanh::lean_dec_ref(v_a_2960_);
                            v_a_3022_ = crate::leanh::lean_ctor_get(v___x_2978_, 0);
                            v_isSharedCheck_3029_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2978_)) as u8;
                            if v_isSharedCheck_3029_ == 0 {
                                v___x_3024_ = v___x_2978_;
                                v_isShared_3025_ = v_isSharedCheck_3029_;
                                state = 9;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3022_);
                                crate::leanh::lean_dec(v___x_2978_);
                                v___x_3024_ = crate::leanh::lean_box(0);
                                v_isShared_3025_ = v_isSharedCheck_3029_;
                                state = 9;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_a_2960_);
                        v_a_3030_ = crate::leanh::lean_ctor_get(v___x_2973_, 0);
                        v_isSharedCheck_3037_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2973_)) as u8;
                        if v_isSharedCheck_3037_ == 0 {
                            v___x_3032_ = v___x_2973_;
                            v_isShared_3033_ = v_isSharedCheck_3037_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3030_);
                            crate::leanh::lean_dec(v___x_2973_);
                            v___x_3032_ = crate::leanh::lean_box(0);
                            v_isShared_3033_ = v_isSharedCheck_3037_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_2960_);
                    v_a_3038_ = crate::leanh::lean_ctor_get(v___x_2972_, 0);
                    v_isSharedCheck_3045_ = (!crate::leanh::lean_is_exclusive(v___x_2972_)) as u8;
                    if v_isSharedCheck_3045_ == 0 {
                        v___x_3040_ = v___x_2972_;
                        v_isShared_3041_ = v_isSharedCheck_3045_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3038_);
                        crate::leanh::lean_dec(v___x_2972_);
                        v___x_3040_ = crate::leanh::lean_box(0);
                        v_isShared_3041_ = v_isSharedCheck_3045_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2992_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2992_, 0, v_a_2979_);
                crate::leanh::lean_ctor_set(v___x_2992_, 1, v_a_2988_);
                v___x_2993_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2993_, 0, v_a_2974_);
                crate::leanh::lean_ctor_set(v___x_2993_, 1, v___x_2992_);
                if v_isShared_2991_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2990_, 0, v___x_2993_);
                    v___x_2995_ = v___x_2990_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2996_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2996_, 0, v___x_2993_);
                    v___x_2995_ = v_reuseFailAlloc_2996_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2995_;
            }
            3 => {
                if v_isShared_3001_ == 0 {
                    v___x_3003_ = v___x_3000_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3004_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
                    v___x_3003_ = v_reuseFailAlloc_3004_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3003_;
            }
            5 => {
                if v_isShared_3009_ == 0 {
                    v___x_3011_ = v___x_3008_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3012_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
                    v___x_3011_ = v_reuseFailAlloc_3012_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3011_;
            }
            7 => {
                if v_isShared_3017_ == 0 {
                    v___x_3019_ = v___x_3016_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3020_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
                    v___x_3019_ = v_reuseFailAlloc_3020_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3019_;
            }
            9 => {
                if v_isShared_3025_ == 0 {
                    v___x_3027_ = v___x_3024_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3028_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
                    v___x_3027_ = v_reuseFailAlloc_3028_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3027_;
            }
            11 => {
                if v_isShared_3033_ == 0 {
                    v___x_3035_ = v___x_3032_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3036_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
                    v___x_3035_ = v_reuseFailAlloc_3036_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3035_;
            }
            13 => {
                if v_isShared_3041_ == 0 {
                    v___x_3043_ = v___x_3040_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3044_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
                    v___x_3043_ = v_reuseFailAlloc_3044_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3043_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_wfRecursion___lam__0___boxed(
    mut v_a_3046_: *mut crate::leanh::LeanObject,
    mut v_sz_3047_: *mut crate::leanh::LeanObject,
    mut v___x_3048_: *mut crate::leanh::LeanObject,
    mut v___x_3049_: *mut crate::leanh::LeanObject,
    mut v___x_3050_: *mut crate::leanh::LeanObject,
    mut v___y_3051_: *mut crate::leanh::LeanObject,
    mut v___y_3052_: *mut crate::leanh::LeanObject,
    mut v___y_3053_: *mut crate::leanh::LeanObject,
    mut v___y_3054_: *mut crate::leanh::LeanObject,
    mut v___y_3055_: *mut crate::leanh::LeanObject,
    mut v___y_3056_: *mut crate::leanh::LeanObject,
    mut v___y_3057_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3058_: usize = 0;
    let mut v___x_46799__boxed_3059_: usize = 0;
    let mut v_res_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3058_ = crate::leanh::lean_unbox_usize(v_sz_3047_);
    crate::leanh::lean_dec(v_sz_3047_);
    v___x_46799__boxed_3059_ = crate::leanh::lean_unbox_usize(v___x_3048_);
    crate::leanh::lean_dec(v___x_3048_);
    v_res_3060_ = l_Lean_Elab_wfRecursion___lam__0(
        v_a_3046_,
        v_sz_boxed_3058_,
        v___x_46799__boxed_3059_,
        v___x_3049_,
        v___x_3050_,
        v___y_3051_,
        v___y_3052_,
        v___y_3053_,
        v___y_3054_,
        v___y_3055_,
        v___y_3056_,
    );
    crate::leanh::lean_dec(v___y_3056_);
    crate::leanh::lean_dec_ref(v___y_3055_);
    crate::leanh::lean_dec(v___y_3054_);
    crate::leanh::lean_dec_ref(v___y_3053_);
    crate::leanh::lean_dec(v___y_3052_);
    crate::leanh::lean_dec_ref(v___y_3051_);
    crate::leanh::lean_dec_ref(v___x_3050_);
    return v_res_3060_;
}
pub unsafe fn l_Lean_Elab_wfRecursion___lam__1(
    mut v___x_3064_: *mut crate::leanh::LeanObject,
    mut v___y_3065_: *mut crate::leanh::LeanObject,
    mut v___y_3066_: *mut crate::leanh::LeanObject,
    mut v___y_3067_: *mut crate::leanh::LeanObject,
    mut v___y_3068_: *mut crate::leanh::LeanObject,
    mut v___y_3069_: *mut crate::leanh::LeanObject,
    mut v___y_3070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3073_: u8 = 0;
    v_options_3072_ = crate::leanh::lean_ctor_get(v___y_3069_, 2);
    v_hasTrace_3073_ = crate::leanh::lean_ctor_get_uint8(
        v_options_3072_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
    );
    if v_hasTrace_3073_ == 0 {
        let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_3064_);
        v___x_3074_ = crate::leanh::lean_box((v_hasTrace_3073_) as usize);
        v___x_3075_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3075_, 0, v___x_3074_);
        return v___x_3075_;
    } else {
        let mut v_inheritedTraceOptions_3076_: *mut crate::leanh::LeanObject =
            core::ptr::null_mut();
        let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3079_: u8 = 0;
        let mut v___x_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_inheritedTraceOptions_3076_ = crate::leanh::lean_ctor_get(v___y_3069_, 13);
        v___x_3077_ = l_Lean_Elab_wfRecursion___lam__1___closed__1;
        v___x_3078_ = l_Lean_Name_append(v___x_3077_, v___x_3064_);
        v___x_3079_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
            v_inheritedTraceOptions_3076_,
            v_options_3072_,
            v___x_3078_,
        );
        crate::leanh::lean_dec(v___x_3078_);
        v___x_3080_ = crate::leanh::lean_box((v___x_3079_) as usize);
        v___x_3081_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3081_, 0, v___x_3080_);
        return v___x_3081_;
    }
}
pub unsafe fn l_Lean_Elab_wfRecursion___lam__1___boxed(
    mut v___x_3082_: *mut crate::leanh::LeanObject,
    mut v___y_3083_: *mut crate::leanh::LeanObject,
    mut v___y_3084_: *mut crate::leanh::LeanObject,
    mut v___y_3085_: *mut crate::leanh::LeanObject,
    mut v___y_3086_: *mut crate::leanh::LeanObject,
    mut v___y_3087_: *mut crate::leanh::LeanObject,
    mut v___y_3088_: *mut crate::leanh::LeanObject,
    mut v___y_3089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3090_ = l_Lean_Elab_wfRecursion___lam__1(
        v___x_3082_,
        v___y_3083_,
        v___y_3084_,
        v___y_3085_,
        v___y_3086_,
        v___y_3087_,
        v___y_3088_,
    );
    crate::leanh::lean_dec(v___y_3088_);
    crate::leanh::lean_dec_ref(v___y_3087_);
    crate::leanh::lean_dec(v___y_3086_);
    crate::leanh::lean_dec_ref(v___y_3085_);
    crate::leanh::lean_dec(v___y_3084_);
    crate::leanh::lean_dec_ref(v___y_3083_);
    return v_res_3090_;
}
pub unsafe fn l_Lean_Elab_wfRecursion___lam__2(
    mut v_snd_3091_: *mut crate::leanh::LeanObject,
    mut v___y_3092_: *mut crate::leanh::LeanObject,
    mut v___y_3093_: *mut crate::leanh::LeanObject,
    mut v___y_3094_: *mut crate::leanh::LeanObject,
    mut v___y_3095_: *mut crate::leanh::LeanObject,
    mut v___y_3096_: *mut crate::leanh::LeanObject,
    mut v___y_3097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3101_: u8 = 0;
    let mut v_levelParams_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifiers_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binders_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSectionVars_3106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_termination_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3112_: u8 = 0;
    let mut v___x_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3117_: u8 = 0;
    let mut v_expr_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3126_: u8 = 0;
    let mut v_a_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3130_: u8 = 0;
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3134_: u8 = 0;
    let mut v_isSharedCheck_3135_: u8 = 0;
    let mut v_a_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3139_: u8 = 0;
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3143_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3099_ =
                    l_Lean_Elab_addAsAxiom___redArg(v_snd_3091_, v___y_3096_, v___y_3097_);
                if crate::leanh::lean_obj_tag(v___x_3099_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3099_, 1);
                    v_ref_3100_ = crate::leanh::lean_ctor_get(v_snd_3091_, 0);
                    v_kind_3101_ = crate::leanh::lean_ctor_get_uint8(
                        v_snd_3091_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                    );
                    v_levelParams_3102_ = crate::leanh::lean_ctor_get(v_snd_3091_, 1);
                    v_modifiers_3103_ = crate::leanh::lean_ctor_get(v_snd_3091_, 2);
                    v_declName_3104_ = crate::leanh::lean_ctor_get(v_snd_3091_, 3);
                    v_binders_3105_ = crate::leanh::lean_ctor_get(v_snd_3091_, 4);
                    v_numSectionVars_3106_ = crate::leanh::lean_ctor_get(v_snd_3091_, 5);
                    v_type_3107_ = crate::leanh::lean_ctor_get(v_snd_3091_, 6);
                    v_value_3108_ = crate::leanh::lean_ctor_get(v_snd_3091_, 7);
                    v_termination_3109_ = crate::leanh::lean_ctor_get(v_snd_3091_, 8);
                    v_isSharedCheck_3135_ = (!crate::leanh::lean_is_exclusive(v_snd_3091_)) as u8;
                    if v_isSharedCheck_3135_ == 0 {
                        v___x_3111_ = v_snd_3091_;
                        v_isShared_3112_ = v_isSharedCheck_3135_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_termination_3109_);
                        crate::leanh::lean_inc(v_value_3108_);
                        crate::leanh::lean_inc(v_type_3107_);
                        crate::leanh::lean_inc(v_numSectionVars_3106_);
                        crate::leanh::lean_inc(v_binders_3105_);
                        crate::leanh::lean_inc(v_declName_3104_);
                        crate::leanh::lean_inc(v_modifiers_3103_);
                        crate::leanh::lean_inc(v_levelParams_3102_);
                        crate::leanh::lean_inc(v_ref_3100_);
                        crate::leanh::lean_dec(v_snd_3091_);
                        v___x_3111_ = crate::leanh::lean_box(0);
                        v_isShared_3112_ = v_isSharedCheck_3135_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_snd_3091_);
                    v_a_3136_ = crate::leanh::lean_ctor_get(v___x_3099_, 0);
                    v_isSharedCheck_3143_ = (!crate::leanh::lean_is_exclusive(v___x_3099_)) as u8;
                    if v_isSharedCheck_3143_ == 0 {
                        v___x_3138_ = v___x_3099_;
                        v_isShared_3139_ = v_isSharedCheck_3143_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3136_);
                        crate::leanh::lean_dec(v___x_3099_);
                        v___x_3138_ = crate::leanh::lean_box(0);
                        v_isShared_3139_ = v_isSharedCheck_3143_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3113_ = l_Lean_Elab_WF_preprocess(
                    v_value_3108_,
                    v___y_3094_,
                    v___y_3095_,
                    v___y_3096_,
                    v___y_3097_,
                );
                if crate::leanh::lean_obj_tag(v___x_3113_) == 0 {
                    v_a_3114_ = crate::leanh::lean_ctor_get(v___x_3113_, 0);
                    v_isSharedCheck_3126_ = (!crate::leanh::lean_is_exclusive(v___x_3113_)) as u8;
                    if v_isSharedCheck_3126_ == 0 {
                        v___x_3116_ = v___x_3113_;
                        v_isShared_3117_ = v_isSharedCheck_3126_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3114_);
                        crate::leanh::lean_dec(v___x_3113_);
                        v___x_3116_ = crate::leanh::lean_box(0);
                        v_isShared_3117_ = v_isSharedCheck_3126_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3111_);
                    crate::leanh::lean_dec_ref(v_termination_3109_);
                    crate::leanh::lean_dec_ref(v_type_3107_);
                    crate::leanh::lean_dec(v_numSectionVars_3106_);
                    crate::leanh::lean_dec(v_binders_3105_);
                    crate::leanh::lean_dec(v_declName_3104_);
                    crate::leanh::lean_dec_ref(v_modifiers_3103_);
                    crate::leanh::lean_dec(v_levelParams_3102_);
                    crate::leanh::lean_dec(v_ref_3100_);
                    v_a_3127_ = crate::leanh::lean_ctor_get(v___x_3113_, 0);
                    v_isSharedCheck_3134_ = (!crate::leanh::lean_is_exclusive(v___x_3113_)) as u8;
                    if v_isSharedCheck_3134_ == 0 {
                        v___x_3129_ = v___x_3113_;
                        v_isShared_3130_ = v_isSharedCheck_3134_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3127_);
                        crate::leanh::lean_dec(v___x_3113_);
                        v___x_3129_ = crate::leanh::lean_box(0);
                        v_isShared_3130_ = v_isSharedCheck_3134_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                v_expr_3118_ = crate::leanh::lean_ctor_get(v_a_3114_, 0);
                crate::leanh::lean_inc_ref(v_expr_3118_);
                if v_isShared_3112_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3111_, 7, v_expr_3118_);
                    v___x_3120_ = v___x_3111_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3125_ = crate::leanh::lean_alloc_ctor(0, 9, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_ref_3100_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 1, v_levelParams_3102_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 2, v_modifiers_3103_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 3, v_declName_3104_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 4, v_binders_3105_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 5, v_numSectionVars_3106_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 6, v_type_3107_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 7, v_expr_3118_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 8, v_termination_3109_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3125_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_kind_3101_,
                    );
                    v___x_3120_ = v_reuseFailAlloc_3125_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3121_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3121_, 0, v___x_3120_);
                crate::leanh::lean_ctor_set(v___x_3121_, 1, v_a_3114_);
                if v_isShared_3117_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3116_, 0, v___x_3121_);
                    v___x_3123_ = v___x_3116_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3124_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3124_, 0, v___x_3121_);
                    v___x_3123_ = v_reuseFailAlloc_3124_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3123_;
            }
            5 => {
                if v_isShared_3130_ == 0 {
                    v___x_3132_ = v___x_3129_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3133_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
                    v___x_3132_ = v_reuseFailAlloc_3133_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3132_;
            }
            7 => {
                if v_isShared_3139_ == 0 {
                    v___x_3141_ = v___x_3138_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3142_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
                    v___x_3141_ = v_reuseFailAlloc_3142_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3141_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_wfRecursion___lam__2___boxed(
    mut v_snd_3144_: *mut crate::leanh::LeanObject,
    mut v___y_3145_: *mut crate::leanh::LeanObject,
    mut v___y_3146_: *mut crate::leanh::LeanObject,
    mut v___y_3147_: *mut crate::leanh::LeanObject,
    mut v___y_3148_: *mut crate::leanh::LeanObject,
    mut v___y_3149_: *mut crate::leanh::LeanObject,
    mut v___y_3150_: *mut crate::leanh::LeanObject,
    mut v___y_3151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3152_ = l_Lean_Elab_wfRecursion___lam__2(
        v_snd_3144_,
        v___y_3145_,
        v___y_3146_,
        v___y_3147_,
        v___y_3148_,
        v___y_3149_,
        v___y_3150_,
    );
    crate::leanh::lean_dec(v___y_3150_);
    crate::leanh::lean_dec_ref(v___y_3149_);
    crate::leanh::lean_dec(v___y_3148_);
    crate::leanh::lean_dec_ref(v___y_3147_);
    crate::leanh::lean_dec(v___y_3146_);
    crate::leanh::lean_dec_ref(v___y_3145_);
    return v_res_3152_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(
    mut v___y_3160_: u8,
    mut v_suppressElabErrors_3161_: u8,
    mut v_x_3162_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_3162_) == 1 {
        let mut v_pre_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_pre_3163_ = crate::leanh::lean_ctor_get(v_x_3162_, 0);
        match crate::leanh::lean_obj_tag(v_pre_3163_) {
            1 => {
                let mut v_pre_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_pre_3164_ = crate::leanh::lean_ctor_get(v_pre_3163_, 0);
                match crate::leanh::lean_obj_tag(v_pre_3164_) {
                    0 => {
                        let mut v_str_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v_str_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_3168_: u8 = 0;
                        v_str_3165_ = crate::leanh::lean_ctor_get(v_x_3162_, 1);
                        v_str_3166_ = crate::leanh::lean_ctor_get(v_pre_3163_, 1);
                        v___x_3167_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__0;
                        v___x_3168_ = lean_string_dec_eq(v_str_3166_, v___x_3167_);
                        if v___x_3168_ == 0 {
                            let mut v___x_3169_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3170_: u8 = 0;
                            v___x_3169_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__1;
                            v___x_3170_ = lean_string_dec_eq(v_str_3166_, v___x_3169_);
                            if v___x_3170_ == 0 {
                                return v___y_3160_;
                            } else {
                                let mut v___x_3171_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3172_: u8 = 0;
                                v___x_3171_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__2;
                                v___x_3172_ = lean_string_dec_eq(v_str_3165_, v___x_3171_);
                                if v___x_3172_ == 0 {
                                    return v___y_3160_;
                                } else {
                                    return v_suppressElabErrors_3161_;
                                }
                            }
                        } else {
                            let mut v___x_3173_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3174_: u8 = 0;
                            v___x_3173_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__3;
                            v___x_3174_ = lean_string_dec_eq(v_str_3165_, v___x_3173_);
                            if v___x_3174_ == 0 {
                                return v___y_3160_;
                            } else {
                                return v_suppressElabErrors_3161_;
                            }
                        }
                    }
                    1 => {
                        let mut v_pre_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v_pre_3175_ = crate::leanh::lean_ctor_get(v_pre_3164_, 0);
                        if crate::leanh::lean_obj_tag(v_pre_3175_) == 0 {
                            let mut v_str_3176_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_3177_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_str_3178_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3179_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_3180_: u8 = 0;
                            v_str_3176_ = crate::leanh::lean_ctor_get(v_x_3162_, 1);
                            v_str_3177_ = crate::leanh::lean_ctor_get(v_pre_3163_, 1);
                            v_str_3178_ = crate::leanh::lean_ctor_get(v_pre_3164_, 1);
                            v___x_3179_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__4;
                            v___x_3180_ = lean_string_dec_eq(v_str_3178_, v___x_3179_);
                            if v___x_3180_ == 0 {
                                return v___y_3160_;
                            } else {
                                let mut v___x_3181_: *mut crate::leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_3182_: u8 = 0;
                                v___x_3181_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__5;
                                v___x_3182_ = lean_string_dec_eq(v_str_3177_, v___x_3181_);
                                if v___x_3182_ == 0 {
                                    return v___y_3160_;
                                } else {
                                    let mut v___x_3183_: *mut crate::leanh::LeanObject =
                                        core::ptr::null_mut();
                                    let mut v___x_3184_: u8 = 0;
                                    v___x_3183_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___closed__6;
                                    v___x_3184_ = lean_string_dec_eq(v_str_3176_, v___x_3183_);
                                    if v___x_3184_ == 0 {
                                        return v___y_3160_;
                                    } else {
                                        return v_suppressElabErrors_3161_;
                                    }
                                }
                            }
                        } else {
                            return v___y_3160_;
                        }
                    }
                    _ => {
                        return v___y_3160_;
                    }
                }
            }
            0 => {
                let mut v_str_3185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3187_: u8 = 0;
                v_str_3185_ = crate::leanh::lean_ctor_get(v_x_3162_, 1);
                v___x_3186_ = l_Lean_Elab_wfRecursion___lam__1___closed__0;
                v___x_3187_ = lean_string_dec_eq(v_str_3185_, v___x_3186_);
                if v___x_3187_ == 0 {
                    return v___y_3160_;
                } else {
                    return v_suppressElabErrors_3161_;
                }
            }
            _ => {
                return v___y_3160_;
            }
        }
    } else {
        return v___y_3160_;
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed(
    mut v___y_3188_: *mut crate::leanh::LeanObject,
    mut v_suppressElabErrors_3189_: *mut crate::leanh::LeanObject,
    mut v_x_3190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_47131__boxed_3191_: u8 = 0;
    let mut v_suppressElabErrors_boxed_3192_: u8 = 0;
    let mut v_res_3193_: u8 = 0;
    let mut v_r_3194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_47131__boxed_3191_ = (crate::leanh::lean_unbox(v___y_3188_) as u8);
    v_suppressElabErrors_boxed_3192_ = (crate::leanh::lean_unbox(v_suppressElabErrors_3189_) as u8);
    v_res_3193_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0(v___y_47131__boxed_3191_, v_suppressElabErrors_boxed_3192_, v_x_3190_);
    crate::leanh::lean_dec(v_x_3190_);
    v_r_3194_ = crate::leanh::lean_box((v_res_3193_) as usize);
    return v_r_3194_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(
    mut v_ref_3196_: *mut crate::leanh::LeanObject,
    mut v_msgData_3197_: *mut crate::leanh::LeanObject,
    mut v_severity_3198_: u8,
    mut v_isSilent_3199_: u8,
    mut v___y_3200_: *mut crate::leanh::LeanObject,
    mut v___y_3201_: *mut crate::leanh::LeanObject,
    mut v___y_3202_: *mut crate::leanh::LeanObject,
    mut v___y_3203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3209_: u8 = 0;
    let mut v___y_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3211_: u8 = 0;
    let mut v___y_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_3216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3229_: u8 = 0;
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3240_: u8 = 0;
    let mut v___y_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3244_: u8 = 0;
    let mut v___y_3245_: u8 = 0;
    let mut v___y_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3248_: u8 = 0;
    let mut v___y_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3255_: u8 = 0;
    let mut v___x_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: u8 = 0;
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3265_: u8 = 0;
    let mut v___y_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3268_: u8 = 0;
    let mut v___y_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3270_: u8 = 0;
    let mut v___y_3271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3272_: u8 = 0;
    let mut v___y_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3280_: u8 = 0;
    let mut v___y_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3283_: u8 = 0;
    let mut v___y_3284_: u8 = 0;
    let mut v_ref_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: u8 = 0;
    let mut v___y_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3292_: u8 = 0;
    let mut v___y_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3296_: u8 = 0;
    let mut v___y_3297_: u8 = 0;
    let mut v___y_3299_: u8 = 0;
    let mut v_fileName_3300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_3304_: u8 = 0;
    let mut v___x_3305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: u8 = 0;
    let mut v___x_3309_: u8 = 0;
    let mut v___x_3310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: u8 = 0;
    let mut v___x_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: u8 = 0;
    let mut v___x_3315_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3289_ = 2;
                v___x_3314_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3198_, v___x_3289_);
                if v___x_3314_ == 0 {
                    v___y_3299_ = v___x_3314_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc_ref(v_msgData_3197_);
                    v___x_3315_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3197_);
                    v___y_3299_ = v___x_3315_;
                    state = 10;
                    continue;
                }
            }
            1 => {
                v___x_3215_ = lean_st_ref_take(v___y_3214_);
                v_currNamespace_3216_ = crate::leanh::lean_ctor_get(v___y_3213_, 6);
                v_openDecls_3217_ = crate::leanh::lean_ctor_get(v___y_3213_, 7);
                v_env_3218_ = crate::leanh::lean_ctor_get(v___x_3215_, 0);
                v_nextMacroScope_3219_ = crate::leanh::lean_ctor_get(v___x_3215_, 1);
                v_ngen_3220_ = crate::leanh::lean_ctor_get(v___x_3215_, 2);
                v_auxDeclNGen_3221_ = crate::leanh::lean_ctor_get(v___x_3215_, 3);
                v_traceState_3222_ = crate::leanh::lean_ctor_get(v___x_3215_, 4);
                v_cache_3223_ = crate::leanh::lean_ctor_get(v___x_3215_, 5);
                v_messages_3224_ = crate::leanh::lean_ctor_get(v___x_3215_, 6);
                v_infoState_3225_ = crate::leanh::lean_ctor_get(v___x_3215_, 7);
                v_snapshotTasks_3226_ = crate::leanh::lean_ctor_get(v___x_3215_, 8);
                v_isSharedCheck_3240_ = (!crate::leanh::lean_is_exclusive(v___x_3215_)) as u8;
                if v_isSharedCheck_3240_ == 0 {
                    v___x_3228_ = v___x_3215_;
                    v_isShared_3229_ = v_isSharedCheck_3240_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3226_);
                    crate::leanh::lean_inc(v_infoState_3225_);
                    crate::leanh::lean_inc(v_messages_3224_);
                    crate::leanh::lean_inc(v_cache_3223_);
                    crate::leanh::lean_inc(v_traceState_3222_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3221_);
                    crate::leanh::lean_inc(v_ngen_3220_);
                    crate::leanh::lean_inc(v_nextMacroScope_3219_);
                    crate::leanh::lean_inc(v_env_3218_);
                    crate::leanh::lean_dec(v___x_3215_);
                    v___x_3228_ = crate::leanh::lean_box(0);
                    v_isShared_3229_ = v_isSharedCheck_3240_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc(v_openDecls_3217_);
                crate::leanh::lean_inc(v_currNamespace_3216_);
                v___x_3230_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3230_, 0, v_currNamespace_3216_);
                crate::leanh::lean_ctor_set(v___x_3230_, 1, v_openDecls_3217_);
                v___x_3231_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3231_, 0, v___x_3230_);
                crate::leanh::lean_ctor_set(v___x_3231_, 1, v___y_3210_);
                crate::leanh::lean_inc_ref(v___y_3206_);
                crate::leanh::lean_inc_ref(v___y_3212_);
                v___x_3232_ = crate::leanh::lean_alloc_ctor(0, 5, (3) as u32);
                crate::leanh::lean_ctor_set(v___x_3232_, 0, v___y_3212_);
                crate::leanh::lean_ctor_set(v___x_3232_, 1, v___y_3208_);
                crate::leanh::lean_ctor_set(v___x_3232_, 2, v___y_3207_);
                crate::leanh::lean_ctor_set(v___x_3232_, 3, v___y_3206_);
                crate::leanh::lean_ctor_set(v___x_3232_, 4, v___x_3231_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3232_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    v___y_3211_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3232_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 1) as u32,
                    v___y_3209_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3232_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5 + 2) as u32,
                    v_isSilent_3199_,
                );
                v___x_3233_ = l_Lean_MessageLog_add(v___x_3232_, v_messages_3224_);
                if v_isShared_3229_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3228_, 6, v___x_3233_);
                    v___x_3235_ = v___x_3228_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3239_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_env_3218_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 1, v_nextMacroScope_3219_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 2, v_ngen_3220_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 3, v_auxDeclNGen_3221_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 4, v_traceState_3222_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 5, v_cache_3223_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 6, v___x_3233_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 7, v_infoState_3225_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3239_, 8, v_snapshotTasks_3226_);
                    v___x_3235_ = v_reuseFailAlloc_3239_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3236_ = lean_st_ref_set(v___y_3214_, v___x_3235_);
                v___x_3237_ = crate::leanh::lean_box(0);
                v___x_3238_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3238_, 0, v___x_3237_);
                return v___x_3238_;
            }
            4 => {
                v___x_3250_ =
                    l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(
                        v_msgData_3197_,
                    );
                v___x_3251_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v___x_3250_, v___y_3200_, v___y_3201_, v___y_3202_, v___y_3203_);
                v_a_3252_ = crate::leanh::lean_ctor_get(v___x_3251_, 0);
                v_isSharedCheck_3265_ = (!crate::leanh::lean_is_exclusive(v___x_3251_)) as u8;
                if v_isSharedCheck_3265_ == 0 {
                    v___x_3254_ = v___x_3251_;
                    v_isShared_3255_ = v_isSharedCheck_3265_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3252_);
                    crate::leanh::lean_dec(v___x_3251_);
                    v___x_3254_ = crate::leanh::lean_box(0);
                    v_isShared_3255_ = v_isSharedCheck_3265_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                crate::leanh::lean_inc_ref_n(v___y_3246_, 2);
                v___x_3256_ = l_Lean_FileMap_toPosition(v___y_3246_, v___y_3243_);
                crate::leanh::lean_dec(v___y_3243_);
                v___x_3257_ = l_Lean_FileMap_toPosition(v___y_3246_, v___y_3249_);
                crate::leanh::lean_dec(v___y_3249_);
                v___x_3258_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3258_, 0, v___x_3257_);
                v___x_3259_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0;
                if v___y_3244_ == 0 {
                    crate::leanh::lean_del_object(v___x_3254_);
                    crate::leanh::lean_dec_ref(v___y_3242_);
                    v___y_3206_ = v___x_3259_;
                    v___y_3207_ = v___x_3258_;
                    v___y_3208_ = v___x_3256_;
                    v___y_3209_ = v___y_3245_;
                    v___y_3210_ = v_a_3252_;
                    v___y_3211_ = v___y_3248_;
                    v___y_3212_ = v___y_3247_;
                    v___y_3213_ = v___y_3202_;
                    v___y_3214_ = v___y_3203_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3252_);
                    v___x_3260_ = l_Lean_MessageData_hasTag(v___y_3242_, v_a_3252_);
                    if v___x_3260_ == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_3258_, 1);
                        crate::leanh::lean_dec_ref(v___x_3256_);
                        crate::leanh::lean_dec(v_a_3252_);
                        v___x_3261_ = crate::leanh::lean_box(0);
                        if v_isShared_3255_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3254_, 0, v___x_3261_);
                            v___x_3263_ = v___x_3254_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3264_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3264_, 0, v___x_3261_);
                            v___x_3263_ = v_reuseFailAlloc_3264_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3254_);
                        v___y_3206_ = v___x_3259_;
                        v___y_3207_ = v___x_3258_;
                        v___y_3208_ = v___x_3256_;
                        v___y_3209_ = v___y_3245_;
                        v___y_3210_ = v_a_3252_;
                        v___y_3211_ = v___y_3248_;
                        v___y_3212_ = v___y_3247_;
                        v___y_3213_ = v___y_3202_;
                        v___y_3214_ = v___y_3203_;
                        state = 1;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_3263_;
            }
            7 => {
                v___x_3275_ = l_Lean_Syntax_getTailPos_x3f(v___y_3271_, v___y_3272_);
                crate::leanh::lean_dec(v___y_3271_);
                if crate::leanh::lean_obj_tag(v___x_3275_) == 0 {
                    crate::leanh::lean_inc(v___y_3274_);
                    v___y_3242_ = v___y_3267_;
                    v___y_3243_ = v___y_3274_;
                    v___y_3244_ = v___y_3268_;
                    v___y_3245_ = v___y_3270_;
                    v___y_3246_ = v___y_3269_;
                    v___y_3247_ = v___y_3273_;
                    v___y_3248_ = v___y_3272_;
                    v___y_3249_ = v___y_3274_;
                    state = 4;
                    continue;
                } else {
                    v_val_3276_ = crate::leanh::lean_ctor_get(v___x_3275_, 0);
                    crate::leanh::lean_inc(v_val_3276_);
                    crate::leanh::lean_dec_ref_known(v___x_3275_, 1);
                    v___y_3242_ = v___y_3267_;
                    v___y_3243_ = v___y_3274_;
                    v___y_3244_ = v___y_3268_;
                    v___y_3245_ = v___y_3270_;
                    v___y_3246_ = v___y_3269_;
                    v___y_3247_ = v___y_3273_;
                    v___y_3248_ = v___y_3272_;
                    v___y_3249_ = v_val_3276_;
                    state = 4;
                    continue;
                }
            }
            8 => {
                v_ref_3285_ = l_Lean_replaceRef(v_ref_3196_, v___y_3279_);
                v___x_3286_ = l_Lean_Syntax_getPos_x3f(v_ref_3285_, v___y_3283_);
                if crate::leanh::lean_obj_tag(v___x_3286_) == 0 {
                    v___x_3287_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_3267_ = v___y_3278_;
                    v___y_3268_ = v___y_3280_;
                    v___y_3269_ = v___y_3281_;
                    v___y_3270_ = v___y_3284_;
                    v___y_3271_ = v_ref_3285_;
                    v___y_3272_ = v___y_3283_;
                    v___y_3273_ = v___y_3282_;
                    v___y_3274_ = v___x_3287_;
                    state = 7;
                    continue;
                } else {
                    v_val_3288_ = crate::leanh::lean_ctor_get(v___x_3286_, 0);
                    crate::leanh::lean_inc(v_val_3288_);
                    crate::leanh::lean_dec_ref_known(v___x_3286_, 1);
                    v___y_3267_ = v___y_3278_;
                    v___y_3268_ = v___y_3280_;
                    v___y_3269_ = v___y_3281_;
                    v___y_3270_ = v___y_3284_;
                    v___y_3271_ = v_ref_3285_;
                    v___y_3272_ = v___y_3283_;
                    v___y_3273_ = v___y_3282_;
                    v___y_3274_ = v_val_3288_;
                    state = 7;
                    continue;
                }
            }
            9 => {
                if v___y_3297_ == 0 {
                    v___y_3278_ = v___y_3293_;
                    v___y_3279_ = v___y_3291_;
                    v___y_3280_ = v___y_3292_;
                    v___y_3281_ = v___y_3294_;
                    v___y_3282_ = v___y_3295_;
                    v___y_3283_ = v___y_3296_;
                    v___y_3284_ = v_severity_3198_;
                    state = 8;
                    continue;
                } else {
                    v___y_3278_ = v___y_3293_;
                    v___y_3279_ = v___y_3291_;
                    v___y_3280_ = v___y_3292_;
                    v___y_3281_ = v___y_3294_;
                    v___y_3282_ = v___y_3295_;
                    v___y_3283_ = v___y_3296_;
                    v___y_3284_ = v___x_3289_;
                    state = 8;
                    continue;
                }
            }
            10 => {
                if v___y_3299_ == 0 {
                    v_fileName_3300_ = crate::leanh::lean_ctor_get(v___y_3202_, 0);
                    v_fileMap_3301_ = crate::leanh::lean_ctor_get(v___y_3202_, 1);
                    v_options_3302_ = crate::leanh::lean_ctor_get(v___y_3202_, 2);
                    v_ref_3303_ = crate::leanh::lean_ctor_get(v___y_3202_, 5);
                    v_suppressElabErrors_3304_ = crate::leanh::lean_ctor_get_uint8(
                        v___y_3202_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v___x_3305_ = crate::leanh::lean_box((v___y_3299_) as usize);
                    v___x_3306_ = crate::leanh::lean_box((v_suppressElabErrors_3304_) as usize);
                    v___f_3307_ = crate::leanh::lean_alloc_closure(l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                    crate::leanh::lean_closure_set(v___f_3307_, 0, v___x_3305_);
                    crate::leanh::lean_closure_set(v___f_3307_, 1, v___x_3306_);
                    v___x_3308_ = 1;
                    v___x_3309_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3198_, v___x_3308_);
                    if v___x_3309_ == 0 {
                        v___y_3291_ = v_ref_3303_;
                        v___y_3292_ = v_suppressElabErrors_3304_;
                        v___y_3293_ = v___f_3307_;
                        v___y_3294_ = v_fileMap_3301_;
                        v___y_3295_ = v_fileName_3300_;
                        v___y_3296_ = v___y_3299_;
                        v___y_3297_ = v___x_3309_;
                        state = 9;
                        continue;
                    } else {
                        v___x_3310_ = l_Lean_warningAsError;
                        v___x_3311_ = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1_spec__4(v_options_3302_, v___x_3310_);
                        v___y_3291_ = v_ref_3303_;
                        v___y_3292_ = v_suppressElabErrors_3304_;
                        v___y_3293_ = v___f_3307_;
                        v___y_3294_ = v_fileMap_3301_;
                        v___y_3295_ = v_fileName_3300_;
                        v___y_3296_ = v___y_3299_;
                        v___y_3297_ = v___x_3311_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_msgData_3197_);
                    v___x_3312_ = crate::leanh::lean_box(0);
                    v___x_3313_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3313_, 0, v___x_3312_);
                    return v___x_3313_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___boxed(
    mut v_ref_3316_: *mut crate::leanh::LeanObject,
    mut v_msgData_3317_: *mut crate::leanh::LeanObject,
    mut v_severity_3318_: *mut crate::leanh::LeanObject,
    mut v_isSilent_3319_: *mut crate::leanh::LeanObject,
    mut v___y_3320_: *mut crate::leanh::LeanObject,
    mut v___y_3321_: *mut crate::leanh::LeanObject,
    mut v___y_3322_: *mut crate::leanh::LeanObject,
    mut v___y_3323_: *mut crate::leanh::LeanObject,
    mut v___y_3324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_3325_: u8 = 0;
    let mut v_isSilent_boxed_3326_: u8 = 0;
    let mut v_res_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_3325_ = (crate::leanh::lean_unbox(v_severity_3318_) as u8);
    v_isSilent_boxed_3326_ = (crate::leanh::lean_unbox(v_isSilent_3319_) as u8);
    v_res_3327_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_3316_, v_msgData_3317_, v_severity_boxed_3325_, v_isSilent_boxed_3326_, v___y_3320_, v___y_3321_, v___y_3322_, v___y_3323_);
    crate::leanh::lean_dec(v___y_3323_);
    crate::leanh::lean_dec_ref(v___y_3322_);
    crate::leanh::lean_dec(v___y_3321_);
    crate::leanh::lean_dec_ref(v___y_3320_);
    crate::leanh::lean_dec(v_ref_3316_);
    return v_res_3327_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(
    mut v_ref_3328_: *mut crate::leanh::LeanObject,
    mut v_msgData_3329_: *mut crate::leanh::LeanObject,
    mut v___y_3330_: *mut crate::leanh::LeanObject,
    mut v___y_3331_: *mut crate::leanh::LeanObject,
    mut v___y_3332_: *mut crate::leanh::LeanObject,
    mut v___y_3333_: *mut crate::leanh::LeanObject,
    mut v___y_3334_: *mut crate::leanh::LeanObject,
    mut v___y_3335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3337_: u8 = 0;
    let mut v___x_3338_: u8 = 0;
    let mut v___x_3339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3337_ = 1;
    v___x_3338_ = 0;
    v___x_3339_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_3328_, v_msgData_3329_, v___x_3337_, v___x_3338_, v___y_3332_, v___y_3333_, v___y_3334_, v___y_3335_);
    return v___x_3339_;
}
pub unsafe fn l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11___boxed(
    mut v_ref_3340_: *mut crate::leanh::LeanObject,
    mut v_msgData_3341_: *mut crate::leanh::LeanObject,
    mut v___y_3342_: *mut crate::leanh::LeanObject,
    mut v___y_3343_: *mut crate::leanh::LeanObject,
    mut v___y_3344_: *mut crate::leanh::LeanObject,
    mut v___y_3345_: *mut crate::leanh::LeanObject,
    mut v___y_3346_: *mut crate::leanh::LeanObject,
    mut v___y_3347_: *mut crate::leanh::LeanObject,
    mut v___y_3348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3349_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(
        v_ref_3340_,
        v_msgData_3341_,
        v___y_3342_,
        v___y_3343_,
        v___y_3344_,
        v___y_3345_,
        v___y_3346_,
        v___y_3347_,
    );
    crate::leanh::lean_dec(v___y_3347_);
    crate::leanh::lean_dec_ref(v___y_3346_);
    crate::leanh::lean_dec(v___y_3345_);
    crate::leanh::lean_dec_ref(v___y_3344_);
    crate::leanh::lean_dec(v___y_3343_);
    crate::leanh::lean_dec_ref(v___y_3342_);
    crate::leanh::lean_dec(v_ref_3340_);
    return v_res_3349_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(
    mut v_as_3358_: *mut crate::leanh::LeanObject,
    mut v_i_3359_: usize,
    mut v_stop_3360_: usize,
    mut v_b_3361_: *mut crate::leanh::LeanObject,
    mut v___y_3362_: *mut crate::leanh::LeanObject,
    mut v___y_3363_: *mut crate::leanh::LeanObject,
    mut v___y_3364_: *mut crate::leanh::LeanObject,
    mut v___y_3365_: *mut crate::leanh::LeanObject,
    mut v___y_3366_: *mut crate::leanh::LeanObject,
    mut v___y_3367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: usize = 0;
    let mut v___x_3372_: usize = 0;
    let mut v___x_3374_: u8 = 0;
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stx_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3379_: u8 = 0;
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: u8 = 0;
    let mut v___x_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: u8 = 0;
    let mut v___x_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3374_ = lean_usize_dec_eq(v_i_3359_, v_stop_3360_);
                if v___x_3374_ == 0 {
                    v___x_3375_ = lean_array_uget_borrowed(v_as_3358_, v_i_3359_);
                    v_name_3376_ = crate::leanh::lean_ctor_get(v___x_3375_, 0);
                    v_stx_3377_ = crate::leanh::lean_ctor_get(v___x_3375_, 1);
                    v___x_3389_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__3;
                    v___x_3390_ = lean_name_eq(v_name_3376_, v___x_3389_);
                    if v___x_3390_ == 0 {
                        v___x_3391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__5;
                        v___x_3392_ = lean_name_eq(v_name_3376_, v___x_3391_);
                        if v___x_3392_ == 0 {
                            v___x_3393_ = crate::leanh::lean_box(0);
                            v_a_3370_ = v___x_3393_;
                            state = 1;
                            continue;
                        } else {
                            v___y_3379_ = v___x_3392_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_3379_ = v___x_3390_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_3394_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3394_, 0, v_b_3361_);
                    return v___x_3394_;
                }
            }
            1 => {
                v___x_3371_ = 1usize;
                v___x_3372_ = lean_usize_add(v_i_3359_, v___x_3371_);
                v_i_3359_ = v___x_3372_;
                v_b_3361_ = v_a_3370_;
                state = 0;
                continue;
            }
            2 => {
                v___x_3380_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__0;
                crate::leanh::lean_inc(v_name_3376_);
                v___x_3381_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_name_3376_,
                    v___y_3379_,
                );
                v___x_3382_ = lean_string_append(v___x_3380_, v___x_3381_);
                crate::leanh::lean_dec_ref(v___x_3381_);
                v___x_3383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___closed__1;
                v___x_3384_ = lean_string_append(v___x_3382_, v___x_3383_);
                v___x_3385_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3385_, 0, v___x_3384_);
                v___x_3386_ = l_Lean_MessageData_ofFormat(v___x_3385_);
                v___x_3387_ = l_Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11(
                    v_stx_3377_,
                    v___x_3386_,
                    v___y_3362_,
                    v___y_3363_,
                    v___y_3364_,
                    v___y_3365_,
                    v___y_3366_,
                    v___y_3367_,
                );
                if crate::leanh::lean_obj_tag(v___x_3387_) == 0 {
                    v_a_3388_ = crate::leanh::lean_ctor_get(v___x_3387_, 0);
                    crate::leanh::lean_inc(v_a_3388_);
                    crate::leanh::lean_dec_ref_known(v___x_3387_, 1);
                    v_a_3370_ = v_a_3388_;
                    state = 1;
                    continue;
                } else {
                    return v___x_3387_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12___boxed(
    mut v_as_3395_: *mut crate::leanh::LeanObject,
    mut v_i_3396_: *mut crate::leanh::LeanObject,
    mut v_stop_3397_: *mut crate::leanh::LeanObject,
    mut v_b_3398_: *mut crate::leanh::LeanObject,
    mut v___y_3399_: *mut crate::leanh::LeanObject,
    mut v___y_3400_: *mut crate::leanh::LeanObject,
    mut v___y_3401_: *mut crate::leanh::LeanObject,
    mut v___y_3402_: *mut crate::leanh::LeanObject,
    mut v___y_3403_: *mut crate::leanh::LeanObject,
    mut v___y_3404_: *mut crate::leanh::LeanObject,
    mut v___y_3405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3406_: usize = 0;
    let mut v_stop_boxed_3407_: usize = 0;
    let mut v_res_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3406_ = crate::leanh::lean_unbox_usize(v_i_3396_);
    crate::leanh::lean_dec(v_i_3396_);
    v_stop_boxed_3407_ = crate::leanh::lean_unbox_usize(v_stop_3397_);
    crate::leanh::lean_dec(v_stop_3397_);
    v_res_3408_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v_as_3395_, v_i_boxed_3406_, v_stop_boxed_3407_, v_b_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
    crate::leanh::lean_dec(v___y_3404_);
    crate::leanh::lean_dec_ref(v___y_3403_);
    crate::leanh::lean_dec(v___y_3402_);
    crate::leanh::lean_dec_ref(v___y_3401_);
    crate::leanh::lean_dec(v___y_3400_);
    crate::leanh::lean_dec_ref(v___y_3399_);
    crate::leanh::lean_dec_ref(v_as_3395_);
    return v_res_3408_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(
    mut v_as_3409_: *mut crate::leanh::LeanObject,
    mut v_i_3410_: usize,
    mut v_stop_3411_: usize,
    mut v_b_3412_: *mut crate::leanh::LeanObject,
    mut v___y_3413_: *mut crate::leanh::LeanObject,
    mut v___y_3414_: *mut crate::leanh::LeanObject,
    mut v___y_3415_: *mut crate::leanh::LeanObject,
    mut v___y_3416_: *mut crate::leanh::LeanObject,
    mut v___y_3417_: *mut crate::leanh::LeanObject,
    mut v___y_3418_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: usize = 0;
    let mut v___x_3423_: usize = 0;
    let mut v___y_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: u8 = 0;
    let mut v___x_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifiers_3430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attrs_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: u8 = 0;
    let mut v___x_3436_: u8 = 0;
    let mut v___x_3437_: usize = 0;
    let mut v___x_3438_: usize = 0;
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: usize = 0;
    let mut v___x_3441_: usize = 0;
    let mut v___x_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3428_ = lean_usize_dec_eq(v_i_3410_, v_stop_3411_);
                if v___x_3428_ == 0 {
                    v___x_3429_ = lean_array_uget_borrowed(v_as_3409_, v_i_3410_);
                    v_modifiers_3430_ = crate::leanh::lean_ctor_get(v___x_3429_, 2);
                    v_attrs_3431_ = crate::leanh::lean_ctor_get(v_modifiers_3430_, 2);
                    v___x_3432_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3433_ = lean_array_get_size(v_attrs_3431_);
                    v___x_3434_ = crate::leanh::lean_box(0);
                    v___x_3435_ = lean_nat_dec_lt(v___x_3432_, v___x_3433_);
                    if v___x_3435_ == 0 {
                        v_a_3421_ = v___x_3434_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3436_ = lean_nat_dec_le(v___x_3433_, v___x_3433_);
                        if v___x_3436_ == 0 {
                            if v___x_3435_ == 0 {
                                v_a_3421_ = v___x_3434_;
                                state = 1;
                                continue;
                            } else {
                                v___x_3437_ = 0usize;
                                v___x_3438_ = lean_usize_of_nat(v___x_3433_);
                                v___x_3439_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v_attrs_3431_, v___x_3437_, v___x_3438_, v___x_3434_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
                                v___y_3426_ = v___x_3439_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_3440_ = 0usize;
                            v___x_3441_ = lean_usize_of_nat(v___x_3433_);
                            v___x_3442_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__12(v_attrs_3431_, v___x_3440_, v___x_3441_, v___x_3434_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_, v___y_3418_);
                            v___y_3426_ = v___x_3442_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_3443_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3443_, 0, v_b_3412_);
                    return v___x_3443_;
                }
            }
            1 => {
                v___x_3422_ = 1usize;
                v___x_3423_ = lean_usize_add(v_i_3410_, v___x_3422_);
                v_i_3410_ = v___x_3423_;
                v_b_3412_ = v_a_3421_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_3426_) == 0 {
                    v_a_3427_ = crate::leanh::lean_ctor_get(v___y_3426_, 0);
                    crate::leanh::lean_inc(v_a_3427_);
                    crate::leanh::lean_dec_ref_known(v___y_3426_, 1);
                    v_a_3421_ = v_a_3427_;
                    state = 1;
                    continue;
                } else {
                    return v___y_3426_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13___boxed(
    mut v_as_3444_: *mut crate::leanh::LeanObject,
    mut v_i_3445_: *mut crate::leanh::LeanObject,
    mut v_stop_3446_: *mut crate::leanh::LeanObject,
    mut v_b_3447_: *mut crate::leanh::LeanObject,
    mut v___y_3448_: *mut crate::leanh::LeanObject,
    mut v___y_3449_: *mut crate::leanh::LeanObject,
    mut v___y_3450_: *mut crate::leanh::LeanObject,
    mut v___y_3451_: *mut crate::leanh::LeanObject,
    mut v___y_3452_: *mut crate::leanh::LeanObject,
    mut v___y_3453_: *mut crate::leanh::LeanObject,
    mut v___y_3454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3455_: usize = 0;
    let mut v_stop_boxed_3456_: usize = 0;
    let mut v_res_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3455_ = crate::leanh::lean_unbox_usize(v_i_3445_);
    crate::leanh::lean_dec(v_i_3445_);
    v_stop_boxed_3456_ = crate::leanh::lean_unbox_usize(v_stop_3446_);
    crate::leanh::lean_dec(v_stop_3446_);
    v_res_3457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v_as_3444_, v_i_boxed_3455_, v_stop_boxed_3456_, v_b_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_, v___y_3452_, v___y_3453_);
    crate::leanh::lean_dec(v___y_3453_);
    crate::leanh::lean_dec_ref(v___y_3452_);
    crate::leanh::lean_dec(v___y_3451_);
    crate::leanh::lean_dec_ref(v___y_3450_);
    crate::leanh::lean_dec(v___y_3449_);
    crate::leanh::lean_dec_ref(v___y_3448_);
    crate::leanh::lean_dec_ref(v_as_3444_);
    return v_res_3457_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(
    mut v_sz_3458_: usize,
    mut v_i_3459_: usize,
    mut v_bs_3460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3461_: u8 = 0;
    let mut v_v_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_termination_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decreasingBy_x3f_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: usize = 0;
    let mut v___x_3468_: usize = 0;
    let mut v___x_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3461_ = lean_usize_dec_lt(v_i_3459_, v_sz_3458_);
                if v___x_3461_ == 0 {
                    return v_bs_3460_;
                } else {
                    v_v_3462_ = lean_array_uget_borrowed(v_bs_3460_, v_i_3459_);
                    v_termination_3463_ = crate::leanh::lean_ctor_get(v_v_3462_, 8);
                    v_decreasingBy_x3f_3464_ = crate::leanh::lean_ctor_get(v_termination_3463_, 4);
                    crate::leanh::lean_inc(v_decreasingBy_x3f_3464_);
                    v___x_3465_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3466_ = lean_array_uset(v_bs_3460_, v_i_3459_, v___x_3465_);
                    v___x_3467_ = 1usize;
                    v___x_3468_ = lean_usize_add(v_i_3459_, v___x_3467_);
                    v___x_3469_ =
                        lean_array_uset(v_bs_x27_3466_, v_i_3459_, v_decreasingBy_x3f_3464_);
                    v_i_3459_ = v___x_3468_;
                    v_bs_3460_ = v___x_3469_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10___boxed(
    mut v_sz_3471_: *mut crate::leanh::LeanObject,
    mut v_i_3472_: *mut crate::leanh::LeanObject,
    mut v_bs_3473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3474_: usize = 0;
    let mut v_i_boxed_3475_: usize = 0;
    let mut v_res_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3474_ = crate::leanh::lean_unbox_usize(v_sz_3471_);
    crate::leanh::lean_dec(v_sz_3471_);
    v_i_boxed_3475_ = crate::leanh::lean_unbox_usize(v_i_3472_);
    crate::leanh::lean_dec(v_i_3472_);
    v_res_3476_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_boxed_3474_, v_i_boxed_3475_, v_bs_3473_);
    return v_res_3476_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0()
-> f64 {
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: f64 = 0.0;
    v___x_3477_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3478_ = lean_float_of_nat(v___x_3477_);
    return v___x_3478_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(
    mut v_cls_3481_: *mut crate::leanh::LeanObject,
    mut v_msg_3482_: *mut crate::leanh::LeanObject,
    mut v___y_3483_: *mut crate::leanh::LeanObject,
    mut v___y_3484_: *mut crate::leanh::LeanObject,
    mut v___y_3485_: *mut crate::leanh::LeanObject,
    mut v___y_3486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3493_: u8 = 0;
    let mut v___x_3494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3506_: u8 = 0;
    let mut v_tid_3507_: u64 = 0;
    let mut v_traces_3508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3511_: u8 = 0;
    let mut v___x_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: f64 = 0.0;
    let mut v___x_3514_: u8 = 0;
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3532_: u8 = 0;
    let mut v_isSharedCheck_3533_: u8 = 0;
    let mut v_isSharedCheck_3534_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3488_ = crate::leanh::lean_ctor_get(v___y_3485_, 5);
                v___x_3489_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__0(v_msg_3482_, v___y_3483_, v___y_3484_, v___y_3485_, v___y_3486_);
                v_a_3490_ = crate::leanh::lean_ctor_get(v___x_3489_, 0);
                v_isSharedCheck_3534_ = (!crate::leanh::lean_is_exclusive(v___x_3489_)) as u8;
                if v_isSharedCheck_3534_ == 0 {
                    v___x_3492_ = v___x_3489_;
                    v_isShared_3493_ = v_isSharedCheck_3534_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_3490_);
                    crate::leanh::lean_dec(v___x_3489_);
                    v___x_3492_ = crate::leanh::lean_box(0);
                    v_isShared_3493_ = v_isSharedCheck_3534_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3494_ = lean_st_ref_take(v___y_3486_);
                v_traceState_3495_ = crate::leanh::lean_ctor_get(v___x_3494_, 4);
                v_env_3496_ = crate::leanh::lean_ctor_get(v___x_3494_, 0);
                v_nextMacroScope_3497_ = crate::leanh::lean_ctor_get(v___x_3494_, 1);
                v_ngen_3498_ = crate::leanh::lean_ctor_get(v___x_3494_, 2);
                v_auxDeclNGen_3499_ = crate::leanh::lean_ctor_get(v___x_3494_, 3);
                v_cache_3500_ = crate::leanh::lean_ctor_get(v___x_3494_, 5);
                v_messages_3501_ = crate::leanh::lean_ctor_get(v___x_3494_, 6);
                v_infoState_3502_ = crate::leanh::lean_ctor_get(v___x_3494_, 7);
                v_snapshotTasks_3503_ = crate::leanh::lean_ctor_get(v___x_3494_, 8);
                v_isSharedCheck_3533_ = (!crate::leanh::lean_is_exclusive(v___x_3494_)) as u8;
                if v_isSharedCheck_3533_ == 0 {
                    v___x_3505_ = v___x_3494_;
                    v_isShared_3506_ = v_isSharedCheck_3533_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3503_);
                    crate::leanh::lean_inc(v_infoState_3502_);
                    crate::leanh::lean_inc(v_messages_3501_);
                    crate::leanh::lean_inc(v_cache_3500_);
                    crate::leanh::lean_inc(v_traceState_3495_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3499_);
                    crate::leanh::lean_inc(v_ngen_3498_);
                    crate::leanh::lean_inc(v_nextMacroScope_3497_);
                    crate::leanh::lean_inc(v_env_3496_);
                    crate::leanh::lean_dec(v___x_3494_);
                    v___x_3505_ = crate::leanh::lean_box(0);
                    v_isShared_3506_ = v_isSharedCheck_3533_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_3507_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3495_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3508_ = crate::leanh::lean_ctor_get(v_traceState_3495_, 0);
                v_isSharedCheck_3532_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3495_)) as u8;
                if v_isSharedCheck_3532_ == 0 {
                    v___x_3510_ = v_traceState_3495_;
                    v_isShared_3511_ = v_isSharedCheck_3532_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_3508_);
                    crate::leanh::lean_dec(v_traceState_3495_);
                    v___x_3510_ = crate::leanh::lean_box(0);
                    v_isShared_3511_ = v_isSharedCheck_3532_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3512_ = crate::leanh::lean_box(0);
                v___x_3513_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__0);
                v___x_3514_ = 0;
                v___x_3515_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg___closed__0;
                v___x_3516_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_3516_, 0, v_cls_3481_);
                crate::leanh::lean_ctor_set(v___x_3516_, 1, v___x_3512_);
                crate::leanh::lean_ctor_set(v___x_3516_, 2, v___x_3515_);
                crate::leanh::lean_ctor_set_float(
                    v___x_3516_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3513_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_3516_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3513_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3516_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3514_,
                );
                v___x_3517_ =
                    l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___closed__1;
                v___x_3518_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3518_, 0, v___x_3516_);
                crate::leanh::lean_ctor_set(v___x_3518_, 1, v_a_3490_);
                crate::leanh::lean_ctor_set(v___x_3518_, 2, v___x_3517_);
                crate::leanh::lean_inc(v_ref_3488_);
                v___x_3519_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3519_, 0, v_ref_3488_);
                crate::leanh::lean_ctor_set(v___x_3519_, 1, v___x_3518_);
                v___x_3520_ = l_Lean_PersistentArray_push___redArg(v_traces_3508_, v___x_3519_);
                if v_isShared_3511_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3510_, 0, v___x_3520_);
                    v___x_3522_ = v___x_3510_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3531_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3520_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3531_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3507_,
                    );
                    v___x_3522_ = v_reuseFailAlloc_3531_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3506_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3505_, 4, v___x_3522_);
                    v___x_3524_ = v___x_3505_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3530_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_env_3496_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3530_, 1, v_nextMacroScope_3497_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3530_, 2, v_ngen_3498_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3530_, 3, v_auxDeclNGen_3499_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3530_, 4, v___x_3522_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3530_, 5, v_cache_3500_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3530_, 6, v_messages_3501_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3530_, 7, v_infoState_3502_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3530_, 8, v_snapshotTasks_3503_);
                    v___x_3524_ = v_reuseFailAlloc_3530_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3525_ = lean_st_ref_set(v___y_3486_, v___x_3524_);
                v___x_3526_ = crate::leanh::lean_box(0);
                if v_isShared_3493_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3492_, 0, v___x_3526_);
                    v___x_3528_ = v___x_3492_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3529_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3529_, 0, v___x_3526_);
                    v___x_3528_ = v_reuseFailAlloc_3529_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3528_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg___boxed(
    mut v_cls_3535_: *mut crate::leanh::LeanObject,
    mut v_msg_3536_: *mut crate::leanh::LeanObject,
    mut v___y_3537_: *mut crate::leanh::LeanObject,
    mut v___y_3538_: *mut crate::leanh::LeanObject,
    mut v___y_3539_: *mut crate::leanh::LeanObject,
    mut v___y_3540_: *mut crate::leanh::LeanObject,
    mut v___y_3541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3542_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(
        v_cls_3535_,
        v_msg_3536_,
        v___y_3537_,
        v___y_3538_,
        v___y_3539_,
        v___y_3540_,
    );
    crate::leanh::lean_dec(v___y_3540_);
    crate::leanh::lean_dec_ref(v___y_3539_);
    crate::leanh::lean_dec(v___y_3538_);
    crate::leanh::lean_dec_ref(v___y_3537_);
    return v_res_3542_;
}
pub unsafe fn _init_l_Lean_Elab_wfRecursion___lam__3___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3544_ = l_Lean_Elab_wfRecursion___lam__3___closed__0;
    v___x_3545_ = l_Lean_stringToMessageData(v___x_3544_);
    return v___x_3545_;
}
pub unsafe fn l_Lean_Elab_wfRecursion___lam__3(
    mut v_fst_3546_: *mut crate::leanh::LeanObject,
    mut v_snd_3547_: *mut crate::leanh::LeanObject,
    mut v_sz_3548_: usize,
    mut v___x_3549_: usize,
    mut v_a_3550_: *mut crate::leanh::LeanObject,
    mut v_fixedArgs_3551_: *mut crate::leanh::LeanObject,
    mut v_fst_3552_: *mut crate::leanh::LeanObject,
    mut v___x_3553_: *mut crate::leanh::LeanObject,
    mut v___x_3554_: *mut crate::leanh::LeanObject,
    mut v___x_3555_: *mut crate::leanh::LeanObject,
    mut v_wfRel_3556_: *mut crate::leanh::LeanObject,
    mut v___y_3557_: *mut crate::leanh::LeanObject,
    mut v___y_3558_: *mut crate::leanh::LeanObject,
    mut v___y_3559_: *mut crate::leanh::LeanObject,
    mut v___y_3560_: *mut crate::leanh::LeanObject,
    mut v___y_3561_: *mut crate::leanh::LeanObject,
    mut v___y_3562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3576_: u8 = 0;
    let mut v___x_3578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3580_: u8 = 0;
    let mut v_unused_3581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3599_: u8 = 0;
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3611_: u8 = 0;
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3624_: u8 = 0;
    let mut v___x_3625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_3630_: u8 = 0;
    let mut v_levelParams_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifiers_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binders_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSectionVars_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_termination_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3640_: u8 = 0;
    let mut v___x_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3647_: u8 = 0;
    let mut v_unused_3648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3650_: u8 = 0;
    let mut v_unused_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3653_: u8 = 0;
    let mut v_unused_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3655_: u8 = 0;
    let mut v_a_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3659_: u8 = 0;
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3663_: u8 = 0;
    let mut v_a_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3691_: u8 = 0;
    let mut v___x_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3695_: u8 = 0;
    let mut v___y_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: u8 = 0;
    let mut v___x_3708_: u8 = 0;
    let mut v___x_3709_: usize = 0;
    let mut v___x_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: usize = 0;
    let mut v___x_3712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3716_: u8 = 0;
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3720_: u8 = 0;
    let mut v_options_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_3722_: u8 = 0;
    let mut v_inheritedTraceOptions_3723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: u8 = 0;
    let mut v___x_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3734_: u8 = 0;
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3738_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3721_ = crate::leanh::lean_ctor_get(v___y_3561_, 2);
                v_hasTrace_3722_ = crate::leanh::lean_ctor_get_uint8(
                    v_options_3721_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_3722_ == 0 {
                    crate::leanh::lean_dec(v___x_3555_);
                    v___y_3697_ = v___y_3557_;
                    v___y_3698_ = v___y_3558_;
                    v___y_3699_ = v___y_3559_;
                    v___y_3700_ = v___y_3560_;
                    v___y_3701_ = v___y_3561_;
                    v___y_3702_ = v___y_3562_;
                    state = 19;
                    continue;
                } else {
                    v_inheritedTraceOptions_3723_ = crate::leanh::lean_ctor_get(v___y_3561_, 13);
                    v___x_3724_ = l_Lean_Elab_wfRecursion___lam__1___closed__1;
                    crate::leanh::lean_inc(v___x_3555_);
                    v___x_3725_ = l_Lean_Name_append(v___x_3724_, v___x_3555_);
                    v___x_3726_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_3723_,
                        v_options_3721_,
                        v___x_3725_,
                    );
                    crate::leanh::lean_dec(v___x_3725_);
                    if v___x_3726_ == 0 {
                        crate::leanh::lean_dec(v___x_3555_);
                        v___y_3697_ = v___y_3557_;
                        v___y_3698_ = v___y_3558_;
                        v___y_3699_ = v___y_3559_;
                        v___y_3700_ = v___y_3560_;
                        v___y_3701_ = v___y_3561_;
                        v___y_3702_ = v___y_3562_;
                        state = 19;
                        continue;
                    } else {
                        v___x_3727_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_wfRecursion___lam__3___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_wfRecursion___lam__3___closed__1_once
                            ),
                            _init_l_Lean_Elab_wfRecursion___lam__3___closed__1,
                        );
                        crate::leanh::lean_inc_ref(v_wfRel_3556_);
                        v___x_3728_ = l_Lean_MessageData_ofExpr(v_wfRel_3556_);
                        v___x_3729_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3729_, 0, v___x_3727_);
                        crate::leanh::lean_ctor_set(v___x_3729_, 1, v___x_3728_);
                        v___x_3730_ =
                            l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(
                                v___x_3555_,
                                v___x_3729_,
                                v___y_3559_,
                                v___y_3560_,
                                v___y_3561_,
                                v___y_3562_,
                            );
                        if crate::leanh::lean_obj_tag(v___x_3730_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_3730_, 1);
                            v___y_3697_ = v___y_3557_;
                            v___y_3698_ = v___y_3558_;
                            v___y_3699_ = v___y_3559_;
                            v___y_3700_ = v___y_3560_;
                            v___y_3701_ = v___y_3561_;
                            v___y_3702_ = v___y_3562_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_wfRel_3556_);
                            crate::leanh::lean_dec_ref(v___x_3553_);
                            crate::leanh::lean_dec_ref(v_fst_3552_);
                            crate::leanh::lean_dec_ref(v_fixedArgs_3551_);
                            crate::leanh::lean_dec_ref(v_a_3550_);
                            crate::leanh::lean_dec_ref(v_fst_3546_);
                            v_a_3731_ = crate::leanh::lean_ctor_get(v___x_3730_, 0);
                            v_isSharedCheck_3738_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3730_)) as u8;
                            if v_isSharedCheck_3738_ == 0 {
                                v___x_3733_ = v___x_3730_;
                                v_isShared_3734_ = v_isSharedCheck_3738_;
                                state = 22;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3731_);
                                crate::leanh::lean_dec(v___x_3730_);
                                v___x_3733_ = crate::leanh::lean_box(0);
                                v_isShared_3734_ = v_isSharedCheck_3738_;
                                state = 22;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3573_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(
                    v___y_3567_,
                    v___y_3570_,
                    v___y_3568_,
                );
                v_isSharedCheck_3580_ = (!crate::leanh::lean_is_exclusive(v___x_3573_)) as u8;
                if v_isSharedCheck_3580_ == 0 {
                    v_unused_3581_ = crate::leanh::lean_ctor_get(v___x_3573_, 0);
                    crate::leanh::lean_dec(v_unused_3581_);
                    v___x_3575_ = v___x_3573_;
                    v_isShared_3576_ = v_isSharedCheck_3580_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3573_);
                    v___x_3575_ = crate::leanh::lean_box(0);
                    v_isShared_3576_ = v_isSharedCheck_3580_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3576_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3575_, 1);
                    crate::leanh::lean_ctor_set(v___x_3575_, 0, v_a_3572_);
                    v___x_3578_ = v___x_3575_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3579_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3572_);
                    v___x_3578_ = v_reuseFailAlloc_3579_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3578_;
            }
            4 => {
                if crate::leanh::lean_obj_tag(v___y_3590_) == 0 {
                    v_a_3591_ = crate::leanh::lean_ctor_get(v___y_3590_, 0);
                    crate::leanh::lean_inc(v_a_3591_);
                    crate::leanh::lean_dec_ref_known(v___y_3590_, 1);
                    v___x_3592_ = lean_st_ref_get(v___y_3586_);
                    v___x_3593_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(
                        v___y_3585_,
                        v___y_3588_,
                        v___y_3586_,
                    );
                    crate::leanh::lean_dec_ref(v___x_3593_);
                    v_env_3594_ = crate::leanh::lean_ctor_get(v___x_3592_, 0);
                    crate::leanh::lean_inc_ref_n(v_env_3594_, 2);
                    crate::leanh::lean_dec(v___x_3592_);
                    v___x_3595_ = l_Lean_Meta_unfoldDeclsFrom(
                        v_env_3594_,
                        v_a_3591_,
                        v___y_3583_,
                        v___y_3586_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3595_) == 0 {
                        v_a_3596_ = crate::leanh::lean_ctor_get(v___x_3595_, 0);
                        v_isSharedCheck_3655_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3595_)) as u8;
                        if v_isSharedCheck_3655_ == 0 {
                            v___x_3598_ = v___x_3595_;
                            v_isShared_3599_ = v_isSharedCheck_3655_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3596_);
                            crate::leanh::lean_dec(v___x_3595_);
                            v___x_3598_ = crate::leanh::lean_box(0);
                            v_isShared_3599_ = v_isSharedCheck_3655_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_env_3594_);
                        crate::leanh::lean_dec_ref(v_fst_3546_);
                        v_a_3656_ = crate::leanh::lean_ctor_get(v___x_3595_, 0);
                        v_isSharedCheck_3663_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3595_)) as u8;
                        if v_isSharedCheck_3663_ == 0 {
                            v___x_3658_ = v___x_3595_;
                            v_isShared_3659_ = v_isSharedCheck_3663_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3656_);
                            crate::leanh::lean_dec(v___x_3595_);
                            v___x_3658_ = crate::leanh::lean_box(0);
                            v_isShared_3659_ = v_isSharedCheck_3663_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_fst_3546_);
                    v_a_3664_ = crate::leanh::lean_ctor_get(v___y_3590_, 0);
                    crate::leanh::lean_inc(v_a_3664_);
                    crate::leanh::lean_dec_ref_known(v___y_3590_, 1);
                    v___y_3565_ = v___y_3583_;
                    v___y_3566_ = v___y_3584_;
                    v___y_3567_ = v___y_3585_;
                    v___y_3568_ = v___y_3586_;
                    v___y_3569_ = v___y_3587_;
                    v___y_3570_ = v___y_3588_;
                    v___y_3571_ = v___y_3589_;
                    v_a_3572_ = v_a_3664_;
                    state = 1;
                    continue;
                }
            }
            5 => {
                v___x_3600_ = lean_st_ref_take(v___y_3586_);
                v_env_3601_ = crate::leanh::lean_ctor_get(v___x_3600_, 0);
                v_nextMacroScope_3602_ = crate::leanh::lean_ctor_get(v___x_3600_, 1);
                v_ngen_3603_ = crate::leanh::lean_ctor_get(v___x_3600_, 2);
                v_auxDeclNGen_3604_ = crate::leanh::lean_ctor_get(v___x_3600_, 3);
                v_traceState_3605_ = crate::leanh::lean_ctor_get(v___x_3600_, 4);
                v_messages_3606_ = crate::leanh::lean_ctor_get(v___x_3600_, 6);
                v_infoState_3607_ = crate::leanh::lean_ctor_get(v___x_3600_, 7);
                v_snapshotTasks_3608_ = crate::leanh::lean_ctor_get(v___x_3600_, 8);
                v_isSharedCheck_3653_ = (!crate::leanh::lean_is_exclusive(v___x_3600_)) as u8;
                if v_isSharedCheck_3653_ == 0 {
                    v_unused_3654_ = crate::leanh::lean_ctor_get(v___x_3600_, 5);
                    crate::leanh::lean_dec(v_unused_3654_);
                    v___x_3610_ = v___x_3600_;
                    v_isShared_3611_ = v_isSharedCheck_3653_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3608_);
                    crate::leanh::lean_inc(v_infoState_3607_);
                    crate::leanh::lean_inc(v_messages_3606_);
                    crate::leanh::lean_inc(v_traceState_3605_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3604_);
                    crate::leanh::lean_inc(v_ngen_3603_);
                    crate::leanh::lean_inc(v_nextMacroScope_3602_);
                    crate::leanh::lean_inc(v_env_3601_);
                    crate::leanh::lean_dec(v___x_3600_);
                    v___x_3610_ = crate::leanh::lean_box(0);
                    v_isShared_3611_ = v_isSharedCheck_3653_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3612_ = l_Lean_copyExtraModUses(v_env_3594_, v_env_3601_);
                v___x_3613_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
                if v_isShared_3611_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3610_, 5, v___x_3613_);
                    crate::leanh::lean_ctor_set(v___x_3610_, 0, v___x_3612_);
                    v___x_3615_ = v___x_3610_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3652_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3612_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 1, v_nextMacroScope_3602_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 2, v_ngen_3603_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 3, v_auxDeclNGen_3604_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 4, v_traceState_3605_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 5, v___x_3613_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 6, v_messages_3606_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 7, v_infoState_3607_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3652_, 8, v_snapshotTasks_3608_);
                    v___x_3615_ = v_reuseFailAlloc_3652_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3616_ = lean_st_ref_set(v___y_3586_, v___x_3615_);
                v___x_3617_ = lean_st_ref_take(v___y_3588_);
                v_mctx_3618_ = crate::leanh::lean_ctor_get(v___x_3617_, 0);
                v_zetaDeltaFVarIds_3619_ = crate::leanh::lean_ctor_get(v___x_3617_, 2);
                v_postponed_3620_ = crate::leanh::lean_ctor_get(v___x_3617_, 3);
                v_diag_3621_ = crate::leanh::lean_ctor_get(v___x_3617_, 4);
                v_isSharedCheck_3650_ = (!crate::leanh::lean_is_exclusive(v___x_3617_)) as u8;
                if v_isSharedCheck_3650_ == 0 {
                    v_unused_3651_ = crate::leanh::lean_ctor_get(v___x_3617_, 1);
                    crate::leanh::lean_dec(v_unused_3651_);
                    v___x_3623_ = v___x_3617_;
                    v_isShared_3624_ = v_isSharedCheck_3650_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_3621_);
                    crate::leanh::lean_inc(v_postponed_3620_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_3619_);
                    crate::leanh::lean_inc(v_mctx_3618_);
                    crate::leanh::lean_dec(v___x_3617_);
                    v___x_3623_ = crate::leanh::lean_box(0);
                    v_isShared_3624_ = v_isSharedCheck_3650_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_3625_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once), _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
                if v_isShared_3624_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3623_, 1, v___x_3625_);
                    v___x_3627_ = v___x_3623_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3649_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_mctx_3618_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3649_, 1, v___x_3625_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3649_,
                        2,
                        v_zetaDeltaFVarIds_3619_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3649_, 3, v_postponed_3620_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3649_, 4, v_diag_3621_);
                    v___x_3627_ = v_reuseFailAlloc_3649_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3628_ = lean_st_ref_set(v___y_3588_, v___x_3627_);
                v_ref_3629_ = crate::leanh::lean_ctor_get(v_fst_3546_, 0);
                v_kind_3630_ = crate::leanh::lean_ctor_get_uint8(
                    v_fst_3546_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                );
                v_levelParams_3631_ = crate::leanh::lean_ctor_get(v_fst_3546_, 1);
                v_modifiers_3632_ = crate::leanh::lean_ctor_get(v_fst_3546_, 2);
                v_declName_3633_ = crate::leanh::lean_ctor_get(v_fst_3546_, 3);
                v_binders_3634_ = crate::leanh::lean_ctor_get(v_fst_3546_, 4);
                v_numSectionVars_3635_ = crate::leanh::lean_ctor_get(v_fst_3546_, 5);
                v_type_3636_ = crate::leanh::lean_ctor_get(v_fst_3546_, 6);
                v_termination_3637_ = crate::leanh::lean_ctor_get(v_fst_3546_, 8);
                v_isSharedCheck_3647_ = (!crate::leanh::lean_is_exclusive(v_fst_3546_)) as u8;
                if v_isSharedCheck_3647_ == 0 {
                    v_unused_3648_ = crate::leanh::lean_ctor_get(v_fst_3546_, 7);
                    crate::leanh::lean_dec(v_unused_3648_);
                    v___x_3639_ = v_fst_3546_;
                    v_isShared_3640_ = v_isSharedCheck_3647_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_termination_3637_);
                    crate::leanh::lean_inc(v_type_3636_);
                    crate::leanh::lean_inc(v_numSectionVars_3635_);
                    crate::leanh::lean_inc(v_binders_3634_);
                    crate::leanh::lean_inc(v_declName_3633_);
                    crate::leanh::lean_inc(v_modifiers_3632_);
                    crate::leanh::lean_inc(v_levelParams_3631_);
                    crate::leanh::lean_inc(v_ref_3629_);
                    crate::leanh::lean_dec(v_fst_3546_);
                    v___x_3639_ = crate::leanh::lean_box(0);
                    v_isShared_3640_ = v_isSharedCheck_3647_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_3640_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3639_, 7, v_a_3596_);
                    v___x_3642_ = v___x_3639_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3646_ = crate::leanh::lean_alloc_ctor(0, 9, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_ref_3629_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 1, v_levelParams_3631_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 2, v_modifiers_3632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 3, v_declName_3633_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 4, v_binders_3634_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 5, v_numSectionVars_3635_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 6, v_type_3636_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 7, v_a_3596_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3646_, 8, v_termination_3637_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_3646_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                        v_kind_3630_,
                    );
                    v___x_3642_ = v_reuseFailAlloc_3646_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3599_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3598_, 0, v___x_3642_);
                    v___x_3644_ = v___x_3598_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3645_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 0, v___x_3642_);
                    v___x_3644_ = v_reuseFailAlloc_3645_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3644_;
            }
            13 => {
                if v_isShared_3659_ == 0 {
                    v___x_3661_ = v___x_3658_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3662_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_a_3656_);
                    v___x_3661_ = v_reuseFailAlloc_3662_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3661_;
            }
            15 => {
                v___x_3672_ = lean_st_ref_get(v___y_3671_);
                v_env_3673_ = crate::leanh::lean_ctor_get(v___x_3672_, 0);
                crate::leanh::lean_inc_ref(v_env_3673_);
                crate::leanh::lean_dec(v___x_3672_);
                v___x_3674_ =
                    l_Lean_Elab_addAsAxiom___redArg(v_snd_3547_, v___y_3670_, v___y_3671_);
                if crate::leanh::lean_obj_tag(v___x_3674_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3674_, 1);
                    v___x_3675_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__10(v_sz_3548_, v___x_3549_, v_a_3550_);
                    crate::leanh::lean_inc_ref(v_fst_3546_);
                    v___x_3676_ = l_Lean_Elab_WF_mkFix(
                        v_fst_3546_,
                        v_fixedArgs_3551_,
                        v_fst_3552_,
                        v_wfRel_3556_,
                        v___x_3553_,
                        v___x_3675_,
                        v___y_3666_,
                        v___y_3667_,
                        v___y_3668_,
                        v___y_3669_,
                        v___y_3670_,
                        v___y_3671_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3676_) == 0 {
                        v_a_3677_ = crate::leanh::lean_ctor_get(v___x_3676_, 0);
                        crate::leanh::lean_inc(v_a_3677_);
                        crate::leanh::lean_dec_ref_known(v___x_3676_, 1);
                        v___x_3678_ =
                            l_Lean_Elab_eraseRecAppSyntaxExpr(v_a_3677_, v___y_3670_, v___y_3671_);
                        v___y_3583_ = v___y_3670_;
                        v___y_3584_ = v___y_3667_;
                        v___y_3585_ = v_env_3673_;
                        v___y_3586_ = v___y_3671_;
                        v___y_3587_ = v___y_3666_;
                        v___y_3588_ = v___y_3669_;
                        v___y_3589_ = v___y_3668_;
                        v___y_3590_ = v___x_3678_;
                        state = 4;
                        continue;
                    } else {
                        v___y_3583_ = v___y_3670_;
                        v___y_3584_ = v___y_3667_;
                        v___y_3585_ = v_env_3673_;
                        v___y_3586_ = v___y_3671_;
                        v___y_3587_ = v___y_3666_;
                        v___y_3588_ = v___y_3669_;
                        v___y_3589_ = v___y_3668_;
                        v___y_3590_ = v___x_3676_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_wfRel_3556_);
                    crate::leanh::lean_dec_ref(v___x_3553_);
                    crate::leanh::lean_dec_ref(v_fst_3552_);
                    crate::leanh::lean_dec_ref(v_fixedArgs_3551_);
                    crate::leanh::lean_dec_ref(v_a_3550_);
                    crate::leanh::lean_dec_ref(v_fst_3546_);
                    v_a_3679_ = crate::leanh::lean_ctor_get(v___x_3674_, 0);
                    crate::leanh::lean_inc(v_a_3679_);
                    crate::leanh::lean_dec_ref_known(v___x_3674_, 1);
                    v___y_3565_ = v___y_3670_;
                    v___y_3566_ = v___y_3667_;
                    v___y_3567_ = v_env_3673_;
                    v___y_3568_ = v___y_3671_;
                    v___y_3569_ = v___y_3666_;
                    v___y_3570_ = v___y_3669_;
                    v___y_3571_ = v___y_3668_;
                    v_a_3572_ = v_a_3679_;
                    state = 1;
                    continue;
                }
            }
            16 => {
                if crate::leanh::lean_obj_tag(v___y_3687_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_3687_, 1);
                    v___y_3666_ = v___y_3682_;
                    v___y_3667_ = v___y_3684_;
                    v___y_3668_ = v___y_3686_;
                    v___y_3669_ = v___y_3683_;
                    v___y_3670_ = v___y_3685_;
                    v___y_3671_ = v___y_3681_;
                    state = 15;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_wfRel_3556_);
                    crate::leanh::lean_dec_ref(v___x_3553_);
                    crate::leanh::lean_dec_ref(v_fst_3552_);
                    crate::leanh::lean_dec_ref(v_fixedArgs_3551_);
                    crate::leanh::lean_dec_ref(v_a_3550_);
                    crate::leanh::lean_dec_ref(v_fst_3546_);
                    v_a_3688_ = crate::leanh::lean_ctor_get(v___y_3687_, 0);
                    v_isSharedCheck_3695_ = (!crate::leanh::lean_is_exclusive(v___y_3687_)) as u8;
                    if v_isSharedCheck_3695_ == 0 {
                        v___x_3690_ = v___y_3687_;
                        v_isShared_3691_ = v_isSharedCheck_3695_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3688_);
                        crate::leanh::lean_dec(v___y_3687_);
                        v___x_3690_ = crate::leanh::lean_box(0);
                        v_isShared_3691_ = v_isSharedCheck_3695_;
                        state = 17;
                        continue;
                    }
                }
            }
            17 => {
                if v_isShared_3691_ == 0 {
                    v___x_3693_ = v___x_3690_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3694_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3688_);
                    v___x_3693_ = v_reuseFailAlloc_3694_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3693_;
            }
            19 => {
                crate::leanh::lean_inc_ref(v_wfRel_3556_);
                v___x_3703_ = l_Lean_Elab_WF_isNatLtWF(
                    v_wfRel_3556_,
                    v___y_3699_,
                    v___y_3700_,
                    v___y_3701_,
                    v___y_3702_,
                );
                if crate::leanh::lean_obj_tag(v___x_3703_) == 0 {
                    v_a_3704_ = crate::leanh::lean_ctor_get(v___x_3703_, 0);
                    crate::leanh::lean_inc(v_a_3704_);
                    crate::leanh::lean_dec_ref_known(v___x_3703_, 1);
                    if crate::leanh::lean_obj_tag(v_a_3704_) == 0 {
                        v___x_3705_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3706_ = lean_array_get_size(v_a_3550_);
                        v___x_3707_ = lean_nat_dec_lt(v___x_3705_, v___x_3706_);
                        if v___x_3707_ == 0 {
                            v___y_3666_ = v___y_3697_;
                            v___y_3667_ = v___y_3698_;
                            v___y_3668_ = v___y_3699_;
                            v___y_3669_ = v___y_3700_;
                            v___y_3670_ = v___y_3701_;
                            v___y_3671_ = v___y_3702_;
                            state = 15;
                            continue;
                        } else {
                            v___x_3708_ = lean_nat_dec_le(v___x_3706_, v___x_3706_);
                            if v___x_3708_ == 0 {
                                if v___x_3707_ == 0 {
                                    v___y_3666_ = v___y_3697_;
                                    v___y_3667_ = v___y_3698_;
                                    v___y_3668_ = v___y_3699_;
                                    v___y_3669_ = v___y_3700_;
                                    v___y_3670_ = v___y_3701_;
                                    v___y_3671_ = v___y_3702_;
                                    state = 15;
                                    continue;
                                } else {
                                    v___x_3709_ = lean_usize_of_nat(v___x_3706_);
                                    v___x_3710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v_a_3550_, v___x_3549_, v___x_3709_, v___x_3554_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
                                    v___y_3681_ = v___y_3702_;
                                    v___y_3682_ = v___y_3697_;
                                    v___y_3683_ = v___y_3700_;
                                    v___y_3684_ = v___y_3698_;
                                    v___y_3685_ = v___y_3701_;
                                    v___y_3686_ = v___y_3699_;
                                    v___y_3687_ = v___x_3710_;
                                    state = 16;
                                    continue;
                                }
                            } else {
                                v___x_3711_ = lean_usize_of_nat(v___x_3706_);
                                v___x_3712_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_wfRecursion_spec__13(v_a_3550_, v___x_3549_, v___x_3711_, v___x_3554_, v___y_3697_, v___y_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
                                v___y_3681_ = v___y_3702_;
                                v___y_3682_ = v___y_3697_;
                                v___y_3683_ = v___y_3700_;
                                v___y_3684_ = v___y_3698_;
                                v___y_3685_ = v___y_3701_;
                                v___y_3686_ = v___y_3699_;
                                v___y_3687_ = v___x_3712_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_3704_, 1);
                        v___y_3666_ = v___y_3697_;
                        v___y_3667_ = v___y_3698_;
                        v___y_3668_ = v___y_3699_;
                        v___y_3669_ = v___y_3700_;
                        v___y_3670_ = v___y_3701_;
                        v___y_3671_ = v___y_3702_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_wfRel_3556_);
                    crate::leanh::lean_dec_ref(v___x_3553_);
                    crate::leanh::lean_dec_ref(v_fst_3552_);
                    crate::leanh::lean_dec_ref(v_fixedArgs_3551_);
                    crate::leanh::lean_dec_ref(v_a_3550_);
                    crate::leanh::lean_dec_ref(v_fst_3546_);
                    v_a_3713_ = crate::leanh::lean_ctor_get(v___x_3703_, 0);
                    v_isSharedCheck_3720_ = (!crate::leanh::lean_is_exclusive(v___x_3703_)) as u8;
                    if v_isSharedCheck_3720_ == 0 {
                        v___x_3715_ = v___x_3703_;
                        v_isShared_3716_ = v_isSharedCheck_3720_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3713_);
                        crate::leanh::lean_dec(v___x_3703_);
                        v___x_3715_ = crate::leanh::lean_box(0);
                        v_isShared_3716_ = v_isSharedCheck_3720_;
                        state = 20;
                        continue;
                    }
                }
            }
            20 => {
                if v_isShared_3716_ == 0 {
                    v___x_3718_ = v___x_3715_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3719_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_a_3713_);
                    v___x_3718_ = v_reuseFailAlloc_3719_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3718_;
            }
            22 => {
                if v_isShared_3734_ == 0 {
                    v___x_3736_ = v___x_3733_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3737_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
                    v___x_3736_ = v_reuseFailAlloc_3737_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3736_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_wfRecursion___lam__3___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_3739_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_snd_3740_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_sz_3741_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_3742_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_a_3743_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_fixedArgs_3744_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_fst_3745_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_3746_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_3747_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_3748_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_wfRel_3749_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_3750_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_3751_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_3752_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_3753_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3754_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3755_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_3756_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_sz_boxed_3757_: usize = 0;
    let mut v___x_47731__boxed_3758_: usize = 0;
    let mut v_res_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3757_ = crate::leanh::lean_unbox_usize(v_sz_3741_);
    crate::leanh::lean_dec(v_sz_3741_);
    v___x_47731__boxed_3758_ = crate::leanh::lean_unbox_usize(v___x_3742_);
    crate::leanh::lean_dec(v___x_3742_);
    v_res_3759_ = l_Lean_Elab_wfRecursion___lam__3(
        v_fst_3739_,
        v_snd_3740_,
        v_sz_boxed_3757_,
        v___x_47731__boxed_3758_,
        v_a_3743_,
        v_fixedArgs_3744_,
        v_fst_3745_,
        v___x_3746_,
        v___x_3747_,
        v___x_3748_,
        v_wfRel_3749_,
        v___y_3750_,
        v___y_3751_,
        v___y_3752_,
        v___y_3753_,
        v___y_3754_,
        v___y_3755_,
    );
    crate::leanh::lean_dec(v___y_3755_);
    crate::leanh::lean_dec_ref(v___y_3754_);
    crate::leanh::lean_dec(v___y_3753_);
    crate::leanh::lean_dec_ref(v___y_3752_);
    crate::leanh::lean_dec(v___y_3751_);
    crate::leanh::lean_dec_ref(v___y_3750_);
    crate::leanh::lean_dec_ref(v_snd_3740_);
    return v_res_3759_;
}
pub unsafe fn _init_l_Lean_Elab_wfRecursion___lam__4___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3761_ = l_Lean_Elab_wfRecursion___lam__4___closed__0;
    v___x_3762_ = l_Lean_stringToMessageData(v___x_3761_);
    return v___x_3762_;
}
pub unsafe fn l_Lean_Elab_wfRecursion___lam__4(
    mut v_sz_3763_: usize,
    mut v___x_3764_: usize,
    mut v_a_3765_: *mut crate::leanh::LeanObject,
    mut v_fst_3766_: *mut crate::leanh::LeanObject,
    mut v_snd_3767_: *mut crate::leanh::LeanObject,
    mut v_fst_3768_: *mut crate::leanh::LeanObject,
    mut v___x_3769_: *mut crate::leanh::LeanObject,
    mut v___x_3770_: *mut crate::leanh::LeanObject,
    mut v_declName_3771_: *mut crate::leanh::LeanObject,
    mut v_fst_3772_: *mut crate::leanh::LeanObject,
    mut v_wf_3773_: *mut crate::leanh::LeanObject,
    mut v_fixedArgs_3774_: *mut crate::leanh::LeanObject,
    mut v_type_3775_: *mut crate::leanh::LeanObject,
    mut v___y_3776_: *mut crate::leanh::LeanObject,
    mut v___y_3777_: *mut crate::leanh::LeanObject,
    mut v___y_3778_: *mut crate::leanh::LeanObject,
    mut v___y_3779_: *mut crate::leanh::LeanObject,
    mut v___y_3780_: *mut crate::leanh::LeanObject,
    mut v___y_3781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: u8 = 0;
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3806_: u8 = 0;
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3810_: u8 = 0;
    let mut v_a_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3814_: u8 = 0;
    let mut v___x_3816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3818_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3783_ = l_Lean_Meta_whnfForall(
                    v_type_3775_,
                    v___y_3778_,
                    v___y_3779_,
                    v___y_3780_,
                    v___y_3781_,
                );
                if crate::leanh::lean_obj_tag(v___x_3783_) == 0 {
                    v_a_3784_ = crate::leanh::lean_ctor_get(v___x_3783_, 0);
                    crate::leanh::lean_inc(v_a_3784_);
                    crate::leanh::lean_dec_ref_known(v___x_3783_, 1);
                    v___x_3798_ = l_Lean_Expr_isForall(v_a_3784_);
                    if v___x_3798_ == 0 {
                        crate::leanh::lean_dec_ref(v_fixedArgs_3774_);
                        crate::leanh::lean_dec_ref(v_wf_3773_);
                        crate::leanh::lean_dec_ref(v_fst_3772_);
                        crate::leanh::lean_dec(v_declName_3771_);
                        crate::leanh::lean_dec(v___x_3770_);
                        crate::leanh::lean_dec_ref(v_fst_3768_);
                        crate::leanh::lean_dec_ref(v_snd_3767_);
                        crate::leanh::lean_dec_ref(v_fst_3766_);
                        crate::leanh::lean_dec_ref(v_a_3765_);
                        v___x_3799_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_wfRecursion___lam__4___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_wfRecursion___lam__4___closed__1_once
                            ),
                            _init_l_Lean_Elab_wfRecursion___lam__4___closed__1,
                        );
                        v___x_3800_ = l_Lean_MessageData_ofExpr(v_a_3784_);
                        v___x_3801_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3801_, 0, v___x_3799_);
                        crate::leanh::lean_ctor_set(v___x_3801_, 1, v___x_3800_);
                        v___x_3802_ =
                            l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(
                                v___x_3801_,
                                v___y_3776_,
                                v___y_3777_,
                                v___y_3778_,
                                v___y_3779_,
                                v___y_3780_,
                                v___y_3781_,
                            );
                        v_a_3803_ = crate::leanh::lean_ctor_get(v___x_3802_, 0);
                        v_isSharedCheck_3810_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3802_)) as u8;
                        if v_isSharedCheck_3810_ == 0 {
                            v___x_3805_ = v___x_3802_;
                            v_isShared_3806_ = v_isSharedCheck_3810_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3803_);
                            crate::leanh::lean_dec(v___x_3802_);
                            v___x_3805_ = crate::leanh::lean_box(0);
                            v_isShared_3806_ = v_isSharedCheck_3810_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___y_3786_ = v___y_3776_;
                        v___y_3787_ = v___y_3777_;
                        v___y_3788_ = v___y_3778_;
                        v___y_3789_ = v___y_3779_;
                        v___y_3790_ = v___y_3780_;
                        v___y_3791_ = v___y_3781_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_fixedArgs_3774_);
                    crate::leanh::lean_dec_ref(v_wf_3773_);
                    crate::leanh::lean_dec_ref(v_fst_3772_);
                    crate::leanh::lean_dec(v_declName_3771_);
                    crate::leanh::lean_dec(v___x_3770_);
                    crate::leanh::lean_dec_ref(v_fst_3768_);
                    crate::leanh::lean_dec_ref(v_snd_3767_);
                    crate::leanh::lean_dec_ref(v_fst_3766_);
                    crate::leanh::lean_dec_ref(v_a_3765_);
                    v_a_3811_ = crate::leanh::lean_ctor_get(v___x_3783_, 0);
                    v_isSharedCheck_3818_ = (!crate::leanh::lean_is_exclusive(v___x_3783_)) as u8;
                    if v_isSharedCheck_3818_ == 0 {
                        v___x_3813_ = v___x_3783_;
                        v_isShared_3814_ = v_isSharedCheck_3818_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3811_);
                        crate::leanh::lean_dec(v___x_3783_);
                        v___x_3813_ = crate::leanh::lean_box(0);
                        v_isShared_3814_ = v_isSharedCheck_3818_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3792_ = l_Lean_Expr_bindingDomain_x21(v_a_3784_);
                crate::leanh::lean_dec(v_a_3784_);
                crate::leanh::lean_inc_ref(v_a_3765_);
                v___x_3793_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__5(v_sz_3763_, v___x_3764_, v_a_3765_);
                v___x_3794_ = crate::leanh::lean_box_usize(v_sz_3763_);
                v___x_3795_ = crate::leanh::lean_box_usize(v___x_3764_);
                crate::leanh::lean_inc_ref(v___x_3793_);
                crate::leanh::lean_inc_ref(v_fst_3768_);
                crate::leanh::lean_inc_ref(v_fixedArgs_3774_);
                v___f_3796_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_wfRecursion___lam__3___boxed as *mut core::ffi::c_void,
                    18,
                    10,
                );
                crate::leanh::lean_closure_set(v___f_3796_, 0, v_fst_3766_);
                crate::leanh::lean_closure_set(v___f_3796_, 1, v_snd_3767_);
                crate::leanh::lean_closure_set(v___f_3796_, 2, v___x_3794_);
                crate::leanh::lean_closure_set(v___f_3796_, 3, v___x_3795_);
                crate::leanh::lean_closure_set(v___f_3796_, 4, v_a_3765_);
                crate::leanh::lean_closure_set(v___f_3796_, 5, v_fixedArgs_3774_);
                crate::leanh::lean_closure_set(v___f_3796_, 6, v_fst_3768_);
                crate::leanh::lean_closure_set(v___f_3796_, 7, v___x_3793_);
                crate::leanh::lean_closure_set(v___f_3796_, 8, v___x_3769_);
                crate::leanh::lean_closure_set(v___f_3796_, 9, v___x_3770_);
                v___x_3797_ = l_Lean_Elab_WF_elabWFRel___redArg(
                    v___x_3793_,
                    v_declName_3771_,
                    v_fst_3772_,
                    v_fixedArgs_3774_,
                    v_fst_3768_,
                    v___x_3792_,
                    v_wf_3773_,
                    v___f_3796_,
                    v___y_3786_,
                    v___y_3787_,
                    v___y_3788_,
                    v___y_3789_,
                    v___y_3790_,
                    v___y_3791_,
                );
                return v___x_3797_;
            }
            2 => {
                if v_isShared_3806_ == 0 {
                    v___x_3808_ = v___x_3805_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3809_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3803_);
                    v___x_3808_ = v_reuseFailAlloc_3809_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3808_;
            }
            4 => {
                if v_isShared_3814_ == 0 {
                    v___x_3816_ = v___x_3813_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3817_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3817_, 0, v_a_3811_);
                    v___x_3816_ = v_reuseFailAlloc_3817_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3816_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_wfRecursion___lam__4___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_3819_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_3820_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_a_3821_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_fst_3822_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_snd_3823_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_fst_3824_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_3825_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_3826_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_declName_3827_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_fst_3828_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_wf_3829_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_fixedArgs_3830_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_type_3831_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_3832_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_3833_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_3834_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_3835_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_3836_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_3837_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_3838_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_sz_boxed_3839_: usize = 0;
    let mut v___x_48089__boxed_3840_: usize = 0;
    let mut v_res_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3839_ = crate::leanh::lean_unbox_usize(v_sz_3819_);
    crate::leanh::lean_dec(v_sz_3819_);
    v___x_48089__boxed_3840_ = crate::leanh::lean_unbox_usize(v___x_3820_);
    crate::leanh::lean_dec(v___x_3820_);
    v_res_3841_ = l_Lean_Elab_wfRecursion___lam__4(
        v_sz_boxed_3839_,
        v___x_48089__boxed_3840_,
        v_a_3821_,
        v_fst_3822_,
        v_snd_3823_,
        v_fst_3824_,
        v___x_3825_,
        v___x_3826_,
        v_declName_3827_,
        v_fst_3828_,
        v_wf_3829_,
        v_fixedArgs_3830_,
        v_type_3831_,
        v___y_3832_,
        v___y_3833_,
        v___y_3834_,
        v___y_3835_,
        v___y_3836_,
        v___y_3837_,
    );
    crate::leanh::lean_dec(v___y_3837_);
    crate::leanh::lean_dec_ref(v___y_3836_);
    crate::leanh::lean_dec(v___y_3835_);
    crate::leanh::lean_dec_ref(v___y_3834_);
    crate::leanh::lean_dec(v___y_3833_);
    crate::leanh::lean_dec_ref(v___y_3832_);
    return v_res_3841_;
}
pub unsafe fn l_Lean_Elab_wfRecursion___lam__5(
    mut v_a_3842_: *mut crate::leanh::LeanObject,
    mut v_fst_3843_: *mut crate::leanh::LeanObject,
    mut v_fst_3844_: *mut crate::leanh::LeanObject,
    mut v_fst_3845_: *mut crate::leanh::LeanObject,
    mut v___y_3846_: *mut crate::leanh::LeanObject,
    mut v___y_3847_: *mut crate::leanh::LeanObject,
    mut v___y_3848_: *mut crate::leanh::LeanObject,
    mut v___y_3849_: *mut crate::leanh::LeanObject,
    mut v___y_3850_: *mut crate::leanh::LeanObject,
    mut v___y_3851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3853_ = l_Lean_Elab_WF_guessLex(
        v_a_3842_,
        v_fst_3843_,
        v_fst_3844_,
        v_fst_3845_,
        v___y_3848_,
        v___y_3849_,
        v___y_3850_,
        v___y_3851_,
    );
    return v___x_3853_;
}
pub unsafe fn l_Lean_Elab_wfRecursion___lam__5___boxed(
    mut v_a_3854_: *mut crate::leanh::LeanObject,
    mut v_fst_3855_: *mut crate::leanh::LeanObject,
    mut v_fst_3856_: *mut crate::leanh::LeanObject,
    mut v_fst_3857_: *mut crate::leanh::LeanObject,
    mut v___y_3858_: *mut crate::leanh::LeanObject,
    mut v___y_3859_: *mut crate::leanh::LeanObject,
    mut v___y_3860_: *mut crate::leanh::LeanObject,
    mut v___y_3861_: *mut crate::leanh::LeanObject,
    mut v___y_3862_: *mut crate::leanh::LeanObject,
    mut v___y_3863_: *mut crate::leanh::LeanObject,
    mut v___y_3864_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3865_ = l_Lean_Elab_wfRecursion___lam__5(
        v_a_3854_,
        v_fst_3855_,
        v_fst_3856_,
        v_fst_3857_,
        v___y_3858_,
        v___y_3859_,
        v___y_3860_,
        v___y_3861_,
        v___y_3862_,
        v___y_3863_,
    );
    crate::leanh::lean_dec(v___y_3863_);
    crate::leanh::lean_dec_ref(v___y_3862_);
    crate::leanh::lean_dec(v___y_3861_);
    crate::leanh::lean_dec_ref(v___y_3860_);
    crate::leanh::lean_dec(v___y_3859_);
    crate::leanh::lean_dec_ref(v___y_3858_);
    return v_res_3865_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(
    mut v___y_3866_: *mut crate::leanh::LeanObject,
    mut v_isExporting_3867_: u8,
    mut v___x_3868_: *mut crate::leanh::LeanObject,
    mut v___y_3869_: *mut crate::leanh::LeanObject,
    mut v___x_3870_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_3871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3884_: u8 = 0;
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3896_: u8 = 0;
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3903_: u8 = 0;
    let mut v_unused_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3906_: u8 = 0;
    let mut v_unused_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3873_ = lean_st_ref_take(v___y_3866_);
                v_env_3874_ = crate::leanh::lean_ctor_get(v___x_3873_, 0);
                v_nextMacroScope_3875_ = crate::leanh::lean_ctor_get(v___x_3873_, 1);
                v_ngen_3876_ = crate::leanh::lean_ctor_get(v___x_3873_, 2);
                v_auxDeclNGen_3877_ = crate::leanh::lean_ctor_get(v___x_3873_, 3);
                v_traceState_3878_ = crate::leanh::lean_ctor_get(v___x_3873_, 4);
                v_messages_3879_ = crate::leanh::lean_ctor_get(v___x_3873_, 6);
                v_infoState_3880_ = crate::leanh::lean_ctor_get(v___x_3873_, 7);
                v_snapshotTasks_3881_ = crate::leanh::lean_ctor_get(v___x_3873_, 8);
                v_isSharedCheck_3906_ = (!crate::leanh::lean_is_exclusive(v___x_3873_)) as u8;
                if v_isSharedCheck_3906_ == 0 {
                    v_unused_3907_ = crate::leanh::lean_ctor_get(v___x_3873_, 5);
                    crate::leanh::lean_dec(v_unused_3907_);
                    v___x_3883_ = v___x_3873_;
                    v_isShared_3884_ = v_isSharedCheck_3906_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3881_);
                    crate::leanh::lean_inc(v_infoState_3880_);
                    crate::leanh::lean_inc(v_messages_3879_);
                    crate::leanh::lean_inc(v_traceState_3878_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3877_);
                    crate::leanh::lean_inc(v_ngen_3876_);
                    crate::leanh::lean_inc(v_nextMacroScope_3875_);
                    crate::leanh::lean_inc(v_env_3874_);
                    crate::leanh::lean_dec(v___x_3873_);
                    v___x_3883_ = crate::leanh::lean_box(0);
                    v_isShared_3884_ = v_isSharedCheck_3906_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3885_ = l_Lean_Environment_setExporting(v_env_3874_, v_isExporting_3867_);
                if v_isShared_3884_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3883_, 5, v___x_3868_);
                    crate::leanh::lean_ctor_set(v___x_3883_, 0, v___x_3885_);
                    v___x_3887_ = v___x_3883_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3905_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3905_, 0, v___x_3885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3905_, 1, v_nextMacroScope_3875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3905_, 2, v_ngen_3876_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3905_, 3, v_auxDeclNGen_3877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3905_, 4, v_traceState_3878_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3905_, 5, v___x_3868_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3905_, 6, v_messages_3879_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3905_, 7, v_infoState_3880_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3905_, 8, v_snapshotTasks_3881_);
                    v___x_3887_ = v_reuseFailAlloc_3905_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3888_ = lean_st_ref_set(v___y_3866_, v___x_3887_);
                v___x_3889_ = lean_st_ref_take(v___y_3869_);
                v_mctx_3890_ = crate::leanh::lean_ctor_get(v___x_3889_, 0);
                v_zetaDeltaFVarIds_3891_ = crate::leanh::lean_ctor_get(v___x_3889_, 2);
                v_postponed_3892_ = crate::leanh::lean_ctor_get(v___x_3889_, 3);
                v_diag_3893_ = crate::leanh::lean_ctor_get(v___x_3889_, 4);
                v_isSharedCheck_3903_ = (!crate::leanh::lean_is_exclusive(v___x_3889_)) as u8;
                if v_isSharedCheck_3903_ == 0 {
                    v_unused_3904_ = crate::leanh::lean_ctor_get(v___x_3889_, 1);
                    crate::leanh::lean_dec(v_unused_3904_);
                    v___x_3895_ = v___x_3889_;
                    v_isShared_3896_ = v_isSharedCheck_3903_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_3893_);
                    crate::leanh::lean_inc(v_postponed_3892_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_3891_);
                    crate::leanh::lean_inc(v_mctx_3890_);
                    crate::leanh::lean_dec(v___x_3889_);
                    v___x_3895_ = crate::leanh::lean_box(0);
                    v_isShared_3896_ = v_isSharedCheck_3903_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3896_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3895_, 1, v___x_3870_);
                    v___x_3898_ = v___x_3895_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3902_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_mctx_3890_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3902_, 1, v___x_3870_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3902_,
                        2,
                        v_zetaDeltaFVarIds_3891_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3902_, 3, v_postponed_3892_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3902_, 4, v_diag_3893_);
                    v___x_3898_ = v_reuseFailAlloc_3902_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3899_ = lean_st_ref_set(v___y_3869_, v___x_3898_);
                v___x_3900_ = crate::leanh::lean_box(0);
                v___x_3901_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3901_, 0, v___x_3900_);
                return v___x_3901_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0___boxed(
    mut v___y_3908_: *mut crate::leanh::LeanObject,
    mut v_isExporting_3909_: *mut crate::leanh::LeanObject,
    mut v___x_3910_: *mut crate::leanh::LeanObject,
    mut v___y_3911_: *mut crate::leanh::LeanObject,
    mut v___x_3912_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_3913_: *mut crate::leanh::LeanObject,
    mut v___y_3914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_3915_: u8 = 0;
    let mut v_res_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_3915_ = (crate::leanh::lean_unbox(v_isExporting_3909_) as u8);
    v_res_3916_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_3908_, v_isExporting_boxed_3915_, v___x_3910_, v___y_3911_, v___x_3912_, v_a_x3f_3913_);
    crate::leanh::lean_dec(v_a_x3f_3913_);
    crate::leanh::lean_dec(v___y_3911_);
    crate::leanh::lean_dec(v___y_3908_);
    return v_res_3916_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(
    mut v_x_3917_: *mut crate::leanh::LeanObject,
    mut v_isExporting_3918_: u8,
    mut v___y_3919_: *mut crate::leanh::LeanObject,
    mut v___y_3920_: *mut crate::leanh::LeanObject,
    mut v___y_3921_: *mut crate::leanh::LeanObject,
    mut v___y_3922_: *mut crate::leanh::LeanObject,
    mut v___y_3923_: *mut crate::leanh::LeanObject,
    mut v___y_3924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_3928_: u8 = 0;
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3940_: u8 = 0;
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3953_: u8 = 0;
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3962_: u8 = 0;
    let mut v___x_3964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3968_: u8 = 0;
    let mut v___x_3970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3972_: u8 = 0;
    let mut v_unused_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3975_: u8 = 0;
    let mut v_a_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3981_: u8 = 0;
    let mut v___x_3983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3985_: u8 = 0;
    let mut v_unused_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3988_: u8 = 0;
    let mut v_unused_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3991_: u8 = 0;
    let mut v_unused_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3926_ = lean_st_ref_get(v___y_3924_);
                v_env_3927_ = crate::leanh::lean_ctor_get(v___x_3926_, 0);
                crate::leanh::lean_inc_ref(v_env_3927_);
                crate::leanh::lean_dec(v___x_3926_);
                v_isExporting_3928_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_3927_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_3927_);
                v___x_3929_ = lean_st_ref_take(v___y_3924_);
                v_env_3930_ = crate::leanh::lean_ctor_get(v___x_3929_, 0);
                v_nextMacroScope_3931_ = crate::leanh::lean_ctor_get(v___x_3929_, 1);
                v_ngen_3932_ = crate::leanh::lean_ctor_get(v___x_3929_, 2);
                v_auxDeclNGen_3933_ = crate::leanh::lean_ctor_get(v___x_3929_, 3);
                v_traceState_3934_ = crate::leanh::lean_ctor_get(v___x_3929_, 4);
                v_messages_3935_ = crate::leanh::lean_ctor_get(v___x_3929_, 6);
                v_infoState_3936_ = crate::leanh::lean_ctor_get(v___x_3929_, 7);
                v_snapshotTasks_3937_ = crate::leanh::lean_ctor_get(v___x_3929_, 8);
                v_isSharedCheck_3991_ = (!crate::leanh::lean_is_exclusive(v___x_3929_)) as u8;
                if v_isSharedCheck_3991_ == 0 {
                    v_unused_3992_ = crate::leanh::lean_ctor_get(v___x_3929_, 5);
                    crate::leanh::lean_dec(v_unused_3992_);
                    v___x_3939_ = v___x_3929_;
                    v_isShared_3940_ = v_isSharedCheck_3991_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3937_);
                    crate::leanh::lean_inc(v_infoState_3936_);
                    crate::leanh::lean_inc(v_messages_3935_);
                    crate::leanh::lean_inc(v_traceState_3934_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3933_);
                    crate::leanh::lean_inc(v_ngen_3932_);
                    crate::leanh::lean_inc(v_nextMacroScope_3931_);
                    crate::leanh::lean_inc(v_env_3930_);
                    crate::leanh::lean_dec(v___x_3929_);
                    v___x_3939_ = crate::leanh::lean_box(0);
                    v_isShared_3940_ = v_isSharedCheck_3991_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3941_ = l_Lean_Environment_setExporting(v_env_3930_, v_isExporting_3918_);
                v___x_3942_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2_once), _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__2);
                if v_isShared_3940_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3939_, 5, v___x_3942_);
                    crate::leanh::lean_ctor_set(v___x_3939_, 0, v___x_3941_);
                    v___x_3944_ = v___x_3939_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3990_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3990_, 0, v___x_3941_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3990_, 1, v_nextMacroScope_3931_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3990_, 2, v_ngen_3932_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3990_, 3, v_auxDeclNGen_3933_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3990_, 4, v_traceState_3934_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3990_, 5, v___x_3942_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3990_, 6, v_messages_3935_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3990_, 7, v_infoState_3936_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3990_, 8, v_snapshotTasks_3937_);
                    v___x_3944_ = v_reuseFailAlloc_3990_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3945_ = lean_st_ref_set(v___y_3924_, v___x_3944_);
                v___x_3946_ = lean_st_ref_take(v___y_3922_);
                v_mctx_3947_ = crate::leanh::lean_ctor_get(v___x_3946_, 0);
                v_zetaDeltaFVarIds_3948_ = crate::leanh::lean_ctor_get(v___x_3946_, 2);
                v_postponed_3949_ = crate::leanh::lean_ctor_get(v___x_3946_, 3);
                v_diag_3950_ = crate::leanh::lean_ctor_get(v___x_3946_, 4);
                v_isSharedCheck_3988_ = (!crate::leanh::lean_is_exclusive(v___x_3946_)) as u8;
                if v_isSharedCheck_3988_ == 0 {
                    v_unused_3989_ = crate::leanh::lean_ctor_get(v___x_3946_, 1);
                    crate::leanh::lean_dec(v_unused_3989_);
                    v___x_3952_ = v___x_3946_;
                    v_isShared_3953_ = v_isSharedCheck_3988_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_3950_);
                    crate::leanh::lean_inc(v_postponed_3949_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_3948_);
                    crate::leanh::lean_inc(v_mctx_3947_);
                    crate::leanh::lean_dec(v___x_3946_);
                    v___x_3952_ = crate::leanh::lean_box(0);
                    v_isShared_3953_ = v_isSharedCheck_3988_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3954_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3_once), _init_l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg___closed__3);
                if v_isShared_3953_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3952_, 1, v___x_3954_);
                    v___x_3956_ = v___x_3952_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3987_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_mctx_3947_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3987_, 1, v___x_3954_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3987_,
                        2,
                        v_zetaDeltaFVarIds_3948_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3987_, 3, v_postponed_3949_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3987_, 4, v_diag_3950_);
                    v___x_3956_ = v_reuseFailAlloc_3987_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3957_ = lean_st_ref_set(v___y_3922_, v___x_3956_);
                crate::leanh::lean_inc(v___y_3924_);
                crate::leanh::lean_inc_ref(v___y_3923_);
                crate::leanh::lean_inc(v___y_3922_);
                crate::leanh::lean_inc_ref(v___y_3921_);
                crate::leanh::lean_inc(v___y_3920_);
                crate::leanh::lean_inc_ref(v___y_3919_);
                v_r_3958_ = crate::leanh::lean_apply_7(
                    v_x_3917_,
                    v___y_3919_,
                    v___y_3920_,
                    v___y_3921_,
                    v___y_3922_,
                    v___y_3923_,
                    v___y_3924_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v_r_3958_) == 0 {
                    v_a_3959_ = crate::leanh::lean_ctor_get(v_r_3958_, 0);
                    v_isSharedCheck_3975_ = (!crate::leanh::lean_is_exclusive(v_r_3958_)) as u8;
                    if v_isSharedCheck_3975_ == 0 {
                        v___x_3961_ = v_r_3958_;
                        v_isShared_3962_ = v_isSharedCheck_3975_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3959_);
                        crate::leanh::lean_dec(v_r_3958_);
                        v___x_3961_ = crate::leanh::lean_box(0);
                        v_isShared_3962_ = v_isSharedCheck_3975_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_3976_ = crate::leanh::lean_ctor_get(v_r_3958_, 0);
                    crate::leanh::lean_inc(v_a_3976_);
                    crate::leanh::lean_dec_ref_known(v_r_3958_, 1);
                    v___x_3977_ = crate::leanh::lean_box(0);
                    v___x_3978_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_3924_, v_isExporting_3928_, v___x_3942_, v___y_3922_, v___x_3954_, v___x_3977_);
                    v_isSharedCheck_3985_ = (!crate::leanh::lean_is_exclusive(v___x_3978_)) as u8;
                    if v_isSharedCheck_3985_ == 0 {
                        v_unused_3986_ = crate::leanh::lean_ctor_get(v___x_3978_, 0);
                        crate::leanh::lean_dec(v_unused_3986_);
                        v___x_3980_ = v___x_3978_;
                        v_isShared_3981_ = v_isSharedCheck_3985_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_3978_);
                        v___x_3980_ = crate::leanh::lean_box(0);
                        v_isShared_3981_ = v_isSharedCheck_3985_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                crate::leanh::lean_inc(v_a_3959_);
                if v_isShared_3962_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3961_, 1);
                    v___x_3964_ = v___x_3961_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3974_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_a_3959_);
                    v___x_3964_ = v_reuseFailAlloc_3974_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3965_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___lam__0(v___y_3924_, v_isExporting_3928_, v___x_3942_, v___y_3922_, v___x_3954_, v___x_3964_);
                crate::leanh::lean_dec_ref(v___x_3964_);
                v_isSharedCheck_3972_ = (!crate::leanh::lean_is_exclusive(v___x_3965_)) as u8;
                if v_isSharedCheck_3972_ == 0 {
                    v_unused_3973_ = crate::leanh::lean_ctor_get(v___x_3965_, 0);
                    crate::leanh::lean_dec(v_unused_3973_);
                    v___x_3967_ = v___x_3965_;
                    v_isShared_3968_ = v_isSharedCheck_3972_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_3965_);
                    v___x_3967_ = crate::leanh::lean_box(0);
                    v_isShared_3968_ = v_isSharedCheck_3972_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_3968_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3967_, 0, v_a_3959_);
                    v___x_3970_ = v___x_3967_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3971_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3959_);
                    v___x_3970_ = v_reuseFailAlloc_3971_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3970_;
            }
            9 => {
                if v_isShared_3981_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3980_, 1);
                    crate::leanh::lean_ctor_set(v___x_3980_, 0, v_a_3976_);
                    v___x_3983_ = v___x_3980_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3984_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_a_3976_);
                    v___x_3983_ = v_reuseFailAlloc_3984_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3983_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg___boxed(
    mut v_x_3993_: *mut crate::leanh::LeanObject,
    mut v_isExporting_3994_: *mut crate::leanh::LeanObject,
    mut v___y_3995_: *mut crate::leanh::LeanObject,
    mut v___y_3996_: *mut crate::leanh::LeanObject,
    mut v___y_3997_: *mut crate::leanh::LeanObject,
    mut v___y_3998_: *mut crate::leanh::LeanObject,
    mut v___y_3999_: *mut crate::leanh::LeanObject,
    mut v___y_4000_: *mut crate::leanh::LeanObject,
    mut v___y_4001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_4002_: u8 = 0;
    let mut v_res_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4002_ = (crate::leanh::lean_unbox(v_isExporting_3994_) as u8);
    v_res_4003_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_3993_, v_isExporting_boxed_4002_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_, v___y_4000_);
    crate::leanh::lean_dec(v___y_4000_);
    crate::leanh::lean_dec_ref(v___y_3999_);
    crate::leanh::lean_dec(v___y_3998_);
    crate::leanh::lean_dec_ref(v___y_3997_);
    crate::leanh::lean_dec(v___y_3996_);
    crate::leanh::lean_dec_ref(v___y_3995_);
    return v_res_4003_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(
    mut v_x_4004_: *mut crate::leanh::LeanObject,
    mut v_when_4005_: u8,
    mut v___y_4006_: *mut crate::leanh::LeanObject,
    mut v___y_4007_: *mut crate::leanh::LeanObject,
    mut v___y_4008_: *mut crate::leanh::LeanObject,
    mut v___y_4009_: *mut crate::leanh::LeanObject,
    mut v___y_4010_: *mut crate::leanh::LeanObject,
    mut v___y_4011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_when_4005_ == 0 {
        let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v___y_4011_);
        crate::leanh::lean_inc_ref(v___y_4010_);
        crate::leanh::lean_inc(v___y_4009_);
        crate::leanh::lean_inc_ref(v___y_4008_);
        crate::leanh::lean_inc(v___y_4007_);
        crate::leanh::lean_inc_ref(v___y_4006_);
        v___x_4013_ = crate::leanh::lean_apply_7(
            v_x_4004_,
            v___y_4006_,
            v___y_4007_,
            v___y_4008_,
            v___y_4009_,
            v___y_4010_,
            v___y_4011_,
            crate::leanh::lean_box(0),
        );
        return v___x_4013_;
    } else {
        let mut v___x_4014_: u8 = 0;
        let mut v___x_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4014_ = 0;
        v___x_4015_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_4004_, v___x_4014_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
        return v___x_4015_;
    }
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg___boxed(
    mut v_x_4016_: *mut crate::leanh::LeanObject,
    mut v_when_4017_: *mut crate::leanh::LeanObject,
    mut v___y_4018_: *mut crate::leanh::LeanObject,
    mut v___y_4019_: *mut crate::leanh::LeanObject,
    mut v___y_4020_: *mut crate::leanh::LeanObject,
    mut v___y_4021_: *mut crate::leanh::LeanObject,
    mut v___y_4022_: *mut crate::leanh::LeanObject,
    mut v___y_4023_: *mut crate::leanh::LeanObject,
    mut v___y_4024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_when_boxed_4025_: u8 = 0;
    let mut v_res_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_4025_ = (crate::leanh::lean_unbox(v_when_4017_) as u8);
    v_res_4026_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(
        v_x_4016_,
        v_when_boxed_4025_,
        v___y_4018_,
        v___y_4019_,
        v___y_4020_,
        v___y_4021_,
        v___y_4022_,
        v___y_4023_,
    );
    crate::leanh::lean_dec(v___y_4023_);
    crate::leanh::lean_dec_ref(v___y_4022_);
    crate::leanh::lean_dec(v___y_4021_);
    crate::leanh::lean_dec_ref(v___y_4020_);
    crate::leanh::lean_dec(v___y_4019_);
    crate::leanh::lean_dec_ref(v___y_4018_);
    return v_res_4026_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(
    mut v_sz_4027_: usize,
    mut v_i_4028_: usize,
    mut v_bs_4029_: *mut crate::leanh::LeanObject,
    mut v___y_4030_: *mut crate::leanh::LeanObject,
    mut v___y_4031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4033_: u8 = 0;
    let mut v___x_4034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_4037_: u8 = 0;
    let mut v_levelParams_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifiers_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binders_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numSectionVars_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_termination_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4048_: u8 = 0;
    let mut v___x_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: usize = 0;
    let mut v___x_4056_: usize = 0;
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4063_: u8 = 0;
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4067_: u8 = 0;
    let mut v_isSharedCheck_4068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4033_ = lean_usize_dec_lt(v_i_4028_, v_sz_4027_);
                if v___x_4033_ == 0 {
                    v___x_4034_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4034_, 0, v_bs_4029_);
                    return v___x_4034_;
                } else {
                    v_v_4035_ = lean_array_uget(v_bs_4029_, v_i_4028_);
                    v_ref_4036_ = crate::leanh::lean_ctor_get(v_v_4035_, 0);
                    v_kind_4037_ = crate::leanh::lean_ctor_get_uint8(
                        v_v_4035_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                    );
                    v_levelParams_4038_ = crate::leanh::lean_ctor_get(v_v_4035_, 1);
                    v_modifiers_4039_ = crate::leanh::lean_ctor_get(v_v_4035_, 2);
                    v_declName_4040_ = crate::leanh::lean_ctor_get(v_v_4035_, 3);
                    v_binders_4041_ = crate::leanh::lean_ctor_get(v_v_4035_, 4);
                    v_numSectionVars_4042_ = crate::leanh::lean_ctor_get(v_v_4035_, 5);
                    v_type_4043_ = crate::leanh::lean_ctor_get(v_v_4035_, 6);
                    v_value_4044_ = crate::leanh::lean_ctor_get(v_v_4035_, 7);
                    v_termination_4045_ = crate::leanh::lean_ctor_get(v_v_4035_, 8);
                    v_isSharedCheck_4068_ = (!crate::leanh::lean_is_exclusive(v_v_4035_)) as u8;
                    if v_isSharedCheck_4068_ == 0 {
                        v___x_4047_ = v_v_4035_;
                        v_isShared_4048_ = v_isSharedCheck_4068_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_termination_4045_);
                        crate::leanh::lean_inc(v_value_4044_);
                        crate::leanh::lean_inc(v_type_4043_);
                        crate::leanh::lean_inc(v_numSectionVars_4042_);
                        crate::leanh::lean_inc(v_binders_4041_);
                        crate::leanh::lean_inc(v_declName_4040_);
                        crate::leanh::lean_inc(v_modifiers_4039_);
                        crate::leanh::lean_inc(v_levelParams_4038_);
                        crate::leanh::lean_inc(v_ref_4036_);
                        crate::leanh::lean_dec(v_v_4035_);
                        v___x_4047_ = crate::leanh::lean_box(0);
                        v_isShared_4048_ = v_isSharedCheck_4068_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4049_ = l_Lean_Elab_WF_floatRecApp(v_value_4044_, v___y_4030_, v___y_4031_);
                if crate::leanh::lean_obj_tag(v___x_4049_) == 0 {
                    v_a_4050_ = crate::leanh::lean_ctor_get(v___x_4049_, 0);
                    crate::leanh::lean_inc(v_a_4050_);
                    crate::leanh::lean_dec_ref_known(v___x_4049_, 1);
                    v___x_4051_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4052_ = lean_array_uset(v_bs_4029_, v_i_4028_, v___x_4051_);
                    if v_isShared_4048_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4047_, 7, v_a_4050_);
                        v___x_4054_ = v___x_4047_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4059_ = crate::leanh::lean_alloc_ctor(0, 9, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_ref_4036_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4059_, 1, v_levelParams_4038_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4059_, 2, v_modifiers_4039_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4059_, 3, v_declName_4040_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4059_, 4, v_binders_4041_);
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_4059_,
                            5,
                            v_numSectionVars_4042_,
                        );
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4059_, 6, v_type_4043_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4059_, 7, v_a_4050_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4059_, 8, v_termination_4045_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_4059_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                            v_kind_4037_,
                        );
                        v___x_4054_ = v_reuseFailAlloc_4059_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4047_);
                    crate::leanh::lean_dec_ref(v_termination_4045_);
                    crate::leanh::lean_dec_ref(v_type_4043_);
                    crate::leanh::lean_dec(v_numSectionVars_4042_);
                    crate::leanh::lean_dec(v_binders_4041_);
                    crate::leanh::lean_dec(v_declName_4040_);
                    crate::leanh::lean_dec_ref(v_modifiers_4039_);
                    crate::leanh::lean_dec(v_levelParams_4038_);
                    crate::leanh::lean_dec(v_ref_4036_);
                    crate::leanh::lean_dec_ref(v_bs_4029_);
                    v_a_4060_ = crate::leanh::lean_ctor_get(v___x_4049_, 0);
                    v_isSharedCheck_4067_ = (!crate::leanh::lean_is_exclusive(v___x_4049_)) as u8;
                    if v_isSharedCheck_4067_ == 0 {
                        v___x_4062_ = v___x_4049_;
                        v_isShared_4063_ = v_isSharedCheck_4067_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4060_);
                        crate::leanh::lean_dec(v___x_4049_);
                        v___x_4062_ = crate::leanh::lean_box(0);
                        v_isShared_4063_ = v_isSharedCheck_4067_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4055_ = 1usize;
                v___x_4056_ = lean_usize_add(v_i_4028_, v___x_4055_);
                v___x_4057_ = lean_array_uset(v_bs_x27_4052_, v_i_4028_, v___x_4054_);
                v_i_4028_ = v___x_4056_;
                v_bs_4029_ = v___x_4057_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_4063_ == 0 {
                    v___x_4065_ = v___x_4062_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4066_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_4060_);
                    v___x_4065_ = v_reuseFailAlloc_4066_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4065_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg___boxed(
    mut v_sz_4069_: *mut crate::leanh::LeanObject,
    mut v_i_4070_: *mut crate::leanh::LeanObject,
    mut v_bs_4071_: *mut crate::leanh::LeanObject,
    mut v___y_4072_: *mut crate::leanh::LeanObject,
    mut v___y_4073_: *mut crate::leanh::LeanObject,
    mut v___y_4074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4075_: usize = 0;
    let mut v_i_boxed_4076_: usize = 0;
    let mut v_res_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4075_ = crate::leanh::lean_unbox_usize(v_sz_4069_);
    crate::leanh::lean_dec(v_sz_4069_);
    v_i_boxed_4076_ = crate::leanh::lean_unbox_usize(v_i_4070_);
    crate::leanh::lean_dec(v_i_4070_);
    v_res_4077_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(v_sz_boxed_4075_, v_i_boxed_4076_, v_bs_4071_, v___y_4072_, v___y_4073_);
    crate::leanh::lean_dec(v___y_4073_);
    crate::leanh::lean_dec_ref(v___y_4072_);
    return v_res_4077_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8(
    mut v_sz_4078_: usize,
    mut v_i_4079_: usize,
    mut v_bs_4080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4081_: u8 = 0;
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: usize = 0;
    let mut v___x_4089_: usize = 0;
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4081_ = lean_usize_dec_lt(v_i_4079_, v_sz_4078_);
                if v___x_4081_ == 0 {
                    v___x_4082_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4082_, 0, v_bs_4080_);
                    return v___x_4082_;
                } else {
                    v_v_4083_ = lean_array_uget_borrowed(v_bs_4080_, v_i_4079_);
                    if crate::leanh::lean_obj_tag(v_v_4083_) == 0 {
                        crate::leanh::lean_dec_ref(v_bs_4080_);
                        v___x_4084_ = crate::leanh::lean_box(0);
                        return v___x_4084_;
                    } else {
                        v_val_4085_ = crate::leanh::lean_ctor_get(v_v_4083_, 0);
                        crate::leanh::lean_inc(v_val_4085_);
                        v___x_4086_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4087_ = lean_array_uset(v_bs_4080_, v_i_4079_, v___x_4086_);
                        v___x_4088_ = 1usize;
                        v___x_4089_ = lean_usize_add(v_i_4079_, v___x_4088_);
                        v___x_4090_ = lean_array_uset(v_bs_x27_4087_, v_i_4079_, v_val_4085_);
                        v_i_4079_ = v___x_4089_;
                        v_bs_4080_ = v___x_4090_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8___boxed(
    mut v_sz_4092_: *mut crate::leanh::LeanObject,
    mut v_i_4093_: *mut crate::leanh::LeanObject,
    mut v_bs_4094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4095_: usize = 0;
    let mut v_i_boxed_4096_: usize = 0;
    let mut v_res_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4095_ = crate::leanh::lean_unbox_usize(v_sz_4092_);
    crate::leanh::lean_dec(v_sz_4092_);
    v_i_boxed_4096_ = crate::leanh::lean_unbox_usize(v_i_4093_);
    crate::leanh::lean_dec(v_i_4093_);
    v_res_4097_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8(v_sz_boxed_4095_, v_i_boxed_4096_, v_bs_4094_);
    return v_res_4097_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(
    mut v_sz_4098_: usize,
    mut v_i_4099_: usize,
    mut v_bs_4100_: *mut crate::leanh::LeanObject,
    mut v___y_4101_: *mut crate::leanh::LeanObject,
    mut v___y_4102_: *mut crate::leanh::LeanObject,
    mut v___y_4103_: *mut crate::leanh::LeanObject,
    mut v___y_4104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4106_: u8 = 0;
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: u8 = 0;
    let mut v_v_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: usize = 0;
    let mut v___x_4115_: usize = 0;
    let mut v___x_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4121_: u8 = 0;
    let mut v___x_4123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4106_ = lean_usize_dec_lt(v_i_4099_, v_sz_4098_);
                if v___x_4106_ == 0 {
                    v___x_4107_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4107_, 0, v_bs_4100_);
                    return v___x_4107_;
                } else {
                    v___x_4108_ = 0;
                    v_v_4109_ = lean_array_uget_borrowed(v_bs_4100_, v_i_4099_);
                    crate::leanh::lean_inc(v_v_4109_);
                    v___x_4110_ = l_Lean_Elab_Mutual_cleanPreDef(
                        v_v_4109_,
                        v___x_4108_,
                        v___y_4101_,
                        v___y_4102_,
                        v___y_4103_,
                        v___y_4104_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4110_) == 0 {
                        v_a_4111_ = crate::leanh::lean_ctor_get(v___x_4110_, 0);
                        crate::leanh::lean_inc(v_a_4111_);
                        crate::leanh::lean_dec_ref_known(v___x_4110_, 1);
                        v___x_4112_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_4113_ = lean_array_uset(v_bs_4100_, v_i_4099_, v___x_4112_);
                        v___x_4114_ = 1usize;
                        v___x_4115_ = lean_usize_add(v_i_4099_, v___x_4114_);
                        v___x_4116_ = lean_array_uset(v_bs_x27_4113_, v_i_4099_, v_a_4111_);
                        v_i_4099_ = v___x_4115_;
                        v_bs_4100_ = v___x_4116_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_4100_);
                        v_a_4118_ = crate::leanh::lean_ctor_get(v___x_4110_, 0);
                        v_isSharedCheck_4125_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4110_)) as u8;
                        if v_isSharedCheck_4125_ == 0 {
                            v___x_4120_ = v___x_4110_;
                            v_isShared_4121_ = v_isSharedCheck_4125_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4118_);
                            crate::leanh::lean_dec(v___x_4110_);
                            v___x_4120_ = crate::leanh::lean_box(0);
                            v_isShared_4121_ = v_isSharedCheck_4125_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4121_ == 0 {
                    v___x_4123_ = v___x_4120_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4124_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_a_4118_);
                    v___x_4123_ = v_reuseFailAlloc_4124_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4123_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg___boxed(
    mut v_sz_4126_: *mut crate::leanh::LeanObject,
    mut v_i_4127_: *mut crate::leanh::LeanObject,
    mut v_bs_4128_: *mut crate::leanh::LeanObject,
    mut v___y_4129_: *mut crate::leanh::LeanObject,
    mut v___y_4130_: *mut crate::leanh::LeanObject,
    mut v___y_4131_: *mut crate::leanh::LeanObject,
    mut v___y_4132_: *mut crate::leanh::LeanObject,
    mut v___y_4133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4134_: usize = 0;
    let mut v_i_boxed_4135_: usize = 0;
    let mut v_res_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4134_ = crate::leanh::lean_unbox_usize(v_sz_4126_);
    crate::leanh::lean_dec(v_sz_4126_);
    v_i_boxed_4135_ = crate::leanh::lean_unbox_usize(v_i_4127_);
    crate::leanh::lean_dec(v_i_4127_);
    v_res_4136_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_boxed_4134_, v_i_boxed_4135_, v_bs_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
    crate::leanh::lean_dec(v___y_4132_);
    crate::leanh::lean_dec_ref(v___y_4131_);
    crate::leanh::lean_dec(v___y_4130_);
    crate::leanh::lean_dec_ref(v___y_4129_);
    return v_res_4136_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(
    mut v_env_4137_: *mut crate::leanh::LeanObject,
    mut v_x_4138_: *mut crate::leanh::LeanObject,
    mut v___y_4139_: *mut crate::leanh::LeanObject,
    mut v___y_4140_: *mut crate::leanh::LeanObject,
    mut v___y_4141_: *mut crate::leanh::LeanObject,
    mut v___y_4142_: *mut crate::leanh::LeanObject,
    mut v___y_4143_: *mut crate::leanh::LeanObject,
    mut v___y_4144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4153_: u8 = 0;
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4157_: u8 = 0;
    let mut v_unused_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4165_: u8 = 0;
    let mut v___x_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4169_: u8 = 0;
    let mut v_unused_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4146_ = lean_st_ref_get(v___y_4144_);
                v_env_4147_ = crate::leanh::lean_ctor_get(v___x_4146_, 0);
                crate::leanh::lean_inc_ref(v_env_4147_);
                crate::leanh::lean_dec(v___x_4146_);
                v___x_4159_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(
                    v_env_4137_,
                    v___y_4142_,
                    v___y_4144_,
                );
                crate::leanh::lean_dec_ref(v___x_4159_);
                crate::leanh::lean_inc(v___y_4144_);
                crate::leanh::lean_inc_ref(v___y_4143_);
                crate::leanh::lean_inc(v___y_4142_);
                crate::leanh::lean_inc_ref(v___y_4141_);
                crate::leanh::lean_inc(v___y_4140_);
                crate::leanh::lean_inc_ref(v___y_4139_);
                v___x_4160_ = crate::leanh::lean_apply_7(
                    v_x_4138_,
                    v___y_4139_,
                    v___y_4140_,
                    v___y_4141_,
                    v___y_4142_,
                    v___y_4143_,
                    v___y_4144_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_4160_) == 0 {
                    v_a_4161_ = crate::leanh::lean_ctor_get(v___x_4160_, 0);
                    crate::leanh::lean_inc(v_a_4161_);
                    crate::leanh::lean_dec_ref_known(v___x_4160_, 1);
                    v___x_4162_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(
                        v_env_4147_,
                        v___y_4142_,
                        v___y_4144_,
                    );
                    v_isSharedCheck_4169_ = (!crate::leanh::lean_is_exclusive(v___x_4162_)) as u8;
                    if v_isSharedCheck_4169_ == 0 {
                        v_unused_4170_ = crate::leanh::lean_ctor_get(v___x_4162_, 0);
                        crate::leanh::lean_dec(v_unused_4170_);
                        v___x_4164_ = v___x_4162_;
                        v_isShared_4165_ = v_isSharedCheck_4169_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4162_);
                        v___x_4164_ = crate::leanh::lean_box(0);
                        v_isShared_4165_ = v_isSharedCheck_4169_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_a_4171_ = crate::leanh::lean_ctor_get(v___x_4160_, 0);
                    crate::leanh::lean_inc(v_a_4171_);
                    crate::leanh::lean_dec_ref_known(v___x_4160_, 1);
                    v_a_4149_ = v_a_4171_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4150_ = l_Lean_setEnv___at___00Lean_Elab_wfRecursion_spec__9___redArg(
                    v_env_4147_,
                    v___y_4142_,
                    v___y_4144_,
                );
                v_isSharedCheck_4157_ = (!crate::leanh::lean_is_exclusive(v___x_4150_)) as u8;
                if v_isSharedCheck_4157_ == 0 {
                    v_unused_4158_ = crate::leanh::lean_ctor_get(v___x_4150_, 0);
                    crate::leanh::lean_dec(v_unused_4158_);
                    v___x_4152_ = v___x_4150_;
                    v_isShared_4153_ = v_isSharedCheck_4157_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_4150_);
                    v___x_4152_ = crate::leanh::lean_box(0);
                    v_isShared_4153_ = v_isSharedCheck_4157_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_4153_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4152_, 1);
                    crate::leanh::lean_ctor_set(v___x_4152_, 0, v_a_4149_);
                    v___x_4155_ = v___x_4152_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4156_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4149_);
                    v___x_4155_ = v_reuseFailAlloc_4156_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4155_;
            }
            4 => {
                if v_isShared_4165_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4164_, 0, v_a_4161_);
                    v___x_4167_ = v___x_4164_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4168_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4168_, 0, v_a_4161_);
                    v___x_4167_ = v_reuseFailAlloc_4168_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4167_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg___boxed(
    mut v_env_4172_: *mut crate::leanh::LeanObject,
    mut v_x_4173_: *mut crate::leanh::LeanObject,
    mut v___y_4174_: *mut crate::leanh::LeanObject,
    mut v___y_4175_: *mut crate::leanh::LeanObject,
    mut v___y_4176_: *mut crate::leanh::LeanObject,
    mut v___y_4177_: *mut crate::leanh::LeanObject,
    mut v___y_4178_: *mut crate::leanh::LeanObject,
    mut v___y_4179_: *mut crate::leanh::LeanObject,
    mut v___y_4180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4181_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(
        v_env_4172_,
        v_x_4173_,
        v___y_4174_,
        v___y_4175_,
        v___y_4176_,
        v___y_4177_,
        v___y_4178_,
        v___y_4179_,
    );
    crate::leanh::lean_dec(v___y_4179_);
    crate::leanh::lean_dec_ref(v___y_4178_);
    crate::leanh::lean_dec(v___y_4177_);
    crate::leanh::lean_dec_ref(v___y_4176_);
    crate::leanh::lean_dec(v___y_4175_);
    crate::leanh::lean_dec_ref(v___y_4174_);
    return v_res_4181_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(
    mut v___x_4182_: *mut crate::leanh::LeanObject,
    mut v_as_4183_: *mut crate::leanh::LeanObject,
    mut v_sz_4184_: usize,
    mut v_i_4185_: usize,
    mut v_b_4186_: *mut crate::leanh::LeanObject,
    mut v___y_4187_: *mut crate::leanh::LeanObject,
    mut v___y_4188_: *mut crate::leanh::LeanObject,
    mut v___y_4189_: *mut crate::leanh::LeanObject,
    mut v___y_4190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: usize = 0;
    let mut v___x_4195_: usize = 0;
    let mut v___x_4197_: u8 = 0;
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_kind_4200_: u8 = 0;
    let mut v_declName_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: u8 = 0;
    let mut v___x_4205_: u8 = 0;
    let mut v___x_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: u8 = 0;
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4213_: u8 = 0;
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4217_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4197_ = lean_usize_dec_lt(v_i_4185_, v_sz_4184_);
                if v___x_4197_ == 0 {
                    crate::leanh::lean_dec(v___x_4182_);
                    v___x_4198_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4198_, 0, v_b_4186_);
                    return v___x_4198_;
                } else {
                    v_a_4199_ = lean_array_uget_borrowed(v_as_4183_, v_i_4185_);
                    v_kind_4200_ = crate::leanh::lean_ctor_get_uint8(
                        v_a_4199_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 9) as u32,
                    );
                    v_declName_4201_ = crate::leanh::lean_ctor_get(v_a_4199_, 3);
                    v_type_4202_ = crate::leanh::lean_ctor_get(v_a_4199_, 6);
                    v___x_4203_ = crate::leanh::lean_box(0);
                    v___x_4204_ = lean_name_eq(v_declName_4201_, v___x_4182_);
                    if v___x_4204_ == 0 {
                        v___x_4205_ = l_Lean_Elab_DefKind_isTheorem(v_kind_4200_);
                        if v___x_4205_ == 0 {
                            crate::leanh::lean_inc_ref(v_type_4202_);
                            v___x_4206_ = l_Lean_Meta_isProp(
                                v_type_4202_,
                                v___y_4187_,
                                v___y_4188_,
                                v___y_4189_,
                                v___y_4190_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4206_) == 0 {
                                v_a_4207_ = crate::leanh::lean_ctor_get(v___x_4206_, 0);
                                crate::leanh::lean_inc(v_a_4207_);
                                crate::leanh::lean_dec_ref_known(v___x_4206_, 1);
                                v___x_4208_ = (crate::leanh::lean_unbox(v_a_4207_) as u8);
                                crate::leanh::lean_dec(v_a_4207_);
                                if v___x_4208_ == 0 {
                                    crate::leanh::lean_inc(v___x_4182_);
                                    crate::leanh::lean_inc(v_a_4199_);
                                    v___x_4209_ = l_Lean_Elab_WF_mkBinaryUnfoldEq(
                                        v_a_4199_,
                                        v___x_4182_,
                                        v___y_4187_,
                                        v___y_4188_,
                                        v___y_4189_,
                                        v___y_4190_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_4209_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_4209_, 1);
                                        v_a_4193_ = v___x_4203_;
                                        state = 1;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_4182_);
                                        return v___x_4209_;
                                    }
                                } else {
                                    v_a_4193_ = v___x_4203_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_4182_);
                                v_a_4210_ = crate::leanh::lean_ctor_get(v___x_4206_, 0);
                                v_isSharedCheck_4217_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4206_)) as u8;
                                if v_isSharedCheck_4217_ == 0 {
                                    v___x_4212_ = v___x_4206_;
                                    v_isShared_4213_ = v_isSharedCheck_4217_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4210_);
                                    crate::leanh::lean_dec(v___x_4206_);
                                    v___x_4212_ = crate::leanh::lean_box(0);
                                    v_isShared_4213_ = v_isSharedCheck_4217_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            v_a_4193_ = v___x_4203_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4193_ = v___x_4203_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4194_ = 1usize;
                v___x_4195_ = lean_usize_add(v_i_4185_, v___x_4194_);
                v_i_4185_ = v___x_4195_;
                v_b_4186_ = v_a_4193_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_4213_ == 0 {
                    v___x_4215_ = v___x_4212_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4216_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_a_4210_);
                    v___x_4215_ = v_reuseFailAlloc_4216_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4215_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg___boxed(
    mut v___x_4218_: *mut crate::leanh::LeanObject,
    mut v_as_4219_: *mut crate::leanh::LeanObject,
    mut v_sz_4220_: *mut crate::leanh::LeanObject,
    mut v_i_4221_: *mut crate::leanh::LeanObject,
    mut v_b_4222_: *mut crate::leanh::LeanObject,
    mut v___y_4223_: *mut crate::leanh::LeanObject,
    mut v___y_4224_: *mut crate::leanh::LeanObject,
    mut v___y_4225_: *mut crate::leanh::LeanObject,
    mut v___y_4226_: *mut crate::leanh::LeanObject,
    mut v___y_4227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4228_: usize = 0;
    let mut v_i_boxed_4229_: usize = 0;
    let mut v_res_4230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4228_ = crate::leanh::lean_unbox_usize(v_sz_4220_);
    crate::leanh::lean_dec(v_sz_4220_);
    v_i_boxed_4229_ = crate::leanh::lean_unbox_usize(v_i_4221_);
    crate::leanh::lean_dec(v_i_4221_);
    v_res_4230_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___x_4218_, v_as_4219_, v_sz_boxed_4228_, v_i_boxed_4229_, v_b_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_);
    crate::leanh::lean_dec(v___y_4226_);
    crate::leanh::lean_dec_ref(v___y_4225_);
    crate::leanh::lean_dec(v___y_4224_);
    crate::leanh::lean_dec_ref(v___y_4223_);
    crate::leanh::lean_dec_ref(v_as_4219_);
    return v_res_4230_;
}
pub unsafe fn _init_l_Lean_Elab_wfRecursion___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4238_ = l_Lean_Elab_wfRecursion___closed__3;
    v___x_4239_ = l_Lean_stringToMessageData(v___x_4238_);
    return v___x_4239_;
}
pub unsafe fn _init_l_Lean_Elab_wfRecursion___closed__6() -> *mut crate::leanh::LeanObject {
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4241_ = l_Lean_Elab_wfRecursion___closed__5;
    v___x_4242_ = l_Lean_stringToMessageData(v___x_4241_);
    return v___x_4242_;
}
pub unsafe fn _init_l_Lean_Elab_wfRecursion___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4244_ = l_Lean_Elab_wfRecursion___closed__7;
    v___x_4245_ = l_Lean_stringToMessageData(v___x_4244_);
    return v___x_4245_;
}
pub unsafe fn _init_l_Lean_Elab_wfRecursion___closed__10() -> *mut crate::leanh::LeanObject {
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4247_ = l_Lean_Elab_wfRecursion___closed__9;
    v___x_4248_ = l_Lean_stringToMessageData(v___x_4247_);
    return v___x_4248_;
}
pub unsafe fn l_Lean_Elab_wfRecursion(
    mut v_docCtx_4251_: *mut crate::leanh::LeanObject,
    mut v_preDefs_4252_: *mut crate::leanh::LeanObject,
    mut v_termMeasure_x3fs_4253_: *mut crate::leanh::LeanObject,
    mut v_a_4254_: *mut crate::leanh::LeanObject,
    mut v_a_4255_: *mut crate::leanh::LeanObject,
    mut v_a_4256_: *mut crate::leanh::LeanObject,
    mut v_a_4257_: *mut crate::leanh::LeanObject,
    mut v_a_4258_: *mut crate::leanh::LeanObject,
    mut v_a_4259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_4261_: usize = 0;
    let mut v___x_4262_: usize = 0;
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4278_: usize = 0;
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4282_: usize = 0;
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4293_: u8 = 0;
    let mut v_fst_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4298_: u8 = 0;
    let mut v___y_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4301_: u8 = 0;
    let mut v___y_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: u8 = 0;
    let mut v___x_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4329_: u8 = 0;
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4333_: u8 = 0;
    let mut v_a_4334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4337_: u8 = 0;
    let mut v___x_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4341_: u8 = 0;
    let mut v_a_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4345_: u8 = 0;
    let mut v___x_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4349_: u8 = 0;
    let mut v_a_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4353_: u8 = 0;
    let mut v___x_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4357_: u8 = 0;
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_wf_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numFixed_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: u8 = 0;
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: u8 = 0;
    let mut v_declName_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4399_: u8 = 0;
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4403_: u8 = 0;
    let mut v___x_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4407_: usize = 0;
    let mut v_termMeasures_x3f_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: u8 = 0;
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4426_: u8 = 0;
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4430_: u8 = 0;
    let mut v___y_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4447_: u8 = 0;
    let mut v___x_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4451_: u8 = 0;
    let mut v_value_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4460_: u8 = 0;
    let mut v_a_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4464_: u8 = 0;
    let mut v___x_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4468_: u8 = 0;
    let mut v___x_4469_: u8 = 0;
    let mut v_value_4470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4476_: u8 = 0;
    let mut v_isSharedCheck_4477_: u8 = 0;
    let mut v_a_4478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4481_: u8 = 0;
    let mut v___x_4483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4485_: u8 = 0;
    let mut v_a_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4489_: u8 = 0;
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4493_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_4261_ = lean_array_size(v_preDefs_4252_);
                v___x_4262_ = 0usize;
                v___x_4263_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(v_sz_4261_, v___x_4262_, v_preDefs_4252_, v_a_4258_, v_a_4259_);
                if crate::leanh::lean_obj_tag(v___x_4263_) == 0 {
                    v_a_4264_ = crate::leanh::lean_ctor_get(v___x_4263_, 0);
                    crate::leanh::lean_inc_n(v_a_4264_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_4263_, 1);
                    v___x_4265_ = lean_st_ref_get(v_a_4259_);
                    v_env_4266_ = crate::leanh::lean_ctor_get(v___x_4265_, 0);
                    crate::leanh::lean_inc_ref(v_env_4266_);
                    crate::leanh::lean_dec(v___x_4265_);
                    v___x_4267_ = l_Lean_Elab_instInhabitedPreDefinition_default;
                    v___x_4268_ = crate::leanh::lean_box(0);
                    v_sz_4282_ = lean_array_size(v_a_4264_);
                    v___x_4283_ = crate::leanh::lean_box_usize(v_sz_4282_);
                    v___x_4284_ = l_Lean_Elab_wfRecursion___boxed__const__1;
                    v___f_4285_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Elab_wfRecursion___lam__0___boxed as *mut core::ffi::c_void,
                        12,
                        5,
                    );
                    crate::leanh::lean_closure_set(v___f_4285_, 0, v_a_4264_);
                    crate::leanh::lean_closure_set(v___f_4285_, 1, v___x_4283_);
                    crate::leanh::lean_closure_set(v___f_4285_, 2, v___x_4284_);
                    crate::leanh::lean_closure_set(v___f_4285_, 3, v___x_4268_);
                    crate::leanh::lean_closure_set(v___f_4285_, 4, v___x_4267_);
                    v___x_4286_ = l_Lean_Environment_unlockAsync(v_env_4266_);
                    v___x_4287_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(
                        v___x_4286_,
                        v___f_4285_,
                        v_a_4254_,
                        v_a_4255_,
                        v_a_4256_,
                        v_a_4257_,
                        v_a_4258_,
                        v_a_4259_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4287_) == 0 {
                        v_a_4288_ = crate::leanh::lean_ctor_get(v___x_4287_, 0);
                        crate::leanh::lean_inc(v_a_4288_);
                        crate::leanh::lean_dec_ref_known(v___x_4287_, 1);
                        v_snd_4289_ = crate::leanh::lean_ctor_get(v_a_4288_, 1);
                        v_fst_4290_ = crate::leanh::lean_ctor_get(v_a_4288_, 0);
                        v_isSharedCheck_4477_ = (!crate::leanh::lean_is_exclusive(v_a_4288_)) as u8;
                        if v_isSharedCheck_4477_ == 0 {
                            v___x_4292_ = v_a_4288_;
                            v_isShared_4293_ = v_isSharedCheck_4477_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_4289_);
                            crate::leanh::lean_inc(v_fst_4290_);
                            crate::leanh::lean_dec(v_a_4288_);
                            v___x_4292_ = crate::leanh::lean_box(0);
                            v_isShared_4293_ = v_isSharedCheck_4477_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4264_);
                        crate::leanh::lean_dec_ref(v_termMeasure_x3fs_4253_);
                        crate::leanh::lean_dec_ref(v_docCtx_4251_);
                        v_a_4478_ = crate::leanh::lean_ctor_get(v___x_4287_, 0);
                        v_isSharedCheck_4485_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4287_)) as u8;
                        if v_isSharedCheck_4485_ == 0 {
                            v___x_4480_ = v___x_4287_;
                            v_isShared_4481_ = v_isSharedCheck_4485_;
                            state = 26;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4478_);
                            crate::leanh::lean_dec(v___x_4287_);
                            v___x_4480_ = crate::leanh::lean_box(0);
                            v_isShared_4481_ = v_isSharedCheck_4485_;
                            state = 26;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_termMeasure_x3fs_4253_);
                    crate::leanh::lean_dec_ref(v_docCtx_4251_);
                    v_a_4486_ = crate::leanh::lean_ctor_get(v___x_4263_, 0);
                    v_isSharedCheck_4493_ = (!crate::leanh::lean_is_exclusive(v___x_4263_)) as u8;
                    if v_isSharedCheck_4493_ == 0 {
                        v___x_4488_ = v___x_4263_;
                        v_isShared_4489_ = v_isSharedCheck_4493_;
                        state = 28;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4486_);
                        crate::leanh::lean_dec(v___x_4263_);
                        v___x_4488_ = crate::leanh::lean_box(0);
                        v_isShared_4489_ = v_isSharedCheck_4493_;
                        state = 28;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_4278_ = lean_array_size(v___y_4270_);
                crate::leanh::lean_inc(v___y_4271_);
                v___x_4279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___y_4271_, v___y_4270_, v_sz_4278_, v___x_4262_, v___x_4268_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
                if crate::leanh::lean_obj_tag(v___x_4279_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4279_, 1);
                    v___x_4280_ =
                        l_Lean_enableRealizationsForConst(v___y_4271_, v___y_4276_, v___y_4277_);
                    if crate::leanh::lean_obj_tag(v___x_4280_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4280_, 1);
                        v___x_4281_ = l_Lean_Elab_Mutual_addPreDefAttributes(
                            v___y_4270_,
                            v___y_4272_,
                            v___y_4273_,
                            v___y_4274_,
                            v___y_4275_,
                            v___y_4276_,
                            v___y_4277_,
                        );
                        return v___x_4281_;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_4270_);
                        return v___x_4280_;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_4271_);
                    crate::leanh::lean_dec_ref(v___y_4270_);
                    return v___x_4279_;
                }
            }
            2 => {
                v_fst_4294_ = crate::leanh::lean_ctor_get(v_snd_4289_, 0);
                v_snd_4295_ = crate::leanh::lean_ctor_get(v_snd_4289_, 1);
                v_isSharedCheck_4476_ = (!crate::leanh::lean_is_exclusive(v_snd_4289_)) as u8;
                if v_isSharedCheck_4476_ == 0 {
                    v___x_4297_ = v_snd_4289_;
                    v_isShared_4298_ = v_isSharedCheck_4476_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_4295_);
                    crate::leanh::lean_inc(v_fst_4294_);
                    crate::leanh::lean_dec(v_snd_4289_);
                    v___x_4297_ = crate::leanh::lean_box(0);
                    v_isShared_4298_ = v_isSharedCheck_4476_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4358_ = l_Lean_Elab_wfRecursion___closed__2;
                v___x_4404_ = l_Lean_Elab_wfRecursion___lam__1(
                    v___x_4358_,
                    v_a_4254_,
                    v_a_4255_,
                    v_a_4256_,
                    v_a_4257_,
                    v_a_4258_,
                    v_a_4259_,
                );
                v_a_4405_ = crate::leanh::lean_ctor_get(v___x_4404_, 0);
                crate::leanh::lean_inc(v_a_4405_);
                crate::leanh::lean_dec_ref(v___x_4404_);
                crate::leanh::lean_inc(v_snd_4295_);
                v___f_4406_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_wfRecursion___lam__2___boxed as *mut core::ffi::c_void,
                    8,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_4406_, 0, v_snd_4295_);
                v_sz_4407_ = lean_array_size(v_termMeasure_x3fs_4253_);
                v_termMeasures_x3f_4408_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__8(v_sz_4407_, v___x_4262_, v_termMeasure_x3fs_4253_);
                v___x_4469_ = (crate::leanh::lean_unbox(v_a_4405_) as u8);
                crate::leanh::lean_dec(v_a_4405_);
                if v___x_4469_ == 0 {
                    v___y_4432_ = v_a_4254_;
                    v___y_4433_ = v_a_4255_;
                    v___y_4434_ = v_a_4256_;
                    v___y_4435_ = v_a_4257_;
                    v___y_4436_ = v_a_4258_;
                    v___y_4437_ = v_a_4259_;
                    state = 21;
                    continue;
                } else {
                    v_value_4470_ = crate::leanh::lean_ctor_get(v_snd_4295_, 7);
                    v___x_4471_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_wfRecursion___closed__10),
                        core::ptr::addr_of_mut!(l_Lean_Elab_wfRecursion___closed__10_once),
                        _init_l_Lean_Elab_wfRecursion___closed__10,
                    );
                    crate::leanh::lean_inc_ref(v_value_4470_);
                    v___x_4472_ = l_Lean_MessageData_ofExpr(v_value_4470_);
                    v___x_4473_ = l_Lean_indentD(v___x_4472_);
                    v___x_4474_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4474_, 0, v___x_4471_);
                    crate::leanh::lean_ctor_set(v___x_4474_, 1, v___x_4473_);
                    v___x_4475_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(
                        v___x_4358_,
                        v___x_4474_,
                        v_a_4256_,
                        v_a_4257_,
                        v_a_4258_,
                        v_a_4259_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4475_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4475_, 1);
                        v___y_4432_ = v_a_4254_;
                        v___y_4433_ = v_a_4255_;
                        v___y_4434_ = v_a_4256_;
                        v___y_4435_ = v_a_4257_;
                        v___y_4436_ = v_a_4258_;
                        v___y_4437_ = v_a_4259_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_termMeasures_x3f_4408_);
                        crate::leanh::lean_dec_ref(v___f_4406_);
                        crate::leanh::lean_del_object(v___x_4297_);
                        crate::leanh::lean_dec(v_snd_4295_);
                        crate::leanh::lean_dec(v_fst_4294_);
                        crate::leanh::lean_del_object(v___x_4292_);
                        crate::leanh::lean_dec(v_fst_4290_);
                        crate::leanh::lean_dec(v_a_4264_);
                        crate::leanh::lean_dec_ref(v_docCtx_4251_);
                        return v___x_4475_;
                    }
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v___y_4300_);
                crate::leanh::lean_inc(v_a_4264_);
                crate::leanh::lean_inc(v_fst_4294_);
                crate::leanh::lean_inc(v_fst_4290_);
                v___x_4309_ = l_Lean_Elab_WF_preDefsFromUnaryNonRec(
                    v_fst_4290_,
                    v_fst_4294_,
                    v_a_4264_,
                    v___y_4300_,
                    v___y_4305_,
                    v___y_4306_,
                    v___y_4307_,
                    v___y_4308_,
                );
                if crate::leanh::lean_obj_tag(v___x_4309_) == 0 {
                    v_a_4310_ = crate::leanh::lean_ctor_get(v___x_4309_, 0);
                    crate::leanh::lean_inc(v_a_4310_);
                    crate::leanh::lean_dec_ref_known(v___x_4309_, 1);
                    crate::leanh::lean_inc_ref(v___y_4300_);
                    crate::leanh::lean_inc(v_a_4264_);
                    crate::leanh::lean_inc_ref(v_docCtx_4251_);
                    v___x_4311_ = l_Lean_Elab_Mutual_addPreDefsFromUnary(
                        v_docCtx_4251_,
                        v_a_4264_,
                        v_a_4310_,
                        v___y_4300_,
                        v___y_4301_,
                        v___y_4303_,
                        v___y_4304_,
                        v___y_4305_,
                        v___y_4306_,
                        v___y_4307_,
                        v___y_4308_,
                    );
                    crate::leanh::lean_dec(v_a_4310_);
                    if crate::leanh::lean_obj_tag(v___x_4311_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4311_, 1);
                        crate::leanh::lean_inc(v_a_4264_);
                        v___x_4312_ = l_Lean_Elab_addAndCompilePartialRec(
                            v_docCtx_4251_,
                            v_a_4264_,
                            v___y_4303_,
                            v___y_4304_,
                            v___y_4305_,
                            v___y_4306_,
                            v___y_4307_,
                            v___y_4308_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4312_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4312_, 1);
                            v___x_4313_ = l_Lean_Elab_Mutual_cleanPreDef(
                                v_snd_4295_,
                                v___y_4301_,
                                v___y_4305_,
                                v___y_4306_,
                                v___y_4307_,
                                v___y_4308_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4313_) == 0 {
                                v_a_4314_ = crate::leanh::lean_ctor_get(v___x_4313_, 0);
                                crate::leanh::lean_inc(v_a_4314_);
                                crate::leanh::lean_dec_ref_known(v___x_4313_, 1);
                                v___x_4315_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_4282_, v___x_4262_, v_a_4264_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_);
                                if crate::leanh::lean_obj_tag(v___x_4315_) == 0 {
                                    v_a_4316_ = crate::leanh::lean_ctor_get(v___x_4315_, 0);
                                    crate::leanh::lean_inc_n(v_a_4316_, 2);
                                    crate::leanh::lean_dec_ref_known(v___x_4315_, 1);
                                    v_declName_4317_ = crate::leanh::lean_ctor_get(v___y_4300_, 3);
                                    crate::leanh::lean_inc_n(v_declName_4317_, 2);
                                    crate::leanh::lean_dec_ref(v___y_4300_);
                                    v___x_4318_ = l_Lean_Elab_WF_registerEqnsInfo(
                                        v_a_4316_,
                                        v_declName_4317_,
                                        v_fst_4290_,
                                        v_fst_4294_,
                                        v___y_4305_,
                                        v___y_4306_,
                                        v___y_4307_,
                                        v___y_4308_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_4318_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_4318_, 1);
                                        v_declName_4319_ =
                                            crate::leanh::lean_ctor_get(v_a_4314_, 3);
                                        v_type_4320_ = crate::leanh::lean_ctor_get(v_a_4314_, 6);
                                        crate::leanh::lean_inc(v_declName_4319_);
                                        v___x_4321_ = l_Lean_Meta_markAsRecursive___redArg(
                                            v_declName_4319_,
                                            v___y_4308_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_4321_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_4321_, 1);
                                            crate::leanh::lean_inc_ref(v_type_4320_);
                                            v___x_4322_ = l_Lean_Meta_isProp(
                                                v_type_4320_,
                                                v___y_4305_,
                                                v___y_4306_,
                                                v___y_4307_,
                                                v___y_4308_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_4322_) == 0 {
                                                v_a_4323_ =
                                                    crate::leanh::lean_ctor_get(v___x_4322_, 0);
                                                crate::leanh::lean_inc(v_a_4323_);
                                                crate::leanh::lean_dec_ref_known(v___x_4322_, 1);
                                                v___x_4324_ =
                                                    (crate::leanh::lean_unbox(v_a_4323_) as u8);
                                                crate::leanh::lean_dec(v_a_4323_);
                                                if v___x_4324_ == 0 {
                                                    crate::leanh::lean_inc(v_declName_4317_);
                                                    v___x_4325_ = l_Lean_Elab_WF_mkUnfoldEq(
                                                        v_a_4314_,
                                                        v_declName_4317_,
                                                        v___y_4302_,
                                                        v___y_4305_,
                                                        v___y_4306_,
                                                        v___y_4307_,
                                                        v___y_4308_,
                                                    );
                                                    if crate::leanh::lean_obj_tag(v___x_4325_) == 0
                                                    {
                                                        crate::leanh::lean_dec_ref_known(
                                                            v___x_4325_,
                                                            1,
                                                        );
                                                        v___y_4270_ = v_a_4316_;
                                                        v___y_4271_ = v_declName_4317_;
                                                        v___y_4272_ = v___y_4303_;
                                                        v___y_4273_ = v___y_4304_;
                                                        v___y_4274_ = v___y_4305_;
                                                        v___y_4275_ = v___y_4306_;
                                                        v___y_4276_ = v___y_4307_;
                                                        v___y_4277_ = v___y_4308_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_dec(v_declName_4317_);
                                                        crate::leanh::lean_dec(v_a_4316_);
                                                        return v___x_4325_;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_a_4314_);
                                                    crate::leanh::lean_dec_ref(v___y_4302_);
                                                    v___y_4270_ = v_a_4316_;
                                                    v___y_4271_ = v_declName_4317_;
                                                    v___y_4272_ = v___y_4303_;
                                                    v___y_4273_ = v___y_4304_;
                                                    v___y_4274_ = v___y_4305_;
                                                    v___y_4275_ = v___y_4306_;
                                                    v___y_4276_ = v___y_4307_;
                                                    v___y_4277_ = v___y_4308_;
                                                    state = 1;
                                                    continue;
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_declName_4317_);
                                                crate::leanh::lean_dec(v_a_4316_);
                                                crate::leanh::lean_dec(v_a_4314_);
                                                crate::leanh::lean_dec_ref(v___y_4302_);
                                                v_a_4326_ =
                                                    crate::leanh::lean_ctor_get(v___x_4322_, 0);
                                                v_isSharedCheck_4333_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_4322_))
                                                        as u8;
                                                if v_isSharedCheck_4333_ == 0 {
                                                    v___x_4328_ = v___x_4322_;
                                                    v_isShared_4329_ = v_isSharedCheck_4333_;
                                                    state = 5;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_4326_);
                                                    crate::leanh::lean_dec(v___x_4322_);
                                                    v___x_4328_ = crate::leanh::lean_box(0);
                                                    v_isShared_4329_ = v_isSharedCheck_4333_;
                                                    state = 5;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_declName_4317_);
                                            crate::leanh::lean_dec(v_a_4316_);
                                            crate::leanh::lean_dec(v_a_4314_);
                                            crate::leanh::lean_dec_ref(v___y_4302_);
                                            return v___x_4321_;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_declName_4317_);
                                        crate::leanh::lean_dec(v_a_4316_);
                                        crate::leanh::lean_dec(v_a_4314_);
                                        crate::leanh::lean_dec_ref(v___y_4302_);
                                        return v___x_4318_;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_4314_);
                                    crate::leanh::lean_dec_ref(v___y_4302_);
                                    crate::leanh::lean_dec_ref(v___y_4300_);
                                    crate::leanh::lean_dec(v_fst_4294_);
                                    crate::leanh::lean_dec(v_fst_4290_);
                                    v_a_4334_ = crate::leanh::lean_ctor_get(v___x_4315_, 0);
                                    v_isSharedCheck_4341_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_4315_)) as u8;
                                    if v_isSharedCheck_4341_ == 0 {
                                        v___x_4336_ = v___x_4315_;
                                        v_isShared_4337_ = v_isSharedCheck_4341_;
                                        state = 7;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_4334_);
                                        crate::leanh::lean_dec(v___x_4315_);
                                        v___x_4336_ = crate::leanh::lean_box(0);
                                        v_isShared_4337_ = v_isSharedCheck_4341_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___y_4302_);
                                crate::leanh::lean_dec_ref(v___y_4300_);
                                crate::leanh::lean_dec(v_fst_4294_);
                                crate::leanh::lean_dec(v_fst_4290_);
                                crate::leanh::lean_dec(v_a_4264_);
                                v_a_4342_ = crate::leanh::lean_ctor_get(v___x_4313_, 0);
                                v_isSharedCheck_4349_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4313_)) as u8;
                                if v_isSharedCheck_4349_ == 0 {
                                    v___x_4344_ = v___x_4313_;
                                    v_isShared_4345_ = v_isSharedCheck_4349_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4342_);
                                    crate::leanh::lean_dec(v___x_4313_);
                                    v___x_4344_ = crate::leanh::lean_box(0);
                                    v_isShared_4345_ = v_isSharedCheck_4349_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___y_4302_);
                            crate::leanh::lean_dec_ref(v___y_4300_);
                            crate::leanh::lean_dec(v_snd_4295_);
                            crate::leanh::lean_dec(v_fst_4294_);
                            crate::leanh::lean_dec(v_fst_4290_);
                            crate::leanh::lean_dec(v_a_4264_);
                            return v___x_4312_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_4302_);
                        crate::leanh::lean_dec_ref(v___y_4300_);
                        crate::leanh::lean_dec(v_snd_4295_);
                        crate::leanh::lean_dec(v_fst_4294_);
                        crate::leanh::lean_dec(v_fst_4290_);
                        crate::leanh::lean_dec(v_a_4264_);
                        crate::leanh::lean_dec_ref(v_docCtx_4251_);
                        return v___x_4311_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4302_);
                    crate::leanh::lean_dec_ref(v___y_4300_);
                    crate::leanh::lean_dec(v_snd_4295_);
                    crate::leanh::lean_dec(v_fst_4294_);
                    crate::leanh::lean_dec(v_fst_4290_);
                    crate::leanh::lean_dec(v_a_4264_);
                    crate::leanh::lean_dec_ref(v_docCtx_4251_);
                    v_a_4350_ = crate::leanh::lean_ctor_get(v___x_4309_, 0);
                    v_isSharedCheck_4357_ = (!crate::leanh::lean_is_exclusive(v___x_4309_)) as u8;
                    if v_isSharedCheck_4357_ == 0 {
                        v___x_4352_ = v___x_4309_;
                        v_isShared_4353_ = v_isSharedCheck_4357_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4350_);
                        crate::leanh::lean_dec(v___x_4309_);
                        v___x_4352_ = crate::leanh::lean_box(0);
                        v_isShared_4353_ = v_isSharedCheck_4357_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_4329_ == 0 {
                    v___x_4331_ = v___x_4328_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4332_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_a_4326_);
                    v___x_4331_ = v_reuseFailAlloc_4332_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4331_;
            }
            7 => {
                if v_isShared_4337_ == 0 {
                    v___x_4339_ = v___x_4336_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4340_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_a_4334_);
                    v___x_4339_ = v_reuseFailAlloc_4340_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4339_;
            }
            9 => {
                if v_isShared_4345_ == 0 {
                    v___x_4347_ = v___x_4344_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4348_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_a_4342_);
                    v___x_4347_ = v_reuseFailAlloc_4348_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4347_;
            }
            11 => {
                if v_isShared_4353_ == 0 {
                    v___x_4355_ = v___x_4352_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4356_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_a_4350_);
                    v___x_4355_ = v_reuseFailAlloc_4356_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4355_;
            }
            13 => {
                v_declName_4369_ = crate::leanh::lean_ctor_get(v_snd_4295_, 3);
                v_type_4370_ = crate::leanh::lean_ctor_get(v_snd_4295_, 6);
                v_numFixed_4371_ = crate::leanh::lean_ctor_get(v_fst_4290_, 0);
                v___x_4372_ = crate::leanh::lean_box_usize(v_sz_4282_);
                v___x_4373_ = l_Lean_Elab_wfRecursion___boxed__const__1;
                crate::leanh::lean_inc(v_fst_4290_);
                crate::leanh::lean_inc(v_declName_4369_);
                crate::leanh::lean_inc(v_fst_4294_);
                crate::leanh::lean_inc(v_snd_4295_);
                crate::leanh::lean_inc(v_a_4264_);
                v___f_4374_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_wfRecursion___lam__4___boxed as *mut core::ffi::c_void,
                    20,
                    11,
                );
                crate::leanh::lean_closure_set(v___f_4374_, 0, v___x_4372_);
                crate::leanh::lean_closure_set(v___f_4374_, 1, v___x_4373_);
                crate::leanh::lean_closure_set(v___f_4374_, 2, v_a_4264_);
                crate::leanh::lean_closure_set(v___f_4374_, 3, v___y_4360_);
                crate::leanh::lean_closure_set(v___f_4374_, 4, v_snd_4295_);
                crate::leanh::lean_closure_set(v___f_4374_, 5, v_fst_4294_);
                crate::leanh::lean_closure_set(v___f_4374_, 6, v___x_4268_);
                crate::leanh::lean_closure_set(v___f_4374_, 7, v___x_4358_);
                crate::leanh::lean_closure_set(v___f_4374_, 8, v_declName_4369_);
                crate::leanh::lean_closure_set(v___f_4374_, 9, v_fst_4290_);
                crate::leanh::lean_closure_set(v___f_4374_, 10, v_wf_4362_);
                crate::leanh::lean_inc(v_numFixed_4371_);
                v___x_4375_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4375_, 0, v_numFixed_4371_);
                v___x_4376_ = 0;
                crate::leanh::lean_inc_ref(v_type_4370_);
                v___x_4377_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Elab_wfRecursion_spec__15___redArg(v_type_4370_, v___x_4375_, v___f_4374_, v___x_4376_, v___x_4376_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
                if crate::leanh::lean_obj_tag(v___x_4377_) == 0 {
                    v_a_4378_ = crate::leanh::lean_ctor_get(v___x_4377_, 0);
                    crate::leanh::lean_inc(v_a_4378_);
                    crate::leanh::lean_dec_ref_known(v___x_4377_, 1);
                    v___x_4379_ = l_Lean_Elab_wfRecursion___lam__1(
                        v___x_4358_,
                        v___y_4363_,
                        v___y_4364_,
                        v___y_4365_,
                        v___y_4366_,
                        v___y_4367_,
                        v___y_4368_,
                    );
                    v_a_4380_ = crate::leanh::lean_ctor_get(v___x_4379_, 0);
                    crate::leanh::lean_inc(v_a_4380_);
                    crate::leanh::lean_dec_ref(v___x_4379_);
                    v___x_4381_ = (crate::leanh::lean_unbox(v_a_4380_) as u8);
                    crate::leanh::lean_dec(v_a_4380_);
                    if v___x_4381_ == 0 {
                        crate::leanh::lean_del_object(v___x_4297_);
                        crate::leanh::lean_del_object(v___x_4292_);
                        v___y_4300_ = v_a_4378_;
                        v___y_4301_ = v___x_4376_;
                        v___y_4302_ = v___y_4361_;
                        v___y_4303_ = v___y_4363_;
                        v___y_4304_ = v___y_4364_;
                        v___y_4305_ = v___y_4365_;
                        v___y_4306_ = v___y_4366_;
                        v___y_4307_ = v___y_4367_;
                        v___y_4308_ = v___y_4368_;
                        state = 4;
                        continue;
                    } else {
                        v_declName_4382_ = crate::leanh::lean_ctor_get(v_a_4378_, 3);
                        v_value_4383_ = crate::leanh::lean_ctor_get(v_a_4378_, 7);
                        v___x_4384_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_wfRecursion___closed__4),
                            core::ptr::addr_of_mut!(l_Lean_Elab_wfRecursion___closed__4_once),
                            _init_l_Lean_Elab_wfRecursion___closed__4,
                        );
                        crate::leanh::lean_inc(v_declName_4382_);
                        v___x_4385_ = l_Lean_MessageData_ofName(v_declName_4382_);
                        if v_isShared_4298_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_4297_, 7);
                            crate::leanh::lean_ctor_set(v___x_4297_, 1, v___x_4385_);
                            crate::leanh::lean_ctor_set(v___x_4297_, 0, v___x_4384_);
                            v___x_4387_ = v___x_4297_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_4395_ =
                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4395_, 0, v___x_4384_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4395_, 1, v___x_4385_);
                            v___x_4387_ = v_reuseFailAlloc_4395_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_4361_);
                    crate::leanh::lean_del_object(v___x_4297_);
                    crate::leanh::lean_dec(v_snd_4295_);
                    crate::leanh::lean_dec(v_fst_4294_);
                    crate::leanh::lean_del_object(v___x_4292_);
                    crate::leanh::lean_dec(v_fst_4290_);
                    crate::leanh::lean_dec(v_a_4264_);
                    crate::leanh::lean_dec_ref(v_docCtx_4251_);
                    v_a_4396_ = crate::leanh::lean_ctor_get(v___x_4377_, 0);
                    v_isSharedCheck_4403_ = (!crate::leanh::lean_is_exclusive(v___x_4377_)) as u8;
                    if v_isSharedCheck_4403_ == 0 {
                        v___x_4398_ = v___x_4377_;
                        v_isShared_4399_ = v_isSharedCheck_4403_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4396_);
                        crate::leanh::lean_dec(v___x_4377_);
                        v___x_4398_ = crate::leanh::lean_box(0);
                        v_isShared_4399_ = v_isSharedCheck_4403_;
                        state = 16;
                        continue;
                    }
                }
            }
            14 => {
                v___x_4388_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_wfRecursion___closed__6),
                    core::ptr::addr_of_mut!(l_Lean_Elab_wfRecursion___closed__6_once),
                    _init_l_Lean_Elab_wfRecursion___closed__6,
                );
                if v_isShared_4293_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4292_, 7);
                    crate::leanh::lean_ctor_set(v___x_4292_, 1, v___x_4388_);
                    crate::leanh::lean_ctor_set(v___x_4292_, 0, v___x_4387_);
                    v___x_4390_ = v___x_4292_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4394_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4394_, 0, v___x_4387_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4394_, 1, v___x_4388_);
                    v___x_4390_ = v_reuseFailAlloc_4394_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                crate::leanh::lean_inc_ref(v_value_4383_);
                v___x_4391_ = l_Lean_MessageData_ofExpr(v_value_4383_);
                v___x_4392_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4392_, 0, v___x_4390_);
                crate::leanh::lean_ctor_set(v___x_4392_, 1, v___x_4391_);
                v___x_4393_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(
                    v___x_4358_,
                    v___x_4392_,
                    v___y_4365_,
                    v___y_4366_,
                    v___y_4367_,
                    v___y_4368_,
                );
                if crate::leanh::lean_obj_tag(v___x_4393_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4393_, 1);
                    v___y_4300_ = v_a_4378_;
                    v___y_4301_ = v___x_4376_;
                    v___y_4302_ = v___y_4361_;
                    v___y_4303_ = v___y_4363_;
                    v___y_4304_ = v___y_4364_;
                    v___y_4305_ = v___y_4365_;
                    v___y_4306_ = v___y_4366_;
                    v___y_4307_ = v___y_4367_;
                    v___y_4308_ = v___y_4368_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_4378_);
                    crate::leanh::lean_dec_ref(v___y_4361_);
                    crate::leanh::lean_dec(v_snd_4295_);
                    crate::leanh::lean_dec(v_fst_4294_);
                    crate::leanh::lean_dec(v_fst_4290_);
                    crate::leanh::lean_dec(v_a_4264_);
                    crate::leanh::lean_dec_ref(v_docCtx_4251_);
                    return v___x_4393_;
                }
            }
            16 => {
                if v_isShared_4399_ == 0 {
                    v___x_4401_ = v___x_4398_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_4402_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_a_4396_);
                    v___x_4401_ = v_reuseFailAlloc_4402_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_4401_;
            }
            18 => {
                if crate::leanh::lean_obj_tag(v_termMeasures_x3f_4408_) == 1 {
                    crate::leanh::lean_dec_ref(v___y_4411_);
                    v_val_4419_ = crate::leanh::lean_ctor_get(v_termMeasures_x3f_4408_, 0);
                    crate::leanh::lean_inc(v_val_4419_);
                    crate::leanh::lean_dec_ref_known(v_termMeasures_x3f_4408_, 1);
                    v___y_4360_ = v___y_4410_;
                    v___y_4361_ = v___y_4412_;
                    v_wf_4362_ = v_val_4419_;
                    v___y_4363_ = v___y_4413_;
                    v___y_4364_ = v___y_4414_;
                    v___y_4365_ = v___y_4415_;
                    v___y_4366_ = v___y_4416_;
                    v___y_4367_ = v___y_4417_;
                    v___y_4368_ = v___y_4418_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_termMeasures_x3f_4408_);
                    v___x_4420_ = 1;
                    v___x_4421_ =
                        l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(
                            v___y_4411_,
                            v___x_4420_,
                            v___y_4413_,
                            v___y_4414_,
                            v___y_4415_,
                            v___y_4416_,
                            v___y_4417_,
                            v___y_4418_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_4421_) == 0 {
                        v_a_4422_ = crate::leanh::lean_ctor_get(v___x_4421_, 0);
                        crate::leanh::lean_inc(v_a_4422_);
                        crate::leanh::lean_dec_ref_known(v___x_4421_, 1);
                        v___y_4360_ = v___y_4410_;
                        v___y_4361_ = v___y_4412_;
                        v_wf_4362_ = v_a_4422_;
                        v___y_4363_ = v___y_4413_;
                        v___y_4364_ = v___y_4414_;
                        v___y_4365_ = v___y_4415_;
                        v___y_4366_ = v___y_4416_;
                        v___y_4367_ = v___y_4417_;
                        v___y_4368_ = v___y_4418_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_4412_);
                        crate::leanh::lean_dec_ref(v___y_4410_);
                        crate::leanh::lean_del_object(v___x_4297_);
                        crate::leanh::lean_dec(v_snd_4295_);
                        crate::leanh::lean_dec(v_fst_4294_);
                        crate::leanh::lean_del_object(v___x_4292_);
                        crate::leanh::lean_dec(v_fst_4290_);
                        crate::leanh::lean_dec(v_a_4264_);
                        crate::leanh::lean_dec_ref(v_docCtx_4251_);
                        v_a_4423_ = crate::leanh::lean_ctor_get(v___x_4421_, 0);
                        v_isSharedCheck_4430_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4421_)) as u8;
                        if v_isSharedCheck_4430_ == 0 {
                            v___x_4425_ = v___x_4421_;
                            v_isShared_4426_ = v_isSharedCheck_4430_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4423_);
                            crate::leanh::lean_dec(v___x_4421_);
                            v___x_4425_ = crate::leanh::lean_box(0);
                            v_isShared_4426_ = v_isSharedCheck_4430_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            19 => {
                if v_isShared_4426_ == 0 {
                    v___x_4428_ = v___x_4425_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4429_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_a_4423_);
                    v___x_4428_ = v_reuseFailAlloc_4429_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4428_;
            }
            21 => {
                v___x_4438_ = lean_st_ref_get(v___y_4437_);
                v_env_4439_ = crate::leanh::lean_ctor_get(v___x_4438_, 0);
                crate::leanh::lean_inc_ref(v_env_4439_);
                crate::leanh::lean_dec(v___x_4438_);
                v___x_4440_ = l_Lean_Environment_unlockAsync(v_env_4439_);
                v___x_4441_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(
                    v___x_4440_,
                    v___f_4406_,
                    v___y_4432_,
                    v___y_4433_,
                    v___y_4434_,
                    v___y_4435_,
                    v___y_4436_,
                    v___y_4437_,
                );
                if crate::leanh::lean_obj_tag(v___x_4441_) == 0 {
                    v_a_4442_ = crate::leanh::lean_ctor_get(v___x_4441_, 0);
                    crate::leanh::lean_inc(v_a_4442_);
                    crate::leanh::lean_dec_ref_known(v___x_4441_, 1);
                    v_fst_4443_ = crate::leanh::lean_ctor_get(v_a_4442_, 0);
                    v_snd_4444_ = crate::leanh::lean_ctor_get(v_a_4442_, 1);
                    v_isSharedCheck_4460_ = (!crate::leanh::lean_is_exclusive(v_a_4442_)) as u8;
                    if v_isSharedCheck_4460_ == 0 {
                        v___x_4446_ = v_a_4442_;
                        v_isShared_4447_ = v_isSharedCheck_4460_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4444_);
                        crate::leanh::lean_inc(v_fst_4443_);
                        crate::leanh::lean_dec(v_a_4442_);
                        v___x_4446_ = crate::leanh::lean_box(0);
                        v_isShared_4447_ = v_isSharedCheck_4460_;
                        state = 22;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_termMeasures_x3f_4408_);
                    crate::leanh::lean_del_object(v___x_4297_);
                    crate::leanh::lean_dec(v_snd_4295_);
                    crate::leanh::lean_dec(v_fst_4294_);
                    crate::leanh::lean_del_object(v___x_4292_);
                    crate::leanh::lean_dec(v_fst_4290_);
                    crate::leanh::lean_dec(v_a_4264_);
                    crate::leanh::lean_dec_ref(v_docCtx_4251_);
                    v_a_4461_ = crate::leanh::lean_ctor_get(v___x_4441_, 0);
                    v_isSharedCheck_4468_ = (!crate::leanh::lean_is_exclusive(v___x_4441_)) as u8;
                    if v_isSharedCheck_4468_ == 0 {
                        v___x_4463_ = v___x_4441_;
                        v_isShared_4464_ = v_isSharedCheck_4468_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4461_);
                        crate::leanh::lean_dec(v___x_4441_);
                        v___x_4463_ = crate::leanh::lean_box(0);
                        v_isShared_4464_ = v_isSharedCheck_4468_;
                        state = 24;
                        continue;
                    }
                }
            }
            22 => {
                v___x_4448_ = l_Lean_Elab_wfRecursion___lam__1(
                    v___x_4358_,
                    v___y_4432_,
                    v___y_4433_,
                    v___y_4434_,
                    v___y_4435_,
                    v___y_4436_,
                    v___y_4437_,
                );
                v_a_4449_ = crate::leanh::lean_ctor_get(v___x_4448_, 0);
                crate::leanh::lean_inc(v_a_4449_);
                crate::leanh::lean_dec_ref(v___x_4448_);
                crate::leanh::lean_inc(v_fst_4294_);
                crate::leanh::lean_inc(v_fst_4290_);
                crate::leanh::lean_inc(v_fst_4443_);
                crate::leanh::lean_inc(v_a_4264_);
                v___f_4450_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_wfRecursion___lam__5___boxed as *mut core::ffi::c_void,
                    11,
                    4,
                );
                crate::leanh::lean_closure_set(v___f_4450_, 0, v_a_4264_);
                crate::leanh::lean_closure_set(v___f_4450_, 1, v_fst_4443_);
                crate::leanh::lean_closure_set(v___f_4450_, 2, v_fst_4290_);
                crate::leanh::lean_closure_set(v___f_4450_, 3, v_fst_4294_);
                v___x_4451_ = (crate::leanh::lean_unbox(v_a_4449_) as u8);
                crate::leanh::lean_dec(v_a_4449_);
                if v___x_4451_ == 0 {
                    crate::leanh::lean_del_object(v___x_4446_);
                    v___y_4410_ = v_fst_4443_;
                    v___y_4411_ = v___f_4450_;
                    v___y_4412_ = v_snd_4444_;
                    v___y_4413_ = v___y_4432_;
                    v___y_4414_ = v___y_4433_;
                    v___y_4415_ = v___y_4434_;
                    v___y_4416_ = v___y_4435_;
                    v___y_4417_ = v___y_4436_;
                    v___y_4418_ = v___y_4437_;
                    state = 18;
                    continue;
                } else {
                    v_value_4452_ = crate::leanh::lean_ctor_get(v_snd_4295_, 7);
                    v___x_4453_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_wfRecursion___closed__8),
                        core::ptr::addr_of_mut!(l_Lean_Elab_wfRecursion___closed__8_once),
                        _init_l_Lean_Elab_wfRecursion___closed__8,
                    );
                    crate::leanh::lean_inc_ref(v_value_4452_);
                    v___x_4454_ = l_Lean_MessageData_ofExpr(v_value_4452_);
                    v___x_4455_ = l_Lean_indentD(v___x_4454_);
                    if v_isShared_4447_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4446_, 7);
                        crate::leanh::lean_ctor_set(v___x_4446_, 1, v___x_4455_);
                        crate::leanh::lean_ctor_set(v___x_4446_, 0, v___x_4453_);
                        v___x_4457_ = v___x_4446_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_4459_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4459_, 0, v___x_4453_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4459_, 1, v___x_4455_);
                        v___x_4457_ = v_reuseFailAlloc_4459_;
                        state = 23;
                        continue;
                    }
                }
            }
            23 => {
                v___x_4458_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(
                    v___x_4358_,
                    v___x_4457_,
                    v___y_4434_,
                    v___y_4435_,
                    v___y_4436_,
                    v___y_4437_,
                );
                if crate::leanh::lean_obj_tag(v___x_4458_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4458_, 1);
                    v___y_4410_ = v_fst_4443_;
                    v___y_4411_ = v___f_4450_;
                    v___y_4412_ = v_snd_4444_;
                    v___y_4413_ = v___y_4432_;
                    v___y_4414_ = v___y_4433_;
                    v___y_4415_ = v___y_4434_;
                    v___y_4416_ = v___y_4435_;
                    v___y_4417_ = v___y_4436_;
                    v___y_4418_ = v___y_4437_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___f_4450_);
                    crate::leanh::lean_dec(v_snd_4444_);
                    crate::leanh::lean_dec(v_fst_4443_);
                    crate::leanh::lean_dec(v_termMeasures_x3f_4408_);
                    crate::leanh::lean_del_object(v___x_4297_);
                    crate::leanh::lean_dec(v_snd_4295_);
                    crate::leanh::lean_dec(v_fst_4294_);
                    crate::leanh::lean_del_object(v___x_4292_);
                    crate::leanh::lean_dec(v_fst_4290_);
                    crate::leanh::lean_dec(v_a_4264_);
                    crate::leanh::lean_dec_ref(v_docCtx_4251_);
                    return v___x_4458_;
                }
            }
            24 => {
                if v_isShared_4464_ == 0 {
                    v___x_4466_ = v___x_4463_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4467_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_a_4461_);
                    v___x_4466_ = v_reuseFailAlloc_4467_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_4466_;
            }
            26 => {
                if v_isShared_4481_ == 0 {
                    v___x_4483_ = v___x_4480_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4484_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_a_4478_);
                    v___x_4483_ = v_reuseFailAlloc_4484_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_4483_;
            }
            28 => {
                if v_isShared_4489_ == 0 {
                    v___x_4491_ = v___x_4488_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4492_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_a_4486_);
                    v___x_4491_ = v_reuseFailAlloc_4492_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_4491_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_wfRecursion___boxed(
    mut v_docCtx_4494_: *mut crate::leanh::LeanObject,
    mut v_preDefs_4495_: *mut crate::leanh::LeanObject,
    mut v_termMeasure_x3fs_4496_: *mut crate::leanh::LeanObject,
    mut v_a_4497_: *mut crate::leanh::LeanObject,
    mut v_a_4498_: *mut crate::leanh::LeanObject,
    mut v_a_4499_: *mut crate::leanh::LeanObject,
    mut v_a_4500_: *mut crate::leanh::LeanObject,
    mut v_a_4501_: *mut crate::leanh::LeanObject,
    mut v_a_4502_: *mut crate::leanh::LeanObject,
    mut v_a_4503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4504_ = l_Lean_Elab_wfRecursion(
        v_docCtx_4494_,
        v_preDefs_4495_,
        v_termMeasure_x3fs_4496_,
        v_a_4497_,
        v_a_4498_,
        v_a_4499_,
        v_a_4500_,
        v_a_4501_,
        v_a_4502_,
    );
    crate::leanh::lean_dec(v_a_4502_);
    crate::leanh::lean_dec_ref(v_a_4501_);
    crate::leanh::lean_dec(v_a_4500_);
    crate::leanh::lean_dec_ref(v_a_4499_);
    crate::leanh::lean_dec(v_a_4498_);
    crate::leanh::lean_dec_ref(v_a_4497_);
    return v_res_4504_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(
    mut v_00_u03b1_4505_: *mut crate::leanh::LeanObject,
    mut v_msg_4506_: *mut crate::leanh::LeanObject,
    mut v___y_4507_: *mut crate::leanh::LeanObject,
    mut v___y_4508_: *mut crate::leanh::LeanObject,
    mut v___y_4509_: *mut crate::leanh::LeanObject,
    mut v___y_4510_: *mut crate::leanh::LeanObject,
    mut v___y_4511_: *mut crate::leanh::LeanObject,
    mut v___y_4512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4514_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___redArg(
        v_msg_4506_,
        v___y_4507_,
        v___y_4508_,
        v___y_4509_,
        v___y_4510_,
        v___y_4511_,
        v___y_4512_,
    );
    return v___x_4514_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0___boxed(
    mut v_00_u03b1_4515_: *mut crate::leanh::LeanObject,
    mut v_msg_4516_: *mut crate::leanh::LeanObject,
    mut v___y_4517_: *mut crate::leanh::LeanObject,
    mut v___y_4518_: *mut crate::leanh::LeanObject,
    mut v___y_4519_: *mut crate::leanh::LeanObject,
    mut v___y_4520_: *mut crate::leanh::LeanObject,
    mut v___y_4521_: *mut crate::leanh::LeanObject,
    mut v___y_4522_: *mut crate::leanh::LeanObject,
    mut v___y_4523_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4524_ = l_Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0(
        v_00_u03b1_4515_,
        v_msg_4516_,
        v___y_4517_,
        v___y_4518_,
        v___y_4519_,
        v___y_4520_,
        v___y_4521_,
        v___y_4522_,
    );
    crate::leanh::lean_dec(v___y_4522_);
    crate::leanh::lean_dec_ref(v___y_4521_);
    crate::leanh::lean_dec(v___y_4520_);
    crate::leanh::lean_dec_ref(v___y_4519_);
    crate::leanh::lean_dec(v___y_4518_);
    crate::leanh::lean_dec_ref(v___y_4517_);
    return v_res_4524_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(
    mut v_sz_4525_: usize,
    mut v_i_4526_: usize,
    mut v_bs_4527_: *mut crate::leanh::LeanObject,
    mut v___y_4528_: *mut crate::leanh::LeanObject,
    mut v___y_4529_: *mut crate::leanh::LeanObject,
    mut v___y_4530_: *mut crate::leanh::LeanObject,
    mut v___y_4531_: *mut crate::leanh::LeanObject,
    mut v___y_4532_: *mut crate::leanh::LeanObject,
    mut v___y_4533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4535_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___redArg(v_sz_4525_, v_i_4526_, v_bs_4527_, v___y_4532_, v___y_4533_);
    return v___x_4535_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1___boxed(
    mut v_sz_4536_: *mut crate::leanh::LeanObject,
    mut v_i_4537_: *mut crate::leanh::LeanObject,
    mut v_bs_4538_: *mut crate::leanh::LeanObject,
    mut v___y_4539_: *mut crate::leanh::LeanObject,
    mut v___y_4540_: *mut crate::leanh::LeanObject,
    mut v___y_4541_: *mut crate::leanh::LeanObject,
    mut v___y_4542_: *mut crate::leanh::LeanObject,
    mut v___y_4543_: *mut crate::leanh::LeanObject,
    mut v___y_4544_: *mut crate::leanh::LeanObject,
    mut v___y_4545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4546_: usize = 0;
    let mut v_i_boxed_4547_: usize = 0;
    let mut v_res_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4546_ = crate::leanh::lean_unbox_usize(v_sz_4536_);
    crate::leanh::lean_dec(v_sz_4536_);
    v_i_boxed_4547_ = crate::leanh::lean_unbox_usize(v_i_4537_);
    crate::leanh::lean_dec(v_i_4537_);
    v_res_4548_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__1(v_sz_boxed_4546_, v_i_boxed_4547_, v_bs_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_, v___y_4543_, v___y_4544_);
    crate::leanh::lean_dec(v___y_4544_);
    crate::leanh::lean_dec_ref(v___y_4543_);
    crate::leanh::lean_dec(v___y_4542_);
    crate::leanh::lean_dec_ref(v___y_4541_);
    crate::leanh::lean_dec(v___y_4540_);
    crate::leanh::lean_dec_ref(v___y_4539_);
    return v_res_4548_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2(
    mut v_as_4549_: *mut crate::leanh::LeanObject,
    mut v_sz_4550_: usize,
    mut v_i_4551_: usize,
    mut v_b_4552_: *mut crate::leanh::LeanObject,
    mut v___y_4553_: *mut crate::leanh::LeanObject,
    mut v___y_4554_: *mut crate::leanh::LeanObject,
    mut v___y_4555_: *mut crate::leanh::LeanObject,
    mut v___y_4556_: *mut crate::leanh::LeanObject,
    mut v___y_4557_: *mut crate::leanh::LeanObject,
    mut v___y_4558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___redArg(v_as_4549_, v_sz_4550_, v_i_4551_, v_b_4552_, v___y_4557_, v___y_4558_);
    return v___x_4560_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2___boxed(
    mut v_as_4561_: *mut crate::leanh::LeanObject,
    mut v_sz_4562_: *mut crate::leanh::LeanObject,
    mut v_i_4563_: *mut crate::leanh::LeanObject,
    mut v_b_4564_: *mut crate::leanh::LeanObject,
    mut v___y_4565_: *mut crate::leanh::LeanObject,
    mut v___y_4566_: *mut crate::leanh::LeanObject,
    mut v___y_4567_: *mut crate::leanh::LeanObject,
    mut v___y_4568_: *mut crate::leanh::LeanObject,
    mut v___y_4569_: *mut crate::leanh::LeanObject,
    mut v___y_4570_: *mut crate::leanh::LeanObject,
    mut v___y_4571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4572_: usize = 0;
    let mut v_i_boxed_4573_: usize = 0;
    let mut v_res_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4572_ = crate::leanh::lean_unbox_usize(v_sz_4562_);
    crate::leanh::lean_dec(v_sz_4562_);
    v_i_boxed_4573_ = crate::leanh::lean_unbox_usize(v_i_4563_);
    crate::leanh::lean_dec(v_i_4563_);
    v_res_4574_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__2(v_as_4561_, v_sz_boxed_4572_, v_i_boxed_4573_, v_b_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_, v___y_4570_);
    crate::leanh::lean_dec(v___y_4570_);
    crate::leanh::lean_dec_ref(v___y_4569_);
    crate::leanh::lean_dec(v___y_4568_);
    crate::leanh::lean_dec_ref(v___y_4567_);
    crate::leanh::lean_dec(v___y_4566_);
    crate::leanh::lean_dec_ref(v___y_4565_);
    crate::leanh::lean_dec_ref(v_as_4561_);
    return v_res_4574_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3(
    mut v_a_4575_: *mut crate::leanh::LeanObject,
    mut v_as_4576_: *mut crate::leanh::LeanObject,
    mut v_i_4577_: *mut crate::leanh::LeanObject,
    mut v_j_4578_: *mut crate::leanh::LeanObject,
    mut v_inv_4579_: *mut crate::leanh::LeanObject,
    mut v_bs_4580_: *mut crate::leanh::LeanObject,
    mut v___y_4581_: *mut crate::leanh::LeanObject,
    mut v___y_4582_: *mut crate::leanh::LeanObject,
    mut v___y_4583_: *mut crate::leanh::LeanObject,
    mut v___y_4584_: *mut crate::leanh::LeanObject,
    mut v___y_4585_: *mut crate::leanh::LeanObject,
    mut v___y_4586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4588_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___redArg(
        v_a_4575_,
        v_as_4576_,
        v_i_4577_,
        v_j_4578_,
        v_bs_4580_,
        v___y_4583_,
        v___y_4584_,
        v___y_4585_,
        v___y_4586_,
    );
    return v___x_4588_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3___boxed(
    mut v_a_4589_: *mut crate::leanh::LeanObject,
    mut v_as_4590_: *mut crate::leanh::LeanObject,
    mut v_i_4591_: *mut crate::leanh::LeanObject,
    mut v_j_4592_: *mut crate::leanh::LeanObject,
    mut v_inv_4593_: *mut crate::leanh::LeanObject,
    mut v_bs_4594_: *mut crate::leanh::LeanObject,
    mut v___y_4595_: *mut crate::leanh::LeanObject,
    mut v___y_4596_: *mut crate::leanh::LeanObject,
    mut v___y_4597_: *mut crate::leanh::LeanObject,
    mut v___y_4598_: *mut crate::leanh::LeanObject,
    mut v___y_4599_: *mut crate::leanh::LeanObject,
    mut v___y_4600_: *mut crate::leanh::LeanObject,
    mut v___y_4601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4602_ = l_Array_mapFinIdxM_map___at___00Lean_Elab_wfRecursion_spec__3(
        v_a_4589_,
        v_as_4590_,
        v_i_4591_,
        v_j_4592_,
        v_inv_4593_,
        v_bs_4594_,
        v___y_4595_,
        v___y_4596_,
        v___y_4597_,
        v___y_4598_,
        v___y_4599_,
        v___y_4600_,
    );
    crate::leanh::lean_dec(v___y_4600_);
    crate::leanh::lean_dec_ref(v___y_4599_);
    crate::leanh::lean_dec(v___y_4598_);
    crate::leanh::lean_dec_ref(v___y_4597_);
    crate::leanh::lean_dec(v___y_4596_);
    crate::leanh::lean_dec_ref(v___y_4595_);
    crate::leanh::lean_dec_ref(v_as_4590_);
    return v_res_4602_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(
    mut v_a_4603_: *mut crate::leanh::LeanObject,
    mut v___x_4604_: *mut crate::leanh::LeanObject,
    mut v_sz_4605_: usize,
    mut v_i_4606_: usize,
    mut v_bs_4607_: *mut crate::leanh::LeanObject,
    mut v___y_4608_: *mut crate::leanh::LeanObject,
    mut v___y_4609_: *mut crate::leanh::LeanObject,
    mut v___y_4610_: *mut crate::leanh::LeanObject,
    mut v___y_4611_: *mut crate::leanh::LeanObject,
    mut v___y_4612_: *mut crate::leanh::LeanObject,
    mut v___y_4613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4615_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___redArg(v_a_4603_, v___x_4604_, v_sz_4605_, v_i_4606_, v_bs_4607_, v___y_4612_, v___y_4613_);
    return v___x_4615_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6___boxed(
    mut v_a_4616_: *mut crate::leanh::LeanObject,
    mut v___x_4617_: *mut crate::leanh::LeanObject,
    mut v_sz_4618_: *mut crate::leanh::LeanObject,
    mut v_i_4619_: *mut crate::leanh::LeanObject,
    mut v_bs_4620_: *mut crate::leanh::LeanObject,
    mut v___y_4621_: *mut crate::leanh::LeanObject,
    mut v___y_4622_: *mut crate::leanh::LeanObject,
    mut v___y_4623_: *mut crate::leanh::LeanObject,
    mut v___y_4624_: *mut crate::leanh::LeanObject,
    mut v___y_4625_: *mut crate::leanh::LeanObject,
    mut v___y_4626_: *mut crate::leanh::LeanObject,
    mut v___y_4627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4628_: usize = 0;
    let mut v_i_boxed_4629_: usize = 0;
    let mut v_res_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4628_ = crate::leanh::lean_unbox_usize(v_sz_4618_);
    crate::leanh::lean_dec(v_sz_4618_);
    v_i_boxed_4629_ = crate::leanh::lean_unbox_usize(v_i_4619_);
    crate::leanh::lean_dec(v_i_4619_);
    v_res_4630_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__6(v_a_4616_, v___x_4617_, v_sz_boxed_4628_, v_i_boxed_4629_, v_bs_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_);
    crate::leanh::lean_dec(v___y_4626_);
    crate::leanh::lean_dec_ref(v___y_4625_);
    crate::leanh::lean_dec(v___y_4624_);
    crate::leanh::lean_dec_ref(v___y_4623_);
    crate::leanh::lean_dec(v___y_4622_);
    crate::leanh::lean_dec_ref(v___y_4621_);
    return v_res_4630_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7(
    mut v_00_u03b1_4631_: *mut crate::leanh::LeanObject,
    mut v_env_4632_: *mut crate::leanh::LeanObject,
    mut v_x_4633_: *mut crate::leanh::LeanObject,
    mut v___y_4634_: *mut crate::leanh::LeanObject,
    mut v___y_4635_: *mut crate::leanh::LeanObject,
    mut v___y_4636_: *mut crate::leanh::LeanObject,
    mut v___y_4637_: *mut crate::leanh::LeanObject,
    mut v___y_4638_: *mut crate::leanh::LeanObject,
    mut v___y_4639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4641_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___redArg(
        v_env_4632_,
        v_x_4633_,
        v___y_4634_,
        v___y_4635_,
        v___y_4636_,
        v___y_4637_,
        v___y_4638_,
        v___y_4639_,
    );
    return v___x_4641_;
}
pub unsafe fn l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7___boxed(
    mut v_00_u03b1_4642_: *mut crate::leanh::LeanObject,
    mut v_env_4643_: *mut crate::leanh::LeanObject,
    mut v_x_4644_: *mut crate::leanh::LeanObject,
    mut v___y_4645_: *mut crate::leanh::LeanObject,
    mut v___y_4646_: *mut crate::leanh::LeanObject,
    mut v___y_4647_: *mut crate::leanh::LeanObject,
    mut v___y_4648_: *mut crate::leanh::LeanObject,
    mut v___y_4649_: *mut crate::leanh::LeanObject,
    mut v___y_4650_: *mut crate::leanh::LeanObject,
    mut v___y_4651_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4652_ = l_Lean_withEnv___at___00Lean_Elab_wfRecursion_spec__7(
        v_00_u03b1_4642_,
        v_env_4643_,
        v_x_4644_,
        v___y_4645_,
        v___y_4646_,
        v___y_4647_,
        v___y_4648_,
        v___y_4649_,
        v___y_4650_,
    );
    crate::leanh::lean_dec(v___y_4650_);
    crate::leanh::lean_dec_ref(v___y_4649_);
    crate::leanh::lean_dec(v___y_4648_);
    crate::leanh::lean_dec_ref(v___y_4647_);
    crate::leanh::lean_dec(v___y_4646_);
    crate::leanh::lean_dec_ref(v___y_4645_);
    return v_res_4652_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(
    mut v_cls_4653_: *mut crate::leanh::LeanObject,
    mut v_msg_4654_: *mut crate::leanh::LeanObject,
    mut v___y_4655_: *mut crate::leanh::LeanObject,
    mut v___y_4656_: *mut crate::leanh::LeanObject,
    mut v___y_4657_: *mut crate::leanh::LeanObject,
    mut v___y_4658_: *mut crate::leanh::LeanObject,
    mut v___y_4659_: *mut crate::leanh::LeanObject,
    mut v___y_4660_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4662_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___redArg(
        v_cls_4653_,
        v_msg_4654_,
        v___y_4657_,
        v___y_4658_,
        v___y_4659_,
        v___y_4660_,
    );
    return v___x_4662_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14___boxed(
    mut v_cls_4663_: *mut crate::leanh::LeanObject,
    mut v_msg_4664_: *mut crate::leanh::LeanObject,
    mut v___y_4665_: *mut crate::leanh::LeanObject,
    mut v___y_4666_: *mut crate::leanh::LeanObject,
    mut v___y_4667_: *mut crate::leanh::LeanObject,
    mut v___y_4668_: *mut crate::leanh::LeanObject,
    mut v___y_4669_: *mut crate::leanh::LeanObject,
    mut v___y_4670_: *mut crate::leanh::LeanObject,
    mut v___y_4671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4672_ = l_Lean_addTrace___at___00Lean_Elab_wfRecursion_spec__14(
        v_cls_4663_,
        v_msg_4664_,
        v___y_4665_,
        v___y_4666_,
        v___y_4667_,
        v___y_4668_,
        v___y_4669_,
        v___y_4670_,
    );
    crate::leanh::lean_dec(v___y_4670_);
    crate::leanh::lean_dec_ref(v___y_4669_);
    crate::leanh::lean_dec(v___y_4668_);
    crate::leanh::lean_dec_ref(v___y_4667_);
    crate::leanh::lean_dec(v___y_4666_);
    crate::leanh::lean_dec_ref(v___y_4665_);
    return v_res_4672_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(
    mut v_sz_4673_: usize,
    mut v_i_4674_: usize,
    mut v_bs_4675_: *mut crate::leanh::LeanObject,
    mut v___y_4676_: *mut crate::leanh::LeanObject,
    mut v___y_4677_: *mut crate::leanh::LeanObject,
    mut v___y_4678_: *mut crate::leanh::LeanObject,
    mut v___y_4679_: *mut crate::leanh::LeanObject,
    mut v___y_4680_: *mut crate::leanh::LeanObject,
    mut v___y_4681_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4683_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___redArg(v_sz_4673_, v_i_4674_, v_bs_4675_, v___y_4678_, v___y_4679_, v___y_4680_, v___y_4681_);
    return v___x_4683_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16___boxed(
    mut v_sz_4684_: *mut crate::leanh::LeanObject,
    mut v_i_4685_: *mut crate::leanh::LeanObject,
    mut v_bs_4686_: *mut crate::leanh::LeanObject,
    mut v___y_4687_: *mut crate::leanh::LeanObject,
    mut v___y_4688_: *mut crate::leanh::LeanObject,
    mut v___y_4689_: *mut crate::leanh::LeanObject,
    mut v___y_4690_: *mut crate::leanh::LeanObject,
    mut v___y_4691_: *mut crate::leanh::LeanObject,
    mut v___y_4692_: *mut crate::leanh::LeanObject,
    mut v___y_4693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4694_: usize = 0;
    let mut v_i_boxed_4695_: usize = 0;
    let mut v_res_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4694_ = crate::leanh::lean_unbox_usize(v_sz_4684_);
    crate::leanh::lean_dec(v_sz_4684_);
    v_i_boxed_4695_ = crate::leanh::lean_unbox_usize(v_i_4685_);
    crate::leanh::lean_dec(v_i_4685_);
    v_res_4696_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_wfRecursion_spec__16(v_sz_boxed_4694_, v_i_boxed_4695_, v_bs_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_);
    crate::leanh::lean_dec(v___y_4692_);
    crate::leanh::lean_dec_ref(v___y_4691_);
    crate::leanh::lean_dec(v___y_4690_);
    crate::leanh::lean_dec_ref(v___y_4689_);
    crate::leanh::lean_dec(v___y_4688_);
    crate::leanh::lean_dec_ref(v___y_4687_);
    return v_res_4696_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(
    mut v___x_4697_: *mut crate::leanh::LeanObject,
    mut v_as_4698_: *mut crate::leanh::LeanObject,
    mut v_sz_4699_: usize,
    mut v_i_4700_: usize,
    mut v_b_4701_: *mut crate::leanh::LeanObject,
    mut v___y_4702_: *mut crate::leanh::LeanObject,
    mut v___y_4703_: *mut crate::leanh::LeanObject,
    mut v___y_4704_: *mut crate::leanh::LeanObject,
    mut v___y_4705_: *mut crate::leanh::LeanObject,
    mut v___y_4706_: *mut crate::leanh::LeanObject,
    mut v___y_4707_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4709_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___redArg(v___x_4697_, v_as_4698_, v_sz_4699_, v_i_4700_, v_b_4701_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_);
    return v___x_4709_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17___boxed(
    mut v___x_4710_: *mut crate::leanh::LeanObject,
    mut v_as_4711_: *mut crate::leanh::LeanObject,
    mut v_sz_4712_: *mut crate::leanh::LeanObject,
    mut v_i_4713_: *mut crate::leanh::LeanObject,
    mut v_b_4714_: *mut crate::leanh::LeanObject,
    mut v___y_4715_: *mut crate::leanh::LeanObject,
    mut v___y_4716_: *mut crate::leanh::LeanObject,
    mut v___y_4717_: *mut crate::leanh::LeanObject,
    mut v___y_4718_: *mut crate::leanh::LeanObject,
    mut v___y_4719_: *mut crate::leanh::LeanObject,
    mut v___y_4720_: *mut crate::leanh::LeanObject,
    mut v___y_4721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4722_: usize = 0;
    let mut v_i_boxed_4723_: usize = 0;
    let mut v_res_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4722_ = crate::leanh::lean_unbox_usize(v_sz_4712_);
    crate::leanh::lean_dec(v_sz_4712_);
    v_i_boxed_4723_ = crate::leanh::lean_unbox_usize(v_i_4713_);
    crate::leanh::lean_dec(v_i_4713_);
    v_res_4724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_wfRecursion_spec__17(v___x_4710_, v_as_4711_, v_sz_boxed_4722_, v_i_boxed_4723_, v_b_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
    crate::leanh::lean_dec(v___y_4720_);
    crate::leanh::lean_dec_ref(v___y_4719_);
    crate::leanh::lean_dec(v___y_4718_);
    crate::leanh::lean_dec_ref(v___y_4717_);
    crate::leanh::lean_dec(v___y_4716_);
    crate::leanh::lean_dec_ref(v___y_4715_);
    crate::leanh::lean_dec_ref(v_as_4711_);
    return v_res_4724_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(
    mut v_00_u03b1_4725_: *mut crate::leanh::LeanObject,
    mut v_x_4726_: *mut crate::leanh::LeanObject,
    mut v_isExporting_4727_: u8,
    mut v___y_4728_: *mut crate::leanh::LeanObject,
    mut v___y_4729_: *mut crate::leanh::LeanObject,
    mut v___y_4730_: *mut crate::leanh::LeanObject,
    mut v___y_4731_: *mut crate::leanh::LeanObject,
    mut v___y_4732_: *mut crate::leanh::LeanObject,
    mut v___y_4733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4735_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___redArg(v_x_4726_, v_isExporting_4727_, v___y_4728_, v___y_4729_, v___y_4730_, v___y_4731_, v___y_4732_, v___y_4733_);
    return v___x_4735_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21___boxed(
    mut v_00_u03b1_4736_: *mut crate::leanh::LeanObject,
    mut v_x_4737_: *mut crate::leanh::LeanObject,
    mut v_isExporting_4738_: *mut crate::leanh::LeanObject,
    mut v___y_4739_: *mut crate::leanh::LeanObject,
    mut v___y_4740_: *mut crate::leanh::LeanObject,
    mut v___y_4741_: *mut crate::leanh::LeanObject,
    mut v___y_4742_: *mut crate::leanh::LeanObject,
    mut v___y_4743_: *mut crate::leanh::LeanObject,
    mut v___y_4744_: *mut crate::leanh::LeanObject,
    mut v___y_4745_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_4746_: u8 = 0;
    let mut v_res_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4746_ = (crate::leanh::lean_unbox(v_isExporting_4738_) as u8);
    v_res_4747_ = l_Lean_withExporting___at___00Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18_spec__21(v_00_u03b1_4736_, v_x_4737_, v_isExporting_boxed_4746_, v___y_4739_, v___y_4740_, v___y_4741_, v___y_4742_, v___y_4743_, v___y_4744_);
    crate::leanh::lean_dec(v___y_4744_);
    crate::leanh::lean_dec_ref(v___y_4743_);
    crate::leanh::lean_dec(v___y_4742_);
    crate::leanh::lean_dec_ref(v___y_4741_);
    crate::leanh::lean_dec(v___y_4740_);
    crate::leanh::lean_dec_ref(v___y_4739_);
    return v_res_4747_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(
    mut v_00_u03b1_4748_: *mut crate::leanh::LeanObject,
    mut v_x_4749_: *mut crate::leanh::LeanObject,
    mut v_when_4750_: u8,
    mut v___y_4751_: *mut crate::leanh::LeanObject,
    mut v___y_4752_: *mut crate::leanh::LeanObject,
    mut v___y_4753_: *mut crate::leanh::LeanObject,
    mut v___y_4754_: *mut crate::leanh::LeanObject,
    mut v___y_4755_: *mut crate::leanh::LeanObject,
    mut v___y_4756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4758_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___redArg(
        v_x_4749_,
        v_when_4750_,
        v___y_4751_,
        v___y_4752_,
        v___y_4753_,
        v___y_4754_,
        v___y_4755_,
        v___y_4756_,
    );
    return v___x_4758_;
}
pub unsafe fn l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18___boxed(
    mut v_00_u03b1_4759_: *mut crate::leanh::LeanObject,
    mut v_x_4760_: *mut crate::leanh::LeanObject,
    mut v_when_4761_: *mut crate::leanh::LeanObject,
    mut v___y_4762_: *mut crate::leanh::LeanObject,
    mut v___y_4763_: *mut crate::leanh::LeanObject,
    mut v___y_4764_: *mut crate::leanh::LeanObject,
    mut v___y_4765_: *mut crate::leanh::LeanObject,
    mut v___y_4766_: *mut crate::leanh::LeanObject,
    mut v___y_4767_: *mut crate::leanh::LeanObject,
    mut v___y_4768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_when_boxed_4769_: u8 = 0;
    let mut v_res_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_when_boxed_4769_ = (crate::leanh::lean_unbox(v_when_4761_) as u8);
    v_res_4770_ = l_Lean_withoutExporting___at___00Lean_Elab_wfRecursion_spec__18(
        v_00_u03b1_4759_,
        v_x_4760_,
        v_when_boxed_4769_,
        v___y_4762_,
        v___y_4763_,
        v___y_4764_,
        v___y_4765_,
        v___y_4766_,
        v___y_4767_,
    );
    crate::leanh::lean_dec(v___y_4767_);
    crate::leanh::lean_dec_ref(v___y_4766_);
    crate::leanh::lean_dec(v___y_4765_);
    crate::leanh::lean_dec_ref(v___y_4764_);
    crate::leanh::lean_dec(v___y_4763_);
    crate::leanh::lean_dec_ref(v___y_4762_);
    return v_res_4770_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(
    mut v_msgData_4771_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4772_: *mut crate::leanh::LeanObject,
    mut v___y_4773_: *mut crate::leanh::LeanObject,
    mut v___y_4774_: *mut crate::leanh::LeanObject,
    mut v___y_4775_: *mut crate::leanh::LeanObject,
    mut v___y_4776_: *mut crate::leanh::LeanObject,
    mut v___y_4777_: *mut crate::leanh::LeanObject,
    mut v___y_4778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4780_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___redArg(v_msgData_4771_, v_macroStack_4772_, v___y_4777_);
    return v___x_4780_;
}
pub unsafe fn l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1___boxed(
    mut v_msgData_4781_: *mut crate::leanh::LeanObject,
    mut v_macroStack_4782_: *mut crate::leanh::LeanObject,
    mut v___y_4783_: *mut crate::leanh::LeanObject,
    mut v___y_4784_: *mut crate::leanh::LeanObject,
    mut v___y_4785_: *mut crate::leanh::LeanObject,
    mut v___y_4786_: *mut crate::leanh::LeanObject,
    mut v___y_4787_: *mut crate::leanh::LeanObject,
    mut v___y_4788_: *mut crate::leanh::LeanObject,
    mut v___y_4789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4790_ = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_wfRecursion_spec__0_spec__1(v_msgData_4781_, v_macroStack_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_);
    crate::leanh::lean_dec(v___y_4788_);
    crate::leanh::lean_dec_ref(v___y_4787_);
    crate::leanh::lean_dec(v___y_4786_);
    crate::leanh::lean_dec_ref(v___y_4785_);
    crate::leanh::lean_dec(v___y_4784_);
    crate::leanh::lean_dec_ref(v___y_4783_);
    return v_res_4790_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(
    mut v_ref_4791_: *mut crate::leanh::LeanObject,
    mut v_msgData_4792_: *mut crate::leanh::LeanObject,
    mut v_severity_4793_: u8,
    mut v_isSilent_4794_: u8,
    mut v___y_4795_: *mut crate::leanh::LeanObject,
    mut v___y_4796_: *mut crate::leanh::LeanObject,
    mut v___y_4797_: *mut crate::leanh::LeanObject,
    mut v___y_4798_: *mut crate::leanh::LeanObject,
    mut v___y_4799_: *mut crate::leanh::LeanObject,
    mut v___y_4800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4802_ = l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___redArg(v_ref_4791_, v_msgData_4792_, v_severity_4793_, v_isSilent_4794_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_);
    return v___x_4802_;
}
pub unsafe fn l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13___boxed(
    mut v_ref_4803_: *mut crate::leanh::LeanObject,
    mut v_msgData_4804_: *mut crate::leanh::LeanObject,
    mut v_severity_4805_: *mut crate::leanh::LeanObject,
    mut v_isSilent_4806_: *mut crate::leanh::LeanObject,
    mut v___y_4807_: *mut crate::leanh::LeanObject,
    mut v___y_4808_: *mut crate::leanh::LeanObject,
    mut v___y_4809_: *mut crate::leanh::LeanObject,
    mut v___y_4810_: *mut crate::leanh::LeanObject,
    mut v___y_4811_: *mut crate::leanh::LeanObject,
    mut v___y_4812_: *mut crate::leanh::LeanObject,
    mut v___y_4813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_severity_boxed_4814_: u8 = 0;
    let mut v_isSilent_boxed_4815_: u8 = 0;
    let mut v_res_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_severity_boxed_4814_ = (crate::leanh::lean_unbox(v_severity_4805_) as u8);
    v_isSilent_boxed_4815_ = (crate::leanh::lean_unbox(v_isSilent_4806_) as u8);
    v_res_4816_ =
        l_Lean_logAt___at___00Lean_logWarningAt___at___00Lean_Elab_wfRecursion_spec__11_spec__13(
            v_ref_4803_,
            v_msgData_4804_,
            v_severity_boxed_4814_,
            v_isSilent_boxed_4815_,
            v___y_4807_,
            v___y_4808_,
            v___y_4809_,
            v___y_4810_,
            v___y_4811_,
            v___y_4812_,
        );
    crate::leanh::lean_dec(v___y_4812_);
    crate::leanh::lean_dec_ref(v___y_4811_);
    crate::leanh::lean_dec(v___y_4810_);
    crate::leanh::lean_dec_ref(v___y_4809_);
    crate::leanh::lean_dec(v___y_4808_);
    crate::leanh::lean_dec_ref(v___y_4807_);
    crate::leanh::lean_dec(v_ref_4803_);
    return v_res_4816_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4888_: u8 = 0;
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4887_ = l_Lean_Elab_wfRecursion___closed__2;
    v___x_4888_ = 0;
    v___x_4889_ = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn___closed__28_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_;
    v___x_4890_ = l_Lean_registerTraceClass(v___x_4887_, v___x_4888_, v___x_4889_);
    return v___x_4890_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2____boxed(
    mut v_a_4891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4892_ = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_();
    return v_res_4892_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_WF_Main(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_PreDefinition_WF_PackMutual(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_WF_Rel(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_WF_Fix(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_WF_Unfold(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_WF_Preprocess(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_WF_GuessLex(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_PreDefinition_WF_Main_0__Lean_Elab_initFn_00___x40_Lean_Elab_PreDefinition_WF_Main_1197449596____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_WF_Main(
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
pub unsafe fn initialize_Lean_Elab_PreDefinition_WF_Main(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_PreDefinition_WF_PackMutual(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_WF_Rel(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_WF_Fix(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_WF_Unfold(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_WF_Preprocess(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_WF_GuessLex(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_WF_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_WF_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_WF_Main(builtin);
}

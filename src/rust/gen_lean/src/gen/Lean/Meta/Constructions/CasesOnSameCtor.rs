// Lean compiler output
// Module: Lean.Meta.Constructions.CasesOnSameCtor
// Imports: Lean.Meta.Basic Lean.Meta.CompletionName Lean.Meta.Constructions.CtorIdx Lean.Meta.Constructions.CtorElim Lean.Elab.App Lean.Meta.SameCtorUtils
use crate::r#gen::Init::Control::StateRef::l_StateRefT_x27_instMonad___redArg;
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_unzip___redArg};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_str___override, l_Lean_replaceRef,
    l_Pi_instInhabited___redArg___lam__0, l_ReaderT_instApplicativeOfMonad___redArg___lam__1,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__3,
    l_ReaderT_instApplicativeOfMonad___redArg___lam__4,
    l_ReaderT_instFunctorOfMonad___redArg___lam__0, l_ReaderT_instFunctorOfMonad___redArg___lam__1,
    l_instInhabitedOfMonad___redArg,
};
use crate::r#gen::Init::System::IO::l_instMonadEIO;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::AddDecl::l_Lean_addDecl;
use crate::r#gen::Lean::AuxRecursor::{l_Lean_markAuxRecursor, l_Lean_mkCasesOnName};
use crate::r#gen::Lean::CoreM::{
    l_Lean_Core_instMonadCoreM___lam__0___boxed, l_Lean_Core_instMonadCoreM___lam__1___boxed,
    l_Lean_compileDecl, l_Lean_enableRealizationsForConst, l_Lean_mkArrow,
};
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::l_Lean_InductiveVal_numCtors;
use crate::r#gen::Lean::Elab::App::{
    initialize_Lean_Elab_App, l_Lean_Elab_Term_elabAsElim, runtime_initialize_Lean_Elab_App,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_EnvExtension_asyncMayModify___redArg, l_Lean_Environment_asyncPrefix_x3f,
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f, l_Lean_Environment_findConstVal_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_hasUnsafe,
    l_Lean_Environment_header, l_Lean_Environment_setExporting,
    l_Lean_EnvironmentHeader_moduleNames, l_Lean_PersistentEnvExtension_addEntry___redArg,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_app___override,
    l_Lean_Expr_bindingBody_x21, l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasMVar,
    l_Lean_Expr_mvarId_x21, l_Lean_Expr_sort___override, l_Lean_instInhabitedExpr, l_Lean_mkApp3,
    l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkNatLit, l_Lean_mkRawNatLit, l_Lean_mkSort,
};
use crate::r#gen::Lean::Level::{l_Lean_Level_ofNat, l_Lean_mkLevelParam};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_nil, l_Lean_MessageData_note, l_Lean_MessageData_ofConstName,
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkEq, l_Lean_Meta_mkEqRefl, l_Lean_Meta_mkEqSymm,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_instMonadMetaM___lam__0___boxed,
    l_Lean_Meta_instMonadMetaM___lam__1___boxed, l_Lean_Meta_instantiateForall,
    l_Lean_Meta_mkForallFVars, l_Lean_Meta_mkLambdaFVars, l_Lean_Meta_setInlineAttribute,
    runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::CompletionName::{
    initialize_Lean_Meta_CompletionName, l_Lean_Meta_addToCompletionBlackList,
    runtime_initialize_Lean_Meta_CompletionName,
};
use crate::r#gen::Lean::Meta::Constructions::CtorElim::{
    initialize_Lean_Meta_Constructions_CtorElim, l_Lean_mkConstructorElimName,
    runtime_initialize_Lean_Meta_Constructions_CtorElim,
};
use crate::r#gen::Lean::Meta::Constructions::CtorIdx::{
    initialize_Lean_Meta_Constructions_CtorIdx, l_mkCtorIdxName,
    runtime_initialize_Lean_Meta_Constructions_CtorIdx,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_inferArgumentTypesN;
use crate::r#gen::Lean::Meta::Match::MatcherInfo::{
    l_Lean_Meta_Match_Extension_addMatcherInfo, l_Lean_Meta_markMatcherLike,
};
use crate::r#gen::Lean::Meta::SameCtorUtils::{
    initialize_Lean_Meta_SameCtorUtils, l_Lean_Meta_withSharedCtorIndices___redArg,
    runtime_initialize_Lean_Meta_SameCtorUtils,
};
use crate::r#gen::Lean::Meta::Tactic::Apply::l_Lean_MVarId_apply;
use crate::r#gen::Lean::Meta::Tactic::Cases::{
    l_Lean_Meta_Cases_unifyEqs_x3f, l_Lean_Meta_withNewEqs___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar;
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Lean::Modifiers::l_Lean_addProtected;
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ReducibilityAttrs::l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore;
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uset, lean_mk_array,
};
use crate::ffi::lean_string_append;
use crate::ffi::{lean_usize_add, lean_usize_dec_lt};
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_mk, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed,
};
use crate::ffi::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::ffi::{lean_infer_type, lean_whnf};
static mut l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0_value:
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
    m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__1_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [69, 113, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__1_value) as *mut crate::leanh::LeanObject,16122875713692181903 as *mut crate::leanh::LeanObject] };
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__3_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__3_value) as *mut crate::leanh::LeanObject,11442535297760353691 as *mut crate::leanh::LeanObject] };
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__0_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__0_value) as *mut crate::leanh::LeanObject,8738205681931236784 as *mut crate::leanh::LeanObject] };
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Core_instMonadCoreM___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instMonadMetaM___lam__1___boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 108, 116, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_mkCasesOnSameCtorHet___lam__3___closed__0_value: crate::leanh::LeanStringObject<
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
    m_data: [109, 111, 116, 105, 118, 101, 0],
};
static mut l_Lean_mkCasesOnSameCtorHet___lam__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16911948307605359233 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [67, 97, 110, 110, 111, 116, 32, 97, 100, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2_value: crate::leanh::LeanStringObject<20> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 116, 111, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4_value: crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [96, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 32, 105, 115, 32, 105, 110, 32, 97, 110, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 109, 111, 100, 117, 108, 101, 0]};
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0_value: crate::leanh::LeanStringObject<51> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 50, m_data: [96, 32, 98, 101, 99, 97, 117, 115, 101, 32, 105, 116, 32, 105, 115, 32, 110, 111, 116, 32, 102, 114, 111, 109, 32, 116, 104, 101, 32, 112, 114, 101, 115, 101, 110, 116, 32, 97, 115, 121, 110, 99, 32, 99, 111, 110, 116, 101, 120, 116, 0]};
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [32, 96, 0]};
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkCasesOnSameCtorHet___closed__0_value: crate::leanh::LeanStringObject<40> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 67, 111, 110, 115, 116, 114, 117, 99, 116,
            105, 111, 110, 115, 46, 67, 97, 115, 101, 115, 79, 110, 83, 97, 109, 101, 67, 116, 111,
            114, 0,
        ],
    };
static mut l_Lean_mkCasesOnSameCtorHet___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkCasesOnSameCtorHet___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkCasesOnSameCtorHet___closed__1_value: crate::leanh::LeanStringObject<26> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 26,
        m_capacity: 26,
        m_length: 25,
        m_data: [
            76, 101, 97, 110, 46, 109, 107, 67, 97, 115, 101, 115, 79, 110, 83, 97, 109, 101, 67,
            116, 111, 114, 72, 101, 116, 0,
        ],
    };
static mut l_Lean_mkCasesOnSameCtorHet___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkCasesOnSameCtorHet___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkCasesOnSameCtorHet___closed__2_value: crate::leanh::LeanStringObject<40> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 117, 110, 105, 118, 101, 114, 115,
            101, 32, 108, 101, 118, 101, 108, 115, 32, 111, 110, 32, 96, 99, 97, 115, 101, 115, 79,
            110, 96, 0,
        ],
    };
static mut l_Lean_mkCasesOnSameCtorHet___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkCasesOnSameCtorHet___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_mkCasesOnSameCtorHet___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkCasesOnSameCtorHet___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_mkCasesOnSameCtorHet___closed__4_value: crate::leanh::LeanStringObject<34> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Lean_mkCasesOnSameCtorHet___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkCasesOnSameCtorHet___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_mkCasesOnSameCtorHet___closed__5_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkCasesOnSameCtorHet___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<17> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 17, m_capacity: 17, m_length: 16, m_data: [99, 111, 117, 108, 100, 32, 110, 111, 116, 32, 97, 112, 112, 108, 121, 32, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [32, 116, 111, 32, 99, 108, 111, 115, 101, 10, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [85, 110, 105, 116, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__5_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [117, 110, 105, 116, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject;
static l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject,9833841078580172006 as *mut crate::leanh::LeanObject] };
pub static l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__5_value) as *mut crate::leanh::LeanObject,565778312915565143 as *mut crate::leanh::LeanObject] };
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8_value: crate::leanh::LeanStringObject<36> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [117, 110, 105, 102, 121, 69, 113, 110, 115, 63, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 108, 121, 32, 99, 108, 111, 115, 101, 100, 32, 103, 111, 97, 108, 0]};
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkCasesOnSameCtor___lam__3___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__4_value) as *mut crate::leanh::LeanObject,9833841078580172006 as *mut crate::leanh::LeanObject] };
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkCasesOnSameCtor___closed__0_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [104, 101, 116, 0],
    };
static mut l_Lean_mkCasesOnSameCtor___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkCasesOnSameCtor___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkCasesOnSameCtor___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_mkCasesOnSameCtor___closed__0_value)
                as *mut crate::leanh::LeanObject,
            6647857897726263867 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_mkCasesOnSameCtor___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkCasesOnSameCtor___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_mkCasesOnSameCtor___closed__2_value: crate::leanh::LeanStringObject<23> =
    crate::leanh::LeanStringObject {
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
            76, 101, 97, 110, 46, 109, 107, 67, 97, 115, 101, 115, 79, 110, 83, 97, 109, 101, 67,
            116, 111, 114, 0,
        ],
    };
static mut l_Lean_mkCasesOnSameCtor___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_mkCasesOnSameCtor___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_mkCasesOnSameCtor___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkCasesOnSameCtor___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_mkCasesOnSameCtor___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_mkCasesOnSameCtor___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0(
    mut v_k_4456_: *mut crate::leanh::LeanObject,
    mut v_b_4457_: *mut crate::leanh::LeanObject,
    mut v_c_4458_: *mut crate::leanh::LeanObject,
    mut v___y_4459_: *mut crate::leanh::LeanObject,
    mut v___y_4460_: *mut crate::leanh::LeanObject,
    mut v___y_4461_: *mut crate::leanh::LeanObject,
    mut v___y_4462_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4462_);
    crate::leanh::lean_inc_ref(v___y_4461_);
    crate::leanh::lean_inc(v___y_4460_);
    crate::leanh::lean_inc_ref(v___y_4459_);
    v___x_4464_ = crate::leanh::lean_apply_7(
        v_k_4456_,
        v_b_4457_,
        v_c_4458_,
        v___y_4459_,
        v___y_4460_,
        v___y_4461_,
        v___y_4462_,
        crate::leanh::lean_box(0),
    );
    return v___x_4464_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0___boxed(
    mut v_k_4465_: *mut crate::leanh::LeanObject,
    mut v_b_4466_: *mut crate::leanh::LeanObject,
    mut v_c_4467_: *mut crate::leanh::LeanObject,
    mut v___y_4468_: *mut crate::leanh::LeanObject,
    mut v___y_4469_: *mut crate::leanh::LeanObject,
    mut v___y_4470_: *mut crate::leanh::LeanObject,
    mut v___y_4471_: *mut crate::leanh::LeanObject,
    mut v___y_4472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4473_ =
        l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0(
            v_k_4465_,
            v_b_4466_,
            v_c_4467_,
            v___y_4468_,
            v___y_4469_,
            v___y_4470_,
            v___y_4471_,
        );
    crate::leanh::lean_dec(v___y_4471_);
    crate::leanh::lean_dec_ref(v___y_4470_);
    crate::leanh::lean_dec(v___y_4469_);
    crate::leanh::lean_dec_ref(v___y_4468_);
    return v_res_4473_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(
    mut v_type_4474_: *mut crate::leanh::LeanObject,
    mut v_k_4475_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4476_: u8,
    mut v___y_4477_: *mut crate::leanh::LeanObject,
    mut v___y_4478_: *mut crate::leanh::LeanObject,
    mut v___y_4479_: *mut crate::leanh::LeanObject,
    mut v___y_4480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: u8 = 0;
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4489_: u8 = 0;
    let mut v___x_4491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4493_: u8 = 0;
    let mut v_a_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4497_: u8 = 0;
    let mut v___x_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4501_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4482_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_4482_, 0, v_k_4475_);
                v___x_4483_ = 0;
                v___x_4484_ = crate::leanh::lean_box(0);
                v___x_4485_ =
                    l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(
                        crate::leanh::lean_box(0),
                        v___x_4483_,
                        v___x_4484_,
                        v_type_4474_,
                        v___f_4482_,
                        v_cleanupAnnotations_4476_,
                        v___x_4483_,
                        v___y_4477_,
                        v___y_4478_,
                        v___y_4479_,
                        v___y_4480_,
                    );
                if crate::leanh::lean_obj_tag(v___x_4485_) == 0 {
                    v_a_4486_ = crate::leanh::lean_ctor_get(v___x_4485_, 0);
                    v_isSharedCheck_4493_ = (!crate::leanh::lean_is_exclusive(v___x_4485_)) as u8;
                    if v_isSharedCheck_4493_ == 0 {
                        v___x_4488_ = v___x_4485_;
                        v_isShared_4489_ = v_isSharedCheck_4493_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4486_);
                        crate::leanh::lean_dec(v___x_4485_);
                        v___x_4488_ = crate::leanh::lean_box(0);
                        v_isShared_4489_ = v_isSharedCheck_4493_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4494_ = crate::leanh::lean_ctor_get(v___x_4485_, 0);
                    v_isSharedCheck_4501_ = (!crate::leanh::lean_is_exclusive(v___x_4485_)) as u8;
                    if v_isSharedCheck_4501_ == 0 {
                        v___x_4496_ = v___x_4485_;
                        v_isShared_4497_ = v_isSharedCheck_4501_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4494_);
                        crate::leanh::lean_dec(v___x_4485_);
                        v___x_4496_ = crate::leanh::lean_box(0);
                        v_isShared_4497_ = v_isSharedCheck_4501_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4489_ == 0 {
                    v___x_4491_ = v___x_4488_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4492_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_a_4486_);
                    v___x_4491_ = v_reuseFailAlloc_4492_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4491_;
            }
            3 => {
                if v_isShared_4497_ == 0 {
                    v___x_4499_ = v___x_4496_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4500_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_a_4494_);
                    v___x_4499_ = v_reuseFailAlloc_4500_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4499_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___boxed(
    mut v_type_4502_: *mut crate::leanh::LeanObject,
    mut v_k_4503_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4504_: *mut crate::leanh::LeanObject,
    mut v___y_4505_: *mut crate::leanh::LeanObject,
    mut v___y_4506_: *mut crate::leanh::LeanObject,
    mut v___y_4507_: *mut crate::leanh::LeanObject,
    mut v___y_4508_: *mut crate::leanh::LeanObject,
    mut v___y_4509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4510_: u8 = 0;
    let mut v_res_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4510_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4504_) as u8);
    v_res_4511_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(
        v_type_4502_,
        v_k_4503_,
        v_cleanupAnnotations_boxed_4510_,
        v___y_4505_,
        v___y_4506_,
        v___y_4507_,
        v___y_4508_,
    );
    crate::leanh::lean_dec(v___y_4508_);
    crate::leanh::lean_dec_ref(v___y_4507_);
    crate::leanh::lean_dec(v___y_4506_);
    crate::leanh::lean_dec_ref(v___y_4505_);
    return v_res_4511_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3(
    mut v_00_u03b1_4512_: *mut crate::leanh::LeanObject,
    mut v_type_4513_: *mut crate::leanh::LeanObject,
    mut v_k_4514_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4515_: u8,
    mut v___y_4516_: *mut crate::leanh::LeanObject,
    mut v___y_4517_: *mut crate::leanh::LeanObject,
    mut v___y_4518_: *mut crate::leanh::LeanObject,
    mut v___y_4519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4521_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(
        v_type_4513_,
        v_k_4514_,
        v_cleanupAnnotations_4515_,
        v___y_4516_,
        v___y_4517_,
        v___y_4518_,
        v___y_4519_,
    );
    return v___x_4521_;
}
pub unsafe fn l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___boxed(
    mut v_00_u03b1_4522_: *mut crate::leanh::LeanObject,
    mut v_type_4523_: *mut crate::leanh::LeanObject,
    mut v_k_4524_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4525_: *mut crate::leanh::LeanObject,
    mut v___y_4526_: *mut crate::leanh::LeanObject,
    mut v___y_4527_: *mut crate::leanh::LeanObject,
    mut v___y_4528_: *mut crate::leanh::LeanObject,
    mut v___y_4529_: *mut crate::leanh::LeanObject,
    mut v___y_4530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4531_: u8 = 0;
    let mut v_res_4532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4531_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4525_) as u8);
    v_res_4532_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3(
        v_00_u03b1_4522_,
        v_type_4523_,
        v_k_4524_,
        v_cleanupAnnotations_boxed_4531_,
        v___y_4526_,
        v___y_4527_,
        v___y_4528_,
        v___y_4529_,
    );
    crate::leanh::lean_dec(v___y_4529_);
    crate::leanh::lean_dec_ref(v___y_4528_);
    crate::leanh::lean_dec(v___y_4527_);
    crate::leanh::lean_dec_ref(v___y_4526_);
    return v_res_4532_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0(
    mut v_k_4533_: *mut crate::leanh::LeanObject,
    mut v_b_4534_: *mut crate::leanh::LeanObject,
    mut v___y_4535_: *mut crate::leanh::LeanObject,
    mut v___y_4536_: *mut crate::leanh::LeanObject,
    mut v___y_4537_: *mut crate::leanh::LeanObject,
    mut v___y_4538_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_4538_);
    crate::leanh::lean_inc_ref(v___y_4537_);
    crate::leanh::lean_inc(v___y_4536_);
    crate::leanh::lean_inc_ref(v___y_4535_);
    v___x_4540_ = crate::leanh::lean_apply_6(
        v_k_4533_,
        v_b_4534_,
        v___y_4535_,
        v___y_4536_,
        v___y_4537_,
        v___y_4538_,
        crate::leanh::lean_box(0),
    );
    return v___x_4540_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0___boxed(
    mut v_k_4541_: *mut crate::leanh::LeanObject,
    mut v_b_4542_: *mut crate::leanh::LeanObject,
    mut v___y_4543_: *mut crate::leanh::LeanObject,
    mut v___y_4544_: *mut crate::leanh::LeanObject,
    mut v___y_4545_: *mut crate::leanh::LeanObject,
    mut v___y_4546_: *mut crate::leanh::LeanObject,
    mut v___y_4547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4548_ =
        l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0(
            v_k_4541_,
            v_b_4542_,
            v___y_4543_,
            v___y_4544_,
            v___y_4545_,
            v___y_4546_,
        );
    crate::leanh::lean_dec(v___y_4546_);
    crate::leanh::lean_dec_ref(v___y_4545_);
    crate::leanh::lean_dec(v___y_4544_);
    crate::leanh::lean_dec_ref(v___y_4543_);
    return v_res_4548_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(
    mut v_name_4549_: *mut crate::leanh::LeanObject,
    mut v_bi_4550_: u8,
    mut v_type_4551_: *mut crate::leanh::LeanObject,
    mut v_k_4552_: *mut crate::leanh::LeanObject,
    mut v_kind_4553_: u8,
    mut v___y_4554_: *mut crate::leanh::LeanObject,
    mut v___y_4555_: *mut crate::leanh::LeanObject,
    mut v___y_4556_: *mut crate::leanh::LeanObject,
    mut v___y_4557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4564_: u8 = 0;
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4568_: u8 = 0;
    let mut v_a_4569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4572_: u8 = 0;
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4576_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4559_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                crate::leanh::lean_closure_set(v___f_4559_, 0, v_k_4552_);
                v___x_4560_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    crate::leanh::lean_box(0),
                    v_name_4549_,
                    v_bi_4550_,
                    v_type_4551_,
                    v___f_4559_,
                    v_kind_4553_,
                    v___y_4554_,
                    v___y_4555_,
                    v___y_4556_,
                    v___y_4557_,
                );
                if crate::leanh::lean_obj_tag(v___x_4560_) == 0 {
                    v_a_4561_ = crate::leanh::lean_ctor_get(v___x_4560_, 0);
                    v_isSharedCheck_4568_ = (!crate::leanh::lean_is_exclusive(v___x_4560_)) as u8;
                    if v_isSharedCheck_4568_ == 0 {
                        v___x_4563_ = v___x_4560_;
                        v_isShared_4564_ = v_isSharedCheck_4568_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4561_);
                        crate::leanh::lean_dec(v___x_4560_);
                        v___x_4563_ = crate::leanh::lean_box(0);
                        v_isShared_4564_ = v_isSharedCheck_4568_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4569_ = crate::leanh::lean_ctor_get(v___x_4560_, 0);
                    v_isSharedCheck_4576_ = (!crate::leanh::lean_is_exclusive(v___x_4560_)) as u8;
                    if v_isSharedCheck_4576_ == 0 {
                        v___x_4571_ = v___x_4560_;
                        v_isShared_4572_ = v_isSharedCheck_4576_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4569_);
                        crate::leanh::lean_dec(v___x_4560_);
                        v___x_4571_ = crate::leanh::lean_box(0);
                        v_isShared_4572_ = v_isSharedCheck_4576_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4564_ == 0 {
                    v___x_4566_ = v___x_4563_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4567_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_a_4561_);
                    v___x_4566_ = v_reuseFailAlloc_4567_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4566_;
            }
            3 => {
                if v_isShared_4572_ == 0 {
                    v___x_4574_ = v___x_4571_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4575_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4575_, 0, v_a_4569_);
                    v___x_4574_ = v_reuseFailAlloc_4575_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4574_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg___boxed(
    mut v_name_4577_: *mut crate::leanh::LeanObject,
    mut v_bi_4578_: *mut crate::leanh::LeanObject,
    mut v_type_4579_: *mut crate::leanh::LeanObject,
    mut v_k_4580_: *mut crate::leanh::LeanObject,
    mut v_kind_4581_: *mut crate::leanh::LeanObject,
    mut v___y_4582_: *mut crate::leanh::LeanObject,
    mut v___y_4583_: *mut crate::leanh::LeanObject,
    mut v___y_4584_: *mut crate::leanh::LeanObject,
    mut v___y_4585_: *mut crate::leanh::LeanObject,
    mut v___y_4586_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_4587_: u8 = 0;
    let mut v_kind_boxed_4588_: u8 = 0;
    let mut v_res_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4587_ = (crate::leanh::lean_unbox(v_bi_4578_) as u8);
    v_kind_boxed_4588_ = (crate::leanh::lean_unbox(v_kind_4581_) as u8);
    v_res_4589_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(
        v_name_4577_,
        v_bi_boxed_4587_,
        v_type_4579_,
        v_k_4580_,
        v_kind_boxed_4588_,
        v___y_4582_,
        v___y_4583_,
        v___y_4584_,
        v___y_4585_,
    );
    crate::leanh::lean_dec(v___y_4585_);
    crate::leanh::lean_dec_ref(v___y_4584_);
    crate::leanh::lean_dec(v___y_4583_);
    crate::leanh::lean_dec_ref(v___y_4582_);
    return v_res_4589_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8(
    mut v_00_u03b1_4590_: *mut crate::leanh::LeanObject,
    mut v_name_4591_: *mut crate::leanh::LeanObject,
    mut v_bi_4592_: u8,
    mut v_type_4593_: *mut crate::leanh::LeanObject,
    mut v_k_4594_: *mut crate::leanh::LeanObject,
    mut v_kind_4595_: u8,
    mut v___y_4596_: *mut crate::leanh::LeanObject,
    mut v___y_4597_: *mut crate::leanh::LeanObject,
    mut v___y_4598_: *mut crate::leanh::LeanObject,
    mut v___y_4599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4601_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(
        v_name_4591_,
        v_bi_4592_,
        v_type_4593_,
        v_k_4594_,
        v_kind_4595_,
        v___y_4596_,
        v___y_4597_,
        v___y_4598_,
        v___y_4599_,
    );
    return v___x_4601_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___boxed(
    mut v_00_u03b1_4602_: *mut crate::leanh::LeanObject,
    mut v_name_4603_: *mut crate::leanh::LeanObject,
    mut v_bi_4604_: *mut crate::leanh::LeanObject,
    mut v_type_4605_: *mut crate::leanh::LeanObject,
    mut v_k_4606_: *mut crate::leanh::LeanObject,
    mut v_kind_4607_: *mut crate::leanh::LeanObject,
    mut v___y_4608_: *mut crate::leanh::LeanObject,
    mut v___y_4609_: *mut crate::leanh::LeanObject,
    mut v___y_4610_: *mut crate::leanh::LeanObject,
    mut v___y_4611_: *mut crate::leanh::LeanObject,
    mut v___y_4612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_bi_boxed_4613_: u8 = 0;
    let mut v_kind_boxed_4614_: u8 = 0;
    let mut v_res_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_4613_ = (crate::leanh::lean_unbox(v_bi_4604_) as u8);
    v_kind_boxed_4614_ = (crate::leanh::lean_unbox(v_kind_4607_) as u8);
    v_res_4615_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8(
        v_00_u03b1_4602_,
        v_name_4603_,
        v_bi_boxed_4613_,
        v_type_4605_,
        v_k_4606_,
        v_kind_boxed_4614_,
        v___y_4608_,
        v___y_4609_,
        v___y_4610_,
        v___y_4611_,
    );
    crate::leanh::lean_dec(v___y_4611_);
    crate::leanh::lean_dec_ref(v___y_4610_);
    crate::leanh::lean_dec(v___y_4609_);
    crate::leanh::lean_dec_ref(v___y_4608_);
    return v_res_4615_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(
    mut v_type_4616_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_4617_: *mut crate::leanh::LeanObject,
    mut v_k_4618_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4619_: u8,
    mut v_whnfType_4620_: u8,
    mut v___y_4621_: *mut crate::leanh::LeanObject,
    mut v___y_4622_: *mut crate::leanh::LeanObject,
    mut v___y_4623_: *mut crate::leanh::LeanObject,
    mut v___y_4624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4631_: u8 = 0;
    let mut v___x_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4635_: u8 = 0;
    let mut v_a_4636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4639_: u8 = 0;
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4643_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4626_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_4626_, 0, v_k_4618_);
                v___x_4627_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(
                    crate::leanh::lean_box(0),
                    v_type_4616_,
                    v_maxFVars_x3f_4617_,
                    v___f_4626_,
                    v_cleanupAnnotations_4619_,
                    v_whnfType_4620_,
                    v___y_4621_,
                    v___y_4622_,
                    v___y_4623_,
                    v___y_4624_,
                );
                if crate::leanh::lean_obj_tag(v___x_4627_) == 0 {
                    v_a_4628_ = crate::leanh::lean_ctor_get(v___x_4627_, 0);
                    v_isSharedCheck_4635_ = (!crate::leanh::lean_is_exclusive(v___x_4627_)) as u8;
                    if v_isSharedCheck_4635_ == 0 {
                        v___x_4630_ = v___x_4627_;
                        v_isShared_4631_ = v_isSharedCheck_4635_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4628_);
                        crate::leanh::lean_dec(v___x_4627_);
                        v___x_4630_ = crate::leanh::lean_box(0);
                        v_isShared_4631_ = v_isSharedCheck_4635_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4636_ = crate::leanh::lean_ctor_get(v___x_4627_, 0);
                    v_isSharedCheck_4643_ = (!crate::leanh::lean_is_exclusive(v___x_4627_)) as u8;
                    if v_isSharedCheck_4643_ == 0 {
                        v___x_4638_ = v___x_4627_;
                        v_isShared_4639_ = v_isSharedCheck_4643_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4636_);
                        crate::leanh::lean_dec(v___x_4627_);
                        v___x_4638_ = crate::leanh::lean_box(0);
                        v_isShared_4639_ = v_isSharedCheck_4643_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4631_ == 0 {
                    v___x_4633_ = v___x_4630_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4634_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4634_, 0, v_a_4628_);
                    v___x_4633_ = v_reuseFailAlloc_4634_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4633_;
            }
            3 => {
                if v_isShared_4639_ == 0 {
                    v___x_4641_ = v___x_4638_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4642_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_a_4636_);
                    v___x_4641_ = v_reuseFailAlloc_4642_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4641_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg___boxed(
    mut v_type_4644_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_4645_: *mut crate::leanh::LeanObject,
    mut v_k_4646_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4647_: *mut crate::leanh::LeanObject,
    mut v_whnfType_4648_: *mut crate::leanh::LeanObject,
    mut v___y_4649_: *mut crate::leanh::LeanObject,
    mut v___y_4650_: *mut crate::leanh::LeanObject,
    mut v___y_4651_: *mut crate::leanh::LeanObject,
    mut v___y_4652_: *mut crate::leanh::LeanObject,
    mut v___y_4653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4654_: u8 = 0;
    let mut v_whnfType_boxed_4655_: u8 = 0;
    let mut v_res_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4654_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4647_) as u8);
    v_whnfType_boxed_4655_ = (crate::leanh::lean_unbox(v_whnfType_4648_) as u8);
    v_res_4656_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(
            v_type_4644_,
            v_maxFVars_x3f_4645_,
            v_k_4646_,
            v_cleanupAnnotations_boxed_4654_,
            v_whnfType_boxed_4655_,
            v___y_4649_,
            v___y_4650_,
            v___y_4651_,
            v___y_4652_,
        );
    crate::leanh::lean_dec(v___y_4652_);
    crate::leanh::lean_dec_ref(v___y_4651_);
    crate::leanh::lean_dec(v___y_4650_);
    crate::leanh::lean_dec_ref(v___y_4649_);
    return v_res_4656_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9(
    mut v_00_u03b1_4657_: *mut crate::leanh::LeanObject,
    mut v_type_4658_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_4659_: *mut crate::leanh::LeanObject,
    mut v_k_4660_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4661_: u8,
    mut v_whnfType_4662_: u8,
    mut v___y_4663_: *mut crate::leanh::LeanObject,
    mut v___y_4664_: *mut crate::leanh::LeanObject,
    mut v___y_4665_: *mut crate::leanh::LeanObject,
    mut v___y_4666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4668_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(
            v_type_4658_,
            v_maxFVars_x3f_4659_,
            v_k_4660_,
            v_cleanupAnnotations_4661_,
            v_whnfType_4662_,
            v___y_4663_,
            v___y_4664_,
            v___y_4665_,
            v___y_4666_,
        );
    return v___x_4668_;
}
pub unsafe fn l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___boxed(
    mut v_00_u03b1_4669_: *mut crate::leanh::LeanObject,
    mut v_type_4670_: *mut crate::leanh::LeanObject,
    mut v_maxFVars_x3f_4671_: *mut crate::leanh::LeanObject,
    mut v_k_4672_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_4673_: *mut crate::leanh::LeanObject,
    mut v_whnfType_4674_: *mut crate::leanh::LeanObject,
    mut v___y_4675_: *mut crate::leanh::LeanObject,
    mut v___y_4676_: *mut crate::leanh::LeanObject,
    mut v___y_4677_: *mut crate::leanh::LeanObject,
    mut v___y_4678_: *mut crate::leanh::LeanObject,
    mut v___y_4679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4680_: u8 = 0;
    let mut v_whnfType_boxed_4681_: u8 = 0;
    let mut v_res_4682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4680_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_4673_) as u8);
    v_whnfType_boxed_4681_ = (crate::leanh::lean_unbox(v_whnfType_4674_) as u8);
    v_res_4682_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9(
        v_00_u03b1_4669_,
        v_type_4670_,
        v_maxFVars_x3f_4671_,
        v_k_4672_,
        v_cleanupAnnotations_boxed_4680_,
        v_whnfType_boxed_4681_,
        v___y_4675_,
        v___y_4676_,
        v___y_4677_,
        v___y_4678_,
    );
    crate::leanh::lean_dec(v___y_4678_);
    crate::leanh::lean_dec_ref(v___y_4677_);
    crate::leanh::lean_dec(v___y_4676_);
    crate::leanh::lean_dec_ref(v___y_4675_);
    return v_res_4682_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(
    mut v_name_4683_: *mut crate::leanh::LeanObject,
    mut v_levelParams_4684_: *mut crate::leanh::LeanObject,
    mut v_type_4685_: *mut crate::leanh::LeanObject,
    mut v_value_4686_: *mut crate::leanh::LeanObject,
    mut v_hints_4687_: *mut crate::leanh::LeanObject,
    mut v___y_4688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4692_: u8 = 0;
    let mut v___x_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4699_: u8 = 0;
    let mut v___x_4700_: u8 = 0;
    let mut v___x_4701_: u8 = 0;
    let mut v_env_4702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4703_: u8 = 0;
    let mut v___x_4704_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4690_ = lean_st_ref_get(v___y_4688_);
                v_env_4702_ = crate::leanh::lean_ctor_get(v___x_4690_, 0);
                crate::leanh::lean_inc_ref_n(v_env_4702_, 2);
                crate::leanh::lean_dec(v___x_4690_);
                v___x_4703_ = l_Lean_Environment_hasUnsafe(v_env_4702_, v_type_4685_);
                if v___x_4703_ == 0 {
                    v___x_4704_ = l_Lean_Environment_hasUnsafe(v_env_4702_, v_value_4686_);
                    v___y_4699_ = v___x_4704_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_env_4702_);
                    v___y_4699_ = v___x_4703_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_name_4683_);
                v___x_4693_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4693_, 0, v_name_4683_);
                crate::leanh::lean_ctor_set(v___x_4693_, 1, v_levelParams_4684_);
                crate::leanh::lean_ctor_set(v___x_4693_, 2, v_type_4685_);
                v___x_4694_ = crate::leanh::lean_box(0);
                v___x_4695_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4695_, 0, v_name_4683_);
                crate::leanh::lean_ctor_set(v___x_4695_, 1, v___x_4694_);
                v___x_4696_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_4696_, 0, v___x_4693_);
                crate::leanh::lean_ctor_set(v___x_4696_, 1, v_value_4686_);
                crate::leanh::lean_ctor_set(v___x_4696_, 2, v_hints_4687_);
                crate::leanh::lean_ctor_set(v___x_4696_, 3, v___x_4695_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_4696_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v___y_4692_,
                );
                v___x_4697_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4697_, 0, v___x_4696_);
                return v___x_4697_;
            }
            2 => {
                if v___y_4699_ == 0 {
                    v___x_4700_ = 1;
                    v___y_4692_ = v___x_4700_;
                    state = 1;
                    continue;
                } else {
                    v___x_4701_ = 0;
                    v___y_4692_ = v___x_4701_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg___boxed(
    mut v_name_4705_: *mut crate::leanh::LeanObject,
    mut v_levelParams_4706_: *mut crate::leanh::LeanObject,
    mut v_type_4707_: *mut crate::leanh::LeanObject,
    mut v_value_4708_: *mut crate::leanh::LeanObject,
    mut v_hints_4709_: *mut crate::leanh::LeanObject,
    mut v___y_4710_: *mut crate::leanh::LeanObject,
    mut v___y_4711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4712_ =
        l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(
            v_name_4705_,
            v_levelParams_4706_,
            v_type_4707_,
            v_value_4708_,
            v_hints_4709_,
            v___y_4710_,
        );
    crate::leanh::lean_dec(v___y_4710_);
    return v_res_4712_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10(
    mut v_name_4713_: *mut crate::leanh::LeanObject,
    mut v_levelParams_4714_: *mut crate::leanh::LeanObject,
    mut v_type_4715_: *mut crate::leanh::LeanObject,
    mut v_value_4716_: *mut crate::leanh::LeanObject,
    mut v_hints_4717_: *mut crate::leanh::LeanObject,
    mut v___y_4718_: *mut crate::leanh::LeanObject,
    mut v___y_4719_: *mut crate::leanh::LeanObject,
    mut v___y_4720_: *mut crate::leanh::LeanObject,
    mut v___y_4721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4723_ =
        l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(
            v_name_4713_,
            v_levelParams_4714_,
            v_type_4715_,
            v_value_4716_,
            v_hints_4717_,
            v___y_4721_,
        );
    return v___x_4723_;
}
pub unsafe fn l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___boxed(
    mut v_name_4724_: *mut crate::leanh::LeanObject,
    mut v_levelParams_4725_: *mut crate::leanh::LeanObject,
    mut v_type_4726_: *mut crate::leanh::LeanObject,
    mut v_value_4727_: *mut crate::leanh::LeanObject,
    mut v_hints_4728_: *mut crate::leanh::LeanObject,
    mut v___y_4729_: *mut crate::leanh::LeanObject,
    mut v___y_4730_: *mut crate::leanh::LeanObject,
    mut v___y_4731_: *mut crate::leanh::LeanObject,
    mut v___y_4732_: *mut crate::leanh::LeanObject,
    mut v___y_4733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4734_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10(
        v_name_4724_,
        v_levelParams_4725_,
        v_type_4726_,
        v_value_4727_,
        v_hints_4728_,
        v___y_4729_,
        v___y_4730_,
        v___y_4731_,
        v___y_4732_,
    );
    crate::leanh::lean_dec(v___y_4732_);
    crate::leanh::lean_dec_ref(v___y_4731_);
    crate::leanh::lean_dec(v___y_4730_);
    crate::leanh::lean_dec_ref(v___y_4729_);
    return v_res_4734_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(
    mut v___y_4735_: *mut crate::leanh::LeanObject,
    mut v_isExporting_4736_: u8,
    mut v___x_4737_: *mut crate::leanh::LeanObject,
    mut v___y_4738_: *mut crate::leanh::LeanObject,
    mut v___x_4739_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_4740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4753_: u8 = 0;
    let mut v___x_4754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4765_: u8 = 0;
    let mut v___x_4767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4772_: u8 = 0;
    let mut v_unused_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4775_: u8 = 0;
    let mut v_unused_4776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4742_ = lean_st_ref_take(v___y_4735_);
                v_env_4743_ = crate::leanh::lean_ctor_get(v___x_4742_, 0);
                v_nextMacroScope_4744_ = crate::leanh::lean_ctor_get(v___x_4742_, 1);
                v_ngen_4745_ = crate::leanh::lean_ctor_get(v___x_4742_, 2);
                v_auxDeclNGen_4746_ = crate::leanh::lean_ctor_get(v___x_4742_, 3);
                v_traceState_4747_ = crate::leanh::lean_ctor_get(v___x_4742_, 4);
                v_messages_4748_ = crate::leanh::lean_ctor_get(v___x_4742_, 6);
                v_infoState_4749_ = crate::leanh::lean_ctor_get(v___x_4742_, 7);
                v_snapshotTasks_4750_ = crate::leanh::lean_ctor_get(v___x_4742_, 8);
                v_isSharedCheck_4775_ = (!crate::leanh::lean_is_exclusive(v___x_4742_)) as u8;
                if v_isSharedCheck_4775_ == 0 {
                    v_unused_4776_ = crate::leanh::lean_ctor_get(v___x_4742_, 5);
                    crate::leanh::lean_dec(v_unused_4776_);
                    v___x_4752_ = v___x_4742_;
                    v_isShared_4753_ = v_isSharedCheck_4775_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4750_);
                    crate::leanh::lean_inc(v_infoState_4749_);
                    crate::leanh::lean_inc(v_messages_4748_);
                    crate::leanh::lean_inc(v_traceState_4747_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4746_);
                    crate::leanh::lean_inc(v_ngen_4745_);
                    crate::leanh::lean_inc(v_nextMacroScope_4744_);
                    crate::leanh::lean_inc(v_env_4743_);
                    crate::leanh::lean_dec(v___x_4742_);
                    v___x_4752_ = crate::leanh::lean_box(0);
                    v_isShared_4753_ = v_isSharedCheck_4775_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4754_ = l_Lean_Environment_setExporting(v_env_4743_, v_isExporting_4736_);
                if v_isShared_4753_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4752_, 5, v___x_4737_);
                    crate::leanh::lean_ctor_set(v___x_4752_, 0, v___x_4754_);
                    v___x_4756_ = v___x_4752_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4774_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4774_, 0, v___x_4754_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4774_, 1, v_nextMacroScope_4744_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4774_, 2, v_ngen_4745_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4774_, 3, v_auxDeclNGen_4746_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4774_, 4, v_traceState_4747_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4774_, 5, v___x_4737_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4774_, 6, v_messages_4748_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4774_, 7, v_infoState_4749_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4774_, 8, v_snapshotTasks_4750_);
                    v___x_4756_ = v_reuseFailAlloc_4774_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4757_ = lean_st_ref_set(v___y_4735_, v___x_4756_);
                v___x_4758_ = lean_st_ref_take(v___y_4738_);
                v_mctx_4759_ = crate::leanh::lean_ctor_get(v___x_4758_, 0);
                v_zetaDeltaFVarIds_4760_ = crate::leanh::lean_ctor_get(v___x_4758_, 2);
                v_postponed_4761_ = crate::leanh::lean_ctor_get(v___x_4758_, 3);
                v_diag_4762_ = crate::leanh::lean_ctor_get(v___x_4758_, 4);
                v_isSharedCheck_4772_ = (!crate::leanh::lean_is_exclusive(v___x_4758_)) as u8;
                if v_isSharedCheck_4772_ == 0 {
                    v_unused_4773_ = crate::leanh::lean_ctor_get(v___x_4758_, 1);
                    crate::leanh::lean_dec(v_unused_4773_);
                    v___x_4764_ = v___x_4758_;
                    v_isShared_4765_ = v_isSharedCheck_4772_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4762_);
                    crate::leanh::lean_inc(v_postponed_4761_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4760_);
                    crate::leanh::lean_inc(v_mctx_4759_);
                    crate::leanh::lean_dec(v___x_4758_);
                    v___x_4764_ = crate::leanh::lean_box(0);
                    v_isShared_4765_ = v_isSharedCheck_4772_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4765_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4764_, 1, v___x_4739_);
                    v___x_4767_ = v___x_4764_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4771_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4771_, 0, v_mctx_4759_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4771_, 1, v___x_4739_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4771_,
                        2,
                        v_zetaDeltaFVarIds_4760_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4771_, 3, v_postponed_4761_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4771_, 4, v_diag_4762_);
                    v___x_4767_ = v_reuseFailAlloc_4771_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4768_ = lean_st_ref_set(v___y_4738_, v___x_4767_);
                v___x_4769_ = crate::leanh::lean_box(0);
                v___x_4770_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4770_, 0, v___x_4769_);
                return v___x_4770_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0___boxed(
    mut v___y_4777_: *mut crate::leanh::LeanObject,
    mut v_isExporting_4778_: *mut crate::leanh::LeanObject,
    mut v___x_4779_: *mut crate::leanh::LeanObject,
    mut v___y_4780_: *mut crate::leanh::LeanObject,
    mut v___x_4781_: *mut crate::leanh::LeanObject,
    mut v_a_x3f_4782_: *mut crate::leanh::LeanObject,
    mut v___y_4783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_4784_: u8 = 0;
    let mut v_res_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4784_ = (crate::leanh::lean_unbox(v_isExporting_4778_) as u8);
    v_res_4785_ =
        l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(
            v___y_4777_,
            v_isExporting_boxed_4784_,
            v___x_4779_,
            v___y_4780_,
            v___x_4781_,
            v_a_x3f_4782_,
        );
    crate::leanh::lean_dec(v_a_x3f_4782_);
    crate::leanh::lean_dec(v___y_4780_);
    crate::leanh::lean_dec(v___y_4777_);
    return v_res_4785_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4786_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4786_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4787_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0_once), _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__0);
    v___x_4788_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4788_, 0, v___x_4787_);
    return v___x_4788_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4789_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
    v___x_4790_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4790_, 0, v___x_4789_);
    crate::leanh::lean_ctor_set(v___x_4790_, 1, v___x_4789_);
    return v___x_4790_;
}
pub unsafe fn _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4791_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1_once), _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__1);
    v___x_4792_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4792_, 0, v___x_4791_);
    crate::leanh::lean_ctor_set(v___x_4792_, 1, v___x_4791_);
    crate::leanh::lean_ctor_set(v___x_4792_, 2, v___x_4791_);
    crate::leanh::lean_ctor_set(v___x_4792_, 3, v___x_4791_);
    crate::leanh::lean_ctor_set(v___x_4792_, 4, v___x_4791_);
    crate::leanh::lean_ctor_set(v___x_4792_, 5, v___x_4791_);
    return v___x_4792_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(
    mut v_x_4793_: *mut crate::leanh::LeanObject,
    mut v_isExporting_4794_: u8,
    mut v___y_4795_: *mut crate::leanh::LeanObject,
    mut v___y_4796_: *mut crate::leanh::LeanObject,
    mut v___y_4797_: *mut crate::leanh::LeanObject,
    mut v___y_4798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isExporting_4802_: u8 = 0;
    let mut v___x_4803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_4806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_4809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_4810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4814_: u8 = 0;
    let mut v___x_4815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4827_: u8 = 0;
    let mut v___x_4828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_4832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4836_: u8 = 0;
    let mut v___x_4838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4842_: u8 = 0;
    let mut v___x_4844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4846_: u8 = 0;
    let mut v_unused_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4849_: u8 = 0;
    let mut v_a_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4855_: u8 = 0;
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4859_: u8 = 0;
    let mut v_unused_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4862_: u8 = 0;
    let mut v_unused_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4865_: u8 = 0;
    let mut v_unused_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4800_ = lean_st_ref_get(v___y_4798_);
                v_env_4801_ = crate::leanh::lean_ctor_get(v___x_4800_, 0);
                crate::leanh::lean_inc_ref(v_env_4801_);
                crate::leanh::lean_dec(v___x_4800_);
                v_isExporting_4802_ = crate::leanh::lean_ctor_get_uint8(
                    v_env_4801_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                );
                crate::leanh::lean_dec_ref(v_env_4801_);
                v___x_4803_ = lean_st_ref_take(v___y_4798_);
                v_env_4804_ = crate::leanh::lean_ctor_get(v___x_4803_, 0);
                v_nextMacroScope_4805_ = crate::leanh::lean_ctor_get(v___x_4803_, 1);
                v_ngen_4806_ = crate::leanh::lean_ctor_get(v___x_4803_, 2);
                v_auxDeclNGen_4807_ = crate::leanh::lean_ctor_get(v___x_4803_, 3);
                v_traceState_4808_ = crate::leanh::lean_ctor_get(v___x_4803_, 4);
                v_messages_4809_ = crate::leanh::lean_ctor_get(v___x_4803_, 6);
                v_infoState_4810_ = crate::leanh::lean_ctor_get(v___x_4803_, 7);
                v_snapshotTasks_4811_ = crate::leanh::lean_ctor_get(v___x_4803_, 8);
                v_isSharedCheck_4865_ = (!crate::leanh::lean_is_exclusive(v___x_4803_)) as u8;
                if v_isSharedCheck_4865_ == 0 {
                    v_unused_4866_ = crate::leanh::lean_ctor_get(v___x_4803_, 5);
                    crate::leanh::lean_dec(v_unused_4866_);
                    v___x_4813_ = v___x_4803_;
                    v_isShared_4814_ = v_isSharedCheck_4865_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_4811_);
                    crate::leanh::lean_inc(v_infoState_4810_);
                    crate::leanh::lean_inc(v_messages_4809_);
                    crate::leanh::lean_inc(v_traceState_4808_);
                    crate::leanh::lean_inc(v_auxDeclNGen_4807_);
                    crate::leanh::lean_inc(v_ngen_4806_);
                    crate::leanh::lean_inc(v_nextMacroScope_4805_);
                    crate::leanh::lean_inc(v_env_4804_);
                    crate::leanh::lean_dec(v___x_4803_);
                    v___x_4813_ = crate::leanh::lean_box(0);
                    v_isShared_4814_ = v_isSharedCheck_4865_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4815_ = l_Lean_Environment_setExporting(v_env_4804_, v_isExporting_4794_);
                v___x_4816_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
                if v_isShared_4814_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4813_, 5, v___x_4816_);
                    crate::leanh::lean_ctor_set(v___x_4813_, 0, v___x_4815_);
                    v___x_4818_ = v___x_4813_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4864_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4864_, 0, v___x_4815_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4864_, 1, v_nextMacroScope_4805_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4864_, 2, v_ngen_4806_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4864_, 3, v_auxDeclNGen_4807_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4864_, 4, v_traceState_4808_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4864_, 5, v___x_4816_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4864_, 6, v_messages_4809_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4864_, 7, v_infoState_4810_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4864_, 8, v_snapshotTasks_4811_);
                    v___x_4818_ = v_reuseFailAlloc_4864_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4819_ = lean_st_ref_set(v___y_4798_, v___x_4818_);
                v___x_4820_ = lean_st_ref_take(v___y_4796_);
                v_mctx_4821_ = crate::leanh::lean_ctor_get(v___x_4820_, 0);
                v_zetaDeltaFVarIds_4822_ = crate::leanh::lean_ctor_get(v___x_4820_, 2);
                v_postponed_4823_ = crate::leanh::lean_ctor_get(v___x_4820_, 3);
                v_diag_4824_ = crate::leanh::lean_ctor_get(v___x_4820_, 4);
                v_isSharedCheck_4862_ = (!crate::leanh::lean_is_exclusive(v___x_4820_)) as u8;
                if v_isSharedCheck_4862_ == 0 {
                    v_unused_4863_ = crate::leanh::lean_ctor_get(v___x_4820_, 1);
                    crate::leanh::lean_dec(v_unused_4863_);
                    v___x_4826_ = v___x_4820_;
                    v_isShared_4827_ = v_isSharedCheck_4862_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_4824_);
                    crate::leanh::lean_inc(v_postponed_4823_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_4822_);
                    crate::leanh::lean_inc(v_mctx_4821_);
                    crate::leanh::lean_dec(v___x_4820_);
                    v___x_4826_ = crate::leanh::lean_box(0);
                    v_isShared_4827_ = v_isSharedCheck_4862_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4828_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once), _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
                if v_isShared_4827_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4826_, 1, v___x_4828_);
                    v___x_4830_ = v___x_4826_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4861_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4861_, 0, v_mctx_4821_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4861_, 1, v___x_4828_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_4861_,
                        2,
                        v_zetaDeltaFVarIds_4822_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4861_, 3, v_postponed_4823_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4861_, 4, v_diag_4824_);
                    v___x_4830_ = v_reuseFailAlloc_4861_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4831_ = lean_st_ref_set(v___y_4796_, v___x_4830_);
                crate::leanh::lean_inc(v___y_4798_);
                crate::leanh::lean_inc_ref(v___y_4797_);
                crate::leanh::lean_inc(v___y_4796_);
                crate::leanh::lean_inc_ref(v___y_4795_);
                v_r_4832_ = crate::leanh::lean_apply_5(
                    v_x_4793_,
                    v___y_4795_,
                    v___y_4796_,
                    v___y_4797_,
                    v___y_4798_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v_r_4832_) == 0 {
                    v_a_4833_ = crate::leanh::lean_ctor_get(v_r_4832_, 0);
                    v_isSharedCheck_4849_ = (!crate::leanh::lean_is_exclusive(v_r_4832_)) as u8;
                    if v_isSharedCheck_4849_ == 0 {
                        v___x_4835_ = v_r_4832_;
                        v_isShared_4836_ = v_isSharedCheck_4849_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4833_);
                        crate::leanh::lean_dec(v_r_4832_);
                        v___x_4835_ = crate::leanh::lean_box(0);
                        v_isShared_4836_ = v_isSharedCheck_4849_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_4850_ = crate::leanh::lean_ctor_get(v_r_4832_, 0);
                    crate::leanh::lean_inc(v_a_4850_);
                    crate::leanh::lean_dec_ref_known(v_r_4832_, 1);
                    v___x_4851_ = crate::leanh::lean_box(0);
                    v___x_4852_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_4798_, v_isExporting_4802_, v___x_4816_, v___y_4796_, v___x_4828_, v___x_4851_);
                    v_isSharedCheck_4859_ = (!crate::leanh::lean_is_exclusive(v___x_4852_)) as u8;
                    if v_isSharedCheck_4859_ == 0 {
                        v_unused_4860_ = crate::leanh::lean_ctor_get(v___x_4852_, 0);
                        crate::leanh::lean_dec(v_unused_4860_);
                        v___x_4854_ = v___x_4852_;
                        v_isShared_4855_ = v_isSharedCheck_4859_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_4852_);
                        v___x_4854_ = crate::leanh::lean_box(0);
                        v_isShared_4855_ = v_isSharedCheck_4859_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                crate::leanh::lean_inc(v_a_4833_);
                if v_isShared_4836_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4835_, 1);
                    v___x_4838_ = v___x_4835_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4848_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4848_, 0, v_a_4833_);
                    v___x_4838_ = v_reuseFailAlloc_4848_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4839_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___lam__0(v___y_4798_, v_isExporting_4802_, v___x_4816_, v___y_4796_, v___x_4828_, v___x_4838_);
                crate::leanh::lean_dec_ref(v___x_4838_);
                v_isSharedCheck_4846_ = (!crate::leanh::lean_is_exclusive(v___x_4839_)) as u8;
                if v_isSharedCheck_4846_ == 0 {
                    v_unused_4847_ = crate::leanh::lean_ctor_get(v___x_4839_, 0);
                    crate::leanh::lean_dec(v_unused_4847_);
                    v___x_4841_ = v___x_4839_;
                    v_isShared_4842_ = v_isSharedCheck_4846_;
                    state = 7;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_4839_);
                    v___x_4841_ = crate::leanh::lean_box(0);
                    v_isShared_4842_ = v_isSharedCheck_4846_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_4842_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4841_, 0, v_a_4833_);
                    v___x_4844_ = v___x_4841_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4845_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4845_, 0, v_a_4833_);
                    v___x_4844_ = v_reuseFailAlloc_4845_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4844_;
            }
            9 => {
                if v_isShared_4855_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4854_, 1);
                    crate::leanh::lean_ctor_set(v___x_4854_, 0, v_a_4850_);
                    v___x_4857_ = v___x_4854_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4858_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4858_, 0, v_a_4850_);
                    v___x_4857_ = v_reuseFailAlloc_4858_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4857_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___boxed(
    mut v_x_4867_: *mut crate::leanh::LeanObject,
    mut v_isExporting_4868_: *mut crate::leanh::LeanObject,
    mut v___y_4869_: *mut crate::leanh::LeanObject,
    mut v___y_4870_: *mut crate::leanh::LeanObject,
    mut v___y_4871_: *mut crate::leanh::LeanObject,
    mut v___y_4872_: *mut crate::leanh::LeanObject,
    mut v___y_4873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_4874_: u8 = 0;
    let mut v_res_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4874_ = (crate::leanh::lean_unbox(v_isExporting_4868_) as u8);
    v_res_4875_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(
        v_x_4867_,
        v_isExporting_boxed_4874_,
        v___y_4869_,
        v___y_4870_,
        v___y_4871_,
        v___y_4872_,
    );
    crate::leanh::lean_dec(v___y_4872_);
    crate::leanh::lean_dec_ref(v___y_4871_);
    crate::leanh::lean_dec(v___y_4870_);
    crate::leanh::lean_dec_ref(v___y_4869_);
    return v_res_4875_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(
    mut v_00_u03b1_4876_: *mut crate::leanh::LeanObject,
    mut v_x_4877_: *mut crate::leanh::LeanObject,
    mut v_isExporting_4878_: u8,
    mut v___y_4879_: *mut crate::leanh::LeanObject,
    mut v___y_4880_: *mut crate::leanh::LeanObject,
    mut v___y_4881_: *mut crate::leanh::LeanObject,
    mut v___y_4882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4884_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(
        v_x_4877_,
        v_isExporting_4878_,
        v___y_4879_,
        v___y_4880_,
        v___y_4881_,
        v___y_4882_,
    );
    return v___x_4884_;
}
pub unsafe fn l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___boxed(
    mut v_00_u03b1_4885_: *mut crate::leanh::LeanObject,
    mut v_x_4886_: *mut crate::leanh::LeanObject,
    mut v_isExporting_4887_: *mut crate::leanh::LeanObject,
    mut v___y_4888_: *mut crate::leanh::LeanObject,
    mut v___y_4889_: *mut crate::leanh::LeanObject,
    mut v___y_4890_: *mut crate::leanh::LeanObject,
    mut v___y_4891_: *mut crate::leanh::LeanObject,
    mut v___y_4892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isExporting_boxed_4893_: u8 = 0;
    let mut v_res_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isExporting_boxed_4893_ = (crate::leanh::lean_unbox(v_isExporting_4887_) as u8);
    v_res_4894_ = l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11(
        v_00_u03b1_4885_,
        v_x_4886_,
        v_isExporting_boxed_4893_,
        v___y_4888_,
        v___y_4889_,
        v___y_4890_,
        v___y_4891_,
    );
    crate::leanh::lean_dec(v___y_4891_);
    crate::leanh::lean_dec_ref(v___y_4890_);
    crate::leanh::lean_dec(v___y_4889_);
    crate::leanh::lean_dec_ref(v___y_4888_);
    return v_res_4894_;
}
pub unsafe fn l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(
    mut v_msg_4896_: *mut crate::leanh::LeanObject,
    mut v___y_4897_: *mut crate::leanh::LeanObject,
    mut v___y_4898_: *mut crate::leanh::LeanObject,
    mut v___y_4899_: *mut crate::leanh::LeanObject,
    mut v___y_4900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_15693__overap_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_4902_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___closed__0;
    v___x_15693__overap_4903_ = lean_panic_fn_borrowed(v___f_4902_, v_msg_4896_);
    crate::leanh::lean_inc(v___y_4900_);
    crate::leanh::lean_inc_ref(v___y_4899_);
    crate::leanh::lean_inc(v___y_4898_);
    crate::leanh::lean_inc_ref(v___y_4897_);
    v___x_4904_ = crate::leanh::lean_apply_5(
        v___x_15693__overap_4903_,
        v___y_4897_,
        v___y_4898_,
        v___y_4899_,
        v___y_4900_,
        crate::leanh::lean_box(0),
    );
    return v___x_4904_;
}
pub unsafe fn l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14___boxed(
    mut v_msg_4905_: *mut crate::leanh::LeanObject,
    mut v___y_4906_: *mut crate::leanh::LeanObject,
    mut v___y_4907_: *mut crate::leanh::LeanObject,
    mut v___y_4908_: *mut crate::leanh::LeanObject,
    mut v___y_4909_: *mut crate::leanh::LeanObject,
    mut v___y_4910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4911_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(
        v_msg_4905_,
        v___y_4906_,
        v___y_4907_,
        v___y_4908_,
        v___y_4909_,
    );
    crate::leanh::lean_dec(v___y_4909_);
    crate::leanh::lean_dec_ref(v___y_4908_);
    crate::leanh::lean_dec(v___y_4907_);
    crate::leanh::lean_dec_ref(v___y_4906_);
    return v_res_4911_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(
    mut v_name_4912_: *mut crate::leanh::LeanObject,
    mut v_type_4913_: *mut crate::leanh::LeanObject,
    mut v_k_4914_: *mut crate::leanh::LeanObject,
    mut v___y_4915_: *mut crate::leanh::LeanObject,
    mut v___y_4916_: *mut crate::leanh::LeanObject,
    mut v___y_4917_: *mut crate::leanh::LeanObject,
    mut v___y_4918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4920_: u8 = 0;
    let mut v___x_4921_: u8 = 0;
    let mut v___x_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4920_ = 0;
    v___x_4921_ = 0;
    v___x_4922_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(
        v_name_4912_,
        v___x_4920_,
        v_type_4913_,
        v_k_4914_,
        v___x_4921_,
        v___y_4915_,
        v___y_4916_,
        v___y_4917_,
        v___y_4918_,
    );
    return v___x_4922_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg___boxed(
    mut v_name_4923_: *mut crate::leanh::LeanObject,
    mut v_type_4924_: *mut crate::leanh::LeanObject,
    mut v_k_4925_: *mut crate::leanh::LeanObject,
    mut v___y_4926_: *mut crate::leanh::LeanObject,
    mut v___y_4927_: *mut crate::leanh::LeanObject,
    mut v___y_4928_: *mut crate::leanh::LeanObject,
    mut v___y_4929_: *mut crate::leanh::LeanObject,
    mut v___y_4930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4931_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(
        v_name_4923_,
        v_type_4924_,
        v_k_4925_,
        v___y_4926_,
        v___y_4927_,
        v___y_4928_,
        v___y_4929_,
    );
    crate::leanh::lean_dec(v___y_4929_);
    crate::leanh::lean_dec_ref(v___y_4928_);
    crate::leanh::lean_dec(v___y_4927_);
    crate::leanh::lean_dec_ref(v___y_4926_);
    return v_res_4931_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(
    mut v___x_4932_: *mut crate::leanh::LeanObject,
    mut v_alts_4933_: *mut crate::leanh::LeanObject,
    mut v_j_4934_: *mut crate::leanh::LeanObject,
    mut v_zs1_4935_: *mut crate::leanh::LeanObject,
    mut v_isZero_4936_: u8,
    mut v___x_4937_: u8,
    mut v___x_4938_: u8,
    mut v_zs2_4939_: *mut crate::leanh::LeanObject,
    mut v_x_4940_: *mut crate::leanh::LeanObject,
    mut v___y_4941_: *mut crate::leanh::LeanObject,
    mut v___y_4942_: *mut crate::leanh::LeanObject,
    mut v___y_4943_: *mut crate::leanh::LeanObject,
    mut v___y_4944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4946_ = lean_array_get_borrowed(v___x_4932_, v_alts_4933_, v_j_4934_);
    v___x_4947_ = l_Array_append___redArg(v_zs1_4935_, v_zs2_4939_);
    crate::leanh::lean_inc(v___x_4946_);
    v___x_4948_ = l_Lean_mkAppN(v___x_4946_, v___x_4947_);
    crate::leanh::lean_dec_ref(v___x_4947_);
    v___x_4949_ = l_Lean_Meta_mkLambdaFVars(
        v_zs2_4939_,
        v___x_4948_,
        v_isZero_4936_,
        v___x_4937_,
        v_isZero_4936_,
        v___x_4937_,
        v___x_4938_,
        v___y_4941_,
        v___y_4942_,
        v___y_4943_,
        v___y_4944_,
    );
    return v___x_4949_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed(
    mut v___x_4950_: *mut crate::leanh::LeanObject,
    mut v_alts_4951_: *mut crate::leanh::LeanObject,
    mut v_j_4952_: *mut crate::leanh::LeanObject,
    mut v_zs1_4953_: *mut crate::leanh::LeanObject,
    mut v_isZero_4954_: *mut crate::leanh::LeanObject,
    mut v___x_4955_: *mut crate::leanh::LeanObject,
    mut v___x_4956_: *mut crate::leanh::LeanObject,
    mut v_zs2_4957_: *mut crate::leanh::LeanObject,
    mut v_x_4958_: *mut crate::leanh::LeanObject,
    mut v___y_4959_: *mut crate::leanh::LeanObject,
    mut v___y_4960_: *mut crate::leanh::LeanObject,
    mut v___y_4961_: *mut crate::leanh::LeanObject,
    mut v___y_4962_: *mut crate::leanh::LeanObject,
    mut v___y_4963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isZero_boxed_4964_: u8 = 0;
    let mut v___x_20783__boxed_4965_: u8 = 0;
    let mut v___x_20784__boxed_4966_: u8 = 0;
    let mut v_res_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isZero_boxed_4964_ = (crate::leanh::lean_unbox(v_isZero_4954_) as u8);
    v___x_20783__boxed_4965_ = (crate::leanh::lean_unbox(v___x_4955_) as u8);
    v___x_20784__boxed_4966_ = (crate::leanh::lean_unbox(v___x_4956_) as u8);
    v_res_4967_ =
        l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0(
            v___x_4950_,
            v_alts_4951_,
            v_j_4952_,
            v_zs1_4953_,
            v_isZero_boxed_4964_,
            v___x_20783__boxed_4965_,
            v___x_20784__boxed_4966_,
            v_zs2_4957_,
            v_x_4958_,
            v___y_4959_,
            v___y_4960_,
            v___y_4961_,
            v___y_4962_,
        );
    crate::leanh::lean_dec(v___y_4962_);
    crate::leanh::lean_dec_ref(v___y_4961_);
    crate::leanh::lean_dec(v___y_4960_);
    crate::leanh::lean_dec_ref(v___y_4959_);
    crate::leanh::lean_dec_ref(v_x_4958_);
    crate::leanh::lean_dec_ref(v_zs2_4957_);
    crate::leanh::lean_dec(v_j_4952_);
    crate::leanh::lean_dec_ref(v_alts_4951_);
    crate::leanh::lean_dec_ref(v___x_4950_);
    return v_res_4967_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(
    mut v___x_4968_: *mut crate::leanh::LeanObject,
    mut v_ism2_4969_: *mut crate::leanh::LeanObject,
    mut v_motive_4970_: *mut crate::leanh::LeanObject,
    mut v_isZero_4971_: u8,
    mut v___x_4972_: u8,
    mut v___x_4973_: u8,
    mut v_a_4974_: *mut crate::leanh::LeanObject,
    mut v___f_4975_: *mut crate::leanh::LeanObject,
    mut v_zs1_4976_: *mut crate::leanh::LeanObject,
    mut v_val_4977_: *mut crate::leanh::LeanObject,
    mut v___x_4978_: *mut crate::leanh::LeanObject,
    mut v_indName_4979_: *mut crate::leanh::LeanObject,
    mut v___x_4980_: *mut crate::leanh::LeanObject,
    mut v___x_4981_: *mut crate::leanh::LeanObject,
    mut v_params_4982_: *mut crate::leanh::LeanObject,
    mut v___x_4983_: *mut crate::leanh::LeanObject,
    mut v_h_4984_: *mut crate::leanh::LeanObject,
    mut v___y_4985_: *mut crate::leanh::LeanObject,
    mut v___y_4986_: *mut crate::leanh::LeanObject,
    mut v___y_4987_: *mut crate::leanh::LeanObject,
    mut v___y_4988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5001_: u8 = 0;
    let mut v___x_5002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4990_ = l_Array_append___redArg(v___x_4968_, v_ism2_4969_);
                v___x_4991_ = l_Lean_mkAppN(v_motive_4970_, v___x_4990_);
                crate::leanh::lean_dec_ref(v___x_4990_);
                v___x_4992_ = l_Lean_Meta_mkLambdaFVars(
                    v_ism2_4969_,
                    v___x_4991_,
                    v_isZero_4971_,
                    v___x_4972_,
                    v_isZero_4971_,
                    v___x_4972_,
                    v___x_4973_,
                    v___y_4985_,
                    v___y_4986_,
                    v___y_4987_,
                    v___y_4988_,
                );
                if crate::leanh::lean_obj_tag(v___x_4992_) == 0 {
                    v_a_4993_ = crate::leanh::lean_ctor_get(v___x_4992_, 0);
                    crate::leanh::lean_inc(v_a_4993_);
                    crate::leanh::lean_dec_ref_known(v___x_4992_, 1);
                    v___x_4994_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_4974_, v___f_4975_, v_isZero_4971_, v___y_4985_, v___y_4986_, v___y_4987_, v___y_4988_);
                    if crate::leanh::lean_obj_tag(v___x_4994_) == 0 {
                        v_a_4995_ = crate::leanh::lean_ctor_get(v___x_4994_, 0);
                        crate::leanh::lean_inc(v_a_4995_);
                        crate::leanh::lean_dec_ref_known(v___x_4994_, 1);
                        v___x_5000_ = l_Lean_InductiveVal_numCtors(v_val_4977_);
                        v___x_5001_ = lean_nat_dec_eq(v___x_5000_, v___x_4978_);
                        crate::leanh::lean_dec(v___x_5000_);
                        if v___x_5001_ == 0 {
                            crate::leanh::lean_dec(v___x_4983_);
                            v___x_5002_ =
                                l_Lean_mkConstructorElimName(v_indName_4979_, v___x_4980_);
                            v___x_5003_ = l_Lean_mkConst(v___x_5002_, v___x_4981_);
                            v___x_5004_ = lean_mk_empty_array_with_capacity(v___x_4978_);
                            v___x_5005_ = lean_array_push(v___x_5004_, v_a_4993_);
                            v___x_5006_ = l_Array_append___redArg(v_params_4982_, v___x_5005_);
                            crate::leanh::lean_dec_ref(v___x_5005_);
                            v___x_5007_ = l_Array_append___redArg(v___x_5006_, v_ism2_4969_);
                            v___x_5008_ = crate::leanh::lean_unsigned_to_nat(2);
                            v___x_5009_ = lean_mk_empty_array_with_capacity(v___x_5008_);
                            crate::leanh::lean_inc_ref(v_h_4984_);
                            v___x_5010_ = lean_array_push(v___x_5009_, v_h_4984_);
                            v___x_5011_ = lean_array_push(v___x_5010_, v_a_4995_);
                            v___x_5012_ = l_Array_append___redArg(v___x_5007_, v___x_5011_);
                            crate::leanh::lean_dec_ref(v___x_5011_);
                            v___x_5013_ = l_Lean_mkAppN(v___x_5003_, v___x_5012_);
                            crate::leanh::lean_dec_ref(v___x_5012_);
                            v___y_4997_ = v___x_5013_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_4980_);
                            crate::leanh::lean_dec(v_indName_4979_);
                            v___x_5014_ = l_Lean_mkConst(v___x_4983_, v___x_4981_);
                            v___x_5015_ = lean_mk_empty_array_with_capacity(v___x_4978_);
                            crate::leanh::lean_inc_ref(v___x_5015_);
                            v___x_5016_ = lean_array_push(v___x_5015_, v_a_4993_);
                            v___x_5017_ = l_Array_append___redArg(v_params_4982_, v___x_5016_);
                            crate::leanh::lean_dec_ref(v___x_5016_);
                            v___x_5018_ = l_Array_append___redArg(v___x_5017_, v_ism2_4969_);
                            v___x_5019_ = lean_array_push(v___x_5015_, v_a_4995_);
                            v___x_5020_ = l_Array_append___redArg(v___x_5018_, v___x_5019_);
                            crate::leanh::lean_dec_ref(v___x_5019_);
                            v___x_5021_ = l_Lean_mkAppN(v___x_5014_, v___x_5020_);
                            crate::leanh::lean_dec_ref(v___x_5020_);
                            v___y_4997_ = v___x_5021_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4993_);
                        crate::leanh::lean_dec_ref(v_h_4984_);
                        crate::leanh::lean_dec(v___x_4983_);
                        crate::leanh::lean_dec_ref(v_params_4982_);
                        crate::leanh::lean_dec(v___x_4981_);
                        crate::leanh::lean_dec(v___x_4980_);
                        crate::leanh::lean_dec(v_indName_4979_);
                        crate::leanh::lean_dec_ref(v_zs1_4976_);
                        return v___x_4994_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_h_4984_);
                    crate::leanh::lean_dec(v___x_4983_);
                    crate::leanh::lean_dec_ref(v_params_4982_);
                    crate::leanh::lean_dec(v___x_4981_);
                    crate::leanh::lean_dec(v___x_4980_);
                    crate::leanh::lean_dec(v_indName_4979_);
                    crate::leanh::lean_dec_ref(v_zs1_4976_);
                    crate::leanh::lean_dec_ref(v___f_4975_);
                    crate::leanh::lean_dec_ref(v_a_4974_);
                    return v___x_4992_;
                }
            }
            1 => {
                v___x_4998_ = lean_array_push(v_zs1_4976_, v_h_4984_);
                v___x_4999_ = l_Lean_Meta_mkLambdaFVars(
                    v___x_4998_,
                    v___y_4997_,
                    v_isZero_4971_,
                    v___x_4972_,
                    v_isZero_4971_,
                    v___x_4972_,
                    v___x_4973_,
                    v___y_4985_,
                    v___y_4986_,
                    v___y_4987_,
                    v___y_4988_,
                );
                crate::leanh::lean_dec_ref(v___x_4998_);
                return v___x_4999_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5022_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_ism2_5023_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_motive_5024_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_isZero_5025_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_5026_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_5027_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_a_5028_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___f_5029_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_zs1_5030_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_val_5031_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_5032_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_indName_5033_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_5034_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___x_5035_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_params_5036_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___x_5037_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_h_5038_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_5039_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_5040_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_5041_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_5042_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___y_5043_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v_isZero_boxed_5044_: u8 = 0;
    let mut v___x_20818__boxed_5045_: u8 = 0;
    let mut v___x_20819__boxed_5046_: u8 = 0;
    let mut v_res_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isZero_boxed_5044_ = (crate::leanh::lean_unbox(v_isZero_5025_) as u8);
    v___x_20818__boxed_5045_ = (crate::leanh::lean_unbox(v___x_5026_) as u8);
    v___x_20819__boxed_5046_ = (crate::leanh::lean_unbox(v___x_5027_) as u8);
    v_res_5047_ =
        l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1(
            v___x_5022_,
            v_ism2_5023_,
            v_motive_5024_,
            v_isZero_boxed_5044_,
            v___x_20818__boxed_5045_,
            v___x_20819__boxed_5046_,
            v_a_5028_,
            v___f_5029_,
            v_zs1_5030_,
            v_val_5031_,
            v___x_5032_,
            v_indName_5033_,
            v___x_5034_,
            v___x_5035_,
            v_params_5036_,
            v___x_5037_,
            v_h_5038_,
            v___y_5039_,
            v___y_5040_,
            v___y_5041_,
            v___y_5042_,
        );
    crate::leanh::lean_dec(v___y_5042_);
    crate::leanh::lean_dec_ref(v___y_5041_);
    crate::leanh::lean_dec(v___y_5040_);
    crate::leanh::lean_dec_ref(v___y_5039_);
    crate::leanh::lean_dec(v___x_5032_);
    crate::leanh::lean_dec_ref(v_val_5031_);
    crate::leanh::lean_dec_ref(v_ism2_5023_);
    return v_res_5047_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_5049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5048_ = crate::leanh::lean_box(0);
    v_dummy_5049_ = l_Lean_Expr_sort___override(v___x_5048_);
    return v_dummy_5049_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5056_ = crate::leanh::lean_box(0);
    v___x_5057_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__4;
    v___x_5058_ = l_Lean_mkConst(v___x_5057_, v___x_5056_);
    return v___x_5058_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(
    mut v___x_5059_: *mut crate::leanh::LeanObject,
    mut v_alts_5060_: *mut crate::leanh::LeanObject,
    mut v_j_5061_: *mut crate::leanh::LeanObject,
    mut v_isZero_5062_: u8,
    mut v___x_5063_: u8,
    mut v___x_5064_: u8,
    mut v___x_5065_: *mut crate::leanh::LeanObject,
    mut v___x_5066_: *mut crate::leanh::LeanObject,
    mut v___x_5067_: *mut crate::leanh::LeanObject,
    mut v_ism2_5068_: *mut crate::leanh::LeanObject,
    mut v_motive_5069_: *mut crate::leanh::LeanObject,
    mut v_a_5070_: *mut crate::leanh::LeanObject,
    mut v_val_5071_: *mut crate::leanh::LeanObject,
    mut v_indName_5072_: *mut crate::leanh::LeanObject,
    mut v___x_5073_: *mut crate::leanh::LeanObject,
    mut v___x_5074_: *mut crate::leanh::LeanObject,
    mut v_params_5075_: *mut crate::leanh::LeanObject,
    mut v___x_5076_: *mut crate::leanh::LeanObject,
    mut v___x_5077_: *mut crate::leanh::LeanObject,
    mut v___x_5078_: *mut crate::leanh::LeanObject,
    mut v_zs1_5079_: *mut crate::leanh::LeanObject,
    mut v_ctorRet1_5080_: *mut crate::leanh::LeanObject,
    mut v___y_5081_: *mut crate::leanh::LeanObject,
    mut v___y_5082_: *mut crate::leanh::LeanObject,
    mut v___y_5083_: *mut crate::leanh::LeanObject,
    mut v___y_5084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_5084_);
    crate::leanh::lean_inc_ref(v___y_5083_);
    crate::leanh::lean_inc(v___y_5082_);
    crate::leanh::lean_inc_ref(v___y_5081_);
    v___x_5086_ = lean_whnf(
        v_ctorRet1_5080_,
        v___y_5081_,
        v___y_5082_,
        v___y_5083_,
        v___y_5084_,
    );
    if crate::leanh::lean_obj_tag(v___x_5086_) == 0 {
        let mut v_a_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_dummy_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_nargs_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_5087_ = crate::leanh::lean_ctor_get(v___x_5086_, 0);
        crate::leanh::lean_inc(v_a_5087_);
        crate::leanh::lean_dec_ref_known(v___x_5086_, 1);
        v___x_5088_ = crate::leanh::lean_box((v_isZero_5062_) as usize);
        v___x_5089_ = crate::leanh::lean_box((v___x_5063_) as usize);
        v___x_5090_ = crate::leanh::lean_box((v___x_5064_) as usize);
        crate::leanh::lean_inc_ref(v_zs1_5079_);
        crate::leanh::lean_inc(v_j_5061_);
        v___f_5091_ = crate::leanh::lean_alloc_closure(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
        crate::leanh::lean_closure_set(v___f_5091_, 0, v___x_5059_);
        crate::leanh::lean_closure_set(v___f_5091_, 1, v_alts_5060_);
        crate::leanh::lean_closure_set(v___f_5091_, 2, v_j_5061_);
        crate::leanh::lean_closure_set(v___f_5091_, 3, v_zs1_5079_);
        crate::leanh::lean_closure_set(v___f_5091_, 4, v___x_5088_);
        crate::leanh::lean_closure_set(v___f_5091_, 5, v___x_5089_);
        crate::leanh::lean_closure_set(v___f_5091_, 6, v___x_5090_);
        v___x_5092_ = l_Lean_mkAppN(v___x_5065_, v_zs1_5079_);
        v_dummy_5093_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once), _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
        v_nargs_5094_ = l_Lean_Expr_getAppNumArgs(v_a_5087_);
        crate::leanh::lean_inc(v_nargs_5094_);
        v___x_5095_ = lean_mk_array(v_nargs_5094_, v_dummy_5093_);
        v___x_5096_ = lean_nat_sub(v_nargs_5094_, v___x_5066_);
        crate::leanh::lean_dec(v_nargs_5094_);
        v___x_5097_ =
            l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_5087_, v___x_5095_, v___x_5096_);
        v___x_5098_ = lean_array_get_size(v___x_5097_);
        v___x_5099_ = l_Array_toSubarray___redArg(v___x_5097_, v___x_5067_, v___x_5098_);
        v___x_5100_ = l_Subarray_copy___redArg(v___x_5099_);
        v___x_5101_ = lean_array_push(v___x_5100_, v___x_5092_);
        v___x_5102_ = crate::leanh::lean_box((v_isZero_5062_) as usize);
        v___x_5103_ = crate::leanh::lean_box((v___x_5063_) as usize);
        v___x_5104_ = crate::leanh::lean_box((v___x_5064_) as usize);
        crate::leanh::lean_inc(v___x_5066_);
        v___f_5105_ = crate::leanh::lean_alloc_closure(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__1___boxed as *mut core::ffi::c_void, 22, 16);
        crate::leanh::lean_closure_set(v___f_5105_, 0, v___x_5101_);
        crate::leanh::lean_closure_set(v___f_5105_, 1, v_ism2_5068_);
        crate::leanh::lean_closure_set(v___f_5105_, 2, v_motive_5069_);
        crate::leanh::lean_closure_set(v___f_5105_, 3, v___x_5102_);
        crate::leanh::lean_closure_set(v___f_5105_, 4, v___x_5103_);
        crate::leanh::lean_closure_set(v___f_5105_, 5, v___x_5104_);
        crate::leanh::lean_closure_set(v___f_5105_, 6, v_a_5070_);
        crate::leanh::lean_closure_set(v___f_5105_, 7, v___f_5091_);
        crate::leanh::lean_closure_set(v___f_5105_, 8, v_zs1_5079_);
        crate::leanh::lean_closure_set(v___f_5105_, 9, v_val_5071_);
        crate::leanh::lean_closure_set(v___f_5105_, 10, v___x_5066_);
        crate::leanh::lean_closure_set(v___f_5105_, 11, v_indName_5072_);
        crate::leanh::lean_closure_set(v___f_5105_, 12, v___x_5073_);
        crate::leanh::lean_closure_set(v___f_5105_, 13, v___x_5074_);
        crate::leanh::lean_closure_set(v___f_5105_, 14, v_params_5075_);
        crate::leanh::lean_closure_set(v___f_5105_, 15, v___x_5076_);
        v___x_5106_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__2;
        v___x_5107_ = l_Lean_Level_ofNat(v___x_5066_);
        crate::leanh::lean_dec(v___x_5066_);
        v___x_5108_ = crate::leanh::lean_box(0);
        v___x_5109_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_5109_, 0, v___x_5107_);
        crate::leanh::lean_ctor_set(v___x_5109_, 1, v___x_5108_);
        v___x_5110_ = l_Lean_mkConst(v___x_5106_, v___x_5109_);
        v___x_5111_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5_once), _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__5);
        v___x_5112_ = l_Lean_mkRawNatLit(v_j_5061_);
        v___x_5113_ = l_Lean_mkApp3(v___x_5110_, v___x_5111_, v___x_5077_, v___x_5112_);
        v___x_5114_ =
            l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(
                v___x_5078_,
                v___x_5113_,
                v___f_5105_,
                v___y_5081_,
                v___y_5082_,
                v___y_5083_,
                v___y_5084_,
            );
        return v___x_5114_;
    } else {
        crate::leanh::lean_dec_ref(v_zs1_5079_);
        crate::leanh::lean_dec(v___x_5078_);
        crate::leanh::lean_dec_ref(v___x_5077_);
        crate::leanh::lean_dec(v___x_5076_);
        crate::leanh::lean_dec_ref(v_params_5075_);
        crate::leanh::lean_dec(v___x_5074_);
        crate::leanh::lean_dec(v___x_5073_);
        crate::leanh::lean_dec(v_indName_5072_);
        crate::leanh::lean_dec_ref(v_val_5071_);
        crate::leanh::lean_dec_ref(v_a_5070_);
        crate::leanh::lean_dec_ref(v_motive_5069_);
        crate::leanh::lean_dec_ref(v_ism2_5068_);
        crate::leanh::lean_dec(v___x_5067_);
        crate::leanh::lean_dec(v___x_5066_);
        crate::leanh::lean_dec_ref(v___x_5065_);
        crate::leanh::lean_dec(v_j_5061_);
        crate::leanh::lean_dec_ref(v_alts_5060_);
        crate::leanh::lean_dec_ref(v___x_5059_);
        return v___x_5086_;
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5115_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_alts_5116_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_j_5117_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_isZero_5118_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_5119_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_5120_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_5121_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_5122_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_5123_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_ism2_5124_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_motive_5125_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_a_5126_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_val_5127_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_indName_5128_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___x_5129_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___x_5130_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_params_5131_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___x_5132_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___x_5133_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___x_5134_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_zs1_5135_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_ctorRet1_5136_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v___y_5137_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v___y_5138_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v___y_5139_: *mut crate::leanh::LeanObject = *_args.add(24);
    let mut v___y_5140_: *mut crate::leanh::LeanObject = *_args.add(25);
    let mut v___y_5141_: *mut crate::leanh::LeanObject = *_args.add(26);
    let mut v_isZero_boxed_5142_: u8 = 0;
    let mut v___x_20949__boxed_5143_: u8 = 0;
    let mut v___x_20950__boxed_5144_: u8 = 0;
    let mut v_res_5145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isZero_boxed_5142_ = (crate::leanh::lean_unbox(v_isZero_5118_) as u8);
    v___x_20949__boxed_5143_ = (crate::leanh::lean_unbox(v___x_5119_) as u8);
    v___x_20950__boxed_5144_ = (crate::leanh::lean_unbox(v___x_5120_) as u8);
    v_res_5145_ =
        l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2(
            v___x_5115_,
            v_alts_5116_,
            v_j_5117_,
            v_isZero_boxed_5142_,
            v___x_20949__boxed_5143_,
            v___x_20950__boxed_5144_,
            v___x_5121_,
            v___x_5122_,
            v___x_5123_,
            v_ism2_5124_,
            v_motive_5125_,
            v_a_5126_,
            v_val_5127_,
            v_indName_5128_,
            v___x_5129_,
            v___x_5130_,
            v_params_5131_,
            v___x_5132_,
            v___x_5133_,
            v___x_5134_,
            v_zs1_5135_,
            v_ctorRet1_5136_,
            v___y_5137_,
            v___y_5138_,
            v___y_5139_,
            v___y_5140_,
        );
    crate::leanh::lean_dec(v___y_5140_);
    crate::leanh::lean_dec_ref(v___y_5139_);
    crate::leanh::lean_dec(v___y_5138_);
    crate::leanh::lean_dec_ref(v___y_5137_);
    return v_res_5145_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(
    mut v_tail_5149_: *mut crate::leanh::LeanObject,
    mut v_params_5150_: *mut crate::leanh::LeanObject,
    mut v_alts_5151_: *mut crate::leanh::LeanObject,
    mut v___x_5152_: *mut crate::leanh::LeanObject,
    mut v_ism2_5153_: *mut crate::leanh::LeanObject,
    mut v_motive_5154_: *mut crate::leanh::LeanObject,
    mut v_val_5155_: *mut crate::leanh::LeanObject,
    mut v_indName_5156_: *mut crate::leanh::LeanObject,
    mut v___x_5157_: *mut crate::leanh::LeanObject,
    mut v___x_5158_: *mut crate::leanh::LeanObject,
    mut v___x_5159_: *mut crate::leanh::LeanObject,
    mut v_as_5160_: *mut crate::leanh::LeanObject,
    mut v_i_5161_: *mut crate::leanh::LeanObject,
    mut v_j_5162_: *mut crate::leanh::LeanObject,
    mut v_bs_5163_: *mut crate::leanh::LeanObject,
    mut v___y_5164_: *mut crate::leanh::LeanObject,
    mut v___y_5165_: *mut crate::leanh::LeanObject,
    mut v___y_5166_: *mut crate::leanh::LeanObject,
    mut v___y_5167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5170_: u8 = 0;
    let mut v___x_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5183_: u8 = 0;
    let mut v___x_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5187_: u8 = 0;
    let mut v___x_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: u8 = 0;
    let mut v___x_5195_: u8 = 0;
    let mut v___x_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5169_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_5170_ = lean_nat_dec_eq(v_i_5161_, v_zero_5169_);
                if v_isZero_5170_ == 1 {
                    crate::leanh::lean_dec(v_j_5162_);
                    crate::leanh::lean_dec(v_i_5161_);
                    crate::leanh::lean_dec_ref(v___x_5159_);
                    crate::leanh::lean_dec(v___x_5158_);
                    crate::leanh::lean_dec(v___x_5157_);
                    crate::leanh::lean_dec(v_indName_5156_);
                    crate::leanh::lean_dec_ref(v_val_5155_);
                    crate::leanh::lean_dec_ref(v_motive_5154_);
                    crate::leanh::lean_dec_ref(v_ism2_5153_);
                    crate::leanh::lean_dec(v___x_5152_);
                    crate::leanh::lean_dec_ref(v_alts_5151_);
                    crate::leanh::lean_dec_ref(v_params_5150_);
                    crate::leanh::lean_dec(v_tail_5149_);
                    v___x_5171_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5171_, 0, v_bs_5163_);
                    return v___x_5171_;
                } else {
                    v___x_5172_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_5173_ = lean_nat_sub(v_i_5161_, v___x_5172_);
                    crate::leanh::lean_dec(v_i_5161_);
                    v___x_5188_ = lean_array_fget_borrowed(v_as_5160_, v_j_5162_);
                    crate::leanh::lean_inc(v_tail_5149_);
                    crate::leanh::lean_inc(v___x_5188_);
                    v___x_5189_ = l_Lean_mkConst(v___x_5188_, v_tail_5149_);
                    v___x_5190_ = l_Lean_mkAppN(v___x_5189_, v_params_5150_);
                    crate::leanh::lean_inc(v___y_5167_);
                    crate::leanh::lean_inc_ref(v___y_5166_);
                    crate::leanh::lean_inc(v___y_5165_);
                    crate::leanh::lean_inc_ref(v___y_5164_);
                    crate::leanh::lean_inc_ref(v___x_5190_);
                    v___x_5191_ = lean_infer_type(
                        v___x_5190_,
                        v___y_5164_,
                        v___y_5165_,
                        v___y_5166_,
                        v___y_5167_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5191_) == 0 {
                        v_a_5192_ = crate::leanh::lean_ctor_get(v___x_5191_, 0);
                        crate::leanh::lean_inc_n(v_a_5192_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_5191_, 1);
                        v___x_5193_ = l_Lean_instInhabitedExpr;
                        v___x_5194_ = 1;
                        v___x_5195_ = 1;
                        v___x_5196_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1;
                        v___x_5197_ = crate::leanh::lean_box((v_isZero_5170_) as usize);
                        v___x_5198_ = crate::leanh::lean_box((v___x_5194_) as usize);
                        v___x_5199_ = crate::leanh::lean_box((v___x_5195_) as usize);
                        crate::leanh::lean_inc_ref(v___x_5159_);
                        crate::leanh::lean_inc(v___x_5158_);
                        crate::leanh::lean_inc_ref(v_params_5150_);
                        crate::leanh::lean_inc(v___x_5157_);
                        crate::leanh::lean_inc(v___x_5188_);
                        crate::leanh::lean_inc(v_indName_5156_);
                        crate::leanh::lean_inc_ref(v_val_5155_);
                        crate::leanh::lean_inc_ref(v_motive_5154_);
                        crate::leanh::lean_inc_ref(v_ism2_5153_);
                        crate::leanh::lean_inc(v___x_5152_);
                        crate::leanh::lean_inc(v_j_5162_);
                        crate::leanh::lean_inc_ref(v_alts_5151_);
                        v___f_5200_ = crate::leanh::lean_alloc_closure(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___boxed as *mut core::ffi::c_void, 27, 20);
                        crate::leanh::lean_closure_set(v___f_5200_, 0, v___x_5193_);
                        crate::leanh::lean_closure_set(v___f_5200_, 1, v_alts_5151_);
                        crate::leanh::lean_closure_set(v___f_5200_, 2, v_j_5162_);
                        crate::leanh::lean_closure_set(v___f_5200_, 3, v___x_5197_);
                        crate::leanh::lean_closure_set(v___f_5200_, 4, v___x_5198_);
                        crate::leanh::lean_closure_set(v___f_5200_, 5, v___x_5199_);
                        crate::leanh::lean_closure_set(v___f_5200_, 6, v___x_5190_);
                        crate::leanh::lean_closure_set(v___f_5200_, 7, v___x_5172_);
                        crate::leanh::lean_closure_set(v___f_5200_, 8, v___x_5152_);
                        crate::leanh::lean_closure_set(v___f_5200_, 9, v_ism2_5153_);
                        crate::leanh::lean_closure_set(v___f_5200_, 10, v_motive_5154_);
                        crate::leanh::lean_closure_set(v___f_5200_, 11, v_a_5192_);
                        crate::leanh::lean_closure_set(v___f_5200_, 12, v_val_5155_);
                        crate::leanh::lean_closure_set(v___f_5200_, 13, v_indName_5156_);
                        crate::leanh::lean_closure_set(v___f_5200_, 14, v___x_5188_);
                        crate::leanh::lean_closure_set(v___f_5200_, 15, v___x_5157_);
                        crate::leanh::lean_closure_set(v___f_5200_, 16, v_params_5150_);
                        crate::leanh::lean_closure_set(v___f_5200_, 17, v___x_5158_);
                        crate::leanh::lean_closure_set(v___f_5200_, 18, v___x_5159_);
                        crate::leanh::lean_closure_set(v___f_5200_, 19, v___x_5196_);
                        v___x_5201_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_5192_, v___f_5200_, v_isZero_5170_, v___y_5164_, v___y_5165_, v___y_5166_, v___y_5167_);
                        v___y_5175_ = v___x_5201_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_5190_);
                        v___y_5175_ = v___x_5191_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_5175_) == 0 {
                    v_a_5176_ = crate::leanh::lean_ctor_get(v___y_5175_, 0);
                    crate::leanh::lean_inc(v_a_5176_);
                    crate::leanh::lean_dec_ref_known(v___y_5175_, 1);
                    v___x_5177_ = lean_nat_add(v_j_5162_, v___x_5172_);
                    crate::leanh::lean_dec(v_j_5162_);
                    v___x_5178_ = lean_array_push(v_bs_5163_, v_a_5176_);
                    v_i_5161_ = v_n_5173_;
                    v_j_5162_ = v___x_5177_;
                    v_bs_5163_ = v___x_5178_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_n_5173_);
                    crate::leanh::lean_dec_ref(v_bs_5163_);
                    crate::leanh::lean_dec(v_j_5162_);
                    crate::leanh::lean_dec_ref(v___x_5159_);
                    crate::leanh::lean_dec(v___x_5158_);
                    crate::leanh::lean_dec(v___x_5157_);
                    crate::leanh::lean_dec(v_indName_5156_);
                    crate::leanh::lean_dec_ref(v_val_5155_);
                    crate::leanh::lean_dec_ref(v_motive_5154_);
                    crate::leanh::lean_dec_ref(v_ism2_5153_);
                    crate::leanh::lean_dec(v___x_5152_);
                    crate::leanh::lean_dec_ref(v_alts_5151_);
                    crate::leanh::lean_dec_ref(v_params_5150_);
                    crate::leanh::lean_dec(v_tail_5149_);
                    v_a_5180_ = crate::leanh::lean_ctor_get(v___y_5175_, 0);
                    v_isSharedCheck_5187_ = (!crate::leanh::lean_is_exclusive(v___y_5175_)) as u8;
                    if v_isSharedCheck_5187_ == 0 {
                        v___x_5182_ = v___y_5175_;
                        v_isShared_5183_ = v_isSharedCheck_5187_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5180_);
                        crate::leanh::lean_dec(v___y_5175_);
                        v___x_5182_ = crate::leanh::lean_box(0);
                        v_isShared_5183_ = v_isSharedCheck_5187_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5183_ == 0 {
                    v___x_5185_ = v___x_5182_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5186_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5186_, 0, v_a_5180_);
                    v___x_5185_ = v_reuseFailAlloc_5186_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5185_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tail_5202_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_params_5203_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_alts_5204_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_5205_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_ism2_5206_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_motive_5207_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_val_5208_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_indName_5209_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_5210_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_5211_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_5212_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_as_5213_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_i_5214_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_j_5215_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_bs_5216_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5217_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5218_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_5219_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_5220_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_5221_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_res_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5222_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(
        v_tail_5202_,
        v_params_5203_,
        v_alts_5204_,
        v___x_5205_,
        v_ism2_5206_,
        v_motive_5207_,
        v_val_5208_,
        v_indName_5209_,
        v___x_5210_,
        v___x_5211_,
        v___x_5212_,
        v_as_5213_,
        v_i_5214_,
        v_j_5215_,
        v_bs_5216_,
        v___y_5217_,
        v___y_5218_,
        v___y_5219_,
        v___y_5220_,
    );
    crate::leanh::lean_dec(v___y_5220_);
    crate::leanh::lean_dec_ref(v___y_5219_);
    crate::leanh::lean_dec(v___y_5218_);
    crate::leanh::lean_dec_ref(v___y_5217_);
    crate::leanh::lean_dec_ref(v_as_5213_);
    return v_res_5222_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtorHet___lam__0(
    mut v_motive_5223_: *mut crate::leanh::LeanObject,
    mut v___x_5224_: *mut crate::leanh::LeanObject,
    mut v_a_5225_: *mut crate::leanh::LeanObject,
    mut v_ism1_5226_: *mut crate::leanh::LeanObject,
    mut v___x_5227_: u8,
    mut v___x_5228_: u8,
    mut v___x_5229_: u8,
    mut v___x_5230_: *mut crate::leanh::LeanObject,
    mut v_tail_5231_: *mut crate::leanh::LeanObject,
    mut v_params_5232_: *mut crate::leanh::LeanObject,
    mut v_alts_5233_: *mut crate::leanh::LeanObject,
    mut v_numParams_5234_: *mut crate::leanh::LeanObject,
    mut v_ism2_5235_: *mut crate::leanh::LeanObject,
    mut v_val_5236_: *mut crate::leanh::LeanObject,
    mut v_indName_5237_: *mut crate::leanh::LeanObject,
    mut v___x_5238_: *mut crate::leanh::LeanObject,
    mut v___x_5239_: *mut crate::leanh::LeanObject,
    mut v___x_5240_: *mut crate::leanh::LeanObject,
    mut v_name_5241_: *mut crate::leanh::LeanObject,
    mut v___x_5242_: *mut crate::leanh::LeanObject,
    mut v_heq_5243_: *mut crate::leanh::LeanObject,
    mut v___y_5244_: *mut crate::leanh::LeanObject,
    mut v___y_5245_: *mut crate::leanh::LeanObject,
    mut v___y_5246_: *mut crate::leanh::LeanObject,
    mut v___y_5247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5279_: u8 = 0;
    let mut v___x_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5283_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_motive_5223_);
                v___x_5249_ = l_Lean_mkAppN(v_motive_5223_, v___x_5224_);
                v___x_5250_ = l_Lean_mkArrow(v_a_5225_, v___x_5249_, v___y_5246_, v___y_5247_);
                if crate::leanh::lean_obj_tag(v___x_5250_) == 0 {
                    v_a_5251_ = crate::leanh::lean_ctor_get(v___x_5250_, 0);
                    crate::leanh::lean_inc(v_a_5251_);
                    crate::leanh::lean_dec_ref_known(v___x_5250_, 1);
                    v___x_5252_ = l_Lean_Meta_mkLambdaFVars(
                        v_ism1_5226_,
                        v_a_5251_,
                        v___x_5227_,
                        v___x_5228_,
                        v___x_5227_,
                        v___x_5228_,
                        v___x_5229_,
                        v___y_5244_,
                        v___y_5245_,
                        v___y_5246_,
                        v___y_5247_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5252_) == 0 {
                        v_a_5253_ = crate::leanh::lean_ctor_get(v___x_5252_, 0);
                        crate::leanh::lean_inc(v_a_5253_);
                        crate::leanh::lean_dec_ref_known(v___x_5252_, 1);
                        v___x_5254_ = lean_array_get_size(v___x_5230_);
                        v___x_5255_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_5256_ = lean_mk_empty_array_with_capacity(v___x_5254_);
                        crate::leanh::lean_inc(v___x_5238_);
                        crate::leanh::lean_inc_ref(v_motive_5223_);
                        crate::leanh::lean_inc_ref(v_ism2_5235_);
                        crate::leanh::lean_inc_ref(v_alts_5233_);
                        crate::leanh::lean_inc_ref(v_params_5232_);
                        v___x_5257_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(v_tail_5231_, v_params_5232_, v_alts_5233_, v_numParams_5234_, v_ism2_5235_, v_motive_5223_, v_val_5236_, v_indName_5237_, v___x_5238_, v___x_5239_, v___x_5240_, v___x_5230_, v___x_5254_, v___x_5255_, v___x_5256_, v___y_5244_, v___y_5245_, v___y_5246_, v___y_5247_);
                        if crate::leanh::lean_obj_tag(v___x_5257_) == 0 {
                            v_a_5258_ = crate::leanh::lean_ctor_get(v___x_5257_, 0);
                            crate::leanh::lean_inc(v_a_5258_);
                            crate::leanh::lean_dec_ref_known(v___x_5257_, 1);
                            crate::leanh::lean_inc_ref(v_heq_5243_);
                            v___x_5259_ = l_Lean_Meta_mkEqSymm(
                                v_heq_5243_,
                                v___y_5244_,
                                v___y_5245_,
                                v___y_5246_,
                                v___y_5247_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5259_) == 0 {
                                v_a_5260_ = crate::leanh::lean_ctor_get(v___x_5259_, 0);
                                crate::leanh::lean_inc(v_a_5260_);
                                crate::leanh::lean_dec_ref_known(v___x_5259_, 1);
                                v___x_5261_ = l_Lean_mkConst(v_name_5241_, v___x_5238_);
                                v___x_5262_ = l_Lean_mkAppN(v___x_5261_, v_params_5232_);
                                v___x_5263_ = l_Lean_Expr_app___override(v___x_5262_, v_a_5253_);
                                v___x_5264_ = l_Lean_mkAppN(v___x_5263_, v_ism1_5226_);
                                v___x_5265_ = l_Lean_mkAppN(v___x_5264_, v_a_5258_);
                                crate::leanh::lean_dec(v_a_5258_);
                                v___x_5266_ = l_Lean_Expr_app___override(v___x_5265_, v_a_5260_);
                                v___x_5267_ = lean_mk_empty_array_with_capacity(v___x_5242_);
                                crate::leanh::lean_inc_ref(v___x_5267_);
                                v___x_5268_ = lean_array_push(v___x_5267_, v_motive_5223_);
                                v___x_5269_ = l_Array_append___redArg(v_params_5232_, v___x_5268_);
                                crate::leanh::lean_dec_ref(v___x_5268_);
                                v___x_5270_ = l_Array_append___redArg(v___x_5269_, v_ism1_5226_);
                                v___x_5271_ = l_Array_append___redArg(v___x_5270_, v_ism2_5235_);
                                crate::leanh::lean_dec_ref(v_ism2_5235_);
                                v___x_5272_ = lean_array_push(v___x_5267_, v_heq_5243_);
                                v___x_5273_ = l_Array_append___redArg(v___x_5271_, v___x_5272_);
                                crate::leanh::lean_dec_ref(v___x_5272_);
                                v___x_5274_ = l_Array_append___redArg(v___x_5273_, v_alts_5233_);
                                crate::leanh::lean_dec_ref(v_alts_5233_);
                                v___x_5275_ = l_Lean_Meta_mkLambdaFVars(
                                    v___x_5274_,
                                    v___x_5266_,
                                    v___x_5227_,
                                    v___x_5228_,
                                    v___x_5227_,
                                    v___x_5228_,
                                    v___x_5229_,
                                    v___y_5244_,
                                    v___y_5245_,
                                    v___y_5246_,
                                    v___y_5247_,
                                );
                                crate::leanh::lean_dec_ref(v___x_5274_);
                                return v___x_5275_;
                            } else {
                                crate::leanh::lean_dec(v_a_5258_);
                                crate::leanh::lean_dec(v_a_5253_);
                                crate::leanh::lean_dec_ref(v_heq_5243_);
                                crate::leanh::lean_dec(v_name_5241_);
                                crate::leanh::lean_dec(v___x_5238_);
                                crate::leanh::lean_dec_ref(v_ism2_5235_);
                                crate::leanh::lean_dec_ref(v_alts_5233_);
                                crate::leanh::lean_dec_ref(v_params_5232_);
                                crate::leanh::lean_dec_ref(v_motive_5223_);
                                return v___x_5259_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5253_);
                            crate::leanh::lean_dec_ref(v_heq_5243_);
                            crate::leanh::lean_dec(v_name_5241_);
                            crate::leanh::lean_dec(v___x_5238_);
                            crate::leanh::lean_dec_ref(v_ism2_5235_);
                            crate::leanh::lean_dec_ref(v_alts_5233_);
                            crate::leanh::lean_dec_ref(v_params_5232_);
                            crate::leanh::lean_dec_ref(v_motive_5223_);
                            v_a_5276_ = crate::leanh::lean_ctor_get(v___x_5257_, 0);
                            v_isSharedCheck_5283_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5257_)) as u8;
                            if v_isSharedCheck_5283_ == 0 {
                                v___x_5278_ = v___x_5257_;
                                v_isShared_5279_ = v_isSharedCheck_5283_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5276_);
                                crate::leanh::lean_dec(v___x_5257_);
                                v___x_5278_ = crate::leanh::lean_box(0);
                                v_isShared_5279_ = v_isSharedCheck_5283_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_heq_5243_);
                        crate::leanh::lean_dec(v_name_5241_);
                        crate::leanh::lean_dec_ref(v___x_5240_);
                        crate::leanh::lean_dec(v___x_5239_);
                        crate::leanh::lean_dec(v___x_5238_);
                        crate::leanh::lean_dec(v_indName_5237_);
                        crate::leanh::lean_dec_ref(v_val_5236_);
                        crate::leanh::lean_dec_ref(v_ism2_5235_);
                        crate::leanh::lean_dec(v_numParams_5234_);
                        crate::leanh::lean_dec_ref(v_alts_5233_);
                        crate::leanh::lean_dec_ref(v_params_5232_);
                        crate::leanh::lean_dec(v_tail_5231_);
                        crate::leanh::lean_dec_ref(v_motive_5223_);
                        return v___x_5252_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_heq_5243_);
                    crate::leanh::lean_dec(v_name_5241_);
                    crate::leanh::lean_dec_ref(v___x_5240_);
                    crate::leanh::lean_dec(v___x_5239_);
                    crate::leanh::lean_dec(v___x_5238_);
                    crate::leanh::lean_dec(v_indName_5237_);
                    crate::leanh::lean_dec_ref(v_val_5236_);
                    crate::leanh::lean_dec_ref(v_ism2_5235_);
                    crate::leanh::lean_dec(v_numParams_5234_);
                    crate::leanh::lean_dec_ref(v_alts_5233_);
                    crate::leanh::lean_dec_ref(v_params_5232_);
                    crate::leanh::lean_dec(v_tail_5231_);
                    crate::leanh::lean_dec_ref(v_motive_5223_);
                    return v___x_5250_;
                }
            }
            1 => {
                if v_isShared_5279_ == 0 {
                    v___x_5281_ = v___x_5278_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5282_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5282_, 0, v_a_5276_);
                    v___x_5281_ = v_reuseFailAlloc_5282_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5281_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkCasesOnSameCtorHet___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_motive_5284_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_5285_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_a_5286_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_ism1_5287_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_5288_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_5289_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_5290_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_5291_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_tail_5292_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_params_5293_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_alts_5294_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_numParams_5295_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_ism2_5296_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_val_5297_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_indName_5298_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___x_5299_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___x_5300_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___x_5301_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_name_5302_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___x_5303_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_heq_5304_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___y_5305_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v___y_5306_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v___y_5307_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v___y_5308_: *mut crate::leanh::LeanObject = *_args.add(24);
    let mut v___y_5309_: *mut crate::leanh::LeanObject = *_args.add(25);
    let mut v___x_21174__boxed_5310_: u8 = 0;
    let mut v___x_21175__boxed_5311_: u8 = 0;
    let mut v___x_21176__boxed_5312_: u8 = 0;
    let mut v_res_5313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_21174__boxed_5310_ = (crate::leanh::lean_unbox(v___x_5288_) as u8);
    v___x_21175__boxed_5311_ = (crate::leanh::lean_unbox(v___x_5289_) as u8);
    v___x_21176__boxed_5312_ = (crate::leanh::lean_unbox(v___x_5290_) as u8);
    v_res_5313_ = l_Lean_mkCasesOnSameCtorHet___lam__0(
        v_motive_5284_,
        v___x_5285_,
        v_a_5286_,
        v_ism1_5287_,
        v___x_21174__boxed_5310_,
        v___x_21175__boxed_5311_,
        v___x_21176__boxed_5312_,
        v___x_5291_,
        v_tail_5292_,
        v_params_5293_,
        v_alts_5294_,
        v_numParams_5295_,
        v_ism2_5296_,
        v_val_5297_,
        v_indName_5298_,
        v___x_5299_,
        v___x_5300_,
        v___x_5301_,
        v_name_5302_,
        v___x_5303_,
        v_heq_5304_,
        v___y_5305_,
        v___y_5306_,
        v___y_5307_,
        v___y_5308_,
    );
    crate::leanh::lean_dec(v___y_5308_);
    crate::leanh::lean_dec_ref(v___y_5307_);
    crate::leanh::lean_dec(v___y_5306_);
    crate::leanh::lean_dec_ref(v___y_5305_);
    crate::leanh::lean_dec(v___x_5303_);
    crate::leanh::lean_dec_ref(v___x_5291_);
    crate::leanh::lean_dec_ref(v_ism1_5287_);
    crate::leanh::lean_dec_ref(v___x_5285_);
    return v_res_5313_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtorHet___lam__1(
    mut v_indName_5314_: *mut crate::leanh::LeanObject,
    mut v_tail_5315_: *mut crate::leanh::LeanObject,
    mut v_params_5316_: *mut crate::leanh::LeanObject,
    mut v_ism1_5317_: *mut crate::leanh::LeanObject,
    mut v_ism2_5318_: *mut crate::leanh::LeanObject,
    mut v_motive_5319_: *mut crate::leanh::LeanObject,
    mut v___x_5320_: *mut crate::leanh::LeanObject,
    mut v___x_5321_: u8,
    mut v___x_5322_: u8,
    mut v___x_5323_: u8,
    mut v___x_5324_: *mut crate::leanh::LeanObject,
    mut v_numParams_5325_: *mut crate::leanh::LeanObject,
    mut v_val_5326_: *mut crate::leanh::LeanObject,
    mut v___x_5327_: *mut crate::leanh::LeanObject,
    mut v___x_5328_: *mut crate::leanh::LeanObject,
    mut v_name_5329_: *mut crate::leanh::LeanObject,
    mut v___x_5330_: *mut crate::leanh::LeanObject,
    mut v_alts_5331_: *mut crate::leanh::LeanObject,
    mut v___y_5332_: *mut crate::leanh::LeanObject,
    mut v___y_5333_: *mut crate::leanh::LeanObject,
    mut v___y_5334_: *mut crate::leanh::LeanObject,
    mut v___y_5335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_indName_5314_);
    v___x_5337_ = l_mkCtorIdxName(v_indName_5314_);
    crate::leanh::lean_inc(v_tail_5315_);
    v___x_5338_ = l_Lean_mkConst(v___x_5337_, v_tail_5315_);
    crate::leanh::lean_inc_ref_n(v_params_5316_, 2);
    v___x_5339_ = l_Array_append___redArg(v_params_5316_, v_ism1_5317_);
    crate::leanh::lean_inc_ref(v___x_5338_);
    v___x_5340_ = l_Lean_mkAppN(v___x_5338_, v___x_5339_);
    crate::leanh::lean_dec_ref(v___x_5339_);
    v___x_5341_ = l_Array_append___redArg(v_params_5316_, v_ism2_5318_);
    v___x_5342_ = l_Lean_mkAppN(v___x_5338_, v___x_5341_);
    crate::leanh::lean_dec_ref(v___x_5341_);
    crate::leanh::lean_inc_ref(v___x_5342_);
    crate::leanh::lean_inc_ref(v___x_5340_);
    v___x_5343_ = l_Lean_Meta_mkEq(
        v___x_5340_,
        v___x_5342_,
        v___y_5332_,
        v___y_5333_,
        v___y_5334_,
        v___y_5335_,
    );
    if crate::leanh::lean_obj_tag(v___x_5343_) == 0 {
        let mut v_a_5344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_5344_ = crate::leanh::lean_ctor_get(v___x_5343_, 0);
        crate::leanh::lean_inc(v_a_5344_);
        crate::leanh::lean_dec_ref_known(v___x_5343_, 1);
        crate::leanh::lean_inc_ref(v___x_5342_);
        v___x_5345_ = l_Lean_Meta_mkEq(
            v___x_5342_,
            v___x_5340_,
            v___y_5332_,
            v___y_5333_,
            v___y_5334_,
            v___y_5335_,
        );
        if crate::leanh::lean_obj_tag(v___x_5345_) == 0 {
            let mut v_a_5346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_5346_ = crate::leanh::lean_ctor_get(v___x_5345_, 0);
            crate::leanh::lean_inc(v_a_5346_);
            crate::leanh::lean_dec_ref_known(v___x_5345_, 1);
            v___x_5347_ = crate::leanh::lean_box((v___x_5321_) as usize);
            v___x_5348_ = crate::leanh::lean_box((v___x_5322_) as usize);
            v___x_5349_ = crate::leanh::lean_box((v___x_5323_) as usize);
            v___f_5350_ = crate::leanh::lean_alloc_closure(
                l_Lean_mkCasesOnSameCtorHet___lam__0___boxed as *mut core::ffi::c_void,
                26,
                20,
            );
            crate::leanh::lean_closure_set(v___f_5350_, 0, v_motive_5319_);
            crate::leanh::lean_closure_set(v___f_5350_, 1, v___x_5320_);
            crate::leanh::lean_closure_set(v___f_5350_, 2, v_a_5346_);
            crate::leanh::lean_closure_set(v___f_5350_, 3, v_ism1_5317_);
            crate::leanh::lean_closure_set(v___f_5350_, 4, v___x_5347_);
            crate::leanh::lean_closure_set(v___f_5350_, 5, v___x_5348_);
            crate::leanh::lean_closure_set(v___f_5350_, 6, v___x_5349_);
            crate::leanh::lean_closure_set(v___f_5350_, 7, v___x_5324_);
            crate::leanh::lean_closure_set(v___f_5350_, 8, v_tail_5315_);
            crate::leanh::lean_closure_set(v___f_5350_, 9, v_params_5316_);
            crate::leanh::lean_closure_set(v___f_5350_, 10, v_alts_5331_);
            crate::leanh::lean_closure_set(v___f_5350_, 11, v_numParams_5325_);
            crate::leanh::lean_closure_set(v___f_5350_, 12, v_ism2_5318_);
            crate::leanh::lean_closure_set(v___f_5350_, 13, v_val_5326_);
            crate::leanh::lean_closure_set(v___f_5350_, 14, v_indName_5314_);
            crate::leanh::lean_closure_set(v___f_5350_, 15, v___x_5327_);
            crate::leanh::lean_closure_set(v___f_5350_, 16, v___x_5328_);
            crate::leanh::lean_closure_set(v___f_5350_, 17, v___x_5342_);
            crate::leanh::lean_closure_set(v___f_5350_, 18, v_name_5329_);
            crate::leanh::lean_closure_set(v___f_5350_, 19, v___x_5330_);
            v___x_5351_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1;
            v___x_5352_ =
                l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(
                    v___x_5351_,
                    v_a_5344_,
                    v___f_5350_,
                    v___y_5332_,
                    v___y_5333_,
                    v___y_5334_,
                    v___y_5335_,
                );
            return v___x_5352_;
        } else {
            crate::leanh::lean_dec(v_a_5344_);
            crate::leanh::lean_dec_ref(v___x_5342_);
            crate::leanh::lean_dec_ref(v_alts_5331_);
            crate::leanh::lean_dec(v___x_5330_);
            crate::leanh::lean_dec(v_name_5329_);
            crate::leanh::lean_dec(v___x_5328_);
            crate::leanh::lean_dec(v___x_5327_);
            crate::leanh::lean_dec_ref(v_val_5326_);
            crate::leanh::lean_dec(v_numParams_5325_);
            crate::leanh::lean_dec_ref(v___x_5324_);
            crate::leanh::lean_dec_ref(v___x_5320_);
            crate::leanh::lean_dec_ref(v_motive_5319_);
            crate::leanh::lean_dec_ref(v_ism2_5318_);
            crate::leanh::lean_dec_ref(v_ism1_5317_);
            crate::leanh::lean_dec_ref(v_params_5316_);
            crate::leanh::lean_dec(v_tail_5315_);
            crate::leanh::lean_dec(v_indName_5314_);
            return v___x_5345_;
        }
    } else {
        crate::leanh::lean_dec_ref(v___x_5342_);
        crate::leanh::lean_dec_ref(v___x_5340_);
        crate::leanh::lean_dec_ref(v_alts_5331_);
        crate::leanh::lean_dec(v___x_5330_);
        crate::leanh::lean_dec(v_name_5329_);
        crate::leanh::lean_dec(v___x_5328_);
        crate::leanh::lean_dec(v___x_5327_);
        crate::leanh::lean_dec_ref(v_val_5326_);
        crate::leanh::lean_dec(v_numParams_5325_);
        crate::leanh::lean_dec_ref(v___x_5324_);
        crate::leanh::lean_dec_ref(v___x_5320_);
        crate::leanh::lean_dec_ref(v_motive_5319_);
        crate::leanh::lean_dec_ref(v_ism2_5318_);
        crate::leanh::lean_dec_ref(v_ism1_5317_);
        crate::leanh::lean_dec_ref(v_params_5316_);
        crate::leanh::lean_dec(v_tail_5315_);
        crate::leanh::lean_dec(v_indName_5314_);
        return v___x_5343_;
    }
}
pub unsafe fn l_Lean_mkCasesOnSameCtorHet___lam__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_indName_5353_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_tail_5354_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_params_5355_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_ism1_5356_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_ism2_5357_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_motive_5358_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_5359_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_5360_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_5361_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_5362_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_5363_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_numParams_5364_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_val_5365_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___x_5366_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___x_5367_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_name_5368_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___x_5369_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_alts_5370_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_5371_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_5372_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_5373_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___y_5374_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v___y_5375_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v___x_21301__boxed_5376_: u8 = 0;
    let mut v___x_21302__boxed_5377_: u8 = 0;
    let mut v___x_21303__boxed_5378_: u8 = 0;
    let mut v_res_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_21301__boxed_5376_ = (crate::leanh::lean_unbox(v___x_5360_) as u8);
    v___x_21302__boxed_5377_ = (crate::leanh::lean_unbox(v___x_5361_) as u8);
    v___x_21303__boxed_5378_ = (crate::leanh::lean_unbox(v___x_5362_) as u8);
    v_res_5379_ = l_Lean_mkCasesOnSameCtorHet___lam__1(
        v_indName_5353_,
        v_tail_5354_,
        v_params_5355_,
        v_ism1_5356_,
        v_ism2_5357_,
        v_motive_5358_,
        v___x_5359_,
        v___x_21301__boxed_5376_,
        v___x_21302__boxed_5377_,
        v___x_21303__boxed_5378_,
        v___x_5363_,
        v_numParams_5364_,
        v_val_5365_,
        v___x_5366_,
        v___x_5367_,
        v_name_5368_,
        v___x_5369_,
        v_alts_5370_,
        v___y_5371_,
        v___y_5372_,
        v___y_5373_,
        v___y_5374_,
    );
    crate::leanh::lean_dec(v___y_5374_);
    crate::leanh::lean_dec_ref(v___y_5373_);
    crate::leanh::lean_dec(v___y_5372_);
    crate::leanh::lean_dec_ref(v___y_5371_);
    return v_res_5379_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(
    mut v_snd_5380_: *mut crate::leanh::LeanObject,
    mut v_x_5381_: *mut crate::leanh::LeanObject,
    mut v___y_5382_: *mut crate::leanh::LeanObject,
    mut v___y_5383_: *mut crate::leanh::LeanObject,
    mut v___y_5384_: *mut crate::leanh::LeanObject,
    mut v___y_5385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5387_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_5387_, 0, v_snd_5380_);
    return v___x_5387_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed(
    mut v_snd_5388_: *mut crate::leanh::LeanObject,
    mut v_x_5389_: *mut crate::leanh::LeanObject,
    mut v___y_5390_: *mut crate::leanh::LeanObject,
    mut v___y_5391_: *mut crate::leanh::LeanObject,
    mut v___y_5392_: *mut crate::leanh::LeanObject,
    mut v___y_5393_: *mut crate::leanh::LeanObject,
    mut v___y_5394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5395_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0(v_snd_5388_, v_x_5389_, v___y_5390_, v___y_5391_, v___y_5392_, v___y_5393_);
    crate::leanh::lean_dec(v___y_5393_);
    crate::leanh::lean_dec_ref(v___y_5392_);
    crate::leanh::lean_dec(v___y_5391_);
    crate::leanh::lean_dec_ref(v___y_5390_);
    crate::leanh::lean_dec_ref(v_x_5389_);
    return v_res_5395_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(
    mut v_sz_5396_: usize,
    mut v_i_5397_: usize,
    mut v_bs_5398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5399_: u8 = 0;
    let mut v_v_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5405_: u8 = 0;
    let mut v___x_5406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: usize = 0;
    let mut v___x_5412_: usize = 0;
    let mut v___x_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5416_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5399_ = lean_usize_dec_lt(v_i_5397_, v_sz_5396_);
                if v___x_5399_ == 0 {
                    return v_bs_5398_;
                } else {
                    v_v_5400_ = lean_array_uget(v_bs_5398_, v_i_5397_);
                    v_fst_5401_ = crate::leanh::lean_ctor_get(v_v_5400_, 0);
                    v_snd_5402_ = crate::leanh::lean_ctor_get(v_v_5400_, 1);
                    v_isSharedCheck_5416_ = (!crate::leanh::lean_is_exclusive(v_v_5400_)) as u8;
                    if v_isSharedCheck_5416_ == 0 {
                        v___x_5404_ = v_v_5400_;
                        v_isShared_5405_ = v_isSharedCheck_5416_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5402_);
                        crate::leanh::lean_inc(v_fst_5401_);
                        crate::leanh::lean_dec(v_v_5400_);
                        v___x_5404_ = crate::leanh::lean_box(0);
                        v_isShared_5405_ = v_isSharedCheck_5416_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5406_ = crate::leanh::lean_unsigned_to_nat(0);
                v_bs_x27_5407_ = lean_array_uset(v_bs_5398_, v_i_5397_, v___x_5406_);
                v___f_5408_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                crate::leanh::lean_closure_set(v___f_5408_, 0, v_snd_5402_);
                if v_isShared_5405_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5404_, 1, v___f_5408_);
                    v___x_5410_ = v___x_5404_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5415_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5415_, 0, v_fst_5401_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5415_, 1, v___f_5408_);
                    v___x_5410_ = v_reuseFailAlloc_5415_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5411_ = 1usize;
                v___x_5412_ = lean_usize_add(v_i_5397_, v___x_5411_);
                v___x_5413_ = lean_array_uset(v_bs_x27_5407_, v_i_5397_, v___x_5410_);
                v_i_5397_ = v___x_5412_;
                v_bs_5398_ = v___x_5413_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8___boxed(
    mut v_sz_5417_: *mut crate::leanh::LeanObject,
    mut v_i_5418_: *mut crate::leanh::LeanObject,
    mut v_bs_5419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5420_: usize = 0;
    let mut v_i_boxed_5421_: usize = 0;
    let mut v_res_5422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5420_ = crate::leanh::lean_unbox_usize(v_sz_5417_);
    crate::leanh::lean_dec(v_sz_5417_);
    v_i_boxed_5421_ = crate::leanh::lean_unbox_usize(v_i_5418_);
    crate::leanh::lean_dec(v_i_5418_);
    v_res_5422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_boxed_5420_, v_i_boxed_5421_, v_bs_5419_);
    return v_res_5422_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(
    mut v___x_5423_: *mut crate::leanh::LeanObject,
    mut v_a_5424_: *mut crate::leanh::LeanObject,
    mut v___y_5425_: *mut crate::leanh::LeanObject,
    mut v___y_5426_: *mut crate::leanh::LeanObject,
    mut v___y_5427_: *mut crate::leanh::LeanObject,
    mut v___y_5428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_20204__overap_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5430_ = l_Lean_instInhabitedExpr;
    v___x_20204__overap_5431_ = l_instInhabitedOfMonad___redArg(v___x_5423_, v___x_5430_);
    crate::leanh::lean_inc(v___y_5428_);
    crate::leanh::lean_inc_ref(v___y_5427_);
    crate::leanh::lean_inc(v___y_5426_);
    crate::leanh::lean_inc_ref(v___y_5425_);
    v___x_5432_ = crate::leanh::lean_apply_5(
        v___x_20204__overap_5431_,
        v___y_5425_,
        v___y_5426_,
        v___y_5427_,
        v___y_5428_,
        crate::leanh::lean_box(0),
    );
    return v___x_5432_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed(
    mut v___x_5433_: *mut crate::leanh::LeanObject,
    mut v_a_5434_: *mut crate::leanh::LeanObject,
    mut v___y_5435_: *mut crate::leanh::LeanObject,
    mut v___y_5436_: *mut crate::leanh::LeanObject,
    mut v___y_5437_: *mut crate::leanh::LeanObject,
    mut v___y_5438_: *mut crate::leanh::LeanObject,
    mut v___y_5439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5440_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0(v___x_5433_, v_a_5434_, v___y_5435_, v___y_5436_, v___y_5437_, v___y_5438_);
    crate::leanh::lean_dec(v___y_5438_);
    crate::leanh::lean_dec_ref(v___y_5437_);
    crate::leanh::lean_dec(v___y_5436_);
    crate::leanh::lean_dec_ref(v___y_5435_);
    crate::leanh::lean_dec_ref(v_a_5434_);
    return v_res_5440_;
}
pub unsafe fn _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5441_ = l_instMonadEIO(crate::leanh::lean_box(0));
    return v___x_5441_;
}
pub unsafe fn _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5442_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0_once), _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__0);
    v___x_5443_ = l_StateRefT_x27_instMonad___redArg(v___x_5442_);
    return v___x_5443_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1___boxed(
    mut v_acc_5448_: *mut crate::leanh::LeanObject,
    mut v_declInfos_5449_: *mut crate::leanh::LeanObject,
    mut v_k_5450_: *mut crate::leanh::LeanObject,
    mut v_kind_5451_: *mut crate::leanh::LeanObject,
    mut v_x_5452_: *mut crate::leanh::LeanObject,
    mut v___y_5453_: *mut crate::leanh::LeanObject,
    mut v___y_5454_: *mut crate::leanh::LeanObject,
    mut v___y_5455_: *mut crate::leanh::LeanObject,
    mut v___y_5456_: *mut crate::leanh::LeanObject,
    mut v___y_5457_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_5458_: u8 = 0;
    let mut v_res_5459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_5458_ = (crate::leanh::lean_unbox(v_kind_5451_) as u8);
    v_res_5459_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1(v_acc_5448_, v_declInfos_5449_, v_k_5450_, v_kind_boxed_5458_, v_x_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_);
    crate::leanh::lean_dec(v___y_5456_);
    crate::leanh::lean_dec_ref(v___y_5455_);
    crate::leanh::lean_dec(v___y_5454_);
    crate::leanh::lean_dec_ref(v___y_5453_);
    return v_res_5459_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(
    mut v_declInfos_5460_: *mut crate::leanh::LeanObject,
    mut v_k_5461_: *mut crate::leanh::LeanObject,
    mut v_kind_5462_: u8,
    mut v_acc_5463_: *mut crate::leanh::LeanObject,
    mut v___y_5464_: *mut crate::leanh::LeanObject,
    mut v___y_5465_: *mut crate::leanh::LeanObject,
    mut v___y_5466_: *mut crate::leanh::LeanObject,
    mut v___y_5467_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_5486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5489_: u8 = 0;
    let mut v_toFunctor_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5496_: u8 = 0;
    let mut v___f_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: u8 = 0;
    let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: u8 = 0;
    let mut v___f_5516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5529_: u8 = 0;
    let mut v___x_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5533_: u8 = 0;
    let mut v_unused_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5535_: u8 = 0;
    let mut v_unused_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5469_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once), _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
                v_toApplicative_5470_ = crate::leanh::lean_ctor_get(v___x_5469_, 0);
                v_toFunctor_5471_ = crate::leanh::lean_ctor_get(v_toApplicative_5470_, 0);
                v_toSeq_5472_ = crate::leanh::lean_ctor_get(v_toApplicative_5470_, 2);
                v_toSeqLeft_5473_ = crate::leanh::lean_ctor_get(v_toApplicative_5470_, 3);
                v_toSeqRight_5474_ = crate::leanh::lean_ctor_get(v_toApplicative_5470_, 4);
                v___f_5475_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2;
                v___f_5476_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_5471_, 2);
                v___f_5477_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5477_, 0, v_toFunctor_5471_);
                v___f_5478_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5478_, 0, v_toFunctor_5471_);
                v___x_5479_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5479_, 0, v___f_5477_);
                crate::leanh::lean_ctor_set(v___x_5479_, 1, v___f_5478_);
                crate::leanh::lean_inc(v_toSeqRight_5474_);
                v___f_5480_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5480_, 0, v_toSeqRight_5474_);
                crate::leanh::lean_inc(v_toSeqLeft_5473_);
                v___f_5481_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5481_, 0, v_toSeqLeft_5473_);
                crate::leanh::lean_inc(v_toSeq_5472_);
                v___f_5482_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5482_, 0, v_toSeq_5472_);
                v___x_5483_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5483_, 0, v___x_5479_);
                crate::leanh::lean_ctor_set(v___x_5483_, 1, v___f_5475_);
                crate::leanh::lean_ctor_set(v___x_5483_, 2, v___f_5482_);
                crate::leanh::lean_ctor_set(v___x_5483_, 3, v___f_5481_);
                crate::leanh::lean_ctor_set(v___x_5483_, 4, v___f_5480_);
                v___x_5484_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5484_, 0, v___x_5483_);
                crate::leanh::lean_ctor_set(v___x_5484_, 1, v___f_5476_);
                v___x_5485_ = l_StateRefT_x27_instMonad___redArg(v___x_5484_);
                v_toApplicative_5486_ = crate::leanh::lean_ctor_get(v___x_5485_, 0);
                v_isSharedCheck_5535_ = (!crate::leanh::lean_is_exclusive(v___x_5485_)) as u8;
                if v_isSharedCheck_5535_ == 0 {
                    v_unused_5536_ = crate::leanh::lean_ctor_get(v___x_5485_, 1);
                    crate::leanh::lean_dec(v_unused_5536_);
                    v___x_5488_ = v___x_5485_;
                    v_isShared_5489_ = v_isSharedCheck_5535_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_5486_);
                    crate::leanh::lean_dec(v___x_5485_);
                    v___x_5488_ = crate::leanh::lean_box(0);
                    v_isShared_5489_ = v_isSharedCheck_5535_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_5490_ = crate::leanh::lean_ctor_get(v_toApplicative_5486_, 0);
                v_toSeq_5491_ = crate::leanh::lean_ctor_get(v_toApplicative_5486_, 2);
                v_toSeqLeft_5492_ = crate::leanh::lean_ctor_get(v_toApplicative_5486_, 3);
                v_toSeqRight_5493_ = crate::leanh::lean_ctor_get(v_toApplicative_5486_, 4);
                v_isSharedCheck_5533_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_5486_)) as u8;
                if v_isSharedCheck_5533_ == 0 {
                    v_unused_5534_ = crate::leanh::lean_ctor_get(v_toApplicative_5486_, 1);
                    crate::leanh::lean_dec(v_unused_5534_);
                    v___x_5495_ = v_toApplicative_5486_;
                    v_isShared_5496_ = v_isSharedCheck_5533_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_5493_);
                    crate::leanh::lean_inc(v_toSeqLeft_5492_);
                    crate::leanh::lean_inc(v_toSeq_5491_);
                    crate::leanh::lean_inc(v_toFunctor_5490_);
                    crate::leanh::lean_dec(v_toApplicative_5486_);
                    v___x_5495_ = crate::leanh::lean_box(0);
                    v_isShared_5496_ = v_isSharedCheck_5533_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_5497_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4;
                v___f_5498_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_5490_);
                v___f_5499_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5499_, 0, v_toFunctor_5490_);
                v___f_5500_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5500_, 0, v_toFunctor_5490_);
                v___x_5501_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5501_, 0, v___f_5499_);
                crate::leanh::lean_ctor_set(v___x_5501_, 1, v___f_5500_);
                v___f_5502_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5502_, 0, v_toSeqRight_5493_);
                v___f_5503_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5503_, 0, v_toSeqLeft_5492_);
                v___f_5504_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_5504_, 0, v_toSeq_5491_);
                if v_isShared_5496_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5495_, 4, v___f_5502_);
                    crate::leanh::lean_ctor_set(v___x_5495_, 3, v___f_5503_);
                    crate::leanh::lean_ctor_set(v___x_5495_, 2, v___f_5504_);
                    crate::leanh::lean_ctor_set(v___x_5495_, 1, v___f_5497_);
                    crate::leanh::lean_ctor_set(v___x_5495_, 0, v___x_5501_);
                    v___x_5506_ = v___x_5495_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5532_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5532_, 0, v___x_5501_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5532_, 1, v___f_5497_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5532_, 2, v___f_5504_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5532_, 3, v___f_5503_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5532_, 4, v___f_5502_);
                    v___x_5506_ = v_reuseFailAlloc_5532_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_5489_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5488_, 1, v___f_5498_);
                    crate::leanh::lean_ctor_set(v___x_5488_, 0, v___x_5506_);
                    v___x_5508_ = v___x_5488_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5531_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5531_, 0, v___x_5506_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5531_, 1, v___f_5498_);
                    v___x_5508_ = v_reuseFailAlloc_5531_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5509_ = lean_array_get_size(v_acc_5463_);
                v___x_5510_ = lean_array_get_size(v_declInfos_5460_);
                v___x_5511_ = lean_nat_dec_lt(v___x_5509_, v___x_5510_);
                if v___x_5511_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_5508_);
                    crate::leanh::lean_dec_ref(v_declInfos_5460_);
                    crate::leanh::lean_inc(v___y_5467_);
                    crate::leanh::lean_inc_ref(v___y_5466_);
                    crate::leanh::lean_inc(v___y_5465_);
                    crate::leanh::lean_inc_ref(v___y_5464_);
                    v___x_5512_ = crate::leanh::lean_apply_6(
                        v_k_5461_,
                        v_acc_5463_,
                        v___y_5464_,
                        v___y_5465_,
                        v___y_5466_,
                        v___y_5467_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_5512_;
                } else {
                    v___f_5513_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                    crate::leanh::lean_closure_set(v___f_5513_, 0, v___x_5508_);
                    v___x_5514_ = crate::leanh::lean_box(0);
                    v___x_5515_ = 0;
                    v___f_5516_ = crate::leanh::lean_alloc_closure(
                        l_Pi_instInhabited___redArg___lam__0 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_5516_, 0, v___f_5513_);
                    v___x_5517_ = crate::leanh::lean_box((v___x_5515_) as usize);
                    v___x_5518_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5518_, 0, v___x_5517_);
                    crate::leanh::lean_ctor_set(v___x_5518_, 1, v___f_5516_);
                    v___x_5519_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5519_, 0, v___x_5514_);
                    crate::leanh::lean_ctor_set(v___x_5519_, 1, v___x_5518_);
                    v___x_5520_ = lean_array_get(v___x_5519_, v_declInfos_5460_, v___x_5509_);
                    crate::leanh::lean_dec_ref_known(v___x_5519_, 2);
                    v_snd_5521_ = crate::leanh::lean_ctor_get(v___x_5520_, 1);
                    crate::leanh::lean_inc(v_snd_5521_);
                    v_fst_5522_ = crate::leanh::lean_ctor_get(v___x_5520_, 0);
                    crate::leanh::lean_inc(v_fst_5522_);
                    crate::leanh::lean_dec(v___x_5520_);
                    v_fst_5523_ = crate::leanh::lean_ctor_get(v_snd_5521_, 0);
                    crate::leanh::lean_inc(v_fst_5523_);
                    v_snd_5524_ = crate::leanh::lean_ctor_get(v_snd_5521_, 1);
                    crate::leanh::lean_inc(v_snd_5524_);
                    crate::leanh::lean_dec(v_snd_5521_);
                    crate::leanh::lean_inc(v___y_5467_);
                    crate::leanh::lean_inc_ref(v___y_5466_);
                    crate::leanh::lean_inc(v___y_5465_);
                    crate::leanh::lean_inc_ref(v___y_5464_);
                    crate::leanh::lean_inc_ref(v_acc_5463_);
                    v___x_5525_ = crate::leanh::lean_apply_6(
                        v_snd_5524_,
                        v_acc_5463_,
                        v___y_5464_,
                        v___y_5465_,
                        v___y_5466_,
                        v___y_5467_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_5525_) == 0 {
                        v_a_5526_ = crate::leanh::lean_ctor_get(v___x_5525_, 0);
                        crate::leanh::lean_inc(v_a_5526_);
                        crate::leanh::lean_dec_ref_known(v___x_5525_, 1);
                        v___x_5527_ = crate::leanh::lean_box((v_kind_5462_) as usize);
                        v___f_5528_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1___boxed as *mut core::ffi::c_void, 10, 4);
                        crate::leanh::lean_closure_set(v___f_5528_, 0, v_acc_5463_);
                        crate::leanh::lean_closure_set(v___f_5528_, 1, v_declInfos_5460_);
                        crate::leanh::lean_closure_set(v___f_5528_, 2, v_k_5461_);
                        crate::leanh::lean_closure_set(v___f_5528_, 3, v___x_5527_);
                        v___x_5529_ = (crate::leanh::lean_unbox(v_fst_5523_) as u8);
                        crate::leanh::lean_dec(v_fst_5523_);
                        v___x_5530_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_5522_, v___x_5529_, v_a_5526_, v___f_5528_, v_kind_5462_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_);
                        return v___x_5530_;
                    } else {
                        crate::leanh::lean_dec(v_fst_5523_);
                        crate::leanh::lean_dec(v_fst_5522_);
                        crate::leanh::lean_dec_ref(v_acc_5463_);
                        crate::leanh::lean_dec_ref(v_k_5461_);
                        crate::leanh::lean_dec_ref(v_declInfos_5460_);
                        return v___x_5525_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__1(
    mut v_acc_5537_: *mut crate::leanh::LeanObject,
    mut v_declInfos_5538_: *mut crate::leanh::LeanObject,
    mut v_k_5539_: *mut crate::leanh::LeanObject,
    mut v_kind_5540_: u8,
    mut v_x_5541_: *mut crate::leanh::LeanObject,
    mut v___y_5542_: *mut crate::leanh::LeanObject,
    mut v___y_5543_: *mut crate::leanh::LeanObject,
    mut v___y_5544_: *mut crate::leanh::LeanObject,
    mut v___y_5545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5547_ = lean_array_push(v_acc_5537_, v_x_5541_);
    v___x_5548_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_5538_, v_k_5539_, v_kind_5540_, v___x_5547_, v___y_5542_, v___y_5543_, v___y_5544_, v___y_5545_);
    return v___x_5548_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___boxed(
    mut v_declInfos_5549_: *mut crate::leanh::LeanObject,
    mut v_k_5550_: *mut crate::leanh::LeanObject,
    mut v_kind_5551_: *mut crate::leanh::LeanObject,
    mut v_acc_5552_: *mut crate::leanh::LeanObject,
    mut v___y_5553_: *mut crate::leanh::LeanObject,
    mut v___y_5554_: *mut crate::leanh::LeanObject,
    mut v___y_5555_: *mut crate::leanh::LeanObject,
    mut v___y_5556_: *mut crate::leanh::LeanObject,
    mut v___y_5557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_5558_: u8 = 0;
    let mut v_res_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_5558_ = (crate::leanh::lean_unbox(v_kind_5551_) as u8);
    v_res_5559_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_5549_, v_k_5550_, v_kind_boxed_5558_, v_acc_5552_, v___y_5553_, v___y_5554_, v___y_5555_, v___y_5556_);
    crate::leanh::lean_dec(v___y_5556_);
    crate::leanh::lean_dec_ref(v___y_5555_);
    crate::leanh::lean_dec(v___y_5554_);
    crate::leanh::lean_dec_ref(v___y_5553_);
    return v_res_5559_;
}
pub unsafe fn l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(
    mut v_declInfos_5562_: *mut crate::leanh::LeanObject,
    mut v_k_5563_: *mut crate::leanh::LeanObject,
    mut v_kind_5564_: u8,
    mut v___y_5565_: *mut crate::leanh::LeanObject,
    mut v___y_5566_: *mut crate::leanh::LeanObject,
    mut v___y_5567_: *mut crate::leanh::LeanObject,
    mut v___y_5568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5570_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0;
    v___x_5571_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22(v_declInfos_5562_, v_k_5563_, v_kind_5564_, v___x_5570_, v___y_5565_, v___y_5566_, v___y_5567_, v___y_5568_);
    return v___x_5571_;
}
pub unsafe fn l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___boxed(
    mut v_declInfos_5572_: *mut crate::leanh::LeanObject,
    mut v_k_5573_: *mut crate::leanh::LeanObject,
    mut v_kind_5574_: *mut crate::leanh::LeanObject,
    mut v___y_5575_: *mut crate::leanh::LeanObject,
    mut v___y_5576_: *mut crate::leanh::LeanObject,
    mut v___y_5577_: *mut crate::leanh::LeanObject,
    mut v___y_5578_: *mut crate::leanh::LeanObject,
    mut v___y_5579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_5580_: u8 = 0;
    let mut v_res_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_5580_ = (crate::leanh::lean_unbox(v_kind_5574_) as u8);
    v_res_5581_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(v_declInfos_5572_, v_k_5573_, v_kind_boxed_5580_, v___y_5575_, v___y_5576_, v___y_5577_, v___y_5578_);
    crate::leanh::lean_dec(v___y_5578_);
    crate::leanh::lean_dec_ref(v___y_5577_);
    crate::leanh::lean_dec(v___y_5576_);
    crate::leanh::lean_dec_ref(v___y_5575_);
    return v_res_5581_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(
    mut v_sz_5582_: usize,
    mut v_i_5583_: usize,
    mut v_bs_5584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5585_: u8 = 0;
    let mut v_v_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5591_: u8 = 0;
    let mut v___x_5592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5594_: u8 = 0;
    let mut v___x_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5599_: usize = 0;
    let mut v___x_5600_: usize = 0;
    let mut v___x_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5604_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5585_ = lean_usize_dec_lt(v_i_5583_, v_sz_5582_);
                if v___x_5585_ == 0 {
                    return v_bs_5584_;
                } else {
                    v_v_5586_ = lean_array_uget(v_bs_5584_, v_i_5583_);
                    v_fst_5587_ = crate::leanh::lean_ctor_get(v_v_5586_, 0);
                    v_snd_5588_ = crate::leanh::lean_ctor_get(v_v_5586_, 1);
                    v_isSharedCheck_5604_ = (!crate::leanh::lean_is_exclusive(v_v_5586_)) as u8;
                    if v_isSharedCheck_5604_ == 0 {
                        v___x_5590_ = v_v_5586_;
                        v_isShared_5591_ = v_isSharedCheck_5604_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5588_);
                        crate::leanh::lean_inc(v_fst_5587_);
                        crate::leanh::lean_dec(v_v_5586_);
                        v___x_5590_ = crate::leanh::lean_box(0);
                        v_isShared_5591_ = v_isSharedCheck_5604_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5592_ = crate::leanh::lean_unsigned_to_nat(0);
                v_bs_x27_5593_ = lean_array_uset(v_bs_5584_, v_i_5583_, v___x_5592_);
                v___x_5594_ = 0;
                v___x_5595_ = crate::leanh::lean_box((v___x_5594_) as usize);
                if v_isShared_5591_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5590_, 0, v___x_5595_);
                    v___x_5597_ = v___x_5590_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5603_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5603_, 0, v___x_5595_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5603_, 1, v_snd_5588_);
                    v___x_5597_ = v_reuseFailAlloc_5603_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5598_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5598_, 0, v_fst_5587_);
                crate::leanh::lean_ctor_set(v___x_5598_, 1, v___x_5597_);
                v___x_5599_ = 1usize;
                v___x_5600_ = lean_usize_add(v_i_5583_, v___x_5599_);
                v___x_5601_ = lean_array_uset(v_bs_x27_5593_, v_i_5583_, v___x_5598_);
                v_i_5583_ = v___x_5600_;
                v_bs_5584_ = v___x_5601_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16___boxed(
    mut v_sz_5605_: *mut crate::leanh::LeanObject,
    mut v_i_5606_: *mut crate::leanh::LeanObject,
    mut v_bs_5607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5608_: usize = 0;
    let mut v_i_boxed_5609_: usize = 0;
    let mut v_res_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5608_ = crate::leanh::lean_unbox_usize(v_sz_5605_);
    crate::leanh::lean_dec(v_sz_5605_);
    v_i_boxed_5609_ = crate::leanh::lean_unbox_usize(v_i_5606_);
    crate::leanh::lean_dec(v_i_5606_);
    v_res_5610_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_boxed_5608_, v_i_boxed_5609_, v_bs_5607_);
    return v_res_5610_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(
    mut v_declInfos_5611_: *mut crate::leanh::LeanObject,
    mut v_k_5612_: *mut crate::leanh::LeanObject,
    mut v_kind_5613_: u8,
    mut v___y_5614_: *mut crate::leanh::LeanObject,
    mut v___y_5615_: *mut crate::leanh::LeanObject,
    mut v___y_5616_: *mut crate::leanh::LeanObject,
    mut v___y_5617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_5619_: usize = 0;
    let mut v___x_5620_: usize = 0;
    let mut v___x_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_5619_ = lean_array_size(v_declInfos_5611_);
    v___x_5620_ = 0usize;
    v___x_5621_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_5619_, v___x_5620_, v_declInfos_5611_);
    v___x_5622_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17(v___x_5621_, v_k_5612_, v_kind_5613_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_);
    return v___x_5622_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9___boxed(
    mut v_declInfos_5623_: *mut crate::leanh::LeanObject,
    mut v_k_5624_: *mut crate::leanh::LeanObject,
    mut v_kind_5625_: *mut crate::leanh::LeanObject,
    mut v___y_5626_: *mut crate::leanh::LeanObject,
    mut v___y_5627_: *mut crate::leanh::LeanObject,
    mut v___y_5628_: *mut crate::leanh::LeanObject,
    mut v___y_5629_: *mut crate::leanh::LeanObject,
    mut v___y_5630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_5631_: u8 = 0;
    let mut v_res_5632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_5631_ = (crate::leanh::lean_unbox(v_kind_5625_) as u8);
    v_res_5632_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v_declInfos_5623_, v_k_5624_, v_kind_boxed_5631_, v___y_5626_, v___y_5627_, v___y_5628_, v___y_5629_);
    crate::leanh::lean_dec(v___y_5629_);
    crate::leanh::lean_dec_ref(v___y_5628_);
    crate::leanh::lean_dec(v___y_5627_);
    crate::leanh::lean_dec_ref(v___y_5626_);
    return v_res_5632_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(
    mut v_declInfos_5633_: *mut crate::leanh::LeanObject,
    mut v_k_5634_: *mut crate::leanh::LeanObject,
    mut v_kind_5635_: u8,
    mut v___y_5636_: *mut crate::leanh::LeanObject,
    mut v___y_5637_: *mut crate::leanh::LeanObject,
    mut v___y_5638_: *mut crate::leanh::LeanObject,
    mut v___y_5639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_5641_: usize = 0;
    let mut v___x_5642_: usize = 0;
    let mut v___x_5643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_5641_ = lean_array_size(v_declInfos_5633_);
    v___x_5642_ = 0usize;
    v___x_5643_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_5641_, v___x_5642_, v_declInfos_5633_);
    v___x_5644_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9(v___x_5643_, v_k_5634_, v_kind_5635_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_);
    return v___x_5644_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7___boxed(
    mut v_declInfos_5645_: *mut crate::leanh::LeanObject,
    mut v_k_5646_: *mut crate::leanh::LeanObject,
    mut v_kind_5647_: *mut crate::leanh::LeanObject,
    mut v___y_5648_: *mut crate::leanh::LeanObject,
    mut v___y_5649_: *mut crate::leanh::LeanObject,
    mut v___y_5650_: *mut crate::leanh::LeanObject,
    mut v___y_5651_: *mut crate::leanh::LeanObject,
    mut v___y_5652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_5653_: u8 = 0;
    let mut v_res_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_5653_ = (crate::leanh::lean_unbox(v_kind_5647_) as u8);
    v_res_5654_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(
        v_declInfos_5645_,
        v_k_5646_,
        v_kind_boxed_5653_,
        v___y_5648_,
        v___y_5649_,
        v___y_5650_,
        v___y_5651_,
    );
    crate::leanh::lean_dec(v___y_5651_);
    crate::leanh::lean_dec_ref(v___y_5650_);
    crate::leanh::lean_dec(v___y_5649_);
    crate::leanh::lean_dec_ref(v___y_5648_);
    return v_res_5654_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(
    mut v___x_5656_: *mut crate::leanh::LeanObject,
    mut v_dummy_5657_: *mut crate::leanh::LeanObject,
    mut v___x_5658_: *mut crate::leanh::LeanObject,
    mut v___x_5659_: *mut crate::leanh::LeanObject,
    mut v___x_5660_: *mut crate::leanh::LeanObject,
    mut v_motive_5661_: *mut crate::leanh::LeanObject,
    mut v_zs1_5662_: *mut crate::leanh::LeanObject,
    mut v_isZero_5663_: u8,
    mut v___x_5664_: u8,
    mut v___x_5665_: u8,
    mut v___x_5666_: *mut crate::leanh::LeanObject,
    mut v_j_5667_: *mut crate::leanh::LeanObject,
    mut v_zs2_5668_: *mut crate::leanh::LeanObject,
    mut v_ctorRet2_5669_: *mut crate::leanh::LeanObject,
    mut v___y_5670_: *mut crate::leanh::LeanObject,
    mut v___y_5671_: *mut crate::leanh::LeanObject,
    mut v___y_5672_: *mut crate::leanh::LeanObject,
    mut v___y_5673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5693_: u8 = 0;
    let mut v___y_5695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5709_: u8 = 0;
    let mut v_a_5710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5713_: u8 = 0;
    let mut v___x_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5717_: u8 = 0;
    let mut v_a_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5721_: u8 = 0;
    let mut v___x_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5725_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_5673_);
                crate::leanh::lean_inc_ref(v___y_5672_);
                crate::leanh::lean_inc(v___y_5671_);
                crate::leanh::lean_inc_ref(v___y_5670_);
                v___x_5675_ = lean_whnf(
                    v_ctorRet2_5669_,
                    v___y_5670_,
                    v___y_5671_,
                    v___y_5672_,
                    v___y_5673_,
                );
                if crate::leanh::lean_obj_tag(v___x_5675_) == 0 {
                    v_a_5676_ = crate::leanh::lean_ctor_get(v___x_5675_, 0);
                    crate::leanh::lean_inc(v_a_5676_);
                    crate::leanh::lean_dec_ref_known(v___x_5675_, 1);
                    v___x_5677_ = l_Lean_mkAppN(v___x_5656_, v_zs2_5668_);
                    v_nargs_5678_ = l_Lean_Expr_getAppNumArgs(v_a_5676_);
                    crate::leanh::lean_inc(v_nargs_5678_);
                    v___x_5679_ = lean_mk_array(v_nargs_5678_, v_dummy_5657_);
                    v___x_5680_ = lean_nat_sub(v_nargs_5678_, v___x_5658_);
                    crate::leanh::lean_dec(v_nargs_5678_);
                    v___x_5681_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_a_5676_,
                        v___x_5679_,
                        v___x_5680_,
                    );
                    v___x_5682_ = lean_array_get_size(v___x_5681_);
                    v___x_5683_ =
                        l_Array_toSubarray___redArg(v___x_5681_, v___x_5659_, v___x_5682_);
                    v___x_5684_ = l_Subarray_copy___redArg(v___x_5683_);
                    v___x_5685_ = lean_array_push(v___x_5684_, v___x_5677_);
                    v___x_5686_ = l_Array_append___redArg(v___x_5660_, v___x_5685_);
                    crate::leanh::lean_dec_ref(v___x_5685_);
                    v___x_5687_ = l_Lean_mkAppN(v_motive_5661_, v___x_5686_);
                    crate::leanh::lean_dec_ref(v___x_5686_);
                    v___x_5688_ = l_Array_append___redArg(v_zs1_5662_, v_zs2_5668_);
                    v___x_5689_ = l_Lean_Meta_mkForallFVars(
                        v___x_5688_,
                        v___x_5687_,
                        v_isZero_5663_,
                        v___x_5664_,
                        v___x_5664_,
                        v___x_5665_,
                        v___y_5670_,
                        v___y_5671_,
                        v___y_5672_,
                        v___y_5673_,
                    );
                    crate::leanh::lean_dec_ref(v___x_5688_);
                    if crate::leanh::lean_obj_tag(v___x_5689_) == 0 {
                        v_a_5690_ = crate::leanh::lean_ctor_get(v___x_5689_, 0);
                        v_isSharedCheck_5709_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5689_)) as u8;
                        if v_isSharedCheck_5709_ == 0 {
                            v___x_5692_ = v___x_5689_;
                            v_isShared_5693_ = v_isSharedCheck_5709_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5690_);
                            crate::leanh::lean_dec(v___x_5689_);
                            v___x_5692_ = crate::leanh::lean_box(0);
                            v_isShared_5693_ = v_isSharedCheck_5709_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_5666_);
                        v_a_5710_ = crate::leanh::lean_ctor_get(v___x_5689_, 0);
                        v_isSharedCheck_5717_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5689_)) as u8;
                        if v_isSharedCheck_5717_ == 0 {
                            v___x_5712_ = v___x_5689_;
                            v_isShared_5713_ = v_isSharedCheck_5717_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5710_);
                            crate::leanh::lean_dec(v___x_5689_);
                            v___x_5712_ = crate::leanh::lean_box(0);
                            v_isShared_5713_ = v_isSharedCheck_5717_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5666_);
                    crate::leanh::lean_dec_ref(v_zs1_5662_);
                    crate::leanh::lean_dec_ref(v_motive_5661_);
                    crate::leanh::lean_dec_ref(v___x_5660_);
                    crate::leanh::lean_dec(v___x_5659_);
                    crate::leanh::lean_dec_ref(v_dummy_5657_);
                    crate::leanh::lean_dec_ref(v___x_5656_);
                    v_a_5718_ = crate::leanh::lean_ctor_get(v___x_5675_, 0);
                    v_isSharedCheck_5725_ = (!crate::leanh::lean_is_exclusive(v___x_5675_)) as u8;
                    if v_isSharedCheck_5725_ == 0 {
                        v___x_5720_ = v___x_5675_;
                        v_isShared_5721_ = v_isSharedCheck_5725_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5718_);
                        crate::leanh::lean_dec(v___x_5675_);
                        v___x_5720_ = crate::leanh::lean_box(0);
                        v_isShared_5721_ = v_isSharedCheck_5725_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___x_5666_) == 1 {
                    v_str_5700_ = crate::leanh::lean_ctor_get(v___x_5666_, 1);
                    crate::leanh::lean_inc_ref(v_str_5700_);
                    crate::leanh::lean_dec_ref_known(v___x_5666_, 2);
                    v___x_5701_ = crate::leanh::lean_box(0);
                    v___x_5702_ = l_Lean_Name_str___override(v___x_5701_, v_str_5700_);
                    v___y_5695_ = v___x_5702_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_5666_);
                    v___x_5703_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0;
                    v___x_5704_ = lean_nat_add(v_j_5667_, v___x_5658_);
                    v___x_5705_ = l_Nat_reprFast(v___x_5704_);
                    v___x_5706_ = lean_string_append(v___x_5703_, v___x_5705_);
                    crate::leanh::lean_dec_ref(v___x_5705_);
                    v___x_5707_ = crate::leanh::lean_box(0);
                    v___x_5708_ = l_Lean_Name_str___override(v___x_5707_, v___x_5706_);
                    v___y_5695_ = v___x_5708_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5696_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5696_, 0, v___y_5695_);
                crate::leanh::lean_ctor_set(v___x_5696_, 1, v_a_5690_);
                if v_isShared_5693_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5692_, 0, v___x_5696_);
                    v___x_5698_ = v___x_5692_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5699_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5699_, 0, v___x_5696_);
                    v___x_5698_ = v_reuseFailAlloc_5699_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5698_;
            }
            4 => {
                if v_isShared_5713_ == 0 {
                    v___x_5715_ = v___x_5712_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5716_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5716_, 0, v_a_5710_);
                    v___x_5715_ = v_reuseFailAlloc_5716_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5715_;
            }
            6 => {
                if v_isShared_5721_ == 0 {
                    v___x_5723_ = v___x_5720_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5724_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5724_, 0, v_a_5718_);
                    v___x_5723_ = v_reuseFailAlloc_5724_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5723_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5726_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_dummy_5727_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_5728_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_5729_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_5730_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_motive_5731_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_zs1_5732_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_isZero_5733_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_5734_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_5735_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_5736_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_j_5737_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_zs2_5738_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_ctorRet2_5739_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5740_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5741_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5742_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_5743_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_5744_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_isZero_boxed_5745_: u8 = 0;
    let mut v___x_21737__boxed_5746_: u8 = 0;
    let mut v___x_21738__boxed_5747_: u8 = 0;
    let mut v_res_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isZero_boxed_5745_ = (crate::leanh::lean_unbox(v_isZero_5733_) as u8);
    v___x_21737__boxed_5746_ = (crate::leanh::lean_unbox(v___x_5734_) as u8);
    v___x_21738__boxed_5747_ = (crate::leanh::lean_unbox(v___x_5735_) as u8);
    v_res_5748_ =
        l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0(
            v___x_5726_,
            v_dummy_5727_,
            v___x_5728_,
            v___x_5729_,
            v___x_5730_,
            v_motive_5731_,
            v_zs1_5732_,
            v_isZero_boxed_5745_,
            v___x_21737__boxed_5746_,
            v___x_21738__boxed_5747_,
            v___x_5736_,
            v_j_5737_,
            v_zs2_5738_,
            v_ctorRet2_5739_,
            v___y_5740_,
            v___y_5741_,
            v___y_5742_,
            v___y_5743_,
        );
    crate::leanh::lean_dec(v___y_5743_);
    crate::leanh::lean_dec_ref(v___y_5742_);
    crate::leanh::lean_dec(v___y_5741_);
    crate::leanh::lean_dec_ref(v___y_5740_);
    crate::leanh::lean_dec_ref(v_zs2_5738_);
    crate::leanh::lean_dec(v_j_5737_);
    crate::leanh::lean_dec(v___x_5728_);
    return v_res_5748_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(
    mut v___x_5749_: *mut crate::leanh::LeanObject,
    mut v___x_5750_: *mut crate::leanh::LeanObject,
    mut v___x_5751_: *mut crate::leanh::LeanObject,
    mut v_motive_5752_: *mut crate::leanh::LeanObject,
    mut v_isZero_5753_: u8,
    mut v___x_5754_: u8,
    mut v___x_5755_: u8,
    mut v___x_5756_: *mut crate::leanh::LeanObject,
    mut v_j_5757_: *mut crate::leanh::LeanObject,
    mut v_a_5758_: *mut crate::leanh::LeanObject,
    mut v_zs1_5759_: *mut crate::leanh::LeanObject,
    mut v_ctorRet1_5760_: *mut crate::leanh::LeanObject,
    mut v___y_5761_: *mut crate::leanh::LeanObject,
    mut v___y_5762_: *mut crate::leanh::LeanObject,
    mut v___y_5763_: *mut crate::leanh::LeanObject,
    mut v___y_5764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5786_: u8 = 0;
    let mut v___x_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5790_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_5764_);
                crate::leanh::lean_inc_ref(v___y_5763_);
                crate::leanh::lean_inc(v___y_5762_);
                crate::leanh::lean_inc_ref(v___y_5761_);
                v___x_5766_ = lean_whnf(
                    v_ctorRet1_5760_,
                    v___y_5761_,
                    v___y_5762_,
                    v___y_5763_,
                    v___y_5764_,
                );
                if crate::leanh::lean_obj_tag(v___x_5766_) == 0 {
                    v_a_5767_ = crate::leanh::lean_ctor_get(v___x_5766_, 0);
                    crate::leanh::lean_inc(v_a_5767_);
                    crate::leanh::lean_dec_ref_known(v___x_5766_, 1);
                    crate::leanh::lean_inc_ref(v___x_5749_);
                    v___x_5768_ = l_Lean_mkAppN(v___x_5749_, v_zs1_5759_);
                    v_dummy_5769_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0_once), _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___lam__2___closed__0);
                    v_nargs_5770_ = l_Lean_Expr_getAppNumArgs(v_a_5767_);
                    crate::leanh::lean_inc(v_nargs_5770_);
                    v___x_5771_ = lean_mk_array(v_nargs_5770_, v_dummy_5769_);
                    v___x_5772_ = lean_nat_sub(v_nargs_5770_, v___x_5750_);
                    crate::leanh::lean_dec(v_nargs_5770_);
                    v___x_5773_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                        v_a_5767_,
                        v___x_5771_,
                        v___x_5772_,
                    );
                    v___x_5774_ = lean_array_get_size(v___x_5773_);
                    crate::leanh::lean_inc(v___x_5751_);
                    v___x_5775_ =
                        l_Array_toSubarray___redArg(v___x_5773_, v___x_5751_, v___x_5774_);
                    v___x_5776_ = l_Subarray_copy___redArg(v___x_5775_);
                    v___x_5777_ = lean_array_push(v___x_5776_, v___x_5768_);
                    v___x_5778_ = crate::leanh::lean_box((v_isZero_5753_) as usize);
                    v___x_5779_ = crate::leanh::lean_box((v___x_5754_) as usize);
                    v___x_5780_ = crate::leanh::lean_box((v___x_5755_) as usize);
                    v___f_5781_ = crate::leanh::lean_alloc_closure(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___boxed as *mut core::ffi::c_void, 19, 12);
                    crate::leanh::lean_closure_set(v___f_5781_, 0, v___x_5749_);
                    crate::leanh::lean_closure_set(v___f_5781_, 1, v_dummy_5769_);
                    crate::leanh::lean_closure_set(v___f_5781_, 2, v___x_5750_);
                    crate::leanh::lean_closure_set(v___f_5781_, 3, v___x_5751_);
                    crate::leanh::lean_closure_set(v___f_5781_, 4, v___x_5777_);
                    crate::leanh::lean_closure_set(v___f_5781_, 5, v_motive_5752_);
                    crate::leanh::lean_closure_set(v___f_5781_, 6, v_zs1_5759_);
                    crate::leanh::lean_closure_set(v___f_5781_, 7, v___x_5778_);
                    crate::leanh::lean_closure_set(v___f_5781_, 8, v___x_5779_);
                    crate::leanh::lean_closure_set(v___f_5781_, 9, v___x_5780_);
                    crate::leanh::lean_closure_set(v___f_5781_, 10, v___x_5756_);
                    crate::leanh::lean_closure_set(v___f_5781_, 11, v_j_5757_);
                    v___x_5782_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_5758_, v___f_5781_, v_isZero_5753_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_);
                    return v___x_5782_;
                } else {
                    crate::leanh::lean_dec_ref(v_zs1_5759_);
                    crate::leanh::lean_dec_ref(v_a_5758_);
                    crate::leanh::lean_dec(v_j_5757_);
                    crate::leanh::lean_dec(v___x_5756_);
                    crate::leanh::lean_dec_ref(v_motive_5752_);
                    crate::leanh::lean_dec(v___x_5751_);
                    crate::leanh::lean_dec(v___x_5750_);
                    crate::leanh::lean_dec_ref(v___x_5749_);
                    v_a_5783_ = crate::leanh::lean_ctor_get(v___x_5766_, 0);
                    v_isSharedCheck_5790_ = (!crate::leanh::lean_is_exclusive(v___x_5766_)) as u8;
                    if v_isSharedCheck_5790_ == 0 {
                        v___x_5785_ = v___x_5766_;
                        v_isShared_5786_ = v_isSharedCheck_5790_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5783_);
                        crate::leanh::lean_dec(v___x_5766_);
                        v___x_5785_ = crate::leanh::lean_box(0);
                        v_isShared_5786_ = v_isSharedCheck_5790_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5786_ == 0 {
                    v___x_5788_ = v___x_5785_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5789_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5789_, 0, v_a_5783_);
                    v___x_5788_ = v_reuseFailAlloc_5789_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5788_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5791_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_5792_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_5793_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_motive_5794_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_isZero_5795_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_5796_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_5797_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_5798_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_j_5799_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_a_5800_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_zs1_5801_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_ctorRet1_5802_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_5803_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_5804_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5805_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5806_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5807_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_isZero_boxed_5808_: u8 = 0;
    let mut v___x_21875__boxed_5809_: u8 = 0;
    let mut v___x_21876__boxed_5810_: u8 = 0;
    let mut v_res_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isZero_boxed_5808_ = (crate::leanh::lean_unbox(v_isZero_5795_) as u8);
    v___x_21875__boxed_5809_ = (crate::leanh::lean_unbox(v___x_5796_) as u8);
    v___x_21876__boxed_5810_ = (crate::leanh::lean_unbox(v___x_5797_) as u8);
    v_res_5811_ =
        l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1(
            v___x_5791_,
            v___x_5792_,
            v___x_5793_,
            v_motive_5794_,
            v_isZero_boxed_5808_,
            v___x_21875__boxed_5809_,
            v___x_21876__boxed_5810_,
            v___x_5798_,
            v_j_5799_,
            v_a_5800_,
            v_zs1_5801_,
            v_ctorRet1_5802_,
            v___y_5803_,
            v___y_5804_,
            v___y_5805_,
            v___y_5806_,
        );
    crate::leanh::lean_dec(v___y_5806_);
    crate::leanh::lean_dec_ref(v___y_5805_);
    crate::leanh::lean_dec(v___y_5804_);
    crate::leanh::lean_dec_ref(v___y_5803_);
    return v_res_5811_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(
    mut v_tail_5812_: *mut crate::leanh::LeanObject,
    mut v_params_5813_: *mut crate::leanh::LeanObject,
    mut v___x_5814_: *mut crate::leanh::LeanObject,
    mut v_motive_5815_: *mut crate::leanh::LeanObject,
    mut v_as_5816_: *mut crate::leanh::LeanObject,
    mut v_i_5817_: *mut crate::leanh::LeanObject,
    mut v_j_5818_: *mut crate::leanh::LeanObject,
    mut v_bs_5819_: *mut crate::leanh::LeanObject,
    mut v___y_5820_: *mut crate::leanh::LeanObject,
    mut v___y_5821_: *mut crate::leanh::LeanObject,
    mut v___y_5822_: *mut crate::leanh::LeanObject,
    mut v___y_5823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5826_: u8 = 0;
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: u8 = 0;
    let mut v___x_5834_: u8 = 0;
    let mut v___x_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5849_: u8 = 0;
    let mut v___x_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5853_: u8 = 0;
    let mut v_a_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5857_: u8 = 0;
    let mut v___x_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5861_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5825_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_5826_ = lean_nat_dec_eq(v_i_5817_, v_zero_5825_);
                if v_isZero_5826_ == 1 {
                    crate::leanh::lean_dec(v_j_5818_);
                    crate::leanh::lean_dec(v_i_5817_);
                    crate::leanh::lean_dec_ref(v_motive_5815_);
                    crate::leanh::lean_dec(v___x_5814_);
                    crate::leanh::lean_dec(v_tail_5812_);
                    v___x_5827_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5827_, 0, v_bs_5819_);
                    return v___x_5827_;
                } else {
                    v___x_5828_ = lean_array_fget_borrowed(v_as_5816_, v_j_5818_);
                    crate::leanh::lean_inc(v_tail_5812_);
                    crate::leanh::lean_inc(v___x_5828_);
                    v___x_5829_ = l_Lean_mkConst(v___x_5828_, v_tail_5812_);
                    v___x_5830_ = l_Lean_mkAppN(v___x_5829_, v_params_5813_);
                    crate::leanh::lean_inc(v___y_5823_);
                    crate::leanh::lean_inc_ref(v___y_5822_);
                    crate::leanh::lean_inc(v___y_5821_);
                    crate::leanh::lean_inc_ref(v___y_5820_);
                    crate::leanh::lean_inc_ref(v___x_5830_);
                    v___x_5831_ = lean_infer_type(
                        v___x_5830_,
                        v___y_5820_,
                        v___y_5821_,
                        v___y_5822_,
                        v___y_5823_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5831_) == 0 {
                        v_a_5832_ = crate::leanh::lean_ctor_get(v___x_5831_, 0);
                        crate::leanh::lean_inc_n(v_a_5832_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_5831_, 1);
                        v___x_5833_ = 1;
                        v___x_5834_ = 1;
                        v___x_5835_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_5836_ = crate::leanh::lean_box((v_isZero_5826_) as usize);
                        v___x_5837_ = crate::leanh::lean_box((v___x_5833_) as usize);
                        v___x_5838_ = crate::leanh::lean_box((v___x_5834_) as usize);
                        crate::leanh::lean_inc(v_j_5818_);
                        crate::leanh::lean_inc(v___x_5828_);
                        crate::leanh::lean_inc_ref(v_motive_5815_);
                        crate::leanh::lean_inc(v___x_5814_);
                        v___f_5839_ = crate::leanh::lean_alloc_closure(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__1___boxed as *mut core::ffi::c_void, 17, 10);
                        crate::leanh::lean_closure_set(v___f_5839_, 0, v___x_5830_);
                        crate::leanh::lean_closure_set(v___f_5839_, 1, v___x_5835_);
                        crate::leanh::lean_closure_set(v___f_5839_, 2, v___x_5814_);
                        crate::leanh::lean_closure_set(v___f_5839_, 3, v_motive_5815_);
                        crate::leanh::lean_closure_set(v___f_5839_, 4, v___x_5836_);
                        crate::leanh::lean_closure_set(v___f_5839_, 5, v___x_5837_);
                        crate::leanh::lean_closure_set(v___f_5839_, 6, v___x_5838_);
                        crate::leanh::lean_closure_set(v___f_5839_, 7, v___x_5828_);
                        crate::leanh::lean_closure_set(v___f_5839_, 8, v_j_5818_);
                        crate::leanh::lean_closure_set(v___f_5839_, 9, v_a_5832_);
                        v___x_5840_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_5832_, v___f_5839_, v_isZero_5826_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_);
                        if crate::leanh::lean_obj_tag(v___x_5840_) == 0 {
                            v_a_5841_ = crate::leanh::lean_ctor_get(v___x_5840_, 0);
                            crate::leanh::lean_inc(v_a_5841_);
                            crate::leanh::lean_dec_ref_known(v___x_5840_, 1);
                            v_n_5842_ = lean_nat_sub(v_i_5817_, v___x_5835_);
                            crate::leanh::lean_dec(v_i_5817_);
                            v___x_5843_ = lean_nat_add(v_j_5818_, v___x_5835_);
                            crate::leanh::lean_dec(v_j_5818_);
                            v___x_5844_ = lean_array_push(v_bs_5819_, v_a_5841_);
                            v_i_5817_ = v_n_5842_;
                            v_j_5818_ = v___x_5843_;
                            v_bs_5819_ = v___x_5844_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_bs_5819_);
                            crate::leanh::lean_dec(v_j_5818_);
                            crate::leanh::lean_dec(v_i_5817_);
                            crate::leanh::lean_dec_ref(v_motive_5815_);
                            crate::leanh::lean_dec(v___x_5814_);
                            crate::leanh::lean_dec(v_tail_5812_);
                            v_a_5846_ = crate::leanh::lean_ctor_get(v___x_5840_, 0);
                            v_isSharedCheck_5853_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5840_)) as u8;
                            if v_isSharedCheck_5853_ == 0 {
                                v___x_5848_ = v___x_5840_;
                                v_isShared_5849_ = v_isSharedCheck_5853_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5846_);
                                crate::leanh::lean_dec(v___x_5840_);
                                v___x_5848_ = crate::leanh::lean_box(0);
                                v_isShared_5849_ = v_isSharedCheck_5853_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_5830_);
                        crate::leanh::lean_dec_ref(v_bs_5819_);
                        crate::leanh::lean_dec(v_j_5818_);
                        crate::leanh::lean_dec(v_i_5817_);
                        crate::leanh::lean_dec_ref(v_motive_5815_);
                        crate::leanh::lean_dec(v___x_5814_);
                        crate::leanh::lean_dec(v_tail_5812_);
                        v_a_5854_ = crate::leanh::lean_ctor_get(v___x_5831_, 0);
                        v_isSharedCheck_5861_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5831_)) as u8;
                        if v_isSharedCheck_5861_ == 0 {
                            v___x_5856_ = v___x_5831_;
                            v_isShared_5857_ = v_isSharedCheck_5861_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5854_);
                            crate::leanh::lean_dec(v___x_5831_);
                            v___x_5856_ = crate::leanh::lean_box(0);
                            v_isShared_5857_ = v_isSharedCheck_5861_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5849_ == 0 {
                    v___x_5851_ = v___x_5848_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5852_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5852_, 0, v_a_5846_);
                    v___x_5851_ = v_reuseFailAlloc_5852_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5851_;
            }
            3 => {
                if v_isShared_5857_ == 0 {
                    v___x_5859_ = v___x_5856_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5860_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5860_, 0, v_a_5854_);
                    v___x_5859_ = v_reuseFailAlloc_5860_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5859_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___boxed(
    mut v_tail_5862_: *mut crate::leanh::LeanObject,
    mut v_params_5863_: *mut crate::leanh::LeanObject,
    mut v___x_5864_: *mut crate::leanh::LeanObject,
    mut v_motive_5865_: *mut crate::leanh::LeanObject,
    mut v_as_5866_: *mut crate::leanh::LeanObject,
    mut v_i_5867_: *mut crate::leanh::LeanObject,
    mut v_j_5868_: *mut crate::leanh::LeanObject,
    mut v_bs_5869_: *mut crate::leanh::LeanObject,
    mut v___y_5870_: *mut crate::leanh::LeanObject,
    mut v___y_5871_: *mut crate::leanh::LeanObject,
    mut v___y_5872_: *mut crate::leanh::LeanObject,
    mut v___y_5873_: *mut crate::leanh::LeanObject,
    mut v___y_5874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5875_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(
        v_tail_5862_,
        v_params_5863_,
        v___x_5864_,
        v_motive_5865_,
        v_as_5866_,
        v_i_5867_,
        v_j_5868_,
        v_bs_5869_,
        v___y_5870_,
        v___y_5871_,
        v___y_5872_,
        v___y_5873_,
    );
    crate::leanh::lean_dec(v___y_5873_);
    crate::leanh::lean_dec_ref(v___y_5872_);
    crate::leanh::lean_dec(v___y_5871_);
    crate::leanh::lean_dec_ref(v___y_5870_);
    crate::leanh::lean_dec_ref(v_as_5866_);
    crate::leanh::lean_dec_ref(v_params_5863_);
    return v_res_5875_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtorHet___lam__2(
    mut v_ctors_5876_: *mut crate::leanh::LeanObject,
    mut v_tail_5877_: *mut crate::leanh::LeanObject,
    mut v_params_5878_: *mut crate::leanh::LeanObject,
    mut v_numParams_5879_: *mut crate::leanh::LeanObject,
    mut v_indName_5880_: *mut crate::leanh::LeanObject,
    mut v_ism1_5881_: *mut crate::leanh::LeanObject,
    mut v_ism2_5882_: *mut crate::leanh::LeanObject,
    mut v___x_5883_: *mut crate::leanh::LeanObject,
    mut v___x_5884_: u8,
    mut v___x_5885_: u8,
    mut v___x_5886_: u8,
    mut v_val_5887_: *mut crate::leanh::LeanObject,
    mut v___x_5888_: *mut crate::leanh::LeanObject,
    mut v___x_5889_: *mut crate::leanh::LeanObject,
    mut v_name_5890_: *mut crate::leanh::LeanObject,
    mut v___x_5891_: *mut crate::leanh::LeanObject,
    mut v_motive_5892_: *mut crate::leanh::LeanObject,
    mut v___y_5893_: *mut crate::leanh::LeanObject,
    mut v___y_5894_: *mut crate::leanh::LeanObject,
    mut v___y_5895_: *mut crate::leanh::LeanObject,
    mut v___y_5896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: u8 = 0;
    let mut v___x_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5913_: u8 = 0;
    let mut v___x_5915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5917_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5898_ = lean_array_mk(v_ctors_5876_);
                v___x_5899_ = lean_array_get_size(v___x_5898_);
                v___x_5900_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5901_ = lean_mk_empty_array_with_capacity(v___x_5899_);
                crate::leanh::lean_inc_ref(v_motive_5892_);
                crate::leanh::lean_inc(v_numParams_5879_);
                crate::leanh::lean_inc(v_tail_5877_);
                v___x_5902_ =
                    l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(
                        v_tail_5877_,
                        v_params_5878_,
                        v_numParams_5879_,
                        v_motive_5892_,
                        v___x_5898_,
                        v___x_5899_,
                        v___x_5900_,
                        v___x_5901_,
                        v___y_5893_,
                        v___y_5894_,
                        v___y_5895_,
                        v___y_5896_,
                    );
                if crate::leanh::lean_obj_tag(v___x_5902_) == 0 {
                    v_a_5903_ = crate::leanh::lean_ctor_get(v___x_5902_, 0);
                    crate::leanh::lean_inc(v_a_5903_);
                    crate::leanh::lean_dec_ref_known(v___x_5902_, 1);
                    v___x_5904_ = crate::leanh::lean_box((v___x_5884_) as usize);
                    v___x_5905_ = crate::leanh::lean_box((v___x_5885_) as usize);
                    v___x_5906_ = crate::leanh::lean_box((v___x_5886_) as usize);
                    v___f_5907_ = crate::leanh::lean_alloc_closure(
                        l_Lean_mkCasesOnSameCtorHet___lam__1___boxed as *mut core::ffi::c_void,
                        23,
                        17,
                    );
                    crate::leanh::lean_closure_set(v___f_5907_, 0, v_indName_5880_);
                    crate::leanh::lean_closure_set(v___f_5907_, 1, v_tail_5877_);
                    crate::leanh::lean_closure_set(v___f_5907_, 2, v_params_5878_);
                    crate::leanh::lean_closure_set(v___f_5907_, 3, v_ism1_5881_);
                    crate::leanh::lean_closure_set(v___f_5907_, 4, v_ism2_5882_);
                    crate::leanh::lean_closure_set(v___f_5907_, 5, v_motive_5892_);
                    crate::leanh::lean_closure_set(v___f_5907_, 6, v___x_5883_);
                    crate::leanh::lean_closure_set(v___f_5907_, 7, v___x_5904_);
                    crate::leanh::lean_closure_set(v___f_5907_, 8, v___x_5905_);
                    crate::leanh::lean_closure_set(v___f_5907_, 9, v___x_5906_);
                    crate::leanh::lean_closure_set(v___f_5907_, 10, v___x_5898_);
                    crate::leanh::lean_closure_set(v___f_5907_, 11, v_numParams_5879_);
                    crate::leanh::lean_closure_set(v___f_5907_, 12, v_val_5887_);
                    crate::leanh::lean_closure_set(v___f_5907_, 13, v___x_5888_);
                    crate::leanh::lean_closure_set(v___f_5907_, 14, v___x_5889_);
                    crate::leanh::lean_closure_set(v___f_5907_, 15, v_name_5890_);
                    crate::leanh::lean_closure_set(v___f_5907_, 16, v___x_5891_);
                    v___x_5908_ = 0;
                    v___x_5909_ =
                        l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7(
                            v_a_5903_,
                            v___f_5907_,
                            v___x_5908_,
                            v___y_5893_,
                            v___y_5894_,
                            v___y_5895_,
                            v___y_5896_,
                        );
                    return v___x_5909_;
                } else {
                    crate::leanh::lean_dec_ref(v___x_5898_);
                    crate::leanh::lean_dec_ref(v_motive_5892_);
                    crate::leanh::lean_dec(v___x_5891_);
                    crate::leanh::lean_dec(v_name_5890_);
                    crate::leanh::lean_dec(v___x_5889_);
                    crate::leanh::lean_dec(v___x_5888_);
                    crate::leanh::lean_dec_ref(v_val_5887_);
                    crate::leanh::lean_dec_ref(v___x_5883_);
                    crate::leanh::lean_dec_ref(v_ism2_5882_);
                    crate::leanh::lean_dec_ref(v_ism1_5881_);
                    crate::leanh::lean_dec(v_indName_5880_);
                    crate::leanh::lean_dec(v_numParams_5879_);
                    crate::leanh::lean_dec_ref(v_params_5878_);
                    crate::leanh::lean_dec(v_tail_5877_);
                    v_a_5910_ = crate::leanh::lean_ctor_get(v___x_5902_, 0);
                    v_isSharedCheck_5917_ = (!crate::leanh::lean_is_exclusive(v___x_5902_)) as u8;
                    if v_isSharedCheck_5917_ == 0 {
                        v___x_5912_ = v___x_5902_;
                        v_isShared_5913_ = v_isSharedCheck_5917_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5910_);
                        crate::leanh::lean_dec(v___x_5902_);
                        v___x_5912_ = crate::leanh::lean_box(0);
                        v_isShared_5913_ = v_isSharedCheck_5917_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5913_ == 0 {
                    v___x_5915_ = v___x_5912_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5916_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5916_, 0, v_a_5910_);
                    v___x_5915_ = v_reuseFailAlloc_5916_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5915_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkCasesOnSameCtorHet___lam__2___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ctors_5918_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_tail_5919_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_params_5920_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_numParams_5921_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_indName_5922_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_ism1_5923_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_ism2_5924_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_5925_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_5926_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_5927_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_5928_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_val_5929_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_5930_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___x_5931_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_name_5932_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___x_5933_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_motive_5934_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_5935_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_5936_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_5937_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_5938_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___y_5939_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v___x_22048__boxed_5940_: u8 = 0;
    let mut v___x_22049__boxed_5941_: u8 = 0;
    let mut v___x_22050__boxed_5942_: u8 = 0;
    let mut v_res_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_22048__boxed_5940_ = (crate::leanh::lean_unbox(v___x_5926_) as u8);
    v___x_22049__boxed_5941_ = (crate::leanh::lean_unbox(v___x_5927_) as u8);
    v___x_22050__boxed_5942_ = (crate::leanh::lean_unbox(v___x_5928_) as u8);
    v_res_5943_ = l_Lean_mkCasesOnSameCtorHet___lam__2(
        v_ctors_5918_,
        v_tail_5919_,
        v_params_5920_,
        v_numParams_5921_,
        v_indName_5922_,
        v_ism1_5923_,
        v_ism2_5924_,
        v___x_5925_,
        v___x_22048__boxed_5940_,
        v___x_22049__boxed_5941_,
        v___x_22050__boxed_5942_,
        v_val_5929_,
        v___x_5930_,
        v___x_5931_,
        v_name_5932_,
        v___x_5933_,
        v_motive_5934_,
        v___y_5935_,
        v___y_5936_,
        v___y_5937_,
        v___y_5938_,
    );
    crate::leanh::lean_dec(v___y_5938_);
    crate::leanh::lean_dec_ref(v___y_5937_);
    crate::leanh::lean_dec(v___y_5936_);
    crate::leanh::lean_dec_ref(v___y_5935_);
    return v_res_5943_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtorHet___lam__3(
    mut v_ism1_5947_: *mut crate::leanh::LeanObject,
    mut v_head_5948_: *mut crate::leanh::LeanObject,
    mut v_ctors_5949_: *mut crate::leanh::LeanObject,
    mut v_tail_5950_: *mut crate::leanh::LeanObject,
    mut v_params_5951_: *mut crate::leanh::LeanObject,
    mut v_numParams_5952_: *mut crate::leanh::LeanObject,
    mut v_indName_5953_: *mut crate::leanh::LeanObject,
    mut v_val_5954_: *mut crate::leanh::LeanObject,
    mut v___x_5955_: *mut crate::leanh::LeanObject,
    mut v___x_5956_: *mut crate::leanh::LeanObject,
    mut v_name_5957_: *mut crate::leanh::LeanObject,
    mut v___x_5958_: *mut crate::leanh::LeanObject,
    mut v_ism2_5959_: *mut crate::leanh::LeanObject,
    mut v_x_5960_: *mut crate::leanh::LeanObject,
    mut v___y_5961_: *mut crate::leanh::LeanObject,
    mut v___y_5962_: *mut crate::leanh::LeanObject,
    mut v___y_5963_: *mut crate::leanh::LeanObject,
    mut v___y_5964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: u8 = 0;
    let mut v___x_5969_: u8 = 0;
    let mut v___x_5970_: u8 = 0;
    let mut v___x_5971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_ism1_5947_);
    v___x_5966_ = l_Array_append___redArg(v_ism1_5947_, v_ism2_5959_);
    v___x_5967_ = l_Lean_mkSort(v_head_5948_);
    v___x_5968_ = 0;
    v___x_5969_ = 1;
    v___x_5970_ = 1;
    v___x_5971_ = l_Lean_Meta_mkForallFVars(
        v___x_5966_,
        v___x_5967_,
        v___x_5968_,
        v___x_5969_,
        v___x_5969_,
        v___x_5970_,
        v___y_5961_,
        v___y_5962_,
        v___y_5963_,
        v___y_5964_,
    );
    if crate::leanh::lean_obj_tag(v___x_5971_) == 0 {
        let mut v_a_5972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5978_: u8 = 0;
        let mut v___x_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_5972_ = crate::leanh::lean_ctor_get(v___x_5971_, 0);
        crate::leanh::lean_inc(v_a_5972_);
        crate::leanh::lean_dec_ref_known(v___x_5971_, 1);
        v___x_5973_ = crate::leanh::lean_box((v___x_5968_) as usize);
        v___x_5974_ = crate::leanh::lean_box((v___x_5969_) as usize);
        v___x_5975_ = crate::leanh::lean_box((v___x_5970_) as usize);
        v___f_5976_ = crate::leanh::lean_alloc_closure(
            l_Lean_mkCasesOnSameCtorHet___lam__2___boxed as *mut core::ffi::c_void,
            22,
            16,
        );
        crate::leanh::lean_closure_set(v___f_5976_, 0, v_ctors_5949_);
        crate::leanh::lean_closure_set(v___f_5976_, 1, v_tail_5950_);
        crate::leanh::lean_closure_set(v___f_5976_, 2, v_params_5951_);
        crate::leanh::lean_closure_set(v___f_5976_, 3, v_numParams_5952_);
        crate::leanh::lean_closure_set(v___f_5976_, 4, v_indName_5953_);
        crate::leanh::lean_closure_set(v___f_5976_, 5, v_ism1_5947_);
        crate::leanh::lean_closure_set(v___f_5976_, 6, v_ism2_5959_);
        crate::leanh::lean_closure_set(v___f_5976_, 7, v___x_5966_);
        crate::leanh::lean_closure_set(v___f_5976_, 8, v___x_5973_);
        crate::leanh::lean_closure_set(v___f_5976_, 9, v___x_5974_);
        crate::leanh::lean_closure_set(v___f_5976_, 10, v___x_5975_);
        crate::leanh::lean_closure_set(v___f_5976_, 11, v_val_5954_);
        crate::leanh::lean_closure_set(v___f_5976_, 12, v___x_5955_);
        crate::leanh::lean_closure_set(v___f_5976_, 13, v___x_5956_);
        crate::leanh::lean_closure_set(v___f_5976_, 14, v_name_5957_);
        crate::leanh::lean_closure_set(v___f_5976_, 15, v___x_5958_);
        v___x_5977_ = l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1;
        v___x_5978_ = 0;
        v___x_5979_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(
            v___x_5977_,
            v___x_5970_,
            v_a_5972_,
            v___f_5976_,
            v___x_5978_,
            v___y_5961_,
            v___y_5962_,
            v___y_5963_,
            v___y_5964_,
        );
        return v___x_5979_;
    } else {
        crate::leanh::lean_dec_ref(v___x_5966_);
        crate::leanh::lean_dec_ref(v_ism2_5959_);
        crate::leanh::lean_dec(v___x_5958_);
        crate::leanh::lean_dec(v_name_5957_);
        crate::leanh::lean_dec(v___x_5956_);
        crate::leanh::lean_dec(v___x_5955_);
        crate::leanh::lean_dec_ref(v_val_5954_);
        crate::leanh::lean_dec(v_indName_5953_);
        crate::leanh::lean_dec(v_numParams_5952_);
        crate::leanh::lean_dec_ref(v_params_5951_);
        crate::leanh::lean_dec(v_tail_5950_);
        crate::leanh::lean_dec(v_ctors_5949_);
        crate::leanh::lean_dec_ref(v_ism1_5947_);
        return v___x_5971_;
    }
}
pub unsafe fn l_Lean_mkCasesOnSameCtorHet___lam__3___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ism1_5980_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_head_5981_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_ctors_5982_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_tail_5983_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_params_5984_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_numParams_5985_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_indName_5986_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_val_5987_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_5988_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_5989_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_name_5990_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_5991_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_ism2_5992_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_x_5993_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5994_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5995_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5996_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_5997_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_5998_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_res_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5999_ = l_Lean_mkCasesOnSameCtorHet___lam__3(
        v_ism1_5980_,
        v_head_5981_,
        v_ctors_5982_,
        v_tail_5983_,
        v_params_5984_,
        v_numParams_5985_,
        v_indName_5986_,
        v_val_5987_,
        v___x_5988_,
        v___x_5989_,
        v_name_5990_,
        v___x_5991_,
        v_ism2_5992_,
        v_x_5993_,
        v___y_5994_,
        v___y_5995_,
        v___y_5996_,
        v___y_5997_,
    );
    crate::leanh::lean_dec(v___y_5997_);
    crate::leanh::lean_dec_ref(v___y_5996_);
    crate::leanh::lean_dec(v___y_5995_);
    crate::leanh::lean_dec_ref(v___y_5994_);
    crate::leanh::lean_dec_ref(v_x_5993_);
    return v_res_5999_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtorHet___lam__4(
    mut v_head_6000_: *mut crate::leanh::LeanObject,
    mut v_ctors_6001_: *mut crate::leanh::LeanObject,
    mut v_tail_6002_: *mut crate::leanh::LeanObject,
    mut v_params_6003_: *mut crate::leanh::LeanObject,
    mut v_numParams_6004_: *mut crate::leanh::LeanObject,
    mut v_indName_6005_: *mut crate::leanh::LeanObject,
    mut v_val_6006_: *mut crate::leanh::LeanObject,
    mut v___x_6007_: *mut crate::leanh::LeanObject,
    mut v___x_6008_: *mut crate::leanh::LeanObject,
    mut v_name_6009_: *mut crate::leanh::LeanObject,
    mut v___x_6010_: *mut crate::leanh::LeanObject,
    mut v_t_6011_: *mut crate::leanh::LeanObject,
    mut v___x_6012_: *mut crate::leanh::LeanObject,
    mut v_ism1_6013_: *mut crate::leanh::LeanObject,
    mut v_x_6014_: *mut crate::leanh::LeanObject,
    mut v___y_6015_: *mut crate::leanh::LeanObject,
    mut v___y_6016_: *mut crate::leanh::LeanObject,
    mut v___y_6017_: *mut crate::leanh::LeanObject,
    mut v___y_6018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: u8 = 0;
    let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_6020_ = crate::leanh::lean_alloc_closure(
        l_Lean_mkCasesOnSameCtorHet___lam__3___boxed as *mut core::ffi::c_void,
        19,
        12,
    );
    crate::leanh::lean_closure_set(v___f_6020_, 0, v_ism1_6013_);
    crate::leanh::lean_closure_set(v___f_6020_, 1, v_head_6000_);
    crate::leanh::lean_closure_set(v___f_6020_, 2, v_ctors_6001_);
    crate::leanh::lean_closure_set(v___f_6020_, 3, v_tail_6002_);
    crate::leanh::lean_closure_set(v___f_6020_, 4, v_params_6003_);
    crate::leanh::lean_closure_set(v___f_6020_, 5, v_numParams_6004_);
    crate::leanh::lean_closure_set(v___f_6020_, 6, v_indName_6005_);
    crate::leanh::lean_closure_set(v___f_6020_, 7, v_val_6006_);
    crate::leanh::lean_closure_set(v___f_6020_, 8, v___x_6007_);
    crate::leanh::lean_closure_set(v___f_6020_, 9, v___x_6008_);
    crate::leanh::lean_closure_set(v___f_6020_, 10, v_name_6009_);
    crate::leanh::lean_closure_set(v___f_6020_, 11, v___x_6010_);
    v___x_6021_ = 0;
    v___x_6022_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(
            v_t_6011_,
            v___x_6012_,
            v___f_6020_,
            v___x_6021_,
            v___x_6021_,
            v___y_6015_,
            v___y_6016_,
            v___y_6017_,
            v___y_6018_,
        );
    return v___x_6022_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtorHet___lam__4___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_6023_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_ctors_6024_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_tail_6025_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_params_6026_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_numParams_6027_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_indName_6028_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_val_6029_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_6030_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_6031_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_name_6032_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_6033_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_t_6034_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_6035_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_ism1_6036_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_x_6037_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_6038_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_6039_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_6040_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_6041_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_6042_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_res_6043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6043_ = l_Lean_mkCasesOnSameCtorHet___lam__4(
        v_head_6023_,
        v_ctors_6024_,
        v_tail_6025_,
        v_params_6026_,
        v_numParams_6027_,
        v_indName_6028_,
        v_val_6029_,
        v___x_6030_,
        v___x_6031_,
        v_name_6032_,
        v___x_6033_,
        v_t_6034_,
        v___x_6035_,
        v_ism1_6036_,
        v_x_6037_,
        v___y_6038_,
        v___y_6039_,
        v___y_6040_,
        v___y_6041_,
    );
    crate::leanh::lean_dec(v___y_6041_);
    crate::leanh::lean_dec_ref(v___y_6040_);
    crate::leanh::lean_dec(v___y_6039_);
    crate::leanh::lean_dec_ref(v___y_6038_);
    crate::leanh::lean_dec_ref(v_x_6037_);
    return v_res_6043_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtorHet___lam__5(
    mut v_numIndices_6044_: *mut crate::leanh::LeanObject,
    mut v___x_6045_: *mut crate::leanh::LeanObject,
    mut v_head_6046_: *mut crate::leanh::LeanObject,
    mut v_ctors_6047_: *mut crate::leanh::LeanObject,
    mut v_tail_6048_: *mut crate::leanh::LeanObject,
    mut v_params_6049_: *mut crate::leanh::LeanObject,
    mut v_numParams_6050_: *mut crate::leanh::LeanObject,
    mut v_indName_6051_: *mut crate::leanh::LeanObject,
    mut v_val_6052_: *mut crate::leanh::LeanObject,
    mut v___x_6053_: *mut crate::leanh::LeanObject,
    mut v___x_6054_: *mut crate::leanh::LeanObject,
    mut v_name_6055_: *mut crate::leanh::LeanObject,
    mut v_x_6056_: *mut crate::leanh::LeanObject,
    mut v_t_6057_: *mut crate::leanh::LeanObject,
    mut v___y_6058_: *mut crate::leanh::LeanObject,
    mut v___y_6059_: *mut crate::leanh::LeanObject,
    mut v___y_6060_: *mut crate::leanh::LeanObject,
    mut v___y_6061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6066_: u8 = 0;
    let mut v___x_6067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6063_ = lean_nat_add(v_numIndices_6044_, v___x_6045_);
    v___x_6064_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6064_, 0, v___x_6063_);
    crate::leanh::lean_inc_ref(v___x_6064_);
    crate::leanh::lean_inc_ref(v_t_6057_);
    v___f_6065_ = crate::leanh::lean_alloc_closure(
        l_Lean_mkCasesOnSameCtorHet___lam__4___boxed as *mut core::ffi::c_void,
        20,
        13,
    );
    crate::leanh::lean_closure_set(v___f_6065_, 0, v_head_6046_);
    crate::leanh::lean_closure_set(v___f_6065_, 1, v_ctors_6047_);
    crate::leanh::lean_closure_set(v___f_6065_, 2, v_tail_6048_);
    crate::leanh::lean_closure_set(v___f_6065_, 3, v_params_6049_);
    crate::leanh::lean_closure_set(v___f_6065_, 4, v_numParams_6050_);
    crate::leanh::lean_closure_set(v___f_6065_, 5, v_indName_6051_);
    crate::leanh::lean_closure_set(v___f_6065_, 6, v_val_6052_);
    crate::leanh::lean_closure_set(v___f_6065_, 7, v___x_6053_);
    crate::leanh::lean_closure_set(v___f_6065_, 8, v___x_6054_);
    crate::leanh::lean_closure_set(v___f_6065_, 9, v_name_6055_);
    crate::leanh::lean_closure_set(v___f_6065_, 10, v___x_6045_);
    crate::leanh::lean_closure_set(v___f_6065_, 11, v_t_6057_);
    crate::leanh::lean_closure_set(v___f_6065_, 12, v___x_6064_);
    v___x_6066_ = 0;
    v___x_6067_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(
            v_t_6057_,
            v___x_6064_,
            v___f_6065_,
            v___x_6066_,
            v___x_6066_,
            v___y_6058_,
            v___y_6059_,
            v___y_6060_,
            v___y_6061_,
        );
    return v___x_6067_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtorHet___lam__5___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_numIndices_6068_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_6069_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_head_6070_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_ctors_6071_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_tail_6072_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_params_6073_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_numParams_6074_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_indName_6075_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_val_6076_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_6077_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_6078_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_name_6079_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_x_6080_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_t_6081_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_6082_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_6083_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_6084_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_6085_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_6086_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_res_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6087_ = l_Lean_mkCasesOnSameCtorHet___lam__5(
        v_numIndices_6068_,
        v___x_6069_,
        v_head_6070_,
        v_ctors_6071_,
        v_tail_6072_,
        v_params_6073_,
        v_numParams_6074_,
        v_indName_6075_,
        v_val_6076_,
        v___x_6077_,
        v___x_6078_,
        v_name_6079_,
        v_x_6080_,
        v_t_6081_,
        v___y_6082_,
        v___y_6083_,
        v___y_6084_,
        v___y_6085_,
    );
    crate::leanh::lean_dec(v___y_6085_);
    crate::leanh::lean_dec_ref(v___y_6084_);
    crate::leanh::lean_dec(v___y_6083_);
    crate::leanh::lean_dec_ref(v___y_6082_);
    crate::leanh::lean_dec_ref(v_x_6080_);
    crate::leanh::lean_dec(v_numIndices_6068_);
    return v_res_6087_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtorHet___lam__6(
    mut v_numIndices_6090_: *mut crate::leanh::LeanObject,
    mut v_head_6091_: *mut crate::leanh::LeanObject,
    mut v_ctors_6092_: *mut crate::leanh::LeanObject,
    mut v_tail_6093_: *mut crate::leanh::LeanObject,
    mut v_numParams_6094_: *mut crate::leanh::LeanObject,
    mut v_indName_6095_: *mut crate::leanh::LeanObject,
    mut v_val_6096_: *mut crate::leanh::LeanObject,
    mut v___x_6097_: *mut crate::leanh::LeanObject,
    mut v___x_6098_: *mut crate::leanh::LeanObject,
    mut v_name_6099_: *mut crate::leanh::LeanObject,
    mut v_params_6100_: *mut crate::leanh::LeanObject,
    mut v_t_6101_: *mut crate::leanh::LeanObject,
    mut v___y_6102_: *mut crate::leanh::LeanObject,
    mut v___y_6103_: *mut crate::leanh::LeanObject,
    mut v___y_6104_: *mut crate::leanh::LeanObject,
    mut v___y_6105_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6110_: u8 = 0;
    let mut v___x_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6107_ = crate::leanh::lean_unsigned_to_nat(1);
    v___f_6108_ = crate::leanh::lean_alloc_closure(
        l_Lean_mkCasesOnSameCtorHet___lam__5___boxed as *mut core::ffi::c_void,
        19,
        12,
    );
    crate::leanh::lean_closure_set(v___f_6108_, 0, v_numIndices_6090_);
    crate::leanh::lean_closure_set(v___f_6108_, 1, v___x_6107_);
    crate::leanh::lean_closure_set(v___f_6108_, 2, v_head_6091_);
    crate::leanh::lean_closure_set(v___f_6108_, 3, v_ctors_6092_);
    crate::leanh::lean_closure_set(v___f_6108_, 4, v_tail_6093_);
    crate::leanh::lean_closure_set(v___f_6108_, 5, v_params_6100_);
    crate::leanh::lean_closure_set(v___f_6108_, 6, v_numParams_6094_);
    crate::leanh::lean_closure_set(v___f_6108_, 7, v_indName_6095_);
    crate::leanh::lean_closure_set(v___f_6108_, 8, v_val_6096_);
    crate::leanh::lean_closure_set(v___f_6108_, 9, v___x_6097_);
    crate::leanh::lean_closure_set(v___f_6108_, 10, v___x_6098_);
    crate::leanh::lean_closure_set(v___f_6108_, 11, v_name_6099_);
    v___x_6109_ = l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0;
    v___x_6110_ = 0;
    v___x_6111_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(
            v_t_6101_,
            v___x_6109_,
            v___f_6108_,
            v___x_6110_,
            v___x_6110_,
            v___y_6102_,
            v___y_6103_,
            v___y_6104_,
            v___y_6105_,
        );
    return v___x_6111_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtorHet___lam__6___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_numIndices_6112_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_head_6113_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_ctors_6114_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_tail_6115_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_numParams_6116_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_indName_6117_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_val_6118_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_6119_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_6120_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_name_6121_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_params_6122_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_t_6123_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_6124_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_6125_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_6126_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_6127_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_6128_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6129_ = l_Lean_mkCasesOnSameCtorHet___lam__6(
        v_numIndices_6112_,
        v_head_6113_,
        v_ctors_6114_,
        v_tail_6115_,
        v_numParams_6116_,
        v_indName_6117_,
        v_val_6118_,
        v___x_6119_,
        v___x_6120_,
        v_name_6121_,
        v_params_6122_,
        v_t_6123_,
        v___y_6124_,
        v___y_6125_,
        v___y_6126_,
        v___y_6127_,
    );
    crate::leanh::lean_dec(v___y_6127_);
    crate::leanh::lean_dec_ref(v___y_6126_);
    crate::leanh::lean_dec(v___y_6125_);
    crate::leanh::lean_dec_ref(v___y_6124_);
    return v_res_6129_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtorHet___lam__7(
    mut v_a_6130_: *mut crate::leanh::LeanObject,
    mut v_declName_6131_: *mut crate::leanh::LeanObject,
    mut v_levelParams_6132_: *mut crate::leanh::LeanObject,
    mut v___x_6133_: u8,
    mut v___y_6134_: *mut crate::leanh::LeanObject,
    mut v___y_6135_: *mut crate::leanh::LeanObject,
    mut v___y_6136_: *mut crate::leanh::LeanObject,
    mut v___y_6137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6146_: u8 = 0;
    let mut v___x_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6151_: u8 = 0;
    let mut v_a_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6155_: u8 = 0;
    let mut v___x_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6159_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_6137_);
                crate::leanh::lean_inc_ref(v___y_6136_);
                crate::leanh::lean_inc_ref(v_a_6130_);
                v___x_6139_ = lean_infer_type(
                    v_a_6130_,
                    v___y_6134_,
                    v___y_6135_,
                    v___y_6136_,
                    v___y_6137_,
                );
                if crate::leanh::lean_obj_tag(v___x_6139_) == 0 {
                    v_a_6140_ = crate::leanh::lean_ctor_get(v___x_6139_, 0);
                    crate::leanh::lean_inc(v_a_6140_);
                    crate::leanh::lean_dec_ref_known(v___x_6139_, 1);
                    v___x_6141_ = crate::leanh::lean_box(1);
                    v___x_6142_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_6131_, v_levelParams_6132_, v_a_6140_, v_a_6130_, v___x_6141_, v___y_6137_);
                    v_a_6143_ = crate::leanh::lean_ctor_get(v___x_6142_, 0);
                    v_isSharedCheck_6151_ = (!crate::leanh::lean_is_exclusive(v___x_6142_)) as u8;
                    if v_isSharedCheck_6151_ == 0 {
                        v___x_6145_ = v___x_6142_;
                        v_isShared_6146_ = v_isSharedCheck_6151_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6143_);
                        crate::leanh::lean_dec(v___x_6142_);
                        v___x_6145_ = crate::leanh::lean_box(0);
                        v_isShared_6146_ = v_isSharedCheck_6151_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_6137_);
                    crate::leanh::lean_dec_ref(v___y_6136_);
                    crate::leanh::lean_dec(v_levelParams_6132_);
                    crate::leanh::lean_dec(v_declName_6131_);
                    crate::leanh::lean_dec_ref(v_a_6130_);
                    v_a_6152_ = crate::leanh::lean_ctor_get(v___x_6139_, 0);
                    v_isSharedCheck_6159_ = (!crate::leanh::lean_is_exclusive(v___x_6139_)) as u8;
                    if v_isSharedCheck_6159_ == 0 {
                        v___x_6154_ = v___x_6139_;
                        v_isShared_6155_ = v_isSharedCheck_6159_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6152_);
                        crate::leanh::lean_dec(v___x_6139_);
                        v___x_6154_ = crate::leanh::lean_box(0);
                        v_isShared_6155_ = v_isSharedCheck_6159_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6146_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6145_, 1);
                    v___x_6148_ = v___x_6145_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6150_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6150_, 0, v_a_6143_);
                    v___x_6148_ = v_reuseFailAlloc_6150_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6149_ = l_Lean_addDecl(v___x_6148_, v___x_6133_, v___y_6136_, v___y_6137_);
                crate::leanh::lean_dec(v___y_6137_);
                crate::leanh::lean_dec_ref(v___y_6136_);
                return v___x_6149_;
            }
            3 => {
                if v_isShared_6155_ == 0 {
                    v___x_6157_ = v___x_6154_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6158_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6158_, 0, v_a_6152_);
                    v___x_6157_ = v_reuseFailAlloc_6158_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6157_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkCasesOnSameCtorHet___lam__7___boxed(
    mut v_a_6160_: *mut crate::leanh::LeanObject,
    mut v_declName_6161_: *mut crate::leanh::LeanObject,
    mut v_levelParams_6162_: *mut crate::leanh::LeanObject,
    mut v___x_6163_: *mut crate::leanh::LeanObject,
    mut v___y_6164_: *mut crate::leanh::LeanObject,
    mut v___y_6165_: *mut crate::leanh::LeanObject,
    mut v___y_6166_: *mut crate::leanh::LeanObject,
    mut v___y_6167_: *mut crate::leanh::LeanObject,
    mut v___y_6168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_22340__boxed_6169_: u8 = 0;
    let mut v_res_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_22340__boxed_6169_ = (crate::leanh::lean_unbox(v___x_6163_) as u8);
    v_res_6170_ = l_Lean_mkCasesOnSameCtorHet___lam__7(
        v_a_6160_,
        v_declName_6161_,
        v_levelParams_6162_,
        v___x_22340__boxed_6169_,
        v___y_6164_,
        v___y_6165_,
        v___y_6166_,
        v___y_6167_,
    );
    return v_res_6170_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(
    mut v_a_6171_: *mut crate::leanh::LeanObject,
    mut v_a_6172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6178_: u8 = 0;
    let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6184_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_6171_) == 0 {
                    v___x_6173_ = l_List_reverse___redArg(v_a_6172_);
                    return v___x_6173_;
                } else {
                    v_head_6174_ = crate::leanh::lean_ctor_get(v_a_6171_, 0);
                    v_tail_6175_ = crate::leanh::lean_ctor_get(v_a_6171_, 1);
                    v_isSharedCheck_6184_ = (!crate::leanh::lean_is_exclusive(v_a_6171_)) as u8;
                    if v_isSharedCheck_6184_ == 0 {
                        v___x_6177_ = v_a_6171_;
                        v_isShared_6178_ = v_isSharedCheck_6184_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_6175_);
                        crate::leanh::lean_inc(v_head_6174_);
                        crate::leanh::lean_dec(v_a_6171_);
                        v___x_6177_ = crate::leanh::lean_box(0);
                        v_isShared_6178_ = v_isSharedCheck_6184_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6179_ = l_Lean_mkLevelParam(v_head_6174_);
                if v_isShared_6178_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6177_, 1, v_a_6172_);
                    crate::leanh::lean_ctor_set(v___x_6177_, 0, v___x_6179_);
                    v___x_6181_ = v___x_6177_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6183_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6183_, 0, v___x_6179_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6183_, 1, v_a_6172_);
                    v___x_6181_ = v_reuseFailAlloc_6183_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_6171_ = v_tail_6175_;
                v_a_6172_ = v___x_6181_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(
    mut v_msgData_6185_: *mut crate::leanh::LeanObject,
    mut v___y_6186_: *mut crate::leanh::LeanObject,
    mut v___y_6187_: *mut crate::leanh::LeanObject,
    mut v___y_6188_: *mut crate::leanh::LeanObject,
    mut v___y_6189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_6195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6191_ = lean_st_ref_get(v___y_6189_);
    v_env_6192_ = crate::leanh::lean_ctor_get(v___x_6191_, 0);
    crate::leanh::lean_inc_ref(v_env_6192_);
    crate::leanh::lean_dec(v___x_6191_);
    v___x_6193_ = lean_st_ref_get(v___y_6187_);
    v_mctx_6194_ = crate::leanh::lean_ctor_get(v___x_6193_, 0);
    crate::leanh::lean_inc_ref(v_mctx_6194_);
    crate::leanh::lean_dec(v___x_6193_);
    v_lctx_6195_ = crate::leanh::lean_ctor_get(v___y_6186_, 2);
    v_options_6196_ = crate::leanh::lean_ctor_get(v___y_6188_, 2);
    crate::leanh::lean_inc_ref(v_options_6196_);
    crate::leanh::lean_inc_ref(v_lctx_6195_);
    v___x_6197_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6197_, 0, v_env_6192_);
    crate::leanh::lean_ctor_set(v___x_6197_, 1, v_mctx_6194_);
    crate::leanh::lean_ctor_set(v___x_6197_, 2, v_lctx_6195_);
    crate::leanh::lean_ctor_set(v___x_6197_, 3, v_options_6196_);
    v___x_6198_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6198_, 0, v___x_6197_);
    crate::leanh::lean_ctor_set(v___x_6198_, 1, v_msgData_6185_);
    v___x_6199_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6199_, 0, v___x_6198_);
    return v___x_6199_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25___boxed(
    mut v_msgData_6200_: *mut crate::leanh::LeanObject,
    mut v___y_6201_: *mut crate::leanh::LeanObject,
    mut v___y_6202_: *mut crate::leanh::LeanObject,
    mut v___y_6203_: *mut crate::leanh::LeanObject,
    mut v___y_6204_: *mut crate::leanh::LeanObject,
    mut v___y_6205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6206_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msgData_6200_, v___y_6201_, v___y_6202_, v___y_6203_, v___y_6204_);
    crate::leanh::lean_dec(v___y_6204_);
    crate::leanh::lean_dec_ref(v___y_6203_);
    crate::leanh::lean_dec(v___y_6202_);
    crate::leanh::lean_dec_ref(v___y_6201_);
    return v_res_6206_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(
    mut v_msg_6207_: *mut crate::leanh::LeanObject,
    mut v___y_6208_: *mut crate::leanh::LeanObject,
    mut v___y_6209_: *mut crate::leanh::LeanObject,
    mut v___y_6210_: *mut crate::leanh::LeanObject,
    mut v___y_6211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_6213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6218_: u8 = 0;
    let mut v___x_6219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6223_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6213_ = crate::leanh::lean_ctor_get(v___y_6210_, 5);
                v___x_6214_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20_spec__25(v_msg_6207_, v___y_6208_, v___y_6209_, v___y_6210_, v___y_6211_);
                v_a_6215_ = crate::leanh::lean_ctor_get(v___x_6214_, 0);
                v_isSharedCheck_6223_ = (!crate::leanh::lean_is_exclusive(v___x_6214_)) as u8;
                if v_isSharedCheck_6223_ == 0 {
                    v___x_6217_ = v___x_6214_;
                    v_isShared_6218_ = v_isSharedCheck_6223_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6215_);
                    crate::leanh::lean_dec(v___x_6214_);
                    v___x_6217_ = crate::leanh::lean_box(0);
                    v_isShared_6218_ = v_isSharedCheck_6223_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_6213_);
                v___x_6219_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6219_, 0, v_ref_6213_);
                crate::leanh::lean_ctor_set(v___x_6219_, 1, v_a_6215_);
                if v_isShared_6218_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6217_, 1);
                    crate::leanh::lean_ctor_set(v___x_6217_, 0, v___x_6219_);
                    v___x_6221_ = v___x_6217_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6222_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6222_, 0, v___x_6219_);
                    v___x_6221_ = v_reuseFailAlloc_6222_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6221_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg___boxed(
    mut v_msg_6224_: *mut crate::leanh::LeanObject,
    mut v___y_6225_: *mut crate::leanh::LeanObject,
    mut v___y_6226_: *mut crate::leanh::LeanObject,
    mut v___y_6227_: *mut crate::leanh::LeanObject,
    mut v___y_6228_: *mut crate::leanh::LeanObject,
    mut v___y_6229_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6230_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_6224_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_);
    crate::leanh::lean_dec(v___y_6228_);
    crate::leanh::lean_dec_ref(v___y_6227_);
    crate::leanh::lean_dec(v___y_6226_);
    crate::leanh::lean_dec_ref(v___y_6225_);
    return v_res_6230_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(
    mut v_ref_6231_: *mut crate::leanh::LeanObject,
    mut v_msg_6232_: *mut crate::leanh::LeanObject,
    mut v___y_6233_: *mut crate::leanh::LeanObject,
    mut v___y_6234_: *mut crate::leanh::LeanObject,
    mut v___y_6235_: *mut crate::leanh::LeanObject,
    mut v___y_6236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6250_: u8 = 0;
    let mut v_cancelTk_x3f_6251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6252_: u8 = 0;
    let mut v_inheritedTraceOptions_6253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_6238_ = crate::leanh::lean_ctor_get(v___y_6235_, 0);
    v_fileMap_6239_ = crate::leanh::lean_ctor_get(v___y_6235_, 1);
    v_options_6240_ = crate::leanh::lean_ctor_get(v___y_6235_, 2);
    v_currRecDepth_6241_ = crate::leanh::lean_ctor_get(v___y_6235_, 3);
    v_maxRecDepth_6242_ = crate::leanh::lean_ctor_get(v___y_6235_, 4);
    v_ref_6243_ = crate::leanh::lean_ctor_get(v___y_6235_, 5);
    v_currNamespace_6244_ = crate::leanh::lean_ctor_get(v___y_6235_, 6);
    v_openDecls_6245_ = crate::leanh::lean_ctor_get(v___y_6235_, 7);
    v_initHeartbeats_6246_ = crate::leanh::lean_ctor_get(v___y_6235_, 8);
    v_maxHeartbeats_6247_ = crate::leanh::lean_ctor_get(v___y_6235_, 9);
    v_quotContext_6248_ = crate::leanh::lean_ctor_get(v___y_6235_, 10);
    v_currMacroScope_6249_ = crate::leanh::lean_ctor_get(v___y_6235_, 11);
    v_diag_6250_ = crate::leanh::lean_ctor_get_uint8(
        v___y_6235_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_6251_ = crate::leanh::lean_ctor_get(v___y_6235_, 12);
    v_suppressElabErrors_6252_ = crate::leanh::lean_ctor_get_uint8(
        v___y_6235_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_6253_ = crate::leanh::lean_ctor_get(v___y_6235_, 13);
    v_ref_6254_ = l_Lean_replaceRef(v_ref_6231_, v_ref_6243_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_6253_);
    crate::leanh::lean_inc(v_cancelTk_x3f_6251_);
    crate::leanh::lean_inc(v_currMacroScope_6249_);
    crate::leanh::lean_inc(v_quotContext_6248_);
    crate::leanh::lean_inc(v_maxHeartbeats_6247_);
    crate::leanh::lean_inc(v_initHeartbeats_6246_);
    crate::leanh::lean_inc(v_openDecls_6245_);
    crate::leanh::lean_inc(v_currNamespace_6244_);
    crate::leanh::lean_inc(v_maxRecDepth_6242_);
    crate::leanh::lean_inc(v_currRecDepth_6241_);
    crate::leanh::lean_inc_ref(v_options_6240_);
    crate::leanh::lean_inc_ref(v_fileMap_6239_);
    crate::leanh::lean_inc_ref(v_fileName_6238_);
    v___x_6255_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_6255_, 0, v_fileName_6238_);
    crate::leanh::lean_ctor_set(v___x_6255_, 1, v_fileMap_6239_);
    crate::leanh::lean_ctor_set(v___x_6255_, 2, v_options_6240_);
    crate::leanh::lean_ctor_set(v___x_6255_, 3, v_currRecDepth_6241_);
    crate::leanh::lean_ctor_set(v___x_6255_, 4, v_maxRecDepth_6242_);
    crate::leanh::lean_ctor_set(v___x_6255_, 5, v_ref_6254_);
    crate::leanh::lean_ctor_set(v___x_6255_, 6, v_currNamespace_6244_);
    crate::leanh::lean_ctor_set(v___x_6255_, 7, v_openDecls_6245_);
    crate::leanh::lean_ctor_set(v___x_6255_, 8, v_initHeartbeats_6246_);
    crate::leanh::lean_ctor_set(v___x_6255_, 9, v_maxHeartbeats_6247_);
    crate::leanh::lean_ctor_set(v___x_6255_, 10, v_quotContext_6248_);
    crate::leanh::lean_ctor_set(v___x_6255_, 11, v_currMacroScope_6249_);
    crate::leanh::lean_ctor_set(v___x_6255_, 12, v_cancelTk_x3f_6251_);
    crate::leanh::lean_ctor_set(v___x_6255_, 13, v_inheritedTraceOptions_6253_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_6255_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_6250_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_6255_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_6252_,
    );
    v___x_6256_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_6232_, v___y_6233_, v___y_6234_, v___x_6255_, v___y_6236_);
    crate::leanh::lean_dec_ref_known(v___x_6255_, 14);
    return v___x_6256_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg___boxed(
    mut v_ref_6257_: *mut crate::leanh::LeanObject,
    mut v_msg_6258_: *mut crate::leanh::LeanObject,
    mut v___y_6259_: *mut crate::leanh::LeanObject,
    mut v___y_6260_: *mut crate::leanh::LeanObject,
    mut v___y_6261_: *mut crate::leanh::LeanObject,
    mut v___y_6262_: *mut crate::leanh::LeanObject,
    mut v___y_6263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6264_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_6257_, v_msg_6258_, v___y_6259_, v___y_6260_, v___y_6261_, v___y_6262_);
    crate::leanh::lean_dec(v___y_6262_);
    crate::leanh::lean_dec_ref(v___y_6261_);
    crate::leanh::lean_dec(v___y_6260_);
    crate::leanh::lean_dec_ref(v___y_6259_);
    crate::leanh::lean_dec(v_ref_6257_);
    return v_res_6264_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6265_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_6265_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6266_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__0);
    v___x_6267_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6267_, 0, v___x_6266_);
    return v___x_6267_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6268_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
    v___x_6269_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6270_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6270_, 0, v___x_6269_);
    crate::leanh::lean_ctor_set(v___x_6270_, 1, v___x_6269_);
    crate::leanh::lean_ctor_set(v___x_6270_, 2, v___x_6269_);
    crate::leanh::lean_ctor_set(v___x_6270_, 3, v___x_6269_);
    crate::leanh::lean_ctor_set(v___x_6270_, 4, v___x_6268_);
    crate::leanh::lean_ctor_set(v___x_6270_, 5, v___x_6268_);
    crate::leanh::lean_ctor_set(v___x_6270_, 6, v___x_6268_);
    crate::leanh::lean_ctor_set(v___x_6270_, 7, v___x_6268_);
    crate::leanh::lean_ctor_set(v___x_6270_, 8, v___x_6268_);
    crate::leanh::lean_ctor_set(v___x_6270_, 9, v___x_6268_);
    return v___x_6270_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6271_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_6272_ = lean_mk_empty_array_with_capacity(v___x_6271_);
    v___x_6273_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6273_, 0, v___x_6272_);
    return v___x_6273_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6274_: usize = 0;
    let mut v___x_6275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6274_ = 5usize;
    v___x_6275_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_6276_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_6277_ = lean_mk_empty_array_with_capacity(v___x_6276_);
    v___x_6278_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__3);
    v___x_6279_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_6279_, 0, v___x_6278_);
    crate::leanh::lean_ctor_set(v___x_6279_, 1, v___x_6277_);
    crate::leanh::lean_ctor_set(v___x_6279_, 2, v___x_6275_);
    crate::leanh::lean_ctor_set(v___x_6279_, 3, v___x_6275_);
    crate::leanh::lean_ctor_set_usize(v___x_6279_, 4, v___x_6274_);
    return v___x_6279_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6280_ = crate::leanh::lean_box(1);
    v___x_6281_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__4);
    v___x_6282_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__1);
    v___x_6283_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6283_, 0, v___x_6282_);
    crate::leanh::lean_ctor_set(v___x_6283_, 1, v___x_6281_);
    crate::leanh::lean_ctor_set(v___x_6283_, 2, v___x_6280_);
    return v___x_6283_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6285_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__6;
    v___x_6286_ = l_Lean_stringToMessageData(v___x_6285_);
    return v___x_6286_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6288_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__8;
    v___x_6289_ = l_Lean_stringToMessageData(v___x_6288_);
    return v___x_6289_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6291_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__10;
    v___x_6292_ = l_Lean_stringToMessageData(v___x_6291_);
    return v___x_6292_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6294_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__12;
    v___x_6295_ = l_Lean_stringToMessageData(v___x_6294_);
    return v___x_6295_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6297_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__14;
    v___x_6298_ = l_Lean_stringToMessageData(v___x_6297_);
    return v___x_6298_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6300_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__16;
    v___x_6301_ = l_Lean_stringToMessageData(v___x_6300_);
    return v___x_6301_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6303_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__18;
    v___x_6304_ = l_Lean_stringToMessageData(v___x_6303_);
    return v___x_6304_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(
    mut v_msg_6305_: *mut crate::leanh::LeanObject,
    mut v_declHint_6306_: *mut crate::leanh::LeanObject,
    mut v___y_6307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6311_: u8 = 0;
    let mut v_isExporting_6312_: u8 = 0;
    let mut v___x_6313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6315_: u8 = 0;
    let mut v___x_6316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_6322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6334_: u8 = 0;
    let mut v___x_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_6338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6339_: u8 = 0;
    let mut v___x_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6366_: u8 = 0;
    let mut v___x_6367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6309_ = lean_st_ref_get(v___y_6307_);
                v_env_6310_ = crate::leanh::lean_ctor_get(v___x_6309_, 0);
                crate::leanh::lean_inc_ref(v_env_6310_);
                crate::leanh::lean_dec(v___x_6309_);
                v___x_6311_ = l_Lean_Name_isAnonymous(v_declHint_6306_);
                if v___x_6311_ == 0 {
                    v_isExporting_6312_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_6310_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_6312_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_6310_);
                        crate::leanh::lean_dec(v_declHint_6306_);
                        v___x_6313_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6313_, 0, v_msg_6305_);
                        return v___x_6313_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_6310_);
                        v___x_6314_ = l_Lean_Environment_setExporting(v_env_6310_, v___x_6311_);
                        crate::leanh::lean_inc(v_declHint_6306_);
                        crate::leanh::lean_inc_ref(v___x_6314_);
                        v___x_6315_ = l_Lean_Environment_contains(
                            v___x_6314_,
                            v_declHint_6306_,
                            v_isExporting_6312_,
                        );
                        if v___x_6315_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_6314_);
                            crate::leanh::lean_dec_ref(v_env_6310_);
                            crate::leanh::lean_dec(v_declHint_6306_);
                            v___x_6316_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6316_, 0, v_msg_6305_);
                            return v___x_6316_;
                        } else {
                            v___x_6317_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__2);
                            v___x_6318_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__5);
                            v___x_6319_ = l_Lean_Options_empty;
                            v___x_6320_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_6320_, 0, v___x_6314_);
                            crate::leanh::lean_ctor_set(v___x_6320_, 1, v___x_6317_);
                            crate::leanh::lean_ctor_set(v___x_6320_, 2, v___x_6318_);
                            crate::leanh::lean_ctor_set(v___x_6320_, 3, v___x_6319_);
                            crate::leanh::lean_inc(v_declHint_6306_);
                            v___x_6321_ =
                                l_Lean_MessageData_ofConstName(v_declHint_6306_, v___x_6311_);
                            v_c_6322_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_6322_, 0, v___x_6320_);
                            crate::leanh::lean_ctor_set(v_c_6322_, 1, v___x_6321_);
                            v___x_6323_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_6310_,
                                v_declHint_6306_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6323_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_6310_);
                                crate::leanh::lean_dec(v_declHint_6306_);
                                v___x_6324_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7);
                                v___x_6325_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6325_, 0, v___x_6324_);
                                crate::leanh::lean_ctor_set(v___x_6325_, 1, v_c_6322_);
                                v___x_6326_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__9);
                                v___x_6327_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6327_, 0, v___x_6325_);
                                crate::leanh::lean_ctor_set(v___x_6327_, 1, v___x_6326_);
                                v___x_6328_ = l_Lean_MessageData_note(v___x_6327_);
                                v___x_6329_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6329_, 0, v_msg_6305_);
                                crate::leanh::lean_ctor_set(v___x_6329_, 1, v___x_6328_);
                                v___x_6330_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6330_, 0, v___x_6329_);
                                return v___x_6330_;
                            } else {
                                v_val_6331_ = crate::leanh::lean_ctor_get(v___x_6323_, 0);
                                v_isSharedCheck_6366_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6323_)) as u8;
                                if v_isSharedCheck_6366_ == 0 {
                                    v___x_6333_ = v___x_6323_;
                                    v_isShared_6334_ = v_isSharedCheck_6366_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_6331_);
                                    crate::leanh::lean_dec(v___x_6323_);
                                    v___x_6333_ = crate::leanh::lean_box(0);
                                    v_isShared_6334_ = v_isSharedCheck_6366_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_6310_);
                    crate::leanh::lean_dec(v_declHint_6306_);
                    v___x_6367_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6367_, 0, v_msg_6305_);
                    return v___x_6367_;
                }
            }
            1 => {
                v___x_6335_ = crate::leanh::lean_box(0);
                v___x_6336_ = l_Lean_Environment_header(v_env_6310_);
                crate::leanh::lean_dec_ref(v_env_6310_);
                v___x_6337_ = l_Lean_EnvironmentHeader_moduleNames(v___x_6336_);
                v_mod_6338_ = lean_array_get(v___x_6335_, v___x_6337_, v_val_6331_);
                crate::leanh::lean_dec(v_val_6331_);
                crate::leanh::lean_dec_ref(v___x_6337_);
                v___x_6339_ = l_Lean_isPrivateName(v_declHint_6306_);
                crate::leanh::lean_dec(v_declHint_6306_);
                if v___x_6339_ == 0 {
                    v___x_6340_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__11);
                    v___x_6341_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6341_, 0, v___x_6340_);
                    crate::leanh::lean_ctor_set(v___x_6341_, 1, v_c_6322_);
                    v___x_6342_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__13);
                    v___x_6343_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6343_, 0, v___x_6341_);
                    crate::leanh::lean_ctor_set(v___x_6343_, 1, v___x_6342_);
                    v___x_6344_ = l_Lean_MessageData_ofName(v_mod_6338_);
                    v___x_6345_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6345_, 0, v___x_6343_);
                    crate::leanh::lean_ctor_set(v___x_6345_, 1, v___x_6344_);
                    v___x_6346_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__15);
                    v___x_6347_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6347_, 0, v___x_6345_);
                    crate::leanh::lean_ctor_set(v___x_6347_, 1, v___x_6346_);
                    v___x_6348_ = l_Lean_MessageData_note(v___x_6347_);
                    v___x_6349_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6349_, 0, v_msg_6305_);
                    crate::leanh::lean_ctor_set(v___x_6349_, 1, v___x_6348_);
                    if v_isShared_6334_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6333_, 0);
                        crate::leanh::lean_ctor_set(v___x_6333_, 0, v___x_6349_);
                        v___x_6351_ = v___x_6333_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6352_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6352_, 0, v___x_6349_);
                        v___x_6351_ = v_reuseFailAlloc_6352_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6353_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__7);
                    v___x_6354_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6354_, 0, v___x_6353_);
                    crate::leanh::lean_ctor_set(v___x_6354_, 1, v_c_6322_);
                    v___x_6355_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__17);
                    v___x_6356_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6356_, 0, v___x_6354_);
                    crate::leanh::lean_ctor_set(v___x_6356_, 1, v___x_6355_);
                    v___x_6357_ = l_Lean_MessageData_ofName(v_mod_6338_);
                    v___x_6358_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6358_, 0, v___x_6356_);
                    crate::leanh::lean_ctor_set(v___x_6358_, 1, v___x_6357_);
                    v___x_6359_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___closed__19);
                    v___x_6360_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6360_, 0, v___x_6358_);
                    crate::leanh::lean_ctor_set(v___x_6360_, 1, v___x_6359_);
                    v___x_6361_ = l_Lean_MessageData_note(v___x_6360_);
                    v___x_6362_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6362_, 0, v_msg_6305_);
                    crate::leanh::lean_ctor_set(v___x_6362_, 1, v___x_6361_);
                    if v_isShared_6334_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6333_, 0);
                        crate::leanh::lean_ctor_set(v___x_6333_, 0, v___x_6362_);
                        v___x_6364_ = v___x_6333_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6365_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6365_, 0, v___x_6362_);
                        v___x_6364_ = v_reuseFailAlloc_6365_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6351_;
            }
            3 => {
                return v___x_6364_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg___boxed(
    mut v_msg_6368_: *mut crate::leanh::LeanObject,
    mut v_declHint_6369_: *mut crate::leanh::LeanObject,
    mut v___y_6370_: *mut crate::leanh::LeanObject,
    mut v___y_6371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6372_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_6368_, v_declHint_6369_, v___y_6370_);
    crate::leanh::lean_dec(v___y_6370_);
    return v_res_6372_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(
    mut v_msg_6373_: *mut crate::leanh::LeanObject,
    mut v_declHint_6374_: *mut crate::leanh::LeanObject,
    mut v___y_6375_: *mut crate::leanh::LeanObject,
    mut v___y_6376_: *mut crate::leanh::LeanObject,
    mut v___y_6377_: *mut crate::leanh::LeanObject,
    mut v___y_6378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6384_: u8 = 0;
    let mut v___x_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6390_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6380_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_6373_, v_declHint_6374_, v___y_6378_);
                v_a_6381_ = crate::leanh::lean_ctor_get(v___x_6380_, 0);
                v_isSharedCheck_6390_ = (!crate::leanh::lean_is_exclusive(v___x_6380_)) as u8;
                if v_isSharedCheck_6390_ == 0 {
                    v___x_6383_ = v___x_6380_;
                    v_isShared_6384_ = v_isSharedCheck_6390_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_6381_);
                    crate::leanh::lean_dec(v___x_6380_);
                    v___x_6383_ = crate::leanh::lean_box(0);
                    v_isShared_6384_ = v_isSharedCheck_6390_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6385_ = l_Lean_unknownIdentifierMessageTag;
                v___x_6386_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6386_, 0, v___x_6385_);
                crate::leanh::lean_ctor_set(v___x_6386_, 1, v_a_6381_);
                if v_isShared_6384_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6383_, 0, v___x_6386_);
                    v___x_6388_ = v___x_6383_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6389_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6389_, 0, v___x_6386_);
                    v___x_6388_ = v_reuseFailAlloc_6389_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6388_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22___boxed(
    mut v_msg_6391_: *mut crate::leanh::LeanObject,
    mut v_declHint_6392_: *mut crate::leanh::LeanObject,
    mut v___y_6393_: *mut crate::leanh::LeanObject,
    mut v___y_6394_: *mut crate::leanh::LeanObject,
    mut v___y_6395_: *mut crate::leanh::LeanObject,
    mut v___y_6396_: *mut crate::leanh::LeanObject,
    mut v___y_6397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6398_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_6391_, v_declHint_6392_, v___y_6393_, v___y_6394_, v___y_6395_, v___y_6396_);
    crate::leanh::lean_dec(v___y_6396_);
    crate::leanh::lean_dec_ref(v___y_6395_);
    crate::leanh::lean_dec(v___y_6394_);
    crate::leanh::lean_dec_ref(v___y_6393_);
    return v_res_6398_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(
    mut v_ref_6399_: *mut crate::leanh::LeanObject,
    mut v_msg_6400_: *mut crate::leanh::LeanObject,
    mut v_declHint_6401_: *mut crate::leanh::LeanObject,
    mut v___y_6402_: *mut crate::leanh::LeanObject,
    mut v___y_6403_: *mut crate::leanh::LeanObject,
    mut v___y_6404_: *mut crate::leanh::LeanObject,
    mut v___y_6405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6407_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22(v_msg_6400_, v_declHint_6401_, v___y_6402_, v___y_6403_, v___y_6404_, v___y_6405_);
    v_a_6408_ = crate::leanh::lean_ctor_get(v___x_6407_, 0);
    crate::leanh::lean_inc(v_a_6408_);
    crate::leanh::lean_dec_ref(v___x_6407_);
    v___x_6409_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_6399_, v_a_6408_, v___y_6402_, v___y_6403_, v___y_6404_, v___y_6405_);
    return v___x_6409_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg___boxed(
    mut v_ref_6410_: *mut crate::leanh::LeanObject,
    mut v_msg_6411_: *mut crate::leanh::LeanObject,
    mut v_declHint_6412_: *mut crate::leanh::LeanObject,
    mut v___y_6413_: *mut crate::leanh::LeanObject,
    mut v___y_6414_: *mut crate::leanh::LeanObject,
    mut v___y_6415_: *mut crate::leanh::LeanObject,
    mut v___y_6416_: *mut crate::leanh::LeanObject,
    mut v___y_6417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6418_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_6410_, v_msg_6411_, v_declHint_6412_, v___y_6413_, v___y_6414_, v___y_6415_, v___y_6416_);
    crate::leanh::lean_dec(v___y_6416_);
    crate::leanh::lean_dec_ref(v___y_6415_);
    crate::leanh::lean_dec(v___y_6414_);
    crate::leanh::lean_dec_ref(v___y_6413_);
    crate::leanh::lean_dec(v_ref_6410_);
    return v_res_6418_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6420_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__0;
    v___x_6421_ = l_Lean_stringToMessageData(v___x_6420_);
    return v___x_6421_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6423_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__2;
    v___x_6424_ = l_Lean_stringToMessageData(v___x_6423_);
    return v___x_6424_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(
    mut v_ref_6425_: *mut crate::leanh::LeanObject,
    mut v_constName_6426_: *mut crate::leanh::LeanObject,
    mut v___y_6427_: *mut crate::leanh::LeanObject,
    mut v___y_6428_: *mut crate::leanh::LeanObject,
    mut v___y_6429_: *mut crate::leanh::LeanObject,
    mut v___y_6430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: u8 = 0;
    let mut v___x_6434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6432_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__1);
    v___x_6433_ = 0;
    crate::leanh::lean_inc(v_constName_6426_);
    v___x_6434_ = l_Lean_MessageData_ofConstName(v_constName_6426_, v___x_6433_);
    v___x_6435_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6435_, 0, v___x_6432_);
    crate::leanh::lean_ctor_set(v___x_6435_, 1, v___x_6434_);
    v___x_6436_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
    v___x_6437_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6437_, 0, v___x_6435_);
    crate::leanh::lean_ctor_set(v___x_6437_, 1, v___x_6436_);
    v___x_6438_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_6425_, v___x_6437_, v_constName_6426_, v___y_6427_, v___y_6428_, v___y_6429_, v___y_6430_);
    return v___x_6438_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___boxed(
    mut v_ref_6439_: *mut crate::leanh::LeanObject,
    mut v_constName_6440_: *mut crate::leanh::LeanObject,
    mut v___y_6441_: *mut crate::leanh::LeanObject,
    mut v___y_6442_: *mut crate::leanh::LeanObject,
    mut v___y_6443_: *mut crate::leanh::LeanObject,
    mut v___y_6444_: *mut crate::leanh::LeanObject,
    mut v___y_6445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6446_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_6439_, v_constName_6440_, v___y_6441_, v___y_6442_, v___y_6443_, v___y_6444_);
    crate::leanh::lean_dec(v___y_6444_);
    crate::leanh::lean_dec_ref(v___y_6443_);
    crate::leanh::lean_dec(v___y_6442_);
    crate::leanh::lean_dec_ref(v___y_6441_);
    crate::leanh::lean_dec(v_ref_6439_);
    return v_res_6446_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(
    mut v_constName_6447_: *mut crate::leanh::LeanObject,
    mut v___y_6448_: *mut crate::leanh::LeanObject,
    mut v___y_6449_: *mut crate::leanh::LeanObject,
    mut v___y_6450_: *mut crate::leanh::LeanObject,
    mut v___y_6451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_6453_ = crate::leanh::lean_ctor_get(v___y_6450_, 5);
    v___x_6454_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_6453_, v_constName_6447_, v___y_6448_, v___y_6449_, v___y_6450_, v___y_6451_);
    return v___x_6454_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg___boxed(
    mut v_constName_6455_: *mut crate::leanh::LeanObject,
    mut v___y_6456_: *mut crate::leanh::LeanObject,
    mut v___y_6457_: *mut crate::leanh::LeanObject,
    mut v___y_6458_: *mut crate::leanh::LeanObject,
    mut v___y_6459_: *mut crate::leanh::LeanObject,
    mut v___y_6460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6461_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_6455_, v___y_6456_, v___y_6457_, v___y_6458_, v___y_6459_);
    crate::leanh::lean_dec(v___y_6459_);
    crate::leanh::lean_dec_ref(v___y_6458_);
    crate::leanh::lean_dec(v___y_6457_);
    crate::leanh::lean_dec_ref(v___y_6456_);
    return v_res_6461_;
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(
    mut v_constName_6462_: *mut crate::leanh::LeanObject,
    mut v___y_6463_: *mut crate::leanh::LeanObject,
    mut v___y_6464_: *mut crate::leanh::LeanObject,
    mut v___y_6465_: *mut crate::leanh::LeanObject,
    mut v___y_6466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6470_: u8 = 0;
    let mut v___x_6471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6476_: u8 = 0;
    let mut v___x_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6468_ = lean_st_ref_get(v___y_6466_);
                v_env_6469_ = crate::leanh::lean_ctor_get(v___x_6468_, 0);
                crate::leanh::lean_inc_ref(v_env_6469_);
                crate::leanh::lean_dec(v___x_6468_);
                v___x_6470_ = 0;
                crate::leanh::lean_inc(v_constName_6462_);
                v___x_6471_ = l_Lean_Environment_findConstVal_x3f(
                    v_env_6469_,
                    v_constName_6462_,
                    v___x_6470_,
                );
                if crate::leanh::lean_obj_tag(v___x_6471_) == 0 {
                    v___x_6472_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_6462_, v___y_6463_, v___y_6464_, v___y_6465_, v___y_6466_);
                    return v___x_6472_;
                } else {
                    crate::leanh::lean_dec(v_constName_6462_);
                    v_val_6473_ = crate::leanh::lean_ctor_get(v___x_6471_, 0);
                    v_isSharedCheck_6480_ = (!crate::leanh::lean_is_exclusive(v___x_6471_)) as u8;
                    if v_isSharedCheck_6480_ == 0 {
                        v___x_6475_ = v___x_6471_;
                        v_isShared_6476_ = v_isSharedCheck_6480_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6473_);
                        crate::leanh::lean_dec(v___x_6471_);
                        v___x_6475_ = crate::leanh::lean_box(0);
                        v_isShared_6476_ = v_isSharedCheck_6480_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6476_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6475_, 0);
                    v___x_6478_ = v___x_6475_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6479_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6479_, 0, v_val_6473_);
                    v___x_6478_ = v_reuseFailAlloc_6479_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6478_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1___boxed(
    mut v_constName_6481_: *mut crate::leanh::LeanObject,
    mut v___y_6482_: *mut crate::leanh::LeanObject,
    mut v___y_6483_: *mut crate::leanh::LeanObject,
    mut v___y_6484_: *mut crate::leanh::LeanObject,
    mut v___y_6485_: *mut crate::leanh::LeanObject,
    mut v___y_6486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6487_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(
        v_constName_6481_,
        v___y_6482_,
        v___y_6483_,
        v___y_6484_,
        v___y_6485_,
    );
    crate::leanh::lean_dec(v___y_6485_);
    crate::leanh::lean_dec_ref(v___y_6484_);
    crate::leanh::lean_dec(v___y_6483_);
    crate::leanh::lean_dec_ref(v___y_6482_);
    return v_res_6487_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(
    mut v_declName_6488_: *mut crate::leanh::LeanObject,
    mut v_s_6489_: u8,
    mut v___y_6490_: *mut crate::leanh::LeanObject,
    mut v___y_6491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6504_: u8 = 0;
    let mut v___x_6505_: u8 = 0;
    let mut v___x_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6519_: u8 = 0;
    let mut v___x_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6527_: u8 = 0;
    let mut v_unused_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6530_: u8 = 0;
    let mut v_unused_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6493_ = lean_st_ref_take(v___y_6491_);
                v_env_6494_ = crate::leanh::lean_ctor_get(v___x_6493_, 0);
                v_nextMacroScope_6495_ = crate::leanh::lean_ctor_get(v___x_6493_, 1);
                v_ngen_6496_ = crate::leanh::lean_ctor_get(v___x_6493_, 2);
                v_auxDeclNGen_6497_ = crate::leanh::lean_ctor_get(v___x_6493_, 3);
                v_traceState_6498_ = crate::leanh::lean_ctor_get(v___x_6493_, 4);
                v_messages_6499_ = crate::leanh::lean_ctor_get(v___x_6493_, 6);
                v_infoState_6500_ = crate::leanh::lean_ctor_get(v___x_6493_, 7);
                v_snapshotTasks_6501_ = crate::leanh::lean_ctor_get(v___x_6493_, 8);
                v_isSharedCheck_6530_ = (!crate::leanh::lean_is_exclusive(v___x_6493_)) as u8;
                if v_isSharedCheck_6530_ == 0 {
                    v_unused_6531_ = crate::leanh::lean_ctor_get(v___x_6493_, 5);
                    crate::leanh::lean_dec(v_unused_6531_);
                    v___x_6503_ = v___x_6493_;
                    v_isShared_6504_ = v_isSharedCheck_6530_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6501_);
                    crate::leanh::lean_inc(v_infoState_6500_);
                    crate::leanh::lean_inc(v_messages_6499_);
                    crate::leanh::lean_inc(v_traceState_6498_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6497_);
                    crate::leanh::lean_inc(v_ngen_6496_);
                    crate::leanh::lean_inc(v_nextMacroScope_6495_);
                    crate::leanh::lean_inc(v_env_6494_);
                    crate::leanh::lean_dec(v___x_6493_);
                    v___x_6503_ = crate::leanh::lean_box(0);
                    v_isShared_6504_ = v_isSharedCheck_6530_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6505_ = 0;
                v___x_6506_ = crate::leanh::lean_box(0);
                v___x_6507_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(
                    v_env_6494_,
                    v_declName_6488_,
                    v_s_6489_,
                    v___x_6505_,
                    v___x_6506_,
                );
                v___x_6508_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
                if v_isShared_6504_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6503_, 5, v___x_6508_);
                    crate::leanh::lean_ctor_set(v___x_6503_, 0, v___x_6507_);
                    v___x_6510_ = v___x_6503_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6529_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6529_, 0, v___x_6507_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6529_, 1, v_nextMacroScope_6495_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6529_, 2, v_ngen_6496_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6529_, 3, v_auxDeclNGen_6497_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6529_, 4, v_traceState_6498_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6529_, 5, v___x_6508_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6529_, 6, v_messages_6499_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6529_, 7, v_infoState_6500_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6529_, 8, v_snapshotTasks_6501_);
                    v___x_6510_ = v_reuseFailAlloc_6529_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6511_ = lean_st_ref_set(v___y_6491_, v___x_6510_);
                v___x_6512_ = lean_st_ref_take(v___y_6490_);
                v_mctx_6513_ = crate::leanh::lean_ctor_get(v___x_6512_, 0);
                v_zetaDeltaFVarIds_6514_ = crate::leanh::lean_ctor_get(v___x_6512_, 2);
                v_postponed_6515_ = crate::leanh::lean_ctor_get(v___x_6512_, 3);
                v_diag_6516_ = crate::leanh::lean_ctor_get(v___x_6512_, 4);
                v_isSharedCheck_6527_ = (!crate::leanh::lean_is_exclusive(v___x_6512_)) as u8;
                if v_isSharedCheck_6527_ == 0 {
                    v_unused_6528_ = crate::leanh::lean_ctor_get(v___x_6512_, 1);
                    crate::leanh::lean_dec(v_unused_6528_);
                    v___x_6518_ = v___x_6512_;
                    v_isShared_6519_ = v_isSharedCheck_6527_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_6516_);
                    crate::leanh::lean_inc(v_postponed_6515_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_6514_);
                    crate::leanh::lean_inc(v_mctx_6513_);
                    crate::leanh::lean_dec(v___x_6512_);
                    v___x_6518_ = crate::leanh::lean_box(0);
                    v_isShared_6519_ = v_isSharedCheck_6527_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6520_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once), _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
                if v_isShared_6519_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6518_, 1, v___x_6520_);
                    v___x_6522_ = v___x_6518_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6526_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6526_, 0, v_mctx_6513_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6526_, 1, v___x_6520_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_6526_,
                        2,
                        v_zetaDeltaFVarIds_6514_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6526_, 3, v_postponed_6515_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6526_, 4, v_diag_6516_);
                    v___x_6522_ = v_reuseFailAlloc_6526_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6523_ = lean_st_ref_set(v___y_6490_, v___x_6522_);
                v___x_6524_ = crate::leanh::lean_box(0);
                v___x_6525_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6525_, 0, v___x_6524_);
                return v___x_6525_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg___boxed(
    mut v_declName_6532_: *mut crate::leanh::LeanObject,
    mut v_s_6533_: *mut crate::leanh::LeanObject,
    mut v___y_6534_: *mut crate::leanh::LeanObject,
    mut v___y_6535_: *mut crate::leanh::LeanObject,
    mut v___y_6536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_boxed_6537_: u8 = 0;
    let mut v_res_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_s_boxed_6537_ = (crate::leanh::lean_unbox(v_s_6533_) as u8);
    v_res_6538_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_6532_, v_s_boxed_6537_, v___y_6534_, v___y_6535_);
    crate::leanh::lean_dec(v___y_6535_);
    crate::leanh::lean_dec(v___y_6534_);
    return v_res_6538_;
}
pub unsafe fn l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(
    mut v_declName_6539_: *mut crate::leanh::LeanObject,
    mut v___y_6540_: *mut crate::leanh::LeanObject,
    mut v___y_6541_: *mut crate::leanh::LeanObject,
    mut v___y_6542_: *mut crate::leanh::LeanObject,
    mut v___y_6543_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6545_: u8 = 0;
    let mut v___x_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6545_ = 0;
    v___x_6546_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_6539_, v___x_6545_, v___y_6541_, v___y_6543_);
    return v___x_6546_;
}
pub unsafe fn l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13___boxed(
    mut v_declName_6547_: *mut crate::leanh::LeanObject,
    mut v___y_6548_: *mut crate::leanh::LeanObject,
    mut v___y_6549_: *mut crate::leanh::LeanObject,
    mut v___y_6550_: *mut crate::leanh::LeanObject,
    mut v___y_6551_: *mut crate::leanh::LeanObject,
    mut v___y_6552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6553_ = l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(
        v_declName_6547_,
        v___y_6548_,
        v___y_6549_,
        v___y_6550_,
        v___y_6551_,
    );
    crate::leanh::lean_dec(v___y_6551_);
    crate::leanh::lean_dec_ref(v___y_6550_);
    crate::leanh::lean_dec(v___y_6549_);
    crate::leanh::lean_dec_ref(v___y_6548_);
    return v_res_6553_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6555_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__0;
    v___x_6556_ = l_Lean_stringToMessageData(v___x_6555_);
    return v___x_6556_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6558_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__2;
    v___x_6559_ = l_Lean_stringToMessageData(v___x_6558_);
    return v___x_6559_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6561_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__4;
    v___x_6562_ = l_Lean_stringToMessageData(v___x_6561_);
    return v___x_6562_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(
    mut v_attrName_6563_: *mut crate::leanh::LeanObject,
    mut v_declName_6564_: *mut crate::leanh::LeanObject,
    mut v___y_6565_: *mut crate::leanh::LeanObject,
    mut v___y_6566_: *mut crate::leanh::LeanObject,
    mut v___y_6567_: *mut crate::leanh::LeanObject,
    mut v___y_6568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6575_: u8 = 0;
    let mut v___x_6576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6570_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once), _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
    v___x_6571_ = l_Lean_MessageData_ofName(v_attrName_6563_);
    v___x_6572_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6572_, 0, v___x_6570_);
    crate::leanh::lean_ctor_set(v___x_6572_, 1, v___x_6571_);
    v___x_6573_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once), _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
    v___x_6574_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6574_, 0, v___x_6572_);
    crate::leanh::lean_ctor_set(v___x_6574_, 1, v___x_6573_);
    v___x_6575_ = 0;
    v___x_6576_ = l_Lean_MessageData_ofConstName(v_declName_6564_, v___x_6575_);
    v___x_6577_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6577_, 0, v___x_6574_);
    crate::leanh::lean_ctor_set(v___x_6577_, 1, v___x_6576_);
    v___x_6578_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5_once), _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__5);
    v___x_6579_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_6579_, 0, v___x_6577_);
    crate::leanh::lean_ctor_set(v___x_6579_, 1, v___x_6578_);
    v___x_6580_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_6579_, v___y_6565_, v___y_6566_, v___y_6567_, v___y_6568_);
    return v___x_6580_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___boxed(
    mut v_attrName_6581_: *mut crate::leanh::LeanObject,
    mut v_declName_6582_: *mut crate::leanh::LeanObject,
    mut v___y_6583_: *mut crate::leanh::LeanObject,
    mut v___y_6584_: *mut crate::leanh::LeanObject,
    mut v___y_6585_: *mut crate::leanh::LeanObject,
    mut v___y_6586_: *mut crate::leanh::LeanObject,
    mut v___y_6587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6588_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_6581_, v_declName_6582_, v___y_6583_, v___y_6584_, v___y_6585_, v___y_6586_);
    crate::leanh::lean_dec(v___y_6586_);
    crate::leanh::lean_dec_ref(v___y_6585_);
    crate::leanh::lean_dec(v___y_6584_);
    crate::leanh::lean_dec_ref(v___y_6583_);
    return v_res_6588_;
}
pub unsafe fn _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6590_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__0;
    v___x_6591_ = l_Lean_stringToMessageData(v___x_6590_);
    return v___x_6591_;
}
pub unsafe fn _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6593_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__2;
    v___x_6594_ = l_Lean_stringToMessageData(v___x_6593_);
    return v___x_6594_;
}
pub unsafe fn l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(
    mut v_attrName_6595_: *mut crate::leanh::LeanObject,
    mut v_declName_6596_: *mut crate::leanh::LeanObject,
    mut v_asyncPrefix_x3f_6597_: *mut crate::leanh::LeanObject,
    mut v___y_6598_: *mut crate::leanh::LeanObject,
    mut v___y_6599_: *mut crate::leanh::LeanObject,
    mut v___y_6600_: *mut crate::leanh::LeanObject,
    mut v___y_6601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6610_: u8 = 0;
    let mut v___x_6611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_asyncPrefix_x3f_6597_) == 0 {
                    v___x_6617_ = l_Lean_MessageData_nil;
                    v___y_6604_ = v___x_6617_;
                    state = 1;
                    continue;
                } else {
                    v_val_6618_ = crate::leanh::lean_ctor_get(v_asyncPrefix_x3f_6597_, 0);
                    crate::leanh::lean_inc(v_val_6618_);
                    crate::leanh::lean_dec_ref_known(v_asyncPrefix_x3f_6597_, 1);
                    v___x_6619_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__3);
                    v___x_6620_ = l_Lean_MessageData_ofName(v_val_6618_);
                    v___x_6621_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6621_, 0, v___x_6619_);
                    crate::leanh::lean_ctor_set(v___x_6621_, 1, v___x_6620_);
                    v___x_6622_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg___closed__3);
                    v___x_6623_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6623_, 0, v___x_6621_);
                    crate::leanh::lean_ctor_set(v___x_6623_, 1, v___x_6622_);
                    v___y_6604_ = v___x_6623_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6605_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1_once), _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__1);
                v___x_6606_ = l_Lean_MessageData_ofName(v_attrName_6595_);
                v___x_6607_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6607_, 0, v___x_6605_);
                crate::leanh::lean_ctor_set(v___x_6607_, 1, v___x_6606_);
                v___x_6608_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3_once), _init_l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg___closed__3);
                v___x_6609_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6609_, 0, v___x_6607_);
                crate::leanh::lean_ctor_set(v___x_6609_, 1, v___x_6608_);
                v___x_6610_ = 0;
                v___x_6611_ = l_Lean_MessageData_ofConstName(v_declName_6596_, v___x_6610_);
                v___x_6612_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6612_, 0, v___x_6609_);
                crate::leanh::lean_ctor_set(v___x_6612_, 1, v___x_6611_);
                v___x_6613_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1_once), _init_l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___closed__1);
                v___x_6614_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6614_, 0, v___x_6612_);
                crate::leanh::lean_ctor_set(v___x_6614_, 1, v___x_6613_);
                v___x_6615_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6615_, 0, v___x_6614_);
                crate::leanh::lean_ctor_set(v___x_6615_, 1, v___y_6604_);
                v___x_6616_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_6615_, v___y_6598_, v___y_6599_, v___y_6600_, v___y_6601_);
                return v___x_6616_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg___boxed(
    mut v_attrName_6624_: *mut crate::leanh::LeanObject,
    mut v_declName_6625_: *mut crate::leanh::LeanObject,
    mut v_asyncPrefix_x3f_6626_: *mut crate::leanh::LeanObject,
    mut v___y_6627_: *mut crate::leanh::LeanObject,
    mut v___y_6628_: *mut crate::leanh::LeanObject,
    mut v___y_6629_: *mut crate::leanh::LeanObject,
    mut v___y_6630_: *mut crate::leanh::LeanObject,
    mut v___y_6631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6632_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_6624_, v_declName_6625_, v_asyncPrefix_x3f_6626_, v___y_6627_, v___y_6628_, v___y_6629_, v___y_6630_);
    crate::leanh::lean_dec(v___y_6630_);
    crate::leanh::lean_dec_ref(v___y_6629_);
    crate::leanh::lean_dec(v___y_6628_);
    crate::leanh::lean_dec_ref(v___y_6627_);
    return v_res_6632_;
}
pub unsafe fn l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(
    mut v_attr_6633_: *mut crate::leanh::LeanObject,
    mut v_decl_6634_: *mut crate::leanh::LeanObject,
    mut v___y_6635_: *mut crate::leanh::LeanObject,
    mut v___y_6636_: *mut crate::leanh::LeanObject,
    mut v___y_6637_: *mut crate::leanh::LeanObject,
    mut v___y_6638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_6644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_6645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6656_: u8 = 0;
    let mut v_asyncMode_6657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6670_: u8 = 0;
    let mut v___x_6671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6678_: u8 = 0;
    let mut v_unused_6679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6681_: u8 = 0;
    let mut v_unused_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_6690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_6691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attr_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_6693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: u8 = 0;
    let mut v_toAttributeImplCore_6695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_attr_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toAttributeImplCore_6701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_6702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6683_ = lean_st_ref_get(v___y_6638_);
                v_env_6684_ = crate::leanh::lean_ctor_get(v___x_6683_, 0);
                crate::leanh::lean_inc_ref(v_env_6684_);
                crate::leanh::lean_dec(v___x_6683_);
                v___x_6699_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_6684_, v_decl_6634_);
                if crate::leanh::lean_obj_tag(v___x_6699_) == 0 {
                    v___y_6686_ = v___y_6635_;
                    v___y_6687_ = v___y_6636_;
                    v___y_6688_ = v___y_6637_;
                    v___y_6689_ = v___y_6638_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_6699_, 1);
                    crate::leanh::lean_dec_ref(v_env_6684_);
                    v_attr_6700_ = crate::leanh::lean_ctor_get(v_attr_6633_, 0);
                    crate::leanh::lean_inc_ref(v_attr_6700_);
                    crate::leanh::lean_dec_ref(v_attr_6633_);
                    v_toAttributeImplCore_6701_ = crate::leanh::lean_ctor_get(v_attr_6700_, 0);
                    crate::leanh::lean_inc_ref(v_toAttributeImplCore_6701_);
                    crate::leanh::lean_dec_ref(v_attr_6700_);
                    v_name_6702_ = crate::leanh::lean_ctor_get(v_toAttributeImplCore_6701_, 1);
                    crate::leanh::lean_inc(v_name_6702_);
                    crate::leanh::lean_dec_ref(v_toAttributeImplCore_6701_);
                    v___x_6703_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_name_6702_, v_decl_6634_, v___y_6635_, v___y_6636_, v___y_6637_, v___y_6638_);
                    return v___x_6703_;
                }
            }
            1 => {
                v___x_6643_ = lean_st_ref_take(v___y_6642_);
                v_ext_6644_ = crate::leanh::lean_ctor_get(v_attr_6633_, 1);
                crate::leanh::lean_inc_ref(v_ext_6644_);
                crate::leanh::lean_dec_ref(v_attr_6633_);
                v_toEnvExtension_6645_ = crate::leanh::lean_ctor_get(v_ext_6644_, 0);
                v_env_6646_ = crate::leanh::lean_ctor_get(v___x_6643_, 0);
                v_nextMacroScope_6647_ = crate::leanh::lean_ctor_get(v___x_6643_, 1);
                v_ngen_6648_ = crate::leanh::lean_ctor_get(v___x_6643_, 2);
                v_auxDeclNGen_6649_ = crate::leanh::lean_ctor_get(v___x_6643_, 3);
                v_traceState_6650_ = crate::leanh::lean_ctor_get(v___x_6643_, 4);
                v_messages_6651_ = crate::leanh::lean_ctor_get(v___x_6643_, 6);
                v_infoState_6652_ = crate::leanh::lean_ctor_get(v___x_6643_, 7);
                v_snapshotTasks_6653_ = crate::leanh::lean_ctor_get(v___x_6643_, 8);
                v_isSharedCheck_6681_ = (!crate::leanh::lean_is_exclusive(v___x_6643_)) as u8;
                if v_isSharedCheck_6681_ == 0 {
                    v_unused_6682_ = crate::leanh::lean_ctor_get(v___x_6643_, 5);
                    crate::leanh::lean_dec(v_unused_6682_);
                    v___x_6655_ = v___x_6643_;
                    v_isShared_6656_ = v_isSharedCheck_6681_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6653_);
                    crate::leanh::lean_inc(v_infoState_6652_);
                    crate::leanh::lean_inc(v_messages_6651_);
                    crate::leanh::lean_inc(v_traceState_6650_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6649_);
                    crate::leanh::lean_inc(v_ngen_6648_);
                    crate::leanh::lean_inc(v_nextMacroScope_6647_);
                    crate::leanh::lean_inc(v_env_6646_);
                    crate::leanh::lean_dec(v___x_6643_);
                    v___x_6655_ = crate::leanh::lean_box(0);
                    v_isShared_6656_ = v_isSharedCheck_6681_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_asyncMode_6657_ = crate::leanh::lean_ctor_get(v_toEnvExtension_6645_, 2);
                crate::leanh::lean_inc(v_asyncMode_6657_);
                crate::leanh::lean_inc(v_decl_6634_);
                v___x_6658_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v_ext_6644_,
                    v_env_6646_,
                    v_decl_6634_,
                    v_asyncMode_6657_,
                    v_decl_6634_,
                );
                crate::leanh::lean_dec(v_asyncMode_6657_);
                v___x_6659_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
                if v_isShared_6656_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6655_, 5, v___x_6659_);
                    crate::leanh::lean_ctor_set(v___x_6655_, 0, v___x_6658_);
                    v___x_6661_ = v___x_6655_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6680_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6680_, 0, v___x_6658_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6680_, 1, v_nextMacroScope_6647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6680_, 2, v_ngen_6648_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6680_, 3, v_auxDeclNGen_6649_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6680_, 4, v_traceState_6650_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6680_, 5, v___x_6659_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6680_, 6, v_messages_6651_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6680_, 7, v_infoState_6652_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6680_, 8, v_snapshotTasks_6653_);
                    v___x_6661_ = v_reuseFailAlloc_6680_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6662_ = lean_st_ref_set(v___y_6642_, v___x_6661_);
                v___x_6663_ = lean_st_ref_take(v___y_6641_);
                v_mctx_6664_ = crate::leanh::lean_ctor_get(v___x_6663_, 0);
                v_zetaDeltaFVarIds_6665_ = crate::leanh::lean_ctor_get(v___x_6663_, 2);
                v_postponed_6666_ = crate::leanh::lean_ctor_get(v___x_6663_, 3);
                v_diag_6667_ = crate::leanh::lean_ctor_get(v___x_6663_, 4);
                v_isSharedCheck_6678_ = (!crate::leanh::lean_is_exclusive(v___x_6663_)) as u8;
                if v_isSharedCheck_6678_ == 0 {
                    v_unused_6679_ = crate::leanh::lean_ctor_get(v___x_6663_, 1);
                    crate::leanh::lean_dec(v_unused_6679_);
                    v___x_6669_ = v___x_6663_;
                    v_isShared_6670_ = v_isSharedCheck_6678_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_6667_);
                    crate::leanh::lean_inc(v_postponed_6666_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_6665_);
                    crate::leanh::lean_inc(v_mctx_6664_);
                    crate::leanh::lean_dec(v___x_6663_);
                    v___x_6669_ = crate::leanh::lean_box(0);
                    v_isShared_6670_ = v_isSharedCheck_6678_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_6671_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once), _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
                if v_isShared_6670_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6669_, 1, v___x_6671_);
                    v___x_6673_ = v___x_6669_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6677_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6677_, 0, v_mctx_6664_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6677_, 1, v___x_6671_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_6677_,
                        2,
                        v_zetaDeltaFVarIds_6665_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6677_, 3, v_postponed_6666_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6677_, 4, v_diag_6667_);
                    v___x_6673_ = v_reuseFailAlloc_6677_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6674_ = lean_st_ref_set(v___y_6641_, v___x_6673_);
                v___x_6675_ = crate::leanh::lean_box(0);
                v___x_6676_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6676_, 0, v___x_6675_);
                return v___x_6676_;
            }
            6 => {
                v_ext_6690_ = crate::leanh::lean_ctor_get(v_attr_6633_, 1);
                v_toEnvExtension_6691_ = crate::leanh::lean_ctor_get(v_ext_6690_, 0);
                v_attr_6692_ = crate::leanh::lean_ctor_get(v_attr_6633_, 0);
                v_asyncMode_6693_ = crate::leanh::lean_ctor_get(v_toEnvExtension_6691_, 2);
                crate::leanh::lean_inc(v_decl_6634_);
                crate::leanh::lean_inc_ref(v_env_6684_);
                v___x_6694_ = l_Lean_EnvExtension_asyncMayModify___redArg(
                    v_env_6684_,
                    v_decl_6634_,
                    v_asyncMode_6693_,
                );
                if v___x_6694_ == 0 {
                    crate::leanh::lean_inc_ref(v_attr_6692_);
                    crate::leanh::lean_dec_ref(v_attr_6633_);
                    v_toAttributeImplCore_6695_ = crate::leanh::lean_ctor_get(v_attr_6692_, 0);
                    crate::leanh::lean_inc_ref(v_toAttributeImplCore_6695_);
                    crate::leanh::lean_dec_ref(v_attr_6692_);
                    v_name_6696_ = crate::leanh::lean_ctor_get(v_toAttributeImplCore_6695_, 1);
                    crate::leanh::lean_inc(v_name_6696_);
                    crate::leanh::lean_dec_ref(v_toAttributeImplCore_6695_);
                    v___x_6697_ = l_Lean_Environment_asyncPrefix_x3f(v_env_6684_);
                    v___x_6698_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_name_6696_, v_decl_6634_, v___x_6697_, v___y_6686_, v___y_6687_, v___y_6688_, v___y_6689_);
                    return v___x_6698_;
                } else {
                    crate::leanh::lean_dec_ref(v_env_6684_);
                    v___y_6641_ = v___y_6687_;
                    v___y_6642_ = v___y_6689_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12___boxed(
    mut v_attr_6704_: *mut crate::leanh::LeanObject,
    mut v_decl_6705_: *mut crate::leanh::LeanObject,
    mut v___y_6706_: *mut crate::leanh::LeanObject,
    mut v___y_6707_: *mut crate::leanh::LeanObject,
    mut v___y_6708_: *mut crate::leanh::LeanObject,
    mut v___y_6709_: *mut crate::leanh::LeanObject,
    mut v___y_6710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6711_ = l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(
        v_attr_6704_,
        v_decl_6705_,
        v___y_6706_,
        v___y_6707_,
        v___y_6708_,
        v___y_6709_,
    );
    crate::leanh::lean_dec(v___y_6709_);
    crate::leanh::lean_dec_ref(v___y_6708_);
    crate::leanh::lean_dec(v___y_6707_);
    crate::leanh::lean_dec_ref(v___y_6706_);
    return v_res_6711_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(
    mut v_constName_6712_: *mut crate::leanh::LeanObject,
    mut v___y_6713_: *mut crate::leanh::LeanObject,
    mut v___y_6714_: *mut crate::leanh::LeanObject,
    mut v___y_6715_: *mut crate::leanh::LeanObject,
    mut v___y_6716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6720_: u8 = 0;
    let mut v___x_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6726_: u8 = 0;
    let mut v___x_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6730_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6718_ = lean_st_ref_get(v___y_6716_);
                v_env_6719_ = crate::leanh::lean_ctor_get(v___x_6718_, 0);
                crate::leanh::lean_inc_ref(v_env_6719_);
                crate::leanh::lean_dec(v___x_6718_);
                v___x_6720_ = 0;
                crate::leanh::lean_inc(v_constName_6712_);
                v___x_6721_ =
                    l_Lean_Environment_find_x3f(v_env_6719_, v_constName_6712_, v___x_6720_);
                if crate::leanh::lean_obj_tag(v___x_6721_) == 0 {
                    v___x_6722_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_6712_, v___y_6713_, v___y_6714_, v___y_6715_, v___y_6716_);
                    return v___x_6722_;
                } else {
                    crate::leanh::lean_dec(v_constName_6712_);
                    v_val_6723_ = crate::leanh::lean_ctor_get(v___x_6721_, 0);
                    v_isSharedCheck_6730_ = (!crate::leanh::lean_is_exclusive(v___x_6721_)) as u8;
                    if v_isSharedCheck_6730_ == 0 {
                        v___x_6725_ = v___x_6721_;
                        v_isShared_6726_ = v_isSharedCheck_6730_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_6723_);
                        crate::leanh::lean_dec(v___x_6721_);
                        v___x_6725_ = crate::leanh::lean_box(0);
                        v_isShared_6726_ = v_isSharedCheck_6730_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6726_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_6725_, 0);
                    v___x_6728_ = v___x_6725_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6729_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6729_, 0, v_val_6723_);
                    v___x_6728_ = v_reuseFailAlloc_6729_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6728_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0___boxed(
    mut v_constName_6731_: *mut crate::leanh::LeanObject,
    mut v___y_6732_: *mut crate::leanh::LeanObject,
    mut v___y_6733_: *mut crate::leanh::LeanObject,
    mut v___y_6734_: *mut crate::leanh::LeanObject,
    mut v___y_6735_: *mut crate::leanh::LeanObject,
    mut v___y_6736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6737_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(
        v_constName_6731_,
        v___y_6732_,
        v___y_6733_,
        v___y_6734_,
        v___y_6735_,
    );
    crate::leanh::lean_dec(v___y_6735_);
    crate::leanh::lean_dec_ref(v___y_6734_);
    crate::leanh::lean_dec(v___y_6733_);
    crate::leanh::lean_dec_ref(v___y_6732_);
    return v_res_6737_;
}
pub unsafe fn _init_l_Lean_mkCasesOnSameCtorHet___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_6741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6741_ = l_Lean_mkCasesOnSameCtorHet___closed__2;
    v___x_6742_ = crate::leanh::lean_unsigned_to_nat(58);
    v___x_6743_ = crate::leanh::lean_unsigned_to_nat(33);
    v___x_6744_ = l_Lean_mkCasesOnSameCtorHet___closed__1;
    v___x_6745_ = l_Lean_mkCasesOnSameCtorHet___closed__0;
    v___x_6746_ = l_mkPanicMessageWithDecl(
        v___x_6745_,
        v___x_6744_,
        v___x_6743_,
        v___x_6742_,
        v___x_6741_,
    );
    return v___x_6746_;
}
pub unsafe fn _init_l_Lean_mkCasesOnSameCtorHet___closed__5() -> *mut crate::leanh::LeanObject {
    let mut v___x_6748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6748_ = l_Lean_mkCasesOnSameCtorHet___closed__4;
    v___x_6749_ = crate::leanh::lean_unsigned_to_nat(60);
    v___x_6750_ = crate::leanh::lean_unsigned_to_nat(30);
    v___x_6751_ = l_Lean_mkCasesOnSameCtorHet___closed__1;
    v___x_6752_ = l_Lean_mkCasesOnSameCtorHet___closed__0;
    v___x_6753_ = l_mkPanicMessageWithDecl(
        v___x_6752_,
        v___x_6751_,
        v___x_6750_,
        v___x_6749_,
        v___x_6748_,
    );
    return v___x_6753_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtorHet(
    mut v_declName_6754_: *mut crate::leanh::LeanObject,
    mut v_indName_6755_: *mut crate::leanh::LeanObject,
    mut v_a_6756_: *mut crate::leanh::LeanObject,
    mut v_a_6757_: *mut crate::leanh::LeanObject,
    mut v_a_6758_: *mut crate::leanh::LeanObject,
    mut v_a_6759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6766_: u8 = 0;
    let mut v___x_6767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_6770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_6775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_6778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_6779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6783_: u8 = 0;
    let mut v___x_6784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6789_: u8 = 0;
    let mut v___x_6790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6802_: u8 = 0;
    let mut v___x_6803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6815_: u8 = 0;
    let mut v___x_6816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6831_: u8 = 0;
    let mut v___x_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6843_: u8 = 0;
    let mut v___x_6845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6858_: u8 = 0;
    let mut v___x_6859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6870_: u8 = 0;
    let mut v___x_6872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6885_: u8 = 0;
    let mut v___x_6886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_6891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_6892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_6893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6897_: u8 = 0;
    let mut v___x_6899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6905_: u8 = 0;
    let mut v_unused_6906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6908_: u8 = 0;
    let mut v_unused_6909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6911_: u8 = 0;
    let mut v_unused_6912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6914_: u8 = 0;
    let mut v_unused_6915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6917_: u8 = 0;
    let mut v_unused_6918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6920_: u8 = 0;
    let mut v_unused_6921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6923_: u8 = 0;
    let mut v_unused_6924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6926_: u8 = 0;
    let mut v_unused_6927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: u8 = 0;
    let mut v___x_6929_: u8 = 0;
    let mut v_a_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6933_: u8 = 0;
    let mut v___x_6935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6937_: u8 = 0;
    let mut v_reuseFailAlloc_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6944_: u8 = 0;
    let mut v___x_6946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6948_: u8 = 0;
    let mut v_isSharedCheck_6949_: u8 = 0;
    let mut v___x_6950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6955_: u8 = 0;
    let mut v___x_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6959_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_indName_6755_);
                v___x_6761_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(
                    v_indName_6755_,
                    v_a_6756_,
                    v_a_6757_,
                    v_a_6758_,
                    v_a_6759_,
                );
                if crate::leanh::lean_obj_tag(v___x_6761_) == 0 {
                    v_a_6762_ = crate::leanh::lean_ctor_get(v___x_6761_, 0);
                    crate::leanh::lean_inc(v_a_6762_);
                    crate::leanh::lean_dec_ref_known(v___x_6761_, 1);
                    if crate::leanh::lean_obj_tag(v_a_6762_) == 5 {
                        v_val_6763_ = crate::leanh::lean_ctor_get(v_a_6762_, 0);
                        v_isSharedCheck_6949_ = (!crate::leanh::lean_is_exclusive(v_a_6762_)) as u8;
                        if v_isSharedCheck_6949_ == 0 {
                            v___x_6765_ = v_a_6762_;
                            v_isShared_6766_ = v_isSharedCheck_6949_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_6763_);
                            crate::leanh::lean_dec(v_a_6762_);
                            v___x_6765_ = crate::leanh::lean_box(0);
                            v_isShared_6766_ = v_isSharedCheck_6949_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6762_);
                        crate::leanh::lean_dec(v_indName_6755_);
                        crate::leanh::lean_dec(v_declName_6754_);
                        v___x_6950_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_mkCasesOnSameCtorHet___closed__5),
                            core::ptr::addr_of_mut!(l_Lean_mkCasesOnSameCtorHet___closed__5_once),
                            _init_l_Lean_mkCasesOnSameCtorHet___closed__5,
                        );
                        v___x_6951_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(
                            v___x_6950_,
                            v_a_6756_,
                            v_a_6757_,
                            v_a_6758_,
                            v_a_6759_,
                        );
                        return v___x_6951_;
                    }
                } else {
                    crate::leanh::lean_dec(v_indName_6755_);
                    crate::leanh::lean_dec(v_declName_6754_);
                    v_a_6952_ = crate::leanh::lean_ctor_get(v___x_6761_, 0);
                    v_isSharedCheck_6959_ = (!crate::leanh::lean_is_exclusive(v___x_6761_)) as u8;
                    if v_isSharedCheck_6959_ == 0 {
                        v___x_6954_ = v___x_6761_;
                        v_isShared_6955_ = v_isSharedCheck_6959_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6952_);
                        crate::leanh::lean_dec(v___x_6761_);
                        v___x_6954_ = crate::leanh::lean_box(0);
                        v_isShared_6955_ = v_isSharedCheck_6959_;
                        state = 24;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_indName_6755_);
                v___x_6767_ = l_Lean_mkCasesOnName(v_indName_6755_);
                crate::leanh::lean_inc(v___x_6767_);
                v___x_6768_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(
                    v___x_6767_,
                    v_a_6756_,
                    v_a_6757_,
                    v_a_6758_,
                    v_a_6759_,
                );
                if crate::leanh::lean_obj_tag(v___x_6768_) == 0 {
                    v_a_6769_ = crate::leanh::lean_ctor_get(v___x_6768_, 0);
                    crate::leanh::lean_inc(v_a_6769_);
                    crate::leanh::lean_dec_ref_known(v___x_6768_, 1);
                    v_name_6770_ = crate::leanh::lean_ctor_get(v_a_6769_, 0);
                    crate::leanh::lean_inc(v_name_6770_);
                    v_levelParams_6771_ = crate::leanh::lean_ctor_get(v_a_6769_, 1);
                    crate::leanh::lean_inc_n(v_levelParams_6771_, 2);
                    v_type_6772_ = crate::leanh::lean_ctor_get(v_a_6769_, 2);
                    crate::leanh::lean_inc_ref(v_type_6772_);
                    crate::leanh::lean_dec(v_a_6769_);
                    v___x_6773_ = crate::leanh::lean_box(0);
                    v___x_6774_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(
                        v_levelParams_6771_,
                        v___x_6773_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6774_) == 1 {
                        v_head_6775_ = crate::leanh::lean_ctor_get(v___x_6774_, 0);
                        crate::leanh::lean_inc(v_head_6775_);
                        v_tail_6776_ = crate::leanh::lean_ctor_get(v___x_6774_, 1);
                        crate::leanh::lean_inc(v_tail_6776_);
                        v_numParams_6777_ = crate::leanh::lean_ctor_get(v_val_6763_, 1);
                        crate::leanh::lean_inc_n(v_numParams_6777_, 2);
                        v_numIndices_6778_ = crate::leanh::lean_ctor_get(v_val_6763_, 2);
                        crate::leanh::lean_inc(v_numIndices_6778_);
                        v_ctors_6779_ = crate::leanh::lean_ctor_get(v_val_6763_, 4);
                        crate::leanh::lean_inc(v_ctors_6779_);
                        v___f_6780_ = crate::leanh::lean_alloc_closure(
                            l_Lean_mkCasesOnSameCtorHet___lam__6___boxed as *mut core::ffi::c_void,
                            17,
                            10,
                        );
                        crate::leanh::lean_closure_set(v___f_6780_, 0, v_numIndices_6778_);
                        crate::leanh::lean_closure_set(v___f_6780_, 1, v_head_6775_);
                        crate::leanh::lean_closure_set(v___f_6780_, 2, v_ctors_6779_);
                        crate::leanh::lean_closure_set(v___f_6780_, 3, v_tail_6776_);
                        crate::leanh::lean_closure_set(v___f_6780_, 4, v_numParams_6777_);
                        crate::leanh::lean_closure_set(v___f_6780_, 5, v_indName_6755_);
                        crate::leanh::lean_closure_set(v___f_6780_, 6, v_val_6763_);
                        crate::leanh::lean_closure_set(v___f_6780_, 7, v___x_6774_);
                        crate::leanh::lean_closure_set(v___f_6780_, 8, v___x_6767_);
                        crate::leanh::lean_closure_set(v___f_6780_, 9, v_name_6770_);
                        if v_isShared_6766_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_6765_, 1);
                            crate::leanh::lean_ctor_set(v___x_6765_, 0, v_numParams_6777_);
                            v___x_6782_ = v___x_6765_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_6938_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_6938_,
                                0,
                                v_numParams_6777_,
                            );
                            v___x_6782_ = v_reuseFailAlloc_6938_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_6774_);
                        crate::leanh::lean_dec_ref(v_type_6772_);
                        crate::leanh::lean_dec(v_levelParams_6771_);
                        crate::leanh::lean_dec(v_name_6770_);
                        crate::leanh::lean_dec(v___x_6767_);
                        crate::leanh::lean_del_object(v___x_6765_);
                        crate::leanh::lean_dec_ref(v_val_6763_);
                        crate::leanh::lean_dec(v_indName_6755_);
                        crate::leanh::lean_dec(v_declName_6754_);
                        v___x_6939_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_mkCasesOnSameCtorHet___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_mkCasesOnSameCtorHet___closed__3_once),
                            _init_l_Lean_mkCasesOnSameCtorHet___closed__3,
                        );
                        v___x_6940_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(
                            v___x_6939_,
                            v_a_6756_,
                            v_a_6757_,
                            v_a_6758_,
                            v_a_6759_,
                        );
                        return v___x_6940_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_6767_);
                    crate::leanh::lean_del_object(v___x_6765_);
                    crate::leanh::lean_dec_ref(v_val_6763_);
                    crate::leanh::lean_dec(v_indName_6755_);
                    crate::leanh::lean_dec(v_declName_6754_);
                    v_a_6941_ = crate::leanh::lean_ctor_get(v___x_6768_, 0);
                    v_isSharedCheck_6948_ = (!crate::leanh::lean_is_exclusive(v___x_6768_)) as u8;
                    if v_isSharedCheck_6948_ == 0 {
                        v___x_6943_ = v___x_6768_;
                        v_isShared_6944_ = v_isSharedCheck_6948_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6941_);
                        crate::leanh::lean_dec(v___x_6768_);
                        v___x_6943_ = crate::leanh::lean_box(0);
                        v_isShared_6944_ = v_isSharedCheck_6948_;
                        state = 22;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6783_ = 0;
                v___x_6784_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_6772_, v___x_6782_, v___f_6780_, v___x_6783_, v___x_6783_, v_a_6756_, v_a_6757_, v_a_6758_, v_a_6759_);
                if crate::leanh::lean_obj_tag(v___x_6784_) == 0 {
                    v_a_6785_ = crate::leanh::lean_ctor_get(v___x_6784_, 0);
                    crate::leanh::lean_inc(v_a_6785_);
                    crate::leanh::lean_dec_ref_known(v___x_6784_, 1);
                    v___x_6786_ = crate::leanh::lean_box((v___x_6783_) as usize);
                    crate::leanh::lean_inc(v_declName_6754_);
                    v___f_6787_ = crate::leanh::lean_alloc_closure(
                        l_Lean_mkCasesOnSameCtorHet___lam__7___boxed as *mut core::ffi::c_void,
                        9,
                        4,
                    );
                    crate::leanh::lean_closure_set(v___f_6787_, 0, v_a_6785_);
                    crate::leanh::lean_closure_set(v___f_6787_, 1, v_declName_6754_);
                    crate::leanh::lean_closure_set(v___f_6787_, 2, v_levelParams_6771_);
                    crate::leanh::lean_closure_set(v___f_6787_, 3, v___x_6786_);
                    v___x_6928_ = l_Lean_isPrivateName(v_declName_6754_);
                    if v___x_6928_ == 0 {
                        v___x_6929_ = 1;
                        v___y_6789_ = v___x_6929_;
                        state = 3;
                        continue;
                    } else {
                        v___y_6789_ = v___x_6783_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_levelParams_6771_);
                    crate::leanh::lean_dec(v_declName_6754_);
                    v_a_6930_ = crate::leanh::lean_ctor_get(v___x_6784_, 0);
                    v_isSharedCheck_6937_ = (!crate::leanh::lean_is_exclusive(v___x_6784_)) as u8;
                    if v_isSharedCheck_6937_ == 0 {
                        v___x_6932_ = v___x_6784_;
                        v_isShared_6933_ = v_isSharedCheck_6937_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6930_);
                        crate::leanh::lean_dec(v___x_6784_);
                        v___x_6932_ = crate::leanh::lean_box(0);
                        v_isShared_6933_ = v_isSharedCheck_6937_;
                        state = 20;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6790_ =
                    l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(
                        v___f_6787_,
                        v___y_6789_,
                        v_a_6756_,
                        v_a_6757_,
                        v_a_6758_,
                        v_a_6759_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6790_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6790_, 1);
                    v___x_6791_ = lean_st_ref_take(v_a_6759_);
                    v_env_6792_ = crate::leanh::lean_ctor_get(v___x_6791_, 0);
                    v_nextMacroScope_6793_ = crate::leanh::lean_ctor_get(v___x_6791_, 1);
                    v_ngen_6794_ = crate::leanh::lean_ctor_get(v___x_6791_, 2);
                    v_auxDeclNGen_6795_ = crate::leanh::lean_ctor_get(v___x_6791_, 3);
                    v_traceState_6796_ = crate::leanh::lean_ctor_get(v___x_6791_, 4);
                    v_messages_6797_ = crate::leanh::lean_ctor_get(v___x_6791_, 6);
                    v_infoState_6798_ = crate::leanh::lean_ctor_get(v___x_6791_, 7);
                    v_snapshotTasks_6799_ = crate::leanh::lean_ctor_get(v___x_6791_, 8);
                    v_isSharedCheck_6926_ = (!crate::leanh::lean_is_exclusive(v___x_6791_)) as u8;
                    if v_isSharedCheck_6926_ == 0 {
                        v_unused_6927_ = crate::leanh::lean_ctor_get(v___x_6791_, 5);
                        crate::leanh::lean_dec(v_unused_6927_);
                        v___x_6801_ = v___x_6791_;
                        v_isShared_6802_ = v_isSharedCheck_6926_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snapshotTasks_6799_);
                        crate::leanh::lean_inc(v_infoState_6798_);
                        crate::leanh::lean_inc(v_messages_6797_);
                        crate::leanh::lean_inc(v_traceState_6796_);
                        crate::leanh::lean_inc(v_auxDeclNGen_6795_);
                        crate::leanh::lean_inc(v_ngen_6794_);
                        crate::leanh::lean_inc(v_nextMacroScope_6793_);
                        crate::leanh::lean_inc(v_env_6792_);
                        crate::leanh::lean_dec(v___x_6791_);
                        v___x_6801_ = crate::leanh::lean_box(0);
                        v_isShared_6802_ = v_isSharedCheck_6926_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_6754_);
                    return v___x_6790_;
                }
            }
            4 => {
                crate::leanh::lean_inc(v_declName_6754_);
                v___x_6803_ = l_Lean_Meta_markMatcherLike(v_env_6792_, v_declName_6754_);
                v___x_6804_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
                if v_isShared_6802_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6801_, 5, v___x_6804_);
                    crate::leanh::lean_ctor_set(v___x_6801_, 0, v___x_6803_);
                    v___x_6806_ = v___x_6801_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6925_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6925_, 0, v___x_6803_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6925_, 1, v_nextMacroScope_6793_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6925_, 2, v_ngen_6794_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6925_, 3, v_auxDeclNGen_6795_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6925_, 4, v_traceState_6796_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6925_, 5, v___x_6804_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6925_, 6, v_messages_6797_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6925_, 7, v_infoState_6798_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6925_, 8, v_snapshotTasks_6799_);
                    v___x_6806_ = v_reuseFailAlloc_6925_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6807_ = lean_st_ref_set(v_a_6759_, v___x_6806_);
                v___x_6808_ = lean_st_ref_take(v_a_6757_);
                v_mctx_6809_ = crate::leanh::lean_ctor_get(v___x_6808_, 0);
                v_zetaDeltaFVarIds_6810_ = crate::leanh::lean_ctor_get(v___x_6808_, 2);
                v_postponed_6811_ = crate::leanh::lean_ctor_get(v___x_6808_, 3);
                v_diag_6812_ = crate::leanh::lean_ctor_get(v___x_6808_, 4);
                v_isSharedCheck_6923_ = (!crate::leanh::lean_is_exclusive(v___x_6808_)) as u8;
                if v_isSharedCheck_6923_ == 0 {
                    v_unused_6924_ = crate::leanh::lean_ctor_get(v___x_6808_, 1);
                    crate::leanh::lean_dec(v_unused_6924_);
                    v___x_6814_ = v___x_6808_;
                    v_isShared_6815_ = v_isSharedCheck_6923_;
                    state = 6;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_6812_);
                    crate::leanh::lean_inc(v_postponed_6811_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_6810_);
                    crate::leanh::lean_inc(v_mctx_6809_);
                    crate::leanh::lean_dec(v___x_6808_);
                    v___x_6814_ = crate::leanh::lean_box(0);
                    v_isShared_6815_ = v_isSharedCheck_6923_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_6816_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once), _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
                if v_isShared_6815_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6814_, 1, v___x_6816_);
                    v___x_6818_ = v___x_6814_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6922_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6922_, 0, v_mctx_6809_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6922_, 1, v___x_6816_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_6922_,
                        2,
                        v_zetaDeltaFVarIds_6810_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6922_, 3, v_postponed_6811_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6922_, 4, v_diag_6812_);
                    v___x_6818_ = v_reuseFailAlloc_6922_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_6819_ = lean_st_ref_set(v_a_6757_, v___x_6818_);
                v___x_6820_ = lean_st_ref_take(v_a_6759_);
                v_env_6821_ = crate::leanh::lean_ctor_get(v___x_6820_, 0);
                v_nextMacroScope_6822_ = crate::leanh::lean_ctor_get(v___x_6820_, 1);
                v_ngen_6823_ = crate::leanh::lean_ctor_get(v___x_6820_, 2);
                v_auxDeclNGen_6824_ = crate::leanh::lean_ctor_get(v___x_6820_, 3);
                v_traceState_6825_ = crate::leanh::lean_ctor_get(v___x_6820_, 4);
                v_messages_6826_ = crate::leanh::lean_ctor_get(v___x_6820_, 6);
                v_infoState_6827_ = crate::leanh::lean_ctor_get(v___x_6820_, 7);
                v_snapshotTasks_6828_ = crate::leanh::lean_ctor_get(v___x_6820_, 8);
                v_isSharedCheck_6920_ = (!crate::leanh::lean_is_exclusive(v___x_6820_)) as u8;
                if v_isSharedCheck_6920_ == 0 {
                    v_unused_6921_ = crate::leanh::lean_ctor_get(v___x_6820_, 5);
                    crate::leanh::lean_dec(v_unused_6921_);
                    v___x_6830_ = v___x_6820_;
                    v_isShared_6831_ = v_isSharedCheck_6920_;
                    state = 8;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6828_);
                    crate::leanh::lean_inc(v_infoState_6827_);
                    crate::leanh::lean_inc(v_messages_6826_);
                    crate::leanh::lean_inc(v_traceState_6825_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6824_);
                    crate::leanh::lean_inc(v_ngen_6823_);
                    crate::leanh::lean_inc(v_nextMacroScope_6822_);
                    crate::leanh::lean_inc(v_env_6821_);
                    crate::leanh::lean_dec(v___x_6820_);
                    v___x_6830_ = crate::leanh::lean_box(0);
                    v_isShared_6831_ = v_isSharedCheck_6920_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                crate::leanh::lean_inc(v_declName_6754_);
                v___x_6832_ = l_Lean_markAuxRecursor(v_env_6821_, v_declName_6754_);
                if v_isShared_6831_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6830_, 5, v___x_6804_);
                    crate::leanh::lean_ctor_set(v___x_6830_, 0, v___x_6832_);
                    v___x_6834_ = v___x_6830_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6919_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6919_, 0, v___x_6832_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6919_, 1, v_nextMacroScope_6822_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6919_, 2, v_ngen_6823_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6919_, 3, v_auxDeclNGen_6824_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6919_, 4, v_traceState_6825_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6919_, 5, v___x_6804_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6919_, 6, v_messages_6826_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6919_, 7, v_infoState_6827_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6919_, 8, v_snapshotTasks_6828_);
                    v___x_6834_ = v_reuseFailAlloc_6919_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_6835_ = lean_st_ref_set(v_a_6759_, v___x_6834_);
                v___x_6836_ = lean_st_ref_take(v_a_6757_);
                v_mctx_6837_ = crate::leanh::lean_ctor_get(v___x_6836_, 0);
                v_zetaDeltaFVarIds_6838_ = crate::leanh::lean_ctor_get(v___x_6836_, 2);
                v_postponed_6839_ = crate::leanh::lean_ctor_get(v___x_6836_, 3);
                v_diag_6840_ = crate::leanh::lean_ctor_get(v___x_6836_, 4);
                v_isSharedCheck_6917_ = (!crate::leanh::lean_is_exclusive(v___x_6836_)) as u8;
                if v_isSharedCheck_6917_ == 0 {
                    v_unused_6918_ = crate::leanh::lean_ctor_get(v___x_6836_, 1);
                    crate::leanh::lean_dec(v_unused_6918_);
                    v___x_6842_ = v___x_6836_;
                    v_isShared_6843_ = v_isSharedCheck_6917_;
                    state = 10;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_6840_);
                    crate::leanh::lean_inc(v_postponed_6839_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_6838_);
                    crate::leanh::lean_inc(v_mctx_6837_);
                    crate::leanh::lean_dec(v___x_6836_);
                    v___x_6842_ = crate::leanh::lean_box(0);
                    v_isShared_6843_ = v_isSharedCheck_6917_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_6843_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6842_, 1, v___x_6816_);
                    v___x_6845_ = v___x_6842_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6916_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6916_, 0, v_mctx_6837_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6916_, 1, v___x_6816_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_6916_,
                        2,
                        v_zetaDeltaFVarIds_6838_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6916_, 3, v_postponed_6839_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6916_, 4, v_diag_6840_);
                    v___x_6845_ = v_reuseFailAlloc_6916_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_6846_ = lean_st_ref_set(v_a_6757_, v___x_6845_);
                v___x_6847_ = lean_st_ref_take(v_a_6759_);
                v_env_6848_ = crate::leanh::lean_ctor_get(v___x_6847_, 0);
                v_nextMacroScope_6849_ = crate::leanh::lean_ctor_get(v___x_6847_, 1);
                v_ngen_6850_ = crate::leanh::lean_ctor_get(v___x_6847_, 2);
                v_auxDeclNGen_6851_ = crate::leanh::lean_ctor_get(v___x_6847_, 3);
                v_traceState_6852_ = crate::leanh::lean_ctor_get(v___x_6847_, 4);
                v_messages_6853_ = crate::leanh::lean_ctor_get(v___x_6847_, 6);
                v_infoState_6854_ = crate::leanh::lean_ctor_get(v___x_6847_, 7);
                v_snapshotTasks_6855_ = crate::leanh::lean_ctor_get(v___x_6847_, 8);
                v_isSharedCheck_6914_ = (!crate::leanh::lean_is_exclusive(v___x_6847_)) as u8;
                if v_isSharedCheck_6914_ == 0 {
                    v_unused_6915_ = crate::leanh::lean_ctor_get(v___x_6847_, 5);
                    crate::leanh::lean_dec(v_unused_6915_);
                    v___x_6857_ = v___x_6847_;
                    v_isShared_6858_ = v_isSharedCheck_6914_;
                    state = 12;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6855_);
                    crate::leanh::lean_inc(v_infoState_6854_);
                    crate::leanh::lean_inc(v_messages_6853_);
                    crate::leanh::lean_inc(v_traceState_6852_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6851_);
                    crate::leanh::lean_inc(v_ngen_6850_);
                    crate::leanh::lean_inc(v_nextMacroScope_6849_);
                    crate::leanh::lean_inc(v_env_6848_);
                    crate::leanh::lean_dec(v___x_6847_);
                    v___x_6857_ = crate::leanh::lean_box(0);
                    v_isShared_6858_ = v_isSharedCheck_6914_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                crate::leanh::lean_inc(v_declName_6754_);
                v___x_6859_ = l_Lean_Meta_addToCompletionBlackList(v_env_6848_, v_declName_6754_);
                if v_isShared_6858_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6857_, 5, v___x_6804_);
                    crate::leanh::lean_ctor_set(v___x_6857_, 0, v___x_6859_);
                    v___x_6861_ = v___x_6857_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6913_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6913_, 0, v___x_6859_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6913_, 1, v_nextMacroScope_6849_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6913_, 2, v_ngen_6850_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6913_, 3, v_auxDeclNGen_6851_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6913_, 4, v_traceState_6852_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6913_, 5, v___x_6804_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6913_, 6, v_messages_6853_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6913_, 7, v_infoState_6854_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6913_, 8, v_snapshotTasks_6855_);
                    v___x_6861_ = v_reuseFailAlloc_6913_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_6862_ = lean_st_ref_set(v_a_6759_, v___x_6861_);
                v___x_6863_ = lean_st_ref_take(v_a_6757_);
                v_mctx_6864_ = crate::leanh::lean_ctor_get(v___x_6863_, 0);
                v_zetaDeltaFVarIds_6865_ = crate::leanh::lean_ctor_get(v___x_6863_, 2);
                v_postponed_6866_ = crate::leanh::lean_ctor_get(v___x_6863_, 3);
                v_diag_6867_ = crate::leanh::lean_ctor_get(v___x_6863_, 4);
                v_isSharedCheck_6911_ = (!crate::leanh::lean_is_exclusive(v___x_6863_)) as u8;
                if v_isSharedCheck_6911_ == 0 {
                    v_unused_6912_ = crate::leanh::lean_ctor_get(v___x_6863_, 1);
                    crate::leanh::lean_dec(v_unused_6912_);
                    v___x_6869_ = v___x_6863_;
                    v_isShared_6870_ = v_isSharedCheck_6911_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_6867_);
                    crate::leanh::lean_inc(v_postponed_6866_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_6865_);
                    crate::leanh::lean_inc(v_mctx_6864_);
                    crate::leanh::lean_dec(v___x_6863_);
                    v___x_6869_ = crate::leanh::lean_box(0);
                    v_isShared_6870_ = v_isSharedCheck_6911_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_6870_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6869_, 1, v___x_6816_);
                    v___x_6872_ = v___x_6869_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6910_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6910_, 0, v_mctx_6864_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6910_, 1, v___x_6816_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_6910_,
                        2,
                        v_zetaDeltaFVarIds_6865_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6910_, 3, v_postponed_6866_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6910_, 4, v_diag_6867_);
                    v___x_6872_ = v_reuseFailAlloc_6910_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_6873_ = lean_st_ref_set(v_a_6757_, v___x_6872_);
                v___x_6874_ = lean_st_ref_take(v_a_6759_);
                v_env_6875_ = crate::leanh::lean_ctor_get(v___x_6874_, 0);
                v_nextMacroScope_6876_ = crate::leanh::lean_ctor_get(v___x_6874_, 1);
                v_ngen_6877_ = crate::leanh::lean_ctor_get(v___x_6874_, 2);
                v_auxDeclNGen_6878_ = crate::leanh::lean_ctor_get(v___x_6874_, 3);
                v_traceState_6879_ = crate::leanh::lean_ctor_get(v___x_6874_, 4);
                v_messages_6880_ = crate::leanh::lean_ctor_get(v___x_6874_, 6);
                v_infoState_6881_ = crate::leanh::lean_ctor_get(v___x_6874_, 7);
                v_snapshotTasks_6882_ = crate::leanh::lean_ctor_get(v___x_6874_, 8);
                v_isSharedCheck_6908_ = (!crate::leanh::lean_is_exclusive(v___x_6874_)) as u8;
                if v_isSharedCheck_6908_ == 0 {
                    v_unused_6909_ = crate::leanh::lean_ctor_get(v___x_6874_, 5);
                    crate::leanh::lean_dec(v_unused_6909_);
                    v___x_6884_ = v___x_6874_;
                    v_isShared_6885_ = v_isSharedCheck_6908_;
                    state = 16;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_6882_);
                    crate::leanh::lean_inc(v_infoState_6881_);
                    crate::leanh::lean_inc(v_messages_6880_);
                    crate::leanh::lean_inc(v_traceState_6879_);
                    crate::leanh::lean_inc(v_auxDeclNGen_6878_);
                    crate::leanh::lean_inc(v_ngen_6877_);
                    crate::leanh::lean_inc(v_nextMacroScope_6876_);
                    crate::leanh::lean_inc(v_env_6875_);
                    crate::leanh::lean_dec(v___x_6874_);
                    v___x_6884_ = crate::leanh::lean_box(0);
                    v_isShared_6885_ = v_isSharedCheck_6908_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                crate::leanh::lean_inc(v_declName_6754_);
                v___x_6886_ = l_Lean_addProtected(v_env_6875_, v_declName_6754_);
                if v_isShared_6885_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6884_, 5, v___x_6804_);
                    crate::leanh::lean_ctor_set(v___x_6884_, 0, v___x_6886_);
                    v___x_6888_ = v___x_6884_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6907_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6907_, 0, v___x_6886_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6907_, 1, v_nextMacroScope_6876_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6907_, 2, v_ngen_6877_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6907_, 3, v_auxDeclNGen_6878_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6907_, 4, v_traceState_6879_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6907_, 5, v___x_6804_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6907_, 6, v_messages_6880_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6907_, 7, v_infoState_6881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6907_, 8, v_snapshotTasks_6882_);
                    v___x_6888_ = v_reuseFailAlloc_6907_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_6889_ = lean_st_ref_set(v_a_6759_, v___x_6888_);
                v___x_6890_ = lean_st_ref_take(v_a_6757_);
                v_mctx_6891_ = crate::leanh::lean_ctor_get(v___x_6890_, 0);
                v_zetaDeltaFVarIds_6892_ = crate::leanh::lean_ctor_get(v___x_6890_, 2);
                v_postponed_6893_ = crate::leanh::lean_ctor_get(v___x_6890_, 3);
                v_diag_6894_ = crate::leanh::lean_ctor_get(v___x_6890_, 4);
                v_isSharedCheck_6905_ = (!crate::leanh::lean_is_exclusive(v___x_6890_)) as u8;
                if v_isSharedCheck_6905_ == 0 {
                    v_unused_6906_ = crate::leanh::lean_ctor_get(v___x_6890_, 1);
                    crate::leanh::lean_dec(v_unused_6906_);
                    v___x_6896_ = v___x_6890_;
                    v_isShared_6897_ = v_isSharedCheck_6905_;
                    state = 18;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_6894_);
                    crate::leanh::lean_inc(v_postponed_6893_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_6892_);
                    crate::leanh::lean_inc(v_mctx_6891_);
                    crate::leanh::lean_dec(v___x_6890_);
                    v___x_6896_ = crate::leanh::lean_box(0);
                    v_isShared_6897_ = v_isSharedCheck_6905_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_6897_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6896_, 1, v___x_6816_);
                    v___x_6899_ = v___x_6896_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_6904_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6904_, 0, v_mctx_6891_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6904_, 1, v___x_6816_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_6904_,
                        2,
                        v_zetaDeltaFVarIds_6892_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6904_, 3, v_postponed_6893_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6904_, 4, v_diag_6894_);
                    v___x_6899_ = v_reuseFailAlloc_6904_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_6900_ = lean_st_ref_set(v_a_6757_, v___x_6899_);
                v___x_6901_ = l_Lean_Elab_Term_elabAsElim;
                crate::leanh::lean_inc(v_declName_6754_);
                v___x_6902_ =
                    l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(
                        v___x_6901_,
                        v_declName_6754_,
                        v_a_6756_,
                        v_a_6757_,
                        v_a_6758_,
                        v_a_6759_,
                    );
                if crate::leanh::lean_obj_tag(v___x_6902_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6902_, 1);
                    v___x_6903_ =
                        l_Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13(
                            v_declName_6754_,
                            v_a_6756_,
                            v_a_6757_,
                            v_a_6758_,
                            v_a_6759_,
                        );
                    return v___x_6903_;
                } else {
                    crate::leanh::lean_dec(v_declName_6754_);
                    return v___x_6902_;
                }
            }
            20 => {
                if v_isShared_6933_ == 0 {
                    v___x_6935_ = v___x_6932_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_6936_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6936_, 0, v_a_6930_);
                    v___x_6935_ = v_reuseFailAlloc_6936_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_6935_;
            }
            22 => {
                if v_isShared_6944_ == 0 {
                    v___x_6946_ = v___x_6943_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_6947_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6947_, 0, v_a_6941_);
                    v___x_6946_ = v_reuseFailAlloc_6947_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_6946_;
            }
            24 => {
                if v_isShared_6955_ == 0 {
                    v___x_6957_ = v___x_6954_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_6958_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6958_, 0, v_a_6952_);
                    v___x_6957_ = v_reuseFailAlloc_6958_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_6957_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkCasesOnSameCtorHet___boxed(
    mut v_declName_6960_: *mut crate::leanh::LeanObject,
    mut v_indName_6961_: *mut crate::leanh::LeanObject,
    mut v_a_6962_: *mut crate::leanh::LeanObject,
    mut v_a_6963_: *mut crate::leanh::LeanObject,
    mut v_a_6964_: *mut crate::leanh::LeanObject,
    mut v_a_6965_: *mut crate::leanh::LeanObject,
    mut v_a_6966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6967_ = l_Lean_mkCasesOnSameCtorHet(
        v_declName_6960_,
        v_indName_6961_,
        v_a_6962_,
        v_a_6963_,
        v_a_6964_,
        v_a_6965_,
    );
    crate::leanh::lean_dec(v_a_6965_);
    crate::leanh::lean_dec_ref(v_a_6964_);
    crate::leanh::lean_dec(v_a_6963_);
    crate::leanh::lean_dec_ref(v_a_6962_);
    return v_res_6967_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(
    mut v_00_u03b1_6968_: *mut crate::leanh::LeanObject,
    mut v_name_6969_: *mut crate::leanh::LeanObject,
    mut v_type_6970_: *mut crate::leanh::LeanObject,
    mut v_k_6971_: *mut crate::leanh::LeanObject,
    mut v___y_6972_: *mut crate::leanh::LeanObject,
    mut v___y_6973_: *mut crate::leanh::LeanObject,
    mut v___y_6974_: *mut crate::leanh::LeanObject,
    mut v___y_6975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6977_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(
        v_name_6969_,
        v_type_6970_,
        v_k_6971_,
        v___y_6972_,
        v___y_6973_,
        v___y_6974_,
        v___y_6975_,
    );
    return v___x_6977_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___boxed(
    mut v_00_u03b1_6978_: *mut crate::leanh::LeanObject,
    mut v_name_6979_: *mut crate::leanh::LeanObject,
    mut v_type_6980_: *mut crate::leanh::LeanObject,
    mut v_k_6981_: *mut crate::leanh::LeanObject,
    mut v___y_6982_: *mut crate::leanh::LeanObject,
    mut v___y_6983_: *mut crate::leanh::LeanObject,
    mut v___y_6984_: *mut crate::leanh::LeanObject,
    mut v___y_6985_: *mut crate::leanh::LeanObject,
    mut v___y_6986_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6987_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4(
        v_00_u03b1_6978_,
        v_name_6979_,
        v_type_6980_,
        v_k_6981_,
        v___y_6982_,
        v___y_6983_,
        v___y_6984_,
        v___y_6985_,
    );
    crate::leanh::lean_dec(v___y_6985_);
    crate::leanh::lean_dec_ref(v___y_6984_);
    crate::leanh::lean_dec(v___y_6983_);
    crate::leanh::lean_dec_ref(v___y_6982_);
    return v_res_6987_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(
    mut v_tail_6988_: *mut crate::leanh::LeanObject,
    mut v_params_6989_: *mut crate::leanh::LeanObject,
    mut v_alts_6990_: *mut crate::leanh::LeanObject,
    mut v___x_6991_: *mut crate::leanh::LeanObject,
    mut v_ism2_6992_: *mut crate::leanh::LeanObject,
    mut v_motive_6993_: *mut crate::leanh::LeanObject,
    mut v_val_6994_: *mut crate::leanh::LeanObject,
    mut v_indName_6995_: *mut crate::leanh::LeanObject,
    mut v___x_6996_: *mut crate::leanh::LeanObject,
    mut v___x_6997_: *mut crate::leanh::LeanObject,
    mut v___x_6998_: *mut crate::leanh::LeanObject,
    mut v_as_6999_: *mut crate::leanh::LeanObject,
    mut v_i_7000_: *mut crate::leanh::LeanObject,
    mut v_j_7001_: *mut crate::leanh::LeanObject,
    mut v_inv_7002_: *mut crate::leanh::LeanObject,
    mut v_bs_7003_: *mut crate::leanh::LeanObject,
    mut v___y_7004_: *mut crate::leanh::LeanObject,
    mut v___y_7005_: *mut crate::leanh::LeanObject,
    mut v___y_7006_: *mut crate::leanh::LeanObject,
    mut v___y_7007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7009_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg(
        v_tail_6988_,
        v_params_6989_,
        v_alts_6990_,
        v___x_6991_,
        v_ism2_6992_,
        v_motive_6993_,
        v_val_6994_,
        v_indName_6995_,
        v___x_6996_,
        v___x_6997_,
        v___x_6998_,
        v_as_6999_,
        v_i_7000_,
        v_j_7001_,
        v_bs_7003_,
        v___y_7004_,
        v___y_7005_,
        v___y_7006_,
        v___y_7007_,
    );
    return v___x_7009_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_tail_7010_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_params_7011_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_alts_7012_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_7013_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_ism2_7014_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_motive_7015_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_val_7016_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_indName_7017_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_7018_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_7019_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_7020_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_as_7021_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_i_7022_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_j_7023_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_inv_7024_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_bs_7025_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_7026_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_7027_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_7028_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_7029_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_7030_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_res_7031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7031_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5(
        v_tail_7010_,
        v_params_7011_,
        v_alts_7012_,
        v___x_7013_,
        v_ism2_7014_,
        v_motive_7015_,
        v_val_7016_,
        v_indName_7017_,
        v___x_7018_,
        v___x_7019_,
        v___x_7020_,
        v_as_7021_,
        v_i_7022_,
        v_j_7023_,
        v_inv_7024_,
        v_bs_7025_,
        v___y_7026_,
        v___y_7027_,
        v___y_7028_,
        v___y_7029_,
    );
    crate::leanh::lean_dec(v___y_7029_);
    crate::leanh::lean_dec_ref(v___y_7028_);
    crate::leanh::lean_dec(v___y_7027_);
    crate::leanh::lean_dec_ref(v___y_7026_);
    crate::leanh::lean_dec_ref(v_as_7021_);
    return v_res_7031_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(
    mut v_tail_7032_: *mut crate::leanh::LeanObject,
    mut v_params_7033_: *mut crate::leanh::LeanObject,
    mut v___x_7034_: *mut crate::leanh::LeanObject,
    mut v_motive_7035_: *mut crate::leanh::LeanObject,
    mut v_as_7036_: *mut crate::leanh::LeanObject,
    mut v_i_7037_: *mut crate::leanh::LeanObject,
    mut v_j_7038_: *mut crate::leanh::LeanObject,
    mut v_inv_7039_: *mut crate::leanh::LeanObject,
    mut v_bs_7040_: *mut crate::leanh::LeanObject,
    mut v___y_7041_: *mut crate::leanh::LeanObject,
    mut v___y_7042_: *mut crate::leanh::LeanObject,
    mut v___y_7043_: *mut crate::leanh::LeanObject,
    mut v___y_7044_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7046_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg(
        v_tail_7032_,
        v_params_7033_,
        v___x_7034_,
        v_motive_7035_,
        v_as_7036_,
        v_i_7037_,
        v_j_7038_,
        v_bs_7040_,
        v___y_7041_,
        v___y_7042_,
        v___y_7043_,
        v___y_7044_,
    );
    return v___x_7046_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___boxed(
    mut v_tail_7047_: *mut crate::leanh::LeanObject,
    mut v_params_7048_: *mut crate::leanh::LeanObject,
    mut v___x_7049_: *mut crate::leanh::LeanObject,
    mut v_motive_7050_: *mut crate::leanh::LeanObject,
    mut v_as_7051_: *mut crate::leanh::LeanObject,
    mut v_i_7052_: *mut crate::leanh::LeanObject,
    mut v_j_7053_: *mut crate::leanh::LeanObject,
    mut v_inv_7054_: *mut crate::leanh::LeanObject,
    mut v_bs_7055_: *mut crate::leanh::LeanObject,
    mut v___y_7056_: *mut crate::leanh::LeanObject,
    mut v___y_7057_: *mut crate::leanh::LeanObject,
    mut v___y_7058_: *mut crate::leanh::LeanObject,
    mut v___y_7059_: *mut crate::leanh::LeanObject,
    mut v___y_7060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7061_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6(
        v_tail_7047_,
        v_params_7048_,
        v___x_7049_,
        v_motive_7050_,
        v_as_7051_,
        v_i_7052_,
        v_j_7053_,
        v_inv_7054_,
        v_bs_7055_,
        v___y_7056_,
        v___y_7057_,
        v___y_7058_,
        v___y_7059_,
    );
    crate::leanh::lean_dec(v___y_7059_);
    crate::leanh::lean_dec_ref(v___y_7058_);
    crate::leanh::lean_dec(v___y_7057_);
    crate::leanh::lean_dec_ref(v___y_7056_);
    crate::leanh::lean_dec_ref(v_as_7051_);
    crate::leanh::lean_dec_ref(v_params_7048_);
    return v_res_7061_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(
    mut v_declName_7062_: *mut crate::leanh::LeanObject,
    mut v_s_7063_: u8,
    mut v___y_7064_: *mut crate::leanh::LeanObject,
    mut v___y_7065_: *mut crate::leanh::LeanObject,
    mut v___y_7066_: *mut crate::leanh::LeanObject,
    mut v___y_7067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7069_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___redArg(v_declName_7062_, v_s_7063_, v___y_7065_, v___y_7067_);
    return v___x_7069_;
}
pub unsafe fn l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18___boxed(
    mut v_declName_7070_: *mut crate::leanh::LeanObject,
    mut v_s_7071_: *mut crate::leanh::LeanObject,
    mut v___y_7072_: *mut crate::leanh::LeanObject,
    mut v___y_7073_: *mut crate::leanh::LeanObject,
    mut v___y_7074_: *mut crate::leanh::LeanObject,
    mut v___y_7075_: *mut crate::leanh::LeanObject,
    mut v___y_7076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_boxed_7077_: u8 = 0;
    let mut v_res_7078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_s_boxed_7077_ = (crate::leanh::lean_unbox(v_s_7071_) as u8);
    v_res_7078_ = l_Lean_setReducibilityStatus___at___00Lean_setReducibleAttribute___at___00Lean_mkCasesOnSameCtorHet_spec__13_spec__18(v_declName_7070_, v_s_boxed_7077_, v___y_7072_, v___y_7073_, v___y_7074_, v___y_7075_);
    crate::leanh::lean_dec(v___y_7075_);
    crate::leanh::lean_dec_ref(v___y_7074_);
    crate::leanh::lean_dec(v___y_7073_);
    crate::leanh::lean_dec_ref(v___y_7072_);
    return v_res_7078_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(
    mut v_00_u03b1_7079_: *mut crate::leanh::LeanObject,
    mut v_constName_7080_: *mut crate::leanh::LeanObject,
    mut v___y_7081_: *mut crate::leanh::LeanObject,
    mut v___y_7082_: *mut crate::leanh::LeanObject,
    mut v___y_7083_: *mut crate::leanh::LeanObject,
    mut v___y_7084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7086_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___redArg(v_constName_7080_, v___y_7081_, v___y_7082_, v___y_7083_, v___y_7084_);
    return v___x_7086_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0___boxed(
    mut v_00_u03b1_7087_: *mut crate::leanh::LeanObject,
    mut v_constName_7088_: *mut crate::leanh::LeanObject,
    mut v___y_7089_: *mut crate::leanh::LeanObject,
    mut v___y_7090_: *mut crate::leanh::LeanObject,
    mut v___y_7091_: *mut crate::leanh::LeanObject,
    mut v___y_7092_: *mut crate::leanh::LeanObject,
    mut v___y_7093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7094_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0(v_00_u03b1_7087_, v_constName_7088_, v___y_7089_, v___y_7090_, v___y_7091_, v___y_7092_);
    crate::leanh::lean_dec(v___y_7092_);
    crate::leanh::lean_dec_ref(v___y_7091_);
    crate::leanh::lean_dec(v___y_7090_);
    crate::leanh::lean_dec_ref(v___y_7089_);
    return v_res_7094_;
}
pub unsafe fn l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(
    mut v_00_u03b1_7095_: *mut crate::leanh::LeanObject,
    mut v_attrName_7096_: *mut crate::leanh::LeanObject,
    mut v_declName_7097_: *mut crate::leanh::LeanObject,
    mut v_asyncPrefix_x3f_7098_: *mut crate::leanh::LeanObject,
    mut v___y_7099_: *mut crate::leanh::LeanObject,
    mut v___y_7100_: *mut crate::leanh::LeanObject,
    mut v___y_7101_: *mut crate::leanh::LeanObject,
    mut v___y_7102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7104_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___redArg(v_attrName_7096_, v_declName_7097_, v_asyncPrefix_x3f_7098_, v___y_7099_, v___y_7100_, v___y_7101_, v___y_7102_);
    return v___x_7104_;
}
pub unsafe fn l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15___boxed(
    mut v_00_u03b1_7105_: *mut crate::leanh::LeanObject,
    mut v_attrName_7106_: *mut crate::leanh::LeanObject,
    mut v_declName_7107_: *mut crate::leanh::LeanObject,
    mut v_asyncPrefix_x3f_7108_: *mut crate::leanh::LeanObject,
    mut v___y_7109_: *mut crate::leanh::LeanObject,
    mut v___y_7110_: *mut crate::leanh::LeanObject,
    mut v___y_7111_: *mut crate::leanh::LeanObject,
    mut v___y_7112_: *mut crate::leanh::LeanObject,
    mut v___y_7113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7114_ = l_Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15(v_00_u03b1_7105_, v_attrName_7106_, v_declName_7107_, v_asyncPrefix_x3f_7108_, v___y_7109_, v___y_7110_, v___y_7111_, v___y_7112_);
    crate::leanh::lean_dec(v___y_7112_);
    crate::leanh::lean_dec_ref(v___y_7111_);
    crate::leanh::lean_dec(v___y_7110_);
    crate::leanh::lean_dec_ref(v___y_7109_);
    return v_res_7114_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(
    mut v_00_u03b1_7115_: *mut crate::leanh::LeanObject,
    mut v_attrName_7116_: *mut crate::leanh::LeanObject,
    mut v_declName_7117_: *mut crate::leanh::LeanObject,
    mut v___y_7118_: *mut crate::leanh::LeanObject,
    mut v___y_7119_: *mut crate::leanh::LeanObject,
    mut v___y_7120_: *mut crate::leanh::LeanObject,
    mut v___y_7121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7123_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___redArg(v_attrName_7116_, v_declName_7117_, v___y_7118_, v___y_7119_, v___y_7120_, v___y_7121_);
    return v___x_7123_;
}
pub unsafe fn l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16___boxed(
    mut v_00_u03b1_7124_: *mut crate::leanh::LeanObject,
    mut v_attrName_7125_: *mut crate::leanh::LeanObject,
    mut v_declName_7126_: *mut crate::leanh::LeanObject,
    mut v___y_7127_: *mut crate::leanh::LeanObject,
    mut v___y_7128_: *mut crate::leanh::LeanObject,
    mut v___y_7129_: *mut crate::leanh::LeanObject,
    mut v___y_7130_: *mut crate::leanh::LeanObject,
    mut v___y_7131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7132_ = l_Lean_throwAttrDeclInImportedModule___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__16(v_00_u03b1_7124_, v_attrName_7125_, v_declName_7126_, v___y_7127_, v___y_7128_, v___y_7129_, v___y_7130_);
    crate::leanh::lean_dec(v___y_7130_);
    crate::leanh::lean_dec_ref(v___y_7129_);
    crate::leanh::lean_dec(v___y_7128_);
    crate::leanh::lean_dec_ref(v___y_7127_);
    return v_res_7132_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(
    mut v_00_u03b1_7133_: *mut crate::leanh::LeanObject,
    mut v_ref_7134_: *mut crate::leanh::LeanObject,
    mut v_constName_7135_: *mut crate::leanh::LeanObject,
    mut v___y_7136_: *mut crate::leanh::LeanObject,
    mut v___y_7137_: *mut crate::leanh::LeanObject,
    mut v___y_7138_: *mut crate::leanh::LeanObject,
    mut v___y_7139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7141_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___redArg(v_ref_7134_, v_constName_7135_, v___y_7136_, v___y_7137_, v___y_7138_, v___y_7139_);
    return v___x_7141_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7___boxed(
    mut v_00_u03b1_7142_: *mut crate::leanh::LeanObject,
    mut v_ref_7143_: *mut crate::leanh::LeanObject,
    mut v_constName_7144_: *mut crate::leanh::LeanObject,
    mut v___y_7145_: *mut crate::leanh::LeanObject,
    mut v___y_7146_: *mut crate::leanh::LeanObject,
    mut v___y_7147_: *mut crate::leanh::LeanObject,
    mut v___y_7148_: *mut crate::leanh::LeanObject,
    mut v___y_7149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7150_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7(v_00_u03b1_7142_, v_ref_7143_, v_constName_7144_, v___y_7145_, v___y_7146_, v___y_7147_, v___y_7148_);
    crate::leanh::lean_dec(v___y_7148_);
    crate::leanh::lean_dec_ref(v___y_7147_);
    crate::leanh::lean_dec(v___y_7146_);
    crate::leanh::lean_dec_ref(v___y_7145_);
    crate::leanh::lean_dec(v_ref_7143_);
    return v_res_7150_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(
    mut v_00_u03b1_7151_: *mut crate::leanh::LeanObject,
    mut v_msg_7152_: *mut crate::leanh::LeanObject,
    mut v___y_7153_: *mut crate::leanh::LeanObject,
    mut v___y_7154_: *mut crate::leanh::LeanObject,
    mut v___y_7155_: *mut crate::leanh::LeanObject,
    mut v___y_7156_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7158_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v_msg_7152_, v___y_7153_, v___y_7154_, v___y_7155_, v___y_7156_);
    return v___x_7158_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___boxed(
    mut v_00_u03b1_7159_: *mut crate::leanh::LeanObject,
    mut v_msg_7160_: *mut crate::leanh::LeanObject,
    mut v___y_7161_: *mut crate::leanh::LeanObject,
    mut v___y_7162_: *mut crate::leanh::LeanObject,
    mut v___y_7163_: *mut crate::leanh::LeanObject,
    mut v___y_7164_: *mut crate::leanh::LeanObject,
    mut v___y_7165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7166_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20(v_00_u03b1_7159_, v_msg_7160_, v___y_7161_, v___y_7162_, v___y_7163_, v___y_7164_);
    crate::leanh::lean_dec(v___y_7164_);
    crate::leanh::lean_dec_ref(v___y_7163_);
    crate::leanh::lean_dec(v___y_7162_);
    crate::leanh::lean_dec_ref(v___y_7161_);
    return v_res_7166_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(
    mut v_00_u03b1_7167_: *mut crate::leanh::LeanObject,
    mut v_ref_7168_: *mut crate::leanh::LeanObject,
    mut v_msg_7169_: *mut crate::leanh::LeanObject,
    mut v_declHint_7170_: *mut crate::leanh::LeanObject,
    mut v___y_7171_: *mut crate::leanh::LeanObject,
    mut v___y_7172_: *mut crate::leanh::LeanObject,
    mut v___y_7173_: *mut crate::leanh::LeanObject,
    mut v___y_7174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7176_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___redArg(v_ref_7168_, v_msg_7169_, v_declHint_7170_, v___y_7171_, v___y_7172_, v___y_7173_, v___y_7174_);
    return v___x_7176_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17___boxed(
    mut v_00_u03b1_7177_: *mut crate::leanh::LeanObject,
    mut v_ref_7178_: *mut crate::leanh::LeanObject,
    mut v_msg_7179_: *mut crate::leanh::LeanObject,
    mut v_declHint_7180_: *mut crate::leanh::LeanObject,
    mut v___y_7181_: *mut crate::leanh::LeanObject,
    mut v___y_7182_: *mut crate::leanh::LeanObject,
    mut v___y_7183_: *mut crate::leanh::LeanObject,
    mut v___y_7184_: *mut crate::leanh::LeanObject,
    mut v___y_7185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7186_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17(v_00_u03b1_7177_, v_ref_7178_, v_msg_7179_, v_declHint_7180_, v___y_7181_, v___y_7182_, v___y_7183_, v___y_7184_);
    crate::leanh::lean_dec(v___y_7184_);
    crate::leanh::lean_dec_ref(v___y_7183_);
    crate::leanh::lean_dec(v___y_7182_);
    crate::leanh::lean_dec_ref(v___y_7181_);
    crate::leanh::lean_dec(v_ref_7178_);
    return v_res_7186_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(
    mut v_msg_7187_: *mut crate::leanh::LeanObject,
    mut v_declHint_7188_: *mut crate::leanh::LeanObject,
    mut v___y_7189_: *mut crate::leanh::LeanObject,
    mut v___y_7190_: *mut crate::leanh::LeanObject,
    mut v___y_7191_: *mut crate::leanh::LeanObject,
    mut v___y_7192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7194_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___redArg(v_msg_7187_, v_declHint_7188_, v___y_7192_);
    return v___x_7194_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27___boxed(
    mut v_msg_7195_: *mut crate::leanh::LeanObject,
    mut v_declHint_7196_: *mut crate::leanh::LeanObject,
    mut v___y_7197_: *mut crate::leanh::LeanObject,
    mut v___y_7198_: *mut crate::leanh::LeanObject,
    mut v___y_7199_: *mut crate::leanh::LeanObject,
    mut v___y_7200_: *mut crate::leanh::LeanObject,
    mut v___y_7201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7202_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__22_spec__27(v_msg_7195_, v_declHint_7196_, v___y_7197_, v___y_7198_, v___y_7199_, v___y_7200_);
    crate::leanh::lean_dec(v___y_7200_);
    crate::leanh::lean_dec_ref(v___y_7199_);
    crate::leanh::lean_dec(v___y_7198_);
    crate::leanh::lean_dec_ref(v___y_7197_);
    return v_res_7202_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(
    mut v_00_u03b1_7203_: *mut crate::leanh::LeanObject,
    mut v_ref_7204_: *mut crate::leanh::LeanObject,
    mut v_msg_7205_: *mut crate::leanh::LeanObject,
    mut v___y_7206_: *mut crate::leanh::LeanObject,
    mut v___y_7207_: *mut crate::leanh::LeanObject,
    mut v___y_7208_: *mut crate::leanh::LeanObject,
    mut v___y_7209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7211_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___redArg(v_ref_7204_, v_msg_7205_, v___y_7206_, v___y_7207_, v___y_7208_, v___y_7209_);
    return v___x_7211_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23___boxed(
    mut v_00_u03b1_7212_: *mut crate::leanh::LeanObject,
    mut v_ref_7213_: *mut crate::leanh::LeanObject,
    mut v_msg_7214_: *mut crate::leanh::LeanObject,
    mut v___y_7215_: *mut crate::leanh::LeanObject,
    mut v___y_7216_: *mut crate::leanh::LeanObject,
    mut v___y_7217_: *mut crate::leanh::LeanObject,
    mut v___y_7218_: *mut crate::leanh::LeanObject,
    mut v___y_7219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7220_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0_spec__0_spec__7_spec__17_spec__23(v_00_u03b1_7212_, v_ref_7213_, v_msg_7214_, v___y_7215_, v___y_7216_, v___y_7217_, v___y_7218_);
    crate::leanh::lean_dec(v___y_7218_);
    crate::leanh::lean_dec_ref(v___y_7217_);
    crate::leanh::lean_dec(v___y_7216_);
    crate::leanh::lean_dec_ref(v___y_7215_);
    crate::leanh::lean_dec(v_ref_7213_);
    return v_res_7220_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(
    mut v_e_7221_: *mut crate::leanh::LeanObject,
    mut v___y_7222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7224_: u8 = 0;
    let mut v___x_7225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_7227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_7233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_7234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7238_: u8 = 0;
    let mut v___x_7240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7244_: u8 = 0;
    let mut v_unused_7245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7224_ = l_Lean_Expr_hasMVar(v_e_7221_);
                if v___x_7224_ == 0 {
                    v___x_7225_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7225_, 0, v_e_7221_);
                    return v___x_7225_;
                } else {
                    v___x_7226_ = lean_st_ref_get(v___y_7222_);
                    v_mctx_7227_ = crate::leanh::lean_ctor_get(v___x_7226_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_7227_);
                    crate::leanh::lean_dec(v___x_7226_);
                    v___x_7228_ = l_Lean_instantiateMVarsCore(v_mctx_7227_, v_e_7221_);
                    v_fst_7229_ = crate::leanh::lean_ctor_get(v___x_7228_, 0);
                    crate::leanh::lean_inc(v_fst_7229_);
                    v_snd_7230_ = crate::leanh::lean_ctor_get(v___x_7228_, 1);
                    crate::leanh::lean_inc(v_snd_7230_);
                    crate::leanh::lean_dec_ref(v___x_7228_);
                    v___x_7231_ = lean_st_ref_take(v___y_7222_);
                    v_cache_7232_ = crate::leanh::lean_ctor_get(v___x_7231_, 1);
                    v_zetaDeltaFVarIds_7233_ = crate::leanh::lean_ctor_get(v___x_7231_, 2);
                    v_postponed_7234_ = crate::leanh::lean_ctor_get(v___x_7231_, 3);
                    v_diag_7235_ = crate::leanh::lean_ctor_get(v___x_7231_, 4);
                    v_isSharedCheck_7244_ = (!crate::leanh::lean_is_exclusive(v___x_7231_)) as u8;
                    if v_isSharedCheck_7244_ == 0 {
                        v_unused_7245_ = crate::leanh::lean_ctor_get(v___x_7231_, 0);
                        crate::leanh::lean_dec(v_unused_7245_);
                        v___x_7237_ = v___x_7231_;
                        v_isShared_7238_ = v_isSharedCheck_7244_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_7235_);
                        crate::leanh::lean_inc(v_postponed_7234_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_7233_);
                        crate::leanh::lean_inc(v_cache_7232_);
                        crate::leanh::lean_dec(v___x_7231_);
                        v___x_7237_ = crate::leanh::lean_box(0);
                        v_isShared_7238_ = v_isSharedCheck_7244_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7238_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7237_, 0, v_snd_7230_);
                    v___x_7240_ = v___x_7237_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7243_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7243_, 0, v_snd_7230_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7243_, 1, v_cache_7232_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_7243_,
                        2,
                        v_zetaDeltaFVarIds_7233_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7243_, 3, v_postponed_7234_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7243_, 4, v_diag_7235_);
                    v___x_7240_ = v_reuseFailAlloc_7243_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7241_ = lean_st_ref_set(v___y_7222_, v___x_7240_);
                v___x_7242_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7242_, 0, v_fst_7229_);
                return v___x_7242_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg___boxed(
    mut v_e_7246_: *mut crate::leanh::LeanObject,
    mut v___y_7247_: *mut crate::leanh::LeanObject,
    mut v___y_7248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7249_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(
        v_e_7246_,
        v___y_7247_,
    );
    crate::leanh::lean_dec(v___y_7247_);
    return v_res_7249_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(
    mut v_e_7250_: *mut crate::leanh::LeanObject,
    mut v___y_7251_: *mut crate::leanh::LeanObject,
    mut v___y_7252_: *mut crate::leanh::LeanObject,
    mut v___y_7253_: *mut crate::leanh::LeanObject,
    mut v___y_7254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7256_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(
        v_e_7250_,
        v___y_7252_,
    );
    return v___x_7256_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___boxed(
    mut v_e_7257_: *mut crate::leanh::LeanObject,
    mut v___y_7258_: *mut crate::leanh::LeanObject,
    mut v___y_7259_: *mut crate::leanh::LeanObject,
    mut v___y_7260_: *mut crate::leanh::LeanObject,
    mut v___y_7261_: *mut crate::leanh::LeanObject,
    mut v___y_7262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7263_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1(
        v_e_7257_,
        v___y_7258_,
        v___y_7259_,
        v___y_7260_,
        v___y_7261_,
    );
    crate::leanh::lean_dec(v___y_7261_);
    crate::leanh::lean_dec_ref(v___y_7260_);
    crate::leanh::lean_dec(v___y_7259_);
    crate::leanh::lean_dec_ref(v___y_7258_);
    return v_res_7263_;
}
pub unsafe fn l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(
    mut v_matcherName_7264_: *mut crate::leanh::LeanObject,
    mut v_info_7265_: *mut crate::leanh::LeanObject,
    mut v___y_7266_: *mut crate::leanh::LeanObject,
    mut v___y_7267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_7271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_7272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_7273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_7274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_7275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_7277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7280_: u8 = 0;
    let mut v___x_7281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_7287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_7288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_7289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7293_: u8 = 0;
    let mut v___x_7294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7301_: u8 = 0;
    let mut v_unused_7302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7304_: u8 = 0;
    let mut v_unused_7305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7269_ = lean_st_ref_take(v___y_7267_);
                v_env_7270_ = crate::leanh::lean_ctor_get(v___x_7269_, 0);
                v_nextMacroScope_7271_ = crate::leanh::lean_ctor_get(v___x_7269_, 1);
                v_ngen_7272_ = crate::leanh::lean_ctor_get(v___x_7269_, 2);
                v_auxDeclNGen_7273_ = crate::leanh::lean_ctor_get(v___x_7269_, 3);
                v_traceState_7274_ = crate::leanh::lean_ctor_get(v___x_7269_, 4);
                v_messages_7275_ = crate::leanh::lean_ctor_get(v___x_7269_, 6);
                v_infoState_7276_ = crate::leanh::lean_ctor_get(v___x_7269_, 7);
                v_snapshotTasks_7277_ = crate::leanh::lean_ctor_get(v___x_7269_, 8);
                v_isSharedCheck_7304_ = (!crate::leanh::lean_is_exclusive(v___x_7269_)) as u8;
                if v_isSharedCheck_7304_ == 0 {
                    v_unused_7305_ = crate::leanh::lean_ctor_get(v___x_7269_, 5);
                    crate::leanh::lean_dec(v_unused_7305_);
                    v___x_7279_ = v___x_7269_;
                    v_isShared_7280_ = v_isSharedCheck_7304_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_7277_);
                    crate::leanh::lean_inc(v_infoState_7276_);
                    crate::leanh::lean_inc(v_messages_7275_);
                    crate::leanh::lean_inc(v_traceState_7274_);
                    crate::leanh::lean_inc(v_auxDeclNGen_7273_);
                    crate::leanh::lean_inc(v_ngen_7272_);
                    crate::leanh::lean_inc(v_nextMacroScope_7271_);
                    crate::leanh::lean_inc(v_env_7270_);
                    crate::leanh::lean_dec(v___x_7269_);
                    v___x_7279_ = crate::leanh::lean_box(0);
                    v_isShared_7280_ = v_isSharedCheck_7304_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7281_ = l_Lean_Meta_Match_Extension_addMatcherInfo(
                    v_env_7270_,
                    v_matcherName_7264_,
                    v_info_7265_,
                );
                v___x_7282_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2_once), _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__2);
                if v_isShared_7280_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7279_, 5, v___x_7282_);
                    crate::leanh::lean_ctor_set(v___x_7279_, 0, v___x_7281_);
                    v___x_7284_ = v___x_7279_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7303_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7303_, 0, v___x_7281_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7303_, 1, v_nextMacroScope_7271_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7303_, 2, v_ngen_7272_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7303_, 3, v_auxDeclNGen_7273_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7303_, 4, v_traceState_7274_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7303_, 5, v___x_7282_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7303_, 6, v_messages_7275_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7303_, 7, v_infoState_7276_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7303_, 8, v_snapshotTasks_7277_);
                    v___x_7284_ = v_reuseFailAlloc_7303_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7285_ = lean_st_ref_set(v___y_7267_, v___x_7284_);
                v___x_7286_ = lean_st_ref_take(v___y_7266_);
                v_mctx_7287_ = crate::leanh::lean_ctor_get(v___x_7286_, 0);
                v_zetaDeltaFVarIds_7288_ = crate::leanh::lean_ctor_get(v___x_7286_, 2);
                v_postponed_7289_ = crate::leanh::lean_ctor_get(v___x_7286_, 3);
                v_diag_7290_ = crate::leanh::lean_ctor_get(v___x_7286_, 4);
                v_isSharedCheck_7301_ = (!crate::leanh::lean_is_exclusive(v___x_7286_)) as u8;
                if v_isSharedCheck_7301_ == 0 {
                    v_unused_7302_ = crate::leanh::lean_ctor_get(v___x_7286_, 1);
                    crate::leanh::lean_dec(v_unused_7302_);
                    v___x_7292_ = v___x_7286_;
                    v_isShared_7293_ = v_isSharedCheck_7301_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_7290_);
                    crate::leanh::lean_inc(v_postponed_7289_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_7288_);
                    crate::leanh::lean_inc(v_mctx_7287_);
                    crate::leanh::lean_dec(v___x_7286_);
                    v___x_7292_ = crate::leanh::lean_box(0);
                    v_isShared_7293_ = v_isSharedCheck_7301_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7294_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3_once), _init_l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg___closed__3);
                if v_isShared_7293_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7292_, 1, v___x_7294_);
                    v___x_7296_ = v___x_7292_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7300_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7300_, 0, v_mctx_7287_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7300_, 1, v___x_7294_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_7300_,
                        2,
                        v_zetaDeltaFVarIds_7288_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7300_, 3, v_postponed_7289_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7300_, 4, v_diag_7290_);
                    v___x_7296_ = v_reuseFailAlloc_7300_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7297_ = lean_st_ref_set(v___y_7266_, v___x_7296_);
                v___x_7298_ = crate::leanh::lean_box(0);
                v___x_7299_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7299_, 0, v___x_7298_);
                return v___x_7299_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg___boxed(
    mut v_matcherName_7306_: *mut crate::leanh::LeanObject,
    mut v_info_7307_: *mut crate::leanh::LeanObject,
    mut v___y_7308_: *mut crate::leanh::LeanObject,
    mut v___y_7309_: *mut crate::leanh::LeanObject,
    mut v___y_7310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7311_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(
        v_matcherName_7306_,
        v_info_7307_,
        v___y_7308_,
        v___y_7309_,
    );
    crate::leanh::lean_dec(v___y_7309_);
    crate::leanh::lean_dec(v___y_7308_);
    return v_res_7311_;
}
pub unsafe fn l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(
    mut v_matcherName_7312_: *mut crate::leanh::LeanObject,
    mut v_info_7313_: *mut crate::leanh::LeanObject,
    mut v___y_7314_: *mut crate::leanh::LeanObject,
    mut v___y_7315_: *mut crate::leanh::LeanObject,
    mut v___y_7316_: *mut crate::leanh::LeanObject,
    mut v___y_7317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7319_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(
        v_matcherName_7312_,
        v_info_7313_,
        v___y_7315_,
        v___y_7317_,
    );
    return v___x_7319_;
}
pub unsafe fn l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___boxed(
    mut v_matcherName_7320_: *mut crate::leanh::LeanObject,
    mut v_info_7321_: *mut crate::leanh::LeanObject,
    mut v___y_7322_: *mut crate::leanh::LeanObject,
    mut v___y_7323_: *mut crate::leanh::LeanObject,
    mut v___y_7324_: *mut crate::leanh::LeanObject,
    mut v___y_7325_: *mut crate::leanh::LeanObject,
    mut v___y_7326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7327_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3(
        v_matcherName_7320_,
        v_info_7321_,
        v___y_7322_,
        v___y_7323_,
        v___y_7324_,
        v___y_7325_,
    );
    crate::leanh::lean_dec(v___y_7325_);
    crate::leanh::lean_dec_ref(v___y_7324_);
    crate::leanh::lean_dec(v___y_7323_);
    crate::leanh::lean_dec_ref(v___y_7322_);
    return v_res_7327_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__0(
    mut v_motive_7328_: *mut crate::leanh::LeanObject,
    mut v___x_7329_: *mut crate::leanh::LeanObject,
    mut v_newEqs1_7330_: *mut crate::leanh::LeanObject,
    mut v___x_7331_: u8,
    mut v___x_7332_: u8,
    mut v___x_7333_: u8,
    mut v_ism1_x27_7334_: *mut crate::leanh::LeanObject,
    mut v_ism2_x27_7335_: *mut crate::leanh::LeanObject,
    mut v_newRefls1_7336_: *mut crate::leanh::LeanObject,
    mut v_newEqs2_7337_: *mut crate::leanh::LeanObject,
    mut v_newRefls2_7338_: *mut crate::leanh::LeanObject,
    mut v___y_7339_: *mut crate::leanh::LeanObject,
    mut v___y_7340_: *mut crate::leanh::LeanObject,
    mut v___y_7341_: *mut crate::leanh::LeanObject,
    mut v___y_7342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7353_: u8 = 0;
    let mut v___x_7354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7359_: u8 = 0;
    let mut v_a_7360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7363_: u8 = 0;
    let mut v___x_7365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7367_: u8 = 0;
    let mut v_a_7368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7371_: u8 = 0;
    let mut v___x_7373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7375_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7344_ = l_Lean_mkAppN(v_motive_7328_, v___x_7329_);
                v___x_7345_ = l_Array_append___redArg(v_newEqs1_7330_, v_newEqs2_7337_);
                v___x_7346_ = l_Lean_Meta_mkForallFVars(
                    v___x_7345_,
                    v___x_7344_,
                    v___x_7331_,
                    v___x_7332_,
                    v___x_7332_,
                    v___x_7333_,
                    v___y_7339_,
                    v___y_7340_,
                    v___y_7341_,
                    v___y_7342_,
                );
                crate::leanh::lean_dec_ref(v___x_7345_);
                if crate::leanh::lean_obj_tag(v___x_7346_) == 0 {
                    v_a_7347_ = crate::leanh::lean_ctor_get(v___x_7346_, 0);
                    crate::leanh::lean_inc(v_a_7347_);
                    crate::leanh::lean_dec_ref_known(v___x_7346_, 1);
                    v___x_7348_ = l_Array_append___redArg(v_ism1_x27_7334_, v_ism2_x27_7335_);
                    v___x_7349_ = l_Lean_Meta_mkLambdaFVars(
                        v___x_7348_,
                        v_a_7347_,
                        v___x_7331_,
                        v___x_7332_,
                        v___x_7331_,
                        v___x_7332_,
                        v___x_7333_,
                        v___y_7339_,
                        v___y_7340_,
                        v___y_7341_,
                        v___y_7342_,
                    );
                    crate::leanh::lean_dec_ref(v___x_7348_);
                    if crate::leanh::lean_obj_tag(v___x_7349_) == 0 {
                        v_a_7350_ = crate::leanh::lean_ctor_get(v___x_7349_, 0);
                        v_isSharedCheck_7359_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7349_)) as u8;
                        if v_isSharedCheck_7359_ == 0 {
                            v___x_7352_ = v___x_7349_;
                            v_isShared_7353_ = v_isSharedCheck_7359_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7350_);
                            crate::leanh::lean_dec(v___x_7349_);
                            v___x_7352_ = crate::leanh::lean_box(0);
                            v_isShared_7353_ = v_isSharedCheck_7359_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_newRefls1_7336_);
                        v_a_7360_ = crate::leanh::lean_ctor_get(v___x_7349_, 0);
                        v_isSharedCheck_7367_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7349_)) as u8;
                        if v_isSharedCheck_7367_ == 0 {
                            v___x_7362_ = v___x_7349_;
                            v_isShared_7363_ = v_isSharedCheck_7367_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7360_);
                            crate::leanh::lean_dec(v___x_7349_);
                            v___x_7362_ = crate::leanh::lean_box(0);
                            v_isShared_7363_ = v_isSharedCheck_7367_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_newRefls1_7336_);
                    crate::leanh::lean_dec_ref(v_ism1_x27_7334_);
                    v_a_7368_ = crate::leanh::lean_ctor_get(v___x_7346_, 0);
                    v_isSharedCheck_7375_ = (!crate::leanh::lean_is_exclusive(v___x_7346_)) as u8;
                    if v_isSharedCheck_7375_ == 0 {
                        v___x_7370_ = v___x_7346_;
                        v_isShared_7371_ = v_isSharedCheck_7375_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7368_);
                        crate::leanh::lean_dec(v___x_7346_);
                        v___x_7370_ = crate::leanh::lean_box(0);
                        v_isShared_7371_ = v_isSharedCheck_7375_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7354_ = l_Array_append___redArg(v_newRefls1_7336_, v_newRefls2_7338_);
                v___x_7355_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7355_, 0, v_a_7350_);
                crate::leanh::lean_ctor_set(v___x_7355_, 1, v___x_7354_);
                if v_isShared_7353_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7352_, 0, v___x_7355_);
                    v___x_7357_ = v___x_7352_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7358_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7358_, 0, v___x_7355_);
                    v___x_7357_ = v_reuseFailAlloc_7358_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7357_;
            }
            3 => {
                if v_isShared_7363_ == 0 {
                    v___x_7365_ = v___x_7362_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7366_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7366_, 0, v_a_7360_);
                    v___x_7365_ = v_reuseFailAlloc_7366_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7365_;
            }
            5 => {
                if v_isShared_7371_ == 0 {
                    v___x_7373_ = v___x_7370_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7374_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7374_, 0, v_a_7368_);
                    v___x_7373_ = v_reuseFailAlloc_7374_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7373_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__0___boxed(
    mut v_motive_7376_: *mut crate::leanh::LeanObject,
    mut v___x_7377_: *mut crate::leanh::LeanObject,
    mut v_newEqs1_7378_: *mut crate::leanh::LeanObject,
    mut v___x_7379_: *mut crate::leanh::LeanObject,
    mut v___x_7380_: *mut crate::leanh::LeanObject,
    mut v___x_7381_: *mut crate::leanh::LeanObject,
    mut v_ism1_x27_7382_: *mut crate::leanh::LeanObject,
    mut v_ism2_x27_7383_: *mut crate::leanh::LeanObject,
    mut v_newRefls1_7384_: *mut crate::leanh::LeanObject,
    mut v_newEqs2_7385_: *mut crate::leanh::LeanObject,
    mut v_newRefls2_7386_: *mut crate::leanh::LeanObject,
    mut v___y_7387_: *mut crate::leanh::LeanObject,
    mut v___y_7388_: *mut crate::leanh::LeanObject,
    mut v___y_7389_: *mut crate::leanh::LeanObject,
    mut v___y_7390_: *mut crate::leanh::LeanObject,
    mut v___y_7391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_15221__boxed_7392_: u8 = 0;
    let mut v___x_15222__boxed_7393_: u8 = 0;
    let mut v___x_15223__boxed_7394_: u8 = 0;
    let mut v_res_7395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_15221__boxed_7392_ = (crate::leanh::lean_unbox(v___x_7379_) as u8);
    v___x_15222__boxed_7393_ = (crate::leanh::lean_unbox(v___x_7380_) as u8);
    v___x_15223__boxed_7394_ = (crate::leanh::lean_unbox(v___x_7381_) as u8);
    v_res_7395_ = l_Lean_mkCasesOnSameCtor___lam__0(
        v_motive_7376_,
        v___x_7377_,
        v_newEqs1_7378_,
        v___x_15221__boxed_7392_,
        v___x_15222__boxed_7393_,
        v___x_15223__boxed_7394_,
        v_ism1_x27_7382_,
        v_ism2_x27_7383_,
        v_newRefls1_7384_,
        v_newEqs2_7385_,
        v_newRefls2_7386_,
        v___y_7387_,
        v___y_7388_,
        v___y_7389_,
        v___y_7390_,
    );
    crate::leanh::lean_dec(v___y_7390_);
    crate::leanh::lean_dec_ref(v___y_7389_);
    crate::leanh::lean_dec(v___y_7388_);
    crate::leanh::lean_dec_ref(v___y_7387_);
    crate::leanh::lean_dec_ref(v_newRefls2_7386_);
    crate::leanh::lean_dec_ref(v_newEqs2_7385_);
    crate::leanh::lean_dec_ref(v_ism2_x27_7383_);
    crate::leanh::lean_dec_ref(v___x_7377_);
    return v_res_7395_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__1(
    mut v_motive_7396_: *mut crate::leanh::LeanObject,
    mut v___x_7397_: *mut crate::leanh::LeanObject,
    mut v___x_7398_: u8,
    mut v___x_7399_: u8,
    mut v___x_7400_: u8,
    mut v_ism1_x27_7401_: *mut crate::leanh::LeanObject,
    mut v_ism2_x27_7402_: *mut crate::leanh::LeanObject,
    mut v_is_7403_: *mut crate::leanh::LeanObject,
    mut v___x_7404_: *mut crate::leanh::LeanObject,
    mut v_newEqs1_7405_: *mut crate::leanh::LeanObject,
    mut v_newRefls1_7406_: *mut crate::leanh::LeanObject,
    mut v___y_7407_: *mut crate::leanh::LeanObject,
    mut v___y_7408_: *mut crate::leanh::LeanObject,
    mut v___y_7409_: *mut crate::leanh::LeanObject,
    mut v___y_7410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7412_ = crate::leanh::lean_box((v___x_7398_) as usize);
    v___x_7413_ = crate::leanh::lean_box((v___x_7399_) as usize);
    v___x_7414_ = crate::leanh::lean_box((v___x_7400_) as usize);
    crate::leanh::lean_inc_ref(v_ism2_x27_7402_);
    v___f_7415_ = crate::leanh::lean_alloc_closure(
        l_Lean_mkCasesOnSameCtor___lam__0___boxed as *mut core::ffi::c_void,
        16,
        9,
    );
    crate::leanh::lean_closure_set(v___f_7415_, 0, v_motive_7396_);
    crate::leanh::lean_closure_set(v___f_7415_, 1, v___x_7397_);
    crate::leanh::lean_closure_set(v___f_7415_, 2, v_newEqs1_7405_);
    crate::leanh::lean_closure_set(v___f_7415_, 3, v___x_7412_);
    crate::leanh::lean_closure_set(v___f_7415_, 4, v___x_7413_);
    crate::leanh::lean_closure_set(v___f_7415_, 5, v___x_7414_);
    crate::leanh::lean_closure_set(v___f_7415_, 6, v_ism1_x27_7401_);
    crate::leanh::lean_closure_set(v___f_7415_, 7, v_ism2_x27_7402_);
    crate::leanh::lean_closure_set(v___f_7415_, 8, v_newRefls1_7406_);
    v___x_7416_ = lean_array_push(v_is_7403_, v___x_7404_);
    v___x_7417_ = l_Lean_Meta_withNewEqs___redArg(
        v___x_7416_,
        v_ism2_x27_7402_,
        v___f_7415_,
        v___y_7407_,
        v___y_7408_,
        v___y_7409_,
        v___y_7410_,
    );
    return v___x_7417_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__1___boxed(
    mut v_motive_7418_: *mut crate::leanh::LeanObject,
    mut v___x_7419_: *mut crate::leanh::LeanObject,
    mut v___x_7420_: *mut crate::leanh::LeanObject,
    mut v___x_7421_: *mut crate::leanh::LeanObject,
    mut v___x_7422_: *mut crate::leanh::LeanObject,
    mut v_ism1_x27_7423_: *mut crate::leanh::LeanObject,
    mut v_ism2_x27_7424_: *mut crate::leanh::LeanObject,
    mut v_is_7425_: *mut crate::leanh::LeanObject,
    mut v___x_7426_: *mut crate::leanh::LeanObject,
    mut v_newEqs1_7427_: *mut crate::leanh::LeanObject,
    mut v_newRefls1_7428_: *mut crate::leanh::LeanObject,
    mut v___y_7429_: *mut crate::leanh::LeanObject,
    mut v___y_7430_: *mut crate::leanh::LeanObject,
    mut v___y_7431_: *mut crate::leanh::LeanObject,
    mut v___y_7432_: *mut crate::leanh::LeanObject,
    mut v___y_7433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_15312__boxed_7434_: u8 = 0;
    let mut v___x_15313__boxed_7435_: u8 = 0;
    let mut v___x_15314__boxed_7436_: u8 = 0;
    let mut v_res_7437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_15312__boxed_7434_ = (crate::leanh::lean_unbox(v___x_7420_) as u8);
    v___x_15313__boxed_7435_ = (crate::leanh::lean_unbox(v___x_7421_) as u8);
    v___x_15314__boxed_7436_ = (crate::leanh::lean_unbox(v___x_7422_) as u8);
    v_res_7437_ = l_Lean_mkCasesOnSameCtor___lam__1(
        v_motive_7418_,
        v___x_7419_,
        v___x_15312__boxed_7434_,
        v___x_15313__boxed_7435_,
        v___x_15314__boxed_7436_,
        v_ism1_x27_7423_,
        v_ism2_x27_7424_,
        v_is_7425_,
        v___x_7426_,
        v_newEqs1_7427_,
        v_newRefls1_7428_,
        v___y_7429_,
        v___y_7430_,
        v___y_7431_,
        v___y_7432_,
    );
    crate::leanh::lean_dec(v___y_7432_);
    crate::leanh::lean_dec_ref(v___y_7431_);
    crate::leanh::lean_dec(v___y_7430_);
    crate::leanh::lean_dec_ref(v___y_7429_);
    return v_res_7437_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__2(
    mut v___x_7438_: *mut crate::leanh::LeanObject,
    mut v___x_7439_: u8,
    mut v___y_7440_: *mut crate::leanh::LeanObject,
    mut v___y_7441_: *mut crate::leanh::LeanObject,
    mut v___y_7442_: *mut crate::leanh::LeanObject,
    mut v___y_7443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7445_ = l_Lean_addDecl(v___x_7438_, v___x_7439_, v___y_7442_, v___y_7443_);
    return v___x_7445_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__2___boxed(
    mut v___x_7446_: *mut crate::leanh::LeanObject,
    mut v___x_7447_: *mut crate::leanh::LeanObject,
    mut v___y_7448_: *mut crate::leanh::LeanObject,
    mut v___y_7449_: *mut crate::leanh::LeanObject,
    mut v___y_7450_: *mut crate::leanh::LeanObject,
    mut v___y_7451_: *mut crate::leanh::LeanObject,
    mut v___y_7452_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_15354__boxed_7453_: u8 = 0;
    let mut v_res_7454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_15354__boxed_7453_ = (crate::leanh::lean_unbox(v___x_7447_) as u8);
    v_res_7454_ = l_Lean_mkCasesOnSameCtor___lam__2(
        v___x_7446_,
        v___x_15354__boxed_7453_,
        v___y_7448_,
        v___y_7449_,
        v___y_7450_,
        v___y_7451_,
    );
    crate::leanh::lean_dec(v___y_7451_);
    crate::leanh::lean_dec_ref(v___y_7450_);
    crate::leanh::lean_dec(v___y_7449_);
    crate::leanh::lean_dec_ref(v___y_7448_);
    return v_res_7454_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7456_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__0;
    v___x_7457_ = l_Lean_stringToMessageData(v___x_7456_);
    return v___x_7457_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7459_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__2;
    v___x_7460_ = l_Lean_stringToMessageData(v___x_7459_);
    return v___x_7460_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7466_ = crate::leanh::lean_box(0);
    v___x_7467_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__6;
    v___x_7468_ = l_Lean_mkConst(v___x_7467_, v___x_7466_);
    return v___x_7468_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7470_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__8;
    v___x_7471_ = l_Lean_stringToMessageData(v___x_7470_);
    return v___x_7471_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(
    mut v___x_7472_: *mut crate::leanh::LeanObject,
    mut v_a_7473_: *mut crate::leanh::LeanObject,
    mut v_j_7474_: *mut crate::leanh::LeanObject,
    mut v_zs1_7475_: *mut crate::leanh::LeanObject,
    mut v_snd_7476_: *mut crate::leanh::LeanObject,
    mut v___x_7477_: u8,
    mut v_isZero_7478_: u8,
    mut v___x_7479_: u8,
    mut v_alts_7480_: *mut crate::leanh::LeanObject,
    mut v_zs2_7481_: *mut crate::leanh::LeanObject,
    mut v___ctorRet2_7482_: *mut crate::leanh::LeanObject,
    mut v___y_7483_: *mut crate::leanh::LeanObject,
    mut v___y_7484_: *mut crate::leanh::LeanObject,
    mut v___y_7485_: *mut crate::leanh::LeanObject,
    mut v___y_7486_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7504_: u8 = 0;
    let mut v_fst_7505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7508_: u8 = 0;
    let mut v___y_7510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7511_: u8 = 0;
    let mut v___x_7512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7533_: u8 = 0;
    let mut v___x_7535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7537_: u8 = 0;
    let mut v___x_7538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7541_: u8 = 0;
    let mut v___x_7542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7543_: u8 = 0;
    let mut v___x_7544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7546_: u8 = 0;
    let mut v_unused_7547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7548_: u8 = 0;
    let mut v___x_7549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7554_: u8 = 0;
    let mut v___x_7556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7558_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7488_ = lean_array_get_borrowed(v___x_7472_, v_a_7473_, v_j_7474_);
                crate::leanh::lean_inc_ref(v_zs1_7475_);
                v___x_7489_ = l_Array_append___redArg(v_zs1_7475_, v_zs2_7481_);
                crate::leanh::lean_inc(v___x_7488_);
                v___x_7490_ = l_Lean_Meta_instantiateForall(
                    v___x_7488_,
                    v___x_7489_,
                    v___y_7483_,
                    v___y_7484_,
                    v___y_7485_,
                    v___y_7486_,
                );
                if crate::leanh::lean_obj_tag(v___x_7490_) == 0 {
                    v_a_7491_ = crate::leanh::lean_ctor_get(v___x_7490_, 0);
                    crate::leanh::lean_inc(v_a_7491_);
                    crate::leanh::lean_dec_ref_known(v___x_7490_, 1);
                    v___x_7492_ = crate::leanh::lean_box(0);
                    v___x_7493_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                        v_a_7491_,
                        v___x_7492_,
                        v___y_7483_,
                        v___y_7484_,
                        v___y_7485_,
                        v___y_7486_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7493_) == 0 {
                        v_a_7494_ = crate::leanh::lean_ctor_get(v___x_7493_, 0);
                        crate::leanh::lean_inc(v_a_7494_);
                        crate::leanh::lean_dec_ref_known(v___x_7493_, 1);
                        v___x_7495_ = l_Lean_Expr_mvarId_x21(v_a_7494_);
                        v___x_7496_ = lean_array_get_size(v_snd_7476_);
                        v___x_7497_ = crate::leanh::lean_box(0);
                        v___x_7498_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc_ref(v___y_7485_);
                        v___x_7499_ = l_Lean_Meta_Cases_unifyEqs_x3f(
                            v___x_7496_,
                            v___x_7495_,
                            v___x_7497_,
                            v___x_7498_,
                            v___y_7483_,
                            v___y_7484_,
                            v___y_7485_,
                            v___y_7486_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_7499_) == 0 {
                            v_a_7500_ = crate::leanh::lean_ctor_get(v___x_7499_, 0);
                            crate::leanh::lean_inc(v_a_7500_);
                            crate::leanh::lean_dec_ref_known(v___x_7499_, 1);
                            if crate::leanh::lean_obj_tag(v_a_7500_) == 1 {
                                v_val_7501_ = crate::leanh::lean_ctor_get(v_a_7500_, 0);
                                v_isSharedCheck_7548_ =
                                    (!crate::leanh::lean_is_exclusive(v_a_7500_)) as u8;
                                if v_isSharedCheck_7548_ == 0 {
                                    v___x_7503_ = v_a_7500_;
                                    v_isShared_7504_ = v_isSharedCheck_7548_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_7501_);
                                    crate::leanh::lean_dec(v_a_7500_);
                                    v___x_7503_ = crate::leanh::lean_box(0);
                                    v_isShared_7504_ = v_isSharedCheck_7548_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_7500_);
                                crate::leanh::lean_dec(v_a_7494_);
                                crate::leanh::lean_dec_ref(v___x_7489_);
                                crate::leanh::lean_dec_ref(v_zs1_7475_);
                                v___x_7549_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9_once), _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__9);
                                v___x_7550_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_7549_, v___y_7483_, v___y_7484_, v___y_7485_, v___y_7486_);
                                return v___x_7550_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_7494_);
                            crate::leanh::lean_dec_ref(v___x_7489_);
                            crate::leanh::lean_dec_ref(v_zs1_7475_);
                            v_a_7551_ = crate::leanh::lean_ctor_get(v___x_7499_, 0);
                            v_isSharedCheck_7558_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7499_)) as u8;
                            if v_isSharedCheck_7558_ == 0 {
                                v___x_7553_ = v___x_7499_;
                                v_isShared_7554_ = v_isSharedCheck_7558_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7551_);
                                crate::leanh::lean_dec(v___x_7499_);
                                v___x_7553_ = crate::leanh::lean_box(0);
                                v_isShared_7554_ = v_isSharedCheck_7558_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_7489_);
                        crate::leanh::lean_dec_ref(v_zs1_7475_);
                        return v___x_7493_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_7489_);
                    crate::leanh::lean_dec_ref(v_zs1_7475_);
                    return v___x_7490_;
                }
            }
            1 => {
                v_fst_7505_ = crate::leanh::lean_ctor_get(v_val_7501_, 0);
                v_isSharedCheck_7546_ = (!crate::leanh::lean_is_exclusive(v_val_7501_)) as u8;
                if v_isSharedCheck_7546_ == 0 {
                    v_unused_7547_ = crate::leanh::lean_ctor_get(v_val_7501_, 1);
                    crate::leanh::lean_dec(v_unused_7547_);
                    v___x_7507_ = v_val_7501_;
                    v_isShared_7508_ = v_isSharedCheck_7546_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_7505_);
                    crate::leanh::lean_dec(v_val_7501_);
                    v___x_7507_ = crate::leanh::lean_box(0);
                    v_isShared_7508_ = v_isSharedCheck_7546_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7538_ = lean_array_get_borrowed(v___x_7472_, v_alts_7480_, v_j_7474_);
                v___x_7539_ = lean_array_get_size(v_zs1_7475_);
                crate::leanh::lean_dec_ref(v_zs1_7475_);
                v___x_7540_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7541_ = lean_nat_dec_eq(v___x_7539_, v___x_7540_);
                if v___x_7541_ == 0 {
                    crate::leanh::lean_inc(v___x_7538_);
                    v___y_7510_ = v___x_7538_;
                    state = 3;
                    continue;
                } else {
                    v___x_7542_ = lean_array_get_size(v_zs2_7481_);
                    v___x_7543_ = lean_nat_dec_eq(v___x_7542_, v___x_7540_);
                    if v___x_7543_ == 0 {
                        crate::leanh::lean_inc(v___x_7538_);
                        v___y_7510_ = v___x_7538_;
                        state = 3;
                        continue;
                    } else {
                        v___x_7544_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7_once), _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__7);
                        crate::leanh::lean_inc(v___x_7538_);
                        v___x_7545_ = l_Lean_Expr_app___override(v___x_7538_, v___x_7544_);
                        v___y_7510_ = v___x_7545_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_7511_ = 0;
                v___x_7512_ = crate::leanh::lean_alloc_ctor(0, 0, (4) as u32);
                crate::leanh::lean_ctor_set_uint8(v___x_7512_, 0 as u32, v___x_7511_);
                crate::leanh::lean_ctor_set_uint8(v___x_7512_, 1 as u32, v___x_7477_);
                crate::leanh::lean_ctor_set_uint8(v___x_7512_, 2 as u32, v_isZero_7478_);
                crate::leanh::lean_ctor_set_uint8(v___x_7512_, 3 as u32, v___x_7477_);
                crate::leanh::lean_inc_ref(v___y_7510_);
                crate::leanh::lean_inc(v_fst_7505_);
                v___x_7513_ = l_Lean_MVarId_apply(
                    v_fst_7505_,
                    v___y_7510_,
                    v___x_7512_,
                    v___x_7498_,
                    v___y_7483_,
                    v___y_7484_,
                    v___y_7485_,
                    v___y_7486_,
                );
                if crate::leanh::lean_obj_tag(v___x_7513_) == 0 {
                    v_a_7514_ = crate::leanh::lean_ctor_get(v___x_7513_, 0);
                    crate::leanh::lean_inc(v_a_7514_);
                    crate::leanh::lean_dec_ref_known(v___x_7513_, 1);
                    if crate::leanh::lean_obj_tag(v_a_7514_) == 0 {
                        crate::leanh::lean_dec_ref(v___y_7510_);
                        crate::leanh::lean_del_object(v___x_7507_);
                        crate::leanh::lean_dec(v_fst_7505_);
                        crate::leanh::lean_del_object(v___x_7503_);
                        v___x_7515_ = l_Lean_instantiateMVars___at___00Lean_mkCasesOnSameCtor_spec__1___redArg(v_a_7494_, v___y_7484_);
                        v_a_7516_ = crate::leanh::lean_ctor_get(v___x_7515_, 0);
                        crate::leanh::lean_inc(v_a_7516_);
                        crate::leanh::lean_dec_ref(v___x_7515_);
                        v___x_7517_ = l_Lean_Meta_mkLambdaFVars(
                            v___x_7489_,
                            v_a_7516_,
                            v_isZero_7478_,
                            v___x_7477_,
                            v_isZero_7478_,
                            v___x_7477_,
                            v___x_7479_,
                            v___y_7483_,
                            v___y_7484_,
                            v___y_7485_,
                            v___y_7486_,
                        );
                        crate::leanh::lean_dec_ref(v___x_7489_);
                        return v___x_7517_;
                    } else {
                        crate::leanh::lean_dec(v_a_7514_);
                        crate::leanh::lean_dec(v_a_7494_);
                        crate::leanh::lean_dec_ref(v___x_7489_);
                        v___x_7518_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1_once), _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__1);
                        v___x_7519_ = l_Lean_MessageData_ofExpr(v___y_7510_);
                        if v_isShared_7508_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_7507_, 7);
                            crate::leanh::lean_ctor_set(v___x_7507_, 1, v___x_7519_);
                            crate::leanh::lean_ctor_set(v___x_7507_, 0, v___x_7518_);
                            v___x_7521_ = v___x_7507_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_7529_ =
                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7529_, 0, v___x_7518_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_7529_, 1, v___x_7519_);
                            v___x_7521_ = v_reuseFailAlloc_7529_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_7510_);
                    crate::leanh::lean_del_object(v___x_7507_);
                    crate::leanh::lean_dec(v_fst_7505_);
                    crate::leanh::lean_del_object(v___x_7503_);
                    crate::leanh::lean_dec(v_a_7494_);
                    crate::leanh::lean_dec_ref(v___x_7489_);
                    v_a_7530_ = crate::leanh::lean_ctor_get(v___x_7513_, 0);
                    v_isSharedCheck_7537_ = (!crate::leanh::lean_is_exclusive(v___x_7513_)) as u8;
                    if v_isSharedCheck_7537_ == 0 {
                        v___x_7532_ = v___x_7513_;
                        v_isShared_7533_ = v_isSharedCheck_7537_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7530_);
                        crate::leanh::lean_dec(v___x_7513_);
                        v___x_7532_ = crate::leanh::lean_box(0);
                        v_isShared_7533_ = v_isSharedCheck_7537_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_7522_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3_once), _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___closed__3);
                v___x_7523_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7523_, 0, v___x_7521_);
                crate::leanh::lean_ctor_set(v___x_7523_, 1, v___x_7522_);
                if v_isShared_7504_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7503_, 0, v_fst_7505_);
                    v___x_7525_ = v___x_7503_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7528_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7528_, 0, v_fst_7505_);
                    v___x_7525_ = v_reuseFailAlloc_7528_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7526_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7526_, 0, v___x_7523_);
                crate::leanh::lean_ctor_set(v___x_7526_, 1, v___x_7525_);
                v___x_7527_ = l_Lean_throwError___at___00Lean_throwAttrNotInAsyncCtx___at___00Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12_spec__15_spec__20___redArg(v___x_7526_, v___y_7483_, v___y_7484_, v___y_7485_, v___y_7486_);
                return v___x_7527_;
            }
            6 => {
                if v_isShared_7533_ == 0 {
                    v___x_7535_ = v___x_7532_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7536_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7536_, 0, v_a_7530_);
                    v___x_7535_ = v_reuseFailAlloc_7536_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7535_;
            }
            8 => {
                if v_isShared_7554_ == 0 {
                    v___x_7556_ = v___x_7553_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7557_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7557_, 0, v_a_7551_);
                    v___x_7556_ = v_reuseFailAlloc_7557_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7556_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed(
    mut v___x_7559_: *mut crate::leanh::LeanObject,
    mut v_a_7560_: *mut crate::leanh::LeanObject,
    mut v_j_7561_: *mut crate::leanh::LeanObject,
    mut v_zs1_7562_: *mut crate::leanh::LeanObject,
    mut v_snd_7563_: *mut crate::leanh::LeanObject,
    mut v___x_7564_: *mut crate::leanh::LeanObject,
    mut v_isZero_7565_: *mut crate::leanh::LeanObject,
    mut v___x_7566_: *mut crate::leanh::LeanObject,
    mut v_alts_7567_: *mut crate::leanh::LeanObject,
    mut v_zs2_7568_: *mut crate::leanh::LeanObject,
    mut v___ctorRet2_7569_: *mut crate::leanh::LeanObject,
    mut v___y_7570_: *mut crate::leanh::LeanObject,
    mut v___y_7571_: *mut crate::leanh::LeanObject,
    mut v___y_7572_: *mut crate::leanh::LeanObject,
    mut v___y_7573_: *mut crate::leanh::LeanObject,
    mut v___y_7574_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_15413__boxed_7575_: u8 = 0;
    let mut v_isZero_boxed_7576_: u8 = 0;
    let mut v___x_15414__boxed_7577_: u8 = 0;
    let mut v_res_7578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_15413__boxed_7575_ = (crate::leanh::lean_unbox(v___x_7564_) as u8);
    v_isZero_boxed_7576_ = (crate::leanh::lean_unbox(v_isZero_7565_) as u8);
    v___x_15414__boxed_7577_ = (crate::leanh::lean_unbox(v___x_7566_) as u8);
    v_res_7578_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0(
        v___x_7559_,
        v_a_7560_,
        v_j_7561_,
        v_zs1_7562_,
        v_snd_7563_,
        v___x_15413__boxed_7575_,
        v_isZero_boxed_7576_,
        v___x_15414__boxed_7577_,
        v_alts_7567_,
        v_zs2_7568_,
        v___ctorRet2_7569_,
        v___y_7570_,
        v___y_7571_,
        v___y_7572_,
        v___y_7573_,
    );
    crate::leanh::lean_dec(v___y_7573_);
    crate::leanh::lean_dec_ref(v___y_7572_);
    crate::leanh::lean_dec(v___y_7571_);
    crate::leanh::lean_dec_ref(v___y_7570_);
    crate::leanh::lean_dec_ref(v___ctorRet2_7569_);
    crate::leanh::lean_dec_ref(v_zs2_7568_);
    crate::leanh::lean_dec_ref(v_alts_7567_);
    crate::leanh::lean_dec_ref(v_snd_7563_);
    crate::leanh::lean_dec(v_j_7561_);
    crate::leanh::lean_dec_ref(v_a_7560_);
    crate::leanh::lean_dec_ref(v___x_7559_);
    return v_res_7578_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(
    mut v___x_7579_: *mut crate::leanh::LeanObject,
    mut v_a_7580_: *mut crate::leanh::LeanObject,
    mut v_j_7581_: *mut crate::leanh::LeanObject,
    mut v_snd_7582_: *mut crate::leanh::LeanObject,
    mut v___x_7583_: u8,
    mut v_isZero_7584_: u8,
    mut v___x_7585_: u8,
    mut v_alts_7586_: *mut crate::leanh::LeanObject,
    mut v_a_7587_: *mut crate::leanh::LeanObject,
    mut v_zs1_7588_: *mut crate::leanh::LeanObject,
    mut v___ctorRet1_7589_: *mut crate::leanh::LeanObject,
    mut v___y_7590_: *mut crate::leanh::LeanObject,
    mut v___y_7591_: *mut crate::leanh::LeanObject,
    mut v___y_7592_: *mut crate::leanh::LeanObject,
    mut v___y_7593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7595_ = crate::leanh::lean_box((v___x_7583_) as usize);
    v___x_7596_ = crate::leanh::lean_box((v_isZero_7584_) as usize);
    v___x_7597_ = crate::leanh::lean_box((v___x_7585_) as usize);
    v___f_7598_ = crate::leanh::lean_alloc_closure(
        l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        16,
        9,
    );
    crate::leanh::lean_closure_set(v___f_7598_, 0, v___x_7579_);
    crate::leanh::lean_closure_set(v___f_7598_, 1, v_a_7580_);
    crate::leanh::lean_closure_set(v___f_7598_, 2, v_j_7581_);
    crate::leanh::lean_closure_set(v___f_7598_, 3, v_zs1_7588_);
    crate::leanh::lean_closure_set(v___f_7598_, 4, v_snd_7582_);
    crate::leanh::lean_closure_set(v___f_7598_, 5, v___x_7595_);
    crate::leanh::lean_closure_set(v___f_7598_, 6, v___x_7596_);
    crate::leanh::lean_closure_set(v___f_7598_, 7, v___x_7597_);
    crate::leanh::lean_closure_set(v___f_7598_, 8, v_alts_7586_);
    v___x_7599_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(
        v_a_7587_,
        v___f_7598_,
        v_isZero_7584_,
        v___y_7590_,
        v___y_7591_,
        v___y_7592_,
        v___y_7593_,
    );
    return v___x_7599_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed(
    mut v___x_7600_: *mut crate::leanh::LeanObject,
    mut v_a_7601_: *mut crate::leanh::LeanObject,
    mut v_j_7602_: *mut crate::leanh::LeanObject,
    mut v_snd_7603_: *mut crate::leanh::LeanObject,
    mut v___x_7604_: *mut crate::leanh::LeanObject,
    mut v_isZero_7605_: *mut crate::leanh::LeanObject,
    mut v___x_7606_: *mut crate::leanh::LeanObject,
    mut v_alts_7607_: *mut crate::leanh::LeanObject,
    mut v_a_7608_: *mut crate::leanh::LeanObject,
    mut v_zs1_7609_: *mut crate::leanh::LeanObject,
    mut v___ctorRet1_7610_: *mut crate::leanh::LeanObject,
    mut v___y_7611_: *mut crate::leanh::LeanObject,
    mut v___y_7612_: *mut crate::leanh::LeanObject,
    mut v___y_7613_: *mut crate::leanh::LeanObject,
    mut v___y_7614_: *mut crate::leanh::LeanObject,
    mut v___y_7615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_15606__boxed_7616_: u8 = 0;
    let mut v_isZero_boxed_7617_: u8 = 0;
    let mut v___x_15607__boxed_7618_: u8 = 0;
    let mut v_res_7619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_15606__boxed_7616_ = (crate::leanh::lean_unbox(v___x_7604_) as u8);
    v_isZero_boxed_7617_ = (crate::leanh::lean_unbox(v_isZero_7605_) as u8);
    v___x_15607__boxed_7618_ = (crate::leanh::lean_unbox(v___x_7606_) as u8);
    v_res_7619_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1(
        v___x_7600_,
        v_a_7601_,
        v_j_7602_,
        v_snd_7603_,
        v___x_15606__boxed_7616_,
        v_isZero_boxed_7617_,
        v___x_15607__boxed_7618_,
        v_alts_7607_,
        v_a_7608_,
        v_zs1_7609_,
        v___ctorRet1_7610_,
        v___y_7611_,
        v___y_7612_,
        v___y_7613_,
        v___y_7614_,
    );
    crate::leanh::lean_dec(v___y_7614_);
    crate::leanh::lean_dec_ref(v___y_7613_);
    crate::leanh::lean_dec(v___y_7612_);
    crate::leanh::lean_dec_ref(v___y_7611_);
    crate::leanh::lean_dec_ref(v___ctorRet1_7610_);
    return v_res_7619_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(
    mut v_tail_7620_: *mut crate::leanh::LeanObject,
    mut v_params_7621_: *mut crate::leanh::LeanObject,
    mut v_a_7622_: *mut crate::leanh::LeanObject,
    mut v_snd_7623_: *mut crate::leanh::LeanObject,
    mut v_alts_7624_: *mut crate::leanh::LeanObject,
    mut v_as_7625_: *mut crate::leanh::LeanObject,
    mut v_i_7626_: *mut crate::leanh::LeanObject,
    mut v_j_7627_: *mut crate::leanh::LeanObject,
    mut v_bs_7628_: *mut crate::leanh::LeanObject,
    mut v___y_7629_: *mut crate::leanh::LeanObject,
    mut v___y_7630_: *mut crate::leanh::LeanObject,
    mut v___y_7631_: *mut crate::leanh::LeanObject,
    mut v___y_7632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_7634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_7635_: u8 = 0;
    let mut v___x_7636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_7637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_7638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7648_: u8 = 0;
    let mut v___x_7650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7652_: u8 = 0;
    let mut v___x_7653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7659_: u8 = 0;
    let mut v___x_7660_: u8 = 0;
    let mut v___x_7661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_7634_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_7635_ = lean_nat_dec_eq(v_i_7626_, v_zero_7634_);
                if v_isZero_7635_ == 1 {
                    crate::leanh::lean_dec(v_j_7627_);
                    crate::leanh::lean_dec(v_i_7626_);
                    crate::leanh::lean_dec_ref(v_alts_7624_);
                    crate::leanh::lean_dec_ref(v_snd_7623_);
                    crate::leanh::lean_dec_ref(v_a_7622_);
                    crate::leanh::lean_dec(v_tail_7620_);
                    v___x_7636_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7636_, 0, v_bs_7628_);
                    return v___x_7636_;
                } else {
                    v_one_7637_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_7638_ = lean_nat_sub(v_i_7626_, v_one_7637_);
                    crate::leanh::lean_dec(v_i_7626_);
                    v___x_7653_ = lean_array_fget_borrowed(v_as_7625_, v_j_7627_);
                    crate::leanh::lean_inc(v_tail_7620_);
                    crate::leanh::lean_inc(v___x_7653_);
                    v___x_7654_ = l_Lean_mkConst(v___x_7653_, v_tail_7620_);
                    v___x_7655_ = l_Lean_mkAppN(v___x_7654_, v_params_7621_);
                    crate::leanh::lean_inc(v___y_7632_);
                    crate::leanh::lean_inc_ref(v___y_7631_);
                    crate::leanh::lean_inc(v___y_7630_);
                    crate::leanh::lean_inc_ref(v___y_7629_);
                    v___x_7656_ = lean_infer_type(
                        v___x_7655_,
                        v___y_7629_,
                        v___y_7630_,
                        v___y_7631_,
                        v___y_7632_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7656_) == 0 {
                        v_a_7657_ = crate::leanh::lean_ctor_get(v___x_7656_, 0);
                        crate::leanh::lean_inc_n(v_a_7657_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_7656_, 1);
                        v___x_7658_ = l_Lean_instInhabitedExpr;
                        v___x_7659_ = 1;
                        v___x_7660_ = 1;
                        v___x_7661_ = crate::leanh::lean_box((v___x_7659_) as usize);
                        v___x_7662_ = crate::leanh::lean_box((v_isZero_7635_) as usize);
                        v___x_7663_ = crate::leanh::lean_box((v___x_7660_) as usize);
                        crate::leanh::lean_inc_ref(v_alts_7624_);
                        crate::leanh::lean_inc_ref(v_snd_7623_);
                        crate::leanh::lean_inc(v_j_7627_);
                        crate::leanh::lean_inc_ref(v_a_7622_);
                        v___f_7664_ = crate::leanh::lean_alloc_closure(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___lam__1___boxed as *mut core::ffi::c_void, 16, 9);
                        crate::leanh::lean_closure_set(v___f_7664_, 0, v___x_7658_);
                        crate::leanh::lean_closure_set(v___f_7664_, 1, v_a_7622_);
                        crate::leanh::lean_closure_set(v___f_7664_, 2, v_j_7627_);
                        crate::leanh::lean_closure_set(v___f_7664_, 3, v_snd_7623_);
                        crate::leanh::lean_closure_set(v___f_7664_, 4, v___x_7661_);
                        crate::leanh::lean_closure_set(v___f_7664_, 5, v___x_7662_);
                        crate::leanh::lean_closure_set(v___f_7664_, 6, v___x_7663_);
                        crate::leanh::lean_closure_set(v___f_7664_, 7, v_alts_7624_);
                        crate::leanh::lean_closure_set(v___f_7664_, 8, v_a_7657_);
                        v___x_7665_ = l_Lean_Meta_forallTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__3___redArg(v_a_7657_, v___f_7664_, v_isZero_7635_, v___y_7629_, v___y_7630_, v___y_7631_, v___y_7632_);
                        v___y_7640_ = v___x_7665_;
                        state = 1;
                        continue;
                    } else {
                        v___y_7640_ = v___x_7656_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_7640_) == 0 {
                    v_a_7641_ = crate::leanh::lean_ctor_get(v___y_7640_, 0);
                    crate::leanh::lean_inc(v_a_7641_);
                    crate::leanh::lean_dec_ref_known(v___y_7640_, 1);
                    v___x_7642_ = lean_nat_add(v_j_7627_, v_one_7637_);
                    crate::leanh::lean_dec(v_j_7627_);
                    v___x_7643_ = lean_array_push(v_bs_7628_, v_a_7641_);
                    v_i_7626_ = v_n_7638_;
                    v_j_7627_ = v___x_7642_;
                    v_bs_7628_ = v___x_7643_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_n_7638_);
                    crate::leanh::lean_dec_ref(v_bs_7628_);
                    crate::leanh::lean_dec(v_j_7627_);
                    crate::leanh::lean_dec_ref(v_alts_7624_);
                    crate::leanh::lean_dec_ref(v_snd_7623_);
                    crate::leanh::lean_dec_ref(v_a_7622_);
                    crate::leanh::lean_dec(v_tail_7620_);
                    v_a_7645_ = crate::leanh::lean_ctor_get(v___y_7640_, 0);
                    v_isSharedCheck_7652_ = (!crate::leanh::lean_is_exclusive(v___y_7640_)) as u8;
                    if v_isSharedCheck_7652_ == 0 {
                        v___x_7647_ = v___y_7640_;
                        v_isShared_7648_ = v_isSharedCheck_7652_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7645_);
                        crate::leanh::lean_dec(v___y_7640_);
                        v___x_7647_ = crate::leanh::lean_box(0);
                        v_isShared_7648_ = v_isSharedCheck_7652_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7648_ == 0 {
                    v___x_7650_ = v___x_7647_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7651_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7651_, 0, v_a_7645_);
                    v___x_7650_ = v_reuseFailAlloc_7651_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7650_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg___boxed(
    mut v_tail_7666_: *mut crate::leanh::LeanObject,
    mut v_params_7667_: *mut crate::leanh::LeanObject,
    mut v_a_7668_: *mut crate::leanh::LeanObject,
    mut v_snd_7669_: *mut crate::leanh::LeanObject,
    mut v_alts_7670_: *mut crate::leanh::LeanObject,
    mut v_as_7671_: *mut crate::leanh::LeanObject,
    mut v_i_7672_: *mut crate::leanh::LeanObject,
    mut v_j_7673_: *mut crate::leanh::LeanObject,
    mut v_bs_7674_: *mut crate::leanh::LeanObject,
    mut v___y_7675_: *mut crate::leanh::LeanObject,
    mut v___y_7676_: *mut crate::leanh::LeanObject,
    mut v___y_7677_: *mut crate::leanh::LeanObject,
    mut v___y_7678_: *mut crate::leanh::LeanObject,
    mut v___y_7679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7680_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(
        v_tail_7666_,
        v_params_7667_,
        v_a_7668_,
        v_snd_7669_,
        v_alts_7670_,
        v_as_7671_,
        v_i_7672_,
        v_j_7673_,
        v_bs_7674_,
        v___y_7675_,
        v___y_7676_,
        v___y_7677_,
        v___y_7678_,
    );
    crate::leanh::lean_dec(v___y_7678_);
    crate::leanh::lean_dec_ref(v___y_7677_);
    crate::leanh::lean_dec(v___y_7676_);
    crate::leanh::lean_dec_ref(v___y_7675_);
    crate::leanh::lean_dec_ref(v_as_7671_);
    crate::leanh::lean_dec_ref(v_params_7667_);
    return v_res_7680_;
}
pub unsafe fn _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_7681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7681_ = crate::leanh::lean_box(0);
    v___x_7682_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_7683_ = lean_mk_array(v___x_7682_, v___x_7681_);
    return v___x_7683_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__3(
    mut v_motive_7684_: *mut crate::leanh::LeanObject,
    mut v___x_7685_: *mut crate::leanh::LeanObject,
    mut v___x_7686_: u8,
    mut v___x_7687_: u8,
    mut v___x_7688_: u8,
    mut v_ism1_x27_7689_: *mut crate::leanh::LeanObject,
    mut v_is_7690_: *mut crate::leanh::LeanObject,
    mut v___x_7691_: *mut crate::leanh::LeanObject,
    mut v___x_7692_: *mut crate::leanh::LeanObject,
    mut v___x_7693_: *mut crate::leanh::LeanObject,
    mut v___x_7694_: *mut crate::leanh::LeanObject,
    mut v_params_7695_: *mut crate::leanh::LeanObject,
    mut v___x_7696_: *mut crate::leanh::LeanObject,
    mut v___x_7697_: *mut crate::leanh::LeanObject,
    mut v_heq_7698_: *mut crate::leanh::LeanObject,
    mut v_val_7699_: *mut crate::leanh::LeanObject,
    mut v___x_7700_: *mut crate::leanh::LeanObject,
    mut v_tail_7701_: *mut crate::leanh::LeanObject,
    mut v_alts_7702_: *mut crate::leanh::LeanObject,
    mut v___x_7703_: *mut crate::leanh::LeanObject,
    mut v___x_7704_: *mut crate::leanh::LeanObject,
    mut v___x_7705_: *mut crate::leanh::LeanObject,
    mut v_declName_7706_: *mut crate::leanh::LeanObject,
    mut v_levelParams_7707_: *mut crate::leanh::LeanObject,
    mut v_numIndices_7708_: *mut crate::leanh::LeanObject,
    mut v___x_7709_: *mut crate::leanh::LeanObject,
    mut v_numParams_7710_: *mut crate::leanh::LeanObject,
    mut v_snd_7711_: *mut crate::leanh::LeanObject,
    mut v_ism2_x27_7712_: *mut crate::leanh::LeanObject,
    mut v_x_7713_: *mut crate::leanh::LeanObject,
    mut v___y_7714_: *mut crate::leanh::LeanObject,
    mut v___y_7715_: *mut crate::leanh::LeanObject,
    mut v___y_7716_: *mut crate::leanh::LeanObject,
    mut v___y_7717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7730_: u8 = 0;
    let mut v___x_7731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7767_: u8 = 0;
    let mut v___x_7769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7784_: u8 = 0;
    let mut v___x_7785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7789_: u8 = 0;
    let mut v___x_7790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7793_: u8 = 0;
    let mut v_reuseFailAlloc_7794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7796_: u8 = 0;
    let mut v_a_7797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7800_: u8 = 0;
    let mut v___x_7802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7804_: u8 = 0;
    let mut v_a_7805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7808_: u8 = 0;
    let mut v___x_7810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7812_: u8 = 0;
    let mut v_a_7813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7816_: u8 = 0;
    let mut v___x_7818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7820_: u8 = 0;
    let mut v_a_7821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7824_: u8 = 0;
    let mut v___x_7826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7828_: u8 = 0;
    let mut v_isSharedCheck_7829_: u8 = 0;
    let mut v_a_7830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7833_: u8 = 0;
    let mut v___x_7835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7837_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7719_ = crate::leanh::lean_box((v___x_7686_) as usize);
                v___x_7720_ = crate::leanh::lean_box((v___x_7687_) as usize);
                v___x_7721_ = crate::leanh::lean_box((v___x_7688_) as usize);
                crate::leanh::lean_inc_ref(v___x_7691_);
                crate::leanh::lean_inc_ref_n(v_is_7690_, 2);
                crate::leanh::lean_inc_ref(v_ism1_x27_7689_);
                crate::leanh::lean_inc_ref(v_motive_7684_);
                v___f_7722_ = crate::leanh::lean_alloc_closure(
                    l_Lean_mkCasesOnSameCtor___lam__1___boxed as *mut core::ffi::c_void,
                    16,
                    9,
                );
                crate::leanh::lean_closure_set(v___f_7722_, 0, v_motive_7684_);
                crate::leanh::lean_closure_set(v___f_7722_, 1, v___x_7685_);
                crate::leanh::lean_closure_set(v___f_7722_, 2, v___x_7719_);
                crate::leanh::lean_closure_set(v___f_7722_, 3, v___x_7720_);
                crate::leanh::lean_closure_set(v___f_7722_, 4, v___x_7721_);
                crate::leanh::lean_closure_set(v___f_7722_, 5, v_ism1_x27_7689_);
                crate::leanh::lean_closure_set(v___f_7722_, 6, v_ism2_x27_7712_);
                crate::leanh::lean_closure_set(v___f_7722_, 7, v_is_7690_);
                crate::leanh::lean_closure_set(v___f_7722_, 8, v___x_7691_);
                crate::leanh::lean_inc_ref(v___x_7692_);
                v___x_7723_ = lean_array_push(v_is_7690_, v___x_7692_);
                v___x_7724_ = l_Lean_Meta_withNewEqs___redArg(
                    v___x_7723_,
                    v_ism1_x27_7689_,
                    v___f_7722_,
                    v___y_7714_,
                    v___y_7715_,
                    v___y_7716_,
                    v___y_7717_,
                );
                if crate::leanh::lean_obj_tag(v___x_7724_) == 0 {
                    v_a_7725_ = crate::leanh::lean_ctor_get(v___x_7724_, 0);
                    crate::leanh::lean_inc(v_a_7725_);
                    crate::leanh::lean_dec_ref_known(v___x_7724_, 1);
                    v_fst_7726_ = crate::leanh::lean_ctor_get(v_a_7725_, 0);
                    v_snd_7727_ = crate::leanh::lean_ctor_get(v_a_7725_, 1);
                    v_isSharedCheck_7829_ = (!crate::leanh::lean_is_exclusive(v_a_7725_)) as u8;
                    if v_isSharedCheck_7829_ == 0 {
                        v___x_7729_ = v_a_7725_;
                        v_isShared_7730_ = v_isSharedCheck_7829_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_7727_);
                        crate::leanh::lean_inc(v_fst_7726_);
                        crate::leanh::lean_dec(v_a_7725_);
                        v___x_7729_ = crate::leanh::lean_box(0);
                        v_isShared_7730_ = v_isSharedCheck_7829_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_snd_7711_);
                    crate::leanh::lean_dec(v_numParams_7710_);
                    crate::leanh::lean_dec(v_levelParams_7707_);
                    crate::leanh::lean_dec(v_declName_7706_);
                    crate::leanh::lean_dec_ref(v___x_7705_);
                    crate::leanh::lean_dec(v___x_7704_);
                    crate::leanh::lean_dec_ref(v_alts_7702_);
                    crate::leanh::lean_dec(v_tail_7701_);
                    crate::leanh::lean_dec(v___x_7700_);
                    crate::leanh::lean_dec_ref(v_heq_7698_);
                    crate::leanh::lean_dec_ref(v_params_7695_);
                    crate::leanh::lean_dec(v___x_7694_);
                    crate::leanh::lean_dec(v___x_7693_);
                    crate::leanh::lean_dec_ref(v___x_7692_);
                    crate::leanh::lean_dec_ref(v___x_7691_);
                    crate::leanh::lean_dec_ref(v_is_7690_);
                    crate::leanh::lean_dec_ref(v_motive_7684_);
                    v_a_7830_ = crate::leanh::lean_ctor_get(v___x_7724_, 0);
                    v_isSharedCheck_7837_ = (!crate::leanh::lean_is_exclusive(v___x_7724_)) as u8;
                    if v_isSharedCheck_7837_ == 0 {
                        v___x_7832_ = v___x_7724_;
                        v_isShared_7833_ = v_isSharedCheck_7837_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7830_);
                        crate::leanh::lean_dec(v___x_7724_);
                        v___x_7832_ = crate::leanh::lean_box(0);
                        v_isShared_7833_ = v_isSharedCheck_7837_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7731_ = l_Lean_mkConst(v___x_7693_, v___x_7694_);
                v___x_7732_ = l_Lean_mkAppN(v___x_7731_, v_params_7695_);
                v___x_7733_ = l_Lean_Expr_app___override(v___x_7732_, v_fst_7726_);
                crate::leanh::lean_inc_ref(v_is_7690_);
                v___x_7734_ = l_Array_append___redArg(v_is_7690_, v___x_7696_);
                v___x_7735_ = l_Array_append___redArg(v___x_7734_, v_is_7690_);
                v___x_7736_ = l_Array_append___redArg(v___x_7735_, v___x_7697_);
                v___x_7737_ = l_Lean_mkAppN(v___x_7733_, v___x_7736_);
                crate::leanh::lean_dec_ref(v___x_7736_);
                crate::leanh::lean_inc_ref(v_heq_7698_);
                v___x_7738_ = l_Lean_Expr_app___override(v___x_7737_, v_heq_7698_);
                v___x_7739_ = l_Lean_InductiveVal_numCtors(v_val_7699_);
                crate::leanh::lean_inc_ref(v___x_7738_);
                v___x_7740_ = l_Lean_Meta_inferArgumentTypesN(
                    v___x_7739_,
                    v___x_7738_,
                    v___y_7714_,
                    v___y_7715_,
                    v___y_7716_,
                    v___y_7717_,
                );
                if crate::leanh::lean_obj_tag(v___x_7740_) == 0 {
                    v_a_7741_ = crate::leanh::lean_ctor_get(v___x_7740_, 0);
                    crate::leanh::lean_inc(v_a_7741_);
                    crate::leanh::lean_dec_ref_known(v___x_7740_, 1);
                    v___x_7742_ = lean_mk_empty_array_with_capacity(v___x_7700_);
                    crate::leanh::lean_inc(v___x_7704_);
                    crate::leanh::lean_inc_ref(v_alts_7702_);
                    crate::leanh::lean_inc(v_snd_7727_);
                    v___x_7743_ =
                        l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(
                            v_tail_7701_,
                            v_params_7695_,
                            v_a_7741_,
                            v_snd_7727_,
                            v_alts_7702_,
                            v___x_7703_,
                            v___x_7700_,
                            v___x_7704_,
                            v___x_7742_,
                            v___y_7714_,
                            v___y_7715_,
                            v___y_7716_,
                            v___y_7717_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_7743_) == 0 {
                        v_a_7744_ = crate::leanh::lean_ctor_get(v___x_7743_, 0);
                        crate::leanh::lean_inc(v_a_7744_);
                        crate::leanh::lean_dec_ref_known(v___x_7743_, 1);
                        v___x_7745_ = l_Lean_mkAppN(v___x_7738_, v_a_7744_);
                        crate::leanh::lean_dec(v_a_7744_);
                        v___x_7746_ = l_Lean_mkAppN(v___x_7745_, v_snd_7727_);
                        crate::leanh::lean_dec(v_snd_7727_);
                        crate::leanh::lean_inc_ref(v___x_7705_);
                        v___x_7747_ = lean_array_push(v___x_7705_, v_motive_7684_);
                        v___x_7748_ = l_Array_append___redArg(v_params_7695_, v___x_7747_);
                        crate::leanh::lean_dec_ref(v___x_7747_);
                        v___x_7749_ = l_Array_append___redArg(v___x_7748_, v_is_7690_);
                        crate::leanh::lean_dec_ref(v_is_7690_);
                        v___x_7750_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_7751_ = lean_mk_empty_array_with_capacity(v___x_7750_);
                        v___x_7752_ = lean_array_push(v___x_7751_, v___x_7692_);
                        v___x_7753_ = lean_array_push(v___x_7752_, v___x_7691_);
                        v___x_7754_ = l_Array_append___redArg(v___x_7749_, v___x_7753_);
                        crate::leanh::lean_dec_ref(v___x_7753_);
                        v___x_7755_ = lean_array_push(v___x_7705_, v_heq_7698_);
                        v___x_7756_ = l_Array_append___redArg(v___x_7754_, v___x_7755_);
                        crate::leanh::lean_dec_ref(v___x_7755_);
                        v___x_7757_ = l_Array_append___redArg(v___x_7756_, v_alts_7702_);
                        crate::leanh::lean_dec_ref(v_alts_7702_);
                        v___x_7758_ = l_Lean_Meta_mkLambdaFVars(
                            v___x_7757_,
                            v___x_7746_,
                            v___x_7686_,
                            v___x_7687_,
                            v___x_7686_,
                            v___x_7687_,
                            v___x_7688_,
                            v___y_7714_,
                            v___y_7715_,
                            v___y_7716_,
                            v___y_7717_,
                        );
                        crate::leanh::lean_dec_ref(v___x_7757_);
                        if crate::leanh::lean_obj_tag(v___x_7758_) == 0 {
                            v_a_7759_ = crate::leanh::lean_ctor_get(v___x_7758_, 0);
                            crate::leanh::lean_inc_n(v_a_7759_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_7758_, 1);
                            crate::leanh::lean_inc(v___y_7717_);
                            crate::leanh::lean_inc_ref(v___y_7716_);
                            crate::leanh::lean_inc(v___y_7715_);
                            crate::leanh::lean_inc_ref(v___y_7714_);
                            v___x_7760_ = lean_infer_type(
                                v_a_7759_,
                                v___y_7714_,
                                v___y_7715_,
                                v___y_7716_,
                                v___y_7717_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_7760_) == 0 {
                                v_a_7761_ = crate::leanh::lean_ctor_get(v___x_7760_, 0);
                                crate::leanh::lean_inc(v_a_7761_);
                                crate::leanh::lean_dec_ref_known(v___x_7760_, 1);
                                v___x_7762_ = crate::leanh::lean_box(1);
                                crate::leanh::lean_inc(v_declName_7706_);
                                v___x_7763_ = l_Lean_mkDefinitionValInferringUnsafe___at___00Lean_mkCasesOnSameCtorHet_spec__10___redArg(v_declName_7706_, v_levelParams_7707_, v_a_7761_, v_a_7759_, v___x_7762_, v___y_7717_);
                                v_a_7764_ = crate::leanh::lean_ctor_get(v___x_7763_, 0);
                                v_isSharedCheck_7796_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7763_)) as u8;
                                if v_isSharedCheck_7796_ == 0 {
                                    v___x_7766_ = v___x_7763_;
                                    v_isShared_7767_ = v_isSharedCheck_7796_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7764_);
                                    crate::leanh::lean_dec(v___x_7763_);
                                    v___x_7766_ = crate::leanh::lean_box(0);
                                    v_isShared_7767_ = v_isSharedCheck_7796_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_7759_);
                                crate::leanh::lean_del_object(v___x_7729_);
                                crate::leanh::lean_dec_ref(v_snd_7711_);
                                crate::leanh::lean_dec(v_numParams_7710_);
                                crate::leanh::lean_dec(v_levelParams_7707_);
                                crate::leanh::lean_dec(v_declName_7706_);
                                crate::leanh::lean_dec(v___x_7704_);
                                v_a_7797_ = crate::leanh::lean_ctor_get(v___x_7760_, 0);
                                v_isSharedCheck_7804_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_7760_)) as u8;
                                if v_isSharedCheck_7804_ == 0 {
                                    v___x_7799_ = v___x_7760_;
                                    v_isShared_7800_ = v_isSharedCheck_7804_;
                                    state = 6;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_7797_);
                                    crate::leanh::lean_dec(v___x_7760_);
                                    v___x_7799_ = crate::leanh::lean_box(0);
                                    v_isShared_7800_ = v_isSharedCheck_7804_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_7729_);
                            crate::leanh::lean_dec_ref(v_snd_7711_);
                            crate::leanh::lean_dec(v_numParams_7710_);
                            crate::leanh::lean_dec(v_levelParams_7707_);
                            crate::leanh::lean_dec(v_declName_7706_);
                            crate::leanh::lean_dec(v___x_7704_);
                            v_a_7805_ = crate::leanh::lean_ctor_get(v___x_7758_, 0);
                            v_isSharedCheck_7812_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7758_)) as u8;
                            if v_isSharedCheck_7812_ == 0 {
                                v___x_7807_ = v___x_7758_;
                                v_isShared_7808_ = v_isSharedCheck_7812_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_7805_);
                                crate::leanh::lean_dec(v___x_7758_);
                                v___x_7807_ = crate::leanh::lean_box(0);
                                v_isShared_7808_ = v_isSharedCheck_7812_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_7738_);
                        crate::leanh::lean_del_object(v___x_7729_);
                        crate::leanh::lean_dec(v_snd_7727_);
                        crate::leanh::lean_dec_ref(v_snd_7711_);
                        crate::leanh::lean_dec(v_numParams_7710_);
                        crate::leanh::lean_dec(v_levelParams_7707_);
                        crate::leanh::lean_dec(v_declName_7706_);
                        crate::leanh::lean_dec_ref(v___x_7705_);
                        crate::leanh::lean_dec(v___x_7704_);
                        crate::leanh::lean_dec_ref(v_alts_7702_);
                        crate::leanh::lean_dec_ref(v_heq_7698_);
                        crate::leanh::lean_dec_ref(v_params_7695_);
                        crate::leanh::lean_dec_ref(v___x_7692_);
                        crate::leanh::lean_dec_ref(v___x_7691_);
                        crate::leanh::lean_dec_ref(v_is_7690_);
                        crate::leanh::lean_dec_ref(v_motive_7684_);
                        v_a_7813_ = crate::leanh::lean_ctor_get(v___x_7743_, 0);
                        v_isSharedCheck_7820_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7743_)) as u8;
                        if v_isSharedCheck_7820_ == 0 {
                            v___x_7815_ = v___x_7743_;
                            v_isShared_7816_ = v_isSharedCheck_7820_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7813_);
                            crate::leanh::lean_dec(v___x_7743_);
                            v___x_7815_ = crate::leanh::lean_box(0);
                            v_isShared_7816_ = v_isSharedCheck_7820_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_7738_);
                    crate::leanh::lean_del_object(v___x_7729_);
                    crate::leanh::lean_dec(v_snd_7727_);
                    crate::leanh::lean_dec_ref(v_snd_7711_);
                    crate::leanh::lean_dec(v_numParams_7710_);
                    crate::leanh::lean_dec(v_levelParams_7707_);
                    crate::leanh::lean_dec(v_declName_7706_);
                    crate::leanh::lean_dec_ref(v___x_7705_);
                    crate::leanh::lean_dec(v___x_7704_);
                    crate::leanh::lean_dec_ref(v_alts_7702_);
                    crate::leanh::lean_dec(v_tail_7701_);
                    crate::leanh::lean_dec(v___x_7700_);
                    crate::leanh::lean_dec_ref(v_heq_7698_);
                    crate::leanh::lean_dec_ref(v_params_7695_);
                    crate::leanh::lean_dec_ref(v___x_7692_);
                    crate::leanh::lean_dec_ref(v___x_7691_);
                    crate::leanh::lean_dec_ref(v_is_7690_);
                    crate::leanh::lean_dec_ref(v_motive_7684_);
                    v_a_7821_ = crate::leanh::lean_ctor_get(v___x_7740_, 0);
                    v_isSharedCheck_7828_ = (!crate::leanh::lean_is_exclusive(v___x_7740_)) as u8;
                    if v_isSharedCheck_7828_ == 0 {
                        v___x_7823_ = v___x_7740_;
                        v_isShared_7824_ = v_isSharedCheck_7828_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7821_);
                        crate::leanh::lean_dec(v___x_7740_);
                        v___x_7823_ = crate::leanh::lean_box(0);
                        v_isShared_7824_ = v_isSharedCheck_7828_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7767_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_7766_, 1);
                    v___x_7769_ = v___x_7766_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7795_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7795_, 0, v_a_7764_);
                    v___x_7769_ = v_reuseFailAlloc_7795_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7770_ = crate::leanh::lean_box((v___x_7686_) as usize);
                crate::leanh::lean_inc_ref(v___x_7769_);
                v___f_7771_ = crate::leanh::lean_alloc_closure(
                    l_Lean_mkCasesOnSameCtor___lam__2___boxed as *mut core::ffi::c_void,
                    7,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_7771_, 0, v___x_7769_);
                crate::leanh::lean_closure_set(v___f_7771_, 1, v___x_7770_);
                v___x_7772_ = lean_nat_add(v_numIndices_7708_, v___x_7709_);
                crate::leanh::lean_inc(v___x_7704_);
                v___x_7773_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7773_, 0, v___x_7704_);
                v___x_7774_ = crate::leanh::lean_box(0);
                v___x_7775_ = lean_mk_empty_array_with_capacity(v___x_7709_);
                v___x_7776_ = lean_array_push(v___x_7775_, v___x_7774_);
                v___x_7777_ = lean_array_push(v___x_7776_, v___x_7774_);
                v___x_7778_ = lean_array_push(v___x_7777_, v___x_7774_);
                v___x_7779_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_mkCasesOnSameCtor___lam__3___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_mkCasesOnSameCtor___lam__3___closed__0_once),
                    _init_l_Lean_mkCasesOnSameCtor___lam__3___closed__0,
                );
                if v_isShared_7730_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7729_, 1, v___x_7779_);
                    crate::leanh::lean_ctor_set(v___x_7729_, 0, v___x_7704_);
                    v___x_7781_ = v___x_7729_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7794_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7794_, 0, v___x_7704_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7794_, 1, v___x_7779_);
                    v___x_7781_ = v_reuseFailAlloc_7794_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7782_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_7782_, 0, v_numParams_7710_);
                crate::leanh::lean_ctor_set(v___x_7782_, 1, v___x_7772_);
                crate::leanh::lean_ctor_set(v___x_7782_, 2, v_snd_7711_);
                crate::leanh::lean_ctor_set(v___x_7782_, 3, v___x_7773_);
                crate::leanh::lean_ctor_set(v___x_7782_, 4, v___x_7778_);
                crate::leanh::lean_ctor_set(v___x_7782_, 5, v___x_7781_);
                v___x_7793_ = l_Lean_isPrivateName(v_declName_7706_);
                if v___x_7793_ == 0 {
                    v___y_7784_ = v___x_7687_;
                    state = 5;
                    continue;
                } else {
                    v___y_7784_ = v___x_7686_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7785_ =
                    l_Lean_withExporting___at___00Lean_mkCasesOnSameCtorHet_spec__11___redArg(
                        v___f_7771_,
                        v___y_7784_,
                        v___y_7714_,
                        v___y_7715_,
                        v___y_7716_,
                        v___y_7717_,
                    );
                if crate::leanh::lean_obj_tag(v___x_7785_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_7785_, 1);
                    v___x_7786_ = l_Lean_Elab_Term_elabAsElim;
                    crate::leanh::lean_inc(v_declName_7706_);
                    v___x_7787_ =
                        l_Lean_TagAttribute_setTag___at___00Lean_mkCasesOnSameCtorHet_spec__12(
                            v___x_7786_,
                            v_declName_7706_,
                            v___y_7714_,
                            v___y_7715_,
                            v___y_7716_,
                            v___y_7717_,
                        );
                    if crate::leanh::lean_obj_tag(v___x_7787_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_7787_, 1);
                        crate::leanh::lean_inc_n(v_declName_7706_, 2);
                        v___x_7788_ = l_Lean_Meta_Match_addMatcherInfo___at___00Lean_mkCasesOnSameCtor_spec__3___redArg(v_declName_7706_, v___x_7782_, v___y_7715_, v___y_7717_);
                        crate::leanh::lean_dec_ref(v___x_7788_);
                        v___x_7789_ = 0;
                        v___x_7790_ = l_Lean_Meta_setInlineAttribute(
                            v_declName_7706_,
                            v___x_7789_,
                            v___y_7714_,
                            v___y_7715_,
                            v___y_7716_,
                            v___y_7717_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_7790_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_7790_, 1);
                            v___x_7791_ = l_Lean_enableRealizationsForConst(
                                v_declName_7706_,
                                v___y_7716_,
                                v___y_7717_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_7791_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_7791_, 1);
                                v___x_7792_ = l_Lean_compileDecl(
                                    v___x_7769_,
                                    v___x_7687_,
                                    v___y_7716_,
                                    v___y_7717_,
                                );
                                return v___x_7792_;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_7769_);
                                return v___x_7791_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_7769_);
                            crate::leanh::lean_dec(v_declName_7706_);
                            return v___x_7790_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_7782_, 6);
                        crate::leanh::lean_dec_ref(v___x_7769_);
                        crate::leanh::lean_dec(v_declName_7706_);
                        return v___x_7787_;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_7782_, 6);
                    crate::leanh::lean_dec_ref(v___x_7769_);
                    crate::leanh::lean_dec(v_declName_7706_);
                    return v___x_7785_;
                }
            }
            6 => {
                if v_isShared_7800_ == 0 {
                    v___x_7802_ = v___x_7799_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7803_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7803_, 0, v_a_7797_);
                    v___x_7802_ = v_reuseFailAlloc_7803_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7802_;
            }
            8 => {
                if v_isShared_7808_ == 0 {
                    v___x_7810_ = v___x_7807_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7811_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7811_, 0, v_a_7805_);
                    v___x_7810_ = v_reuseFailAlloc_7811_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7810_;
            }
            10 => {
                if v_isShared_7816_ == 0 {
                    v___x_7818_ = v___x_7815_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7819_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7819_, 0, v_a_7813_);
                    v___x_7818_ = v_reuseFailAlloc_7819_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_7818_;
            }
            12 => {
                if v_isShared_7824_ == 0 {
                    v___x_7826_ = v___x_7823_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_7827_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7827_, 0, v_a_7821_);
                    v___x_7826_ = v_reuseFailAlloc_7827_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_7826_;
            }
            14 => {
                if v_isShared_7833_ == 0 {
                    v___x_7835_ = v___x_7832_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_7836_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7836_, 0, v_a_7830_);
                    v___x_7835_ = v_reuseFailAlloc_7836_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_7835_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__3___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_motive_7838_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_7839_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_7840_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_7841_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_7842_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_ism1_x27_7843_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_is_7844_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_7845_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_7846_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_7847_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_7848_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_params_7849_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_7850_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___x_7851_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_heq_7852_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_val_7853_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___x_7854_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_tail_7855_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_alts_7856_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___x_7857_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___x_7858_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___x_7859_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v_declName_7860_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v_levelParams_7861_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v_numIndices_7862_: *mut crate::leanh::LeanObject = *_args.add(24);
    let mut v___x_7863_: *mut crate::leanh::LeanObject = *_args.add(25);
    let mut v_numParams_7864_: *mut crate::leanh::LeanObject = *_args.add(26);
    let mut v_snd_7865_: *mut crate::leanh::LeanObject = *_args.add(27);
    let mut v_ism2_x27_7866_: *mut crate::leanh::LeanObject = *_args.add(28);
    let mut v_x_7867_: *mut crate::leanh::LeanObject = *_args.add(29);
    let mut v___y_7868_: *mut crate::leanh::LeanObject = *_args.add(30);
    let mut v___y_7869_: *mut crate::leanh::LeanObject = *_args.add(31);
    let mut v___y_7870_: *mut crate::leanh::LeanObject = *_args.add(32);
    let mut v___y_7871_: *mut crate::leanh::LeanObject = *_args.add(33);
    let mut v___y_7872_: *mut crate::leanh::LeanObject = *_args.add(34);
    let mut v___x_15736__boxed_7873_: u8 = 0;
    let mut v___x_15737__boxed_7874_: u8 = 0;
    let mut v___x_15738__boxed_7875_: u8 = 0;
    let mut v_res_7876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_15736__boxed_7873_ = (crate::leanh::lean_unbox(v___x_7840_) as u8);
    v___x_15737__boxed_7874_ = (crate::leanh::lean_unbox(v___x_7841_) as u8);
    v___x_15738__boxed_7875_ = (crate::leanh::lean_unbox(v___x_7842_) as u8);
    v_res_7876_ = l_Lean_mkCasesOnSameCtor___lam__3(
        v_motive_7838_,
        v___x_7839_,
        v___x_15736__boxed_7873_,
        v___x_15737__boxed_7874_,
        v___x_15738__boxed_7875_,
        v_ism1_x27_7843_,
        v_is_7844_,
        v___x_7845_,
        v___x_7846_,
        v___x_7847_,
        v___x_7848_,
        v_params_7849_,
        v___x_7850_,
        v___x_7851_,
        v_heq_7852_,
        v_val_7853_,
        v___x_7854_,
        v_tail_7855_,
        v_alts_7856_,
        v___x_7857_,
        v___x_7858_,
        v___x_7859_,
        v_declName_7860_,
        v_levelParams_7861_,
        v_numIndices_7862_,
        v___x_7863_,
        v_numParams_7864_,
        v_snd_7865_,
        v_ism2_x27_7866_,
        v_x_7867_,
        v___y_7868_,
        v___y_7869_,
        v___y_7870_,
        v___y_7871_,
    );
    crate::leanh::lean_dec(v___y_7871_);
    crate::leanh::lean_dec_ref(v___y_7870_);
    crate::leanh::lean_dec(v___y_7869_);
    crate::leanh::lean_dec_ref(v___y_7868_);
    crate::leanh::lean_dec_ref(v_x_7867_);
    crate::leanh::lean_dec(v___x_7863_);
    crate::leanh::lean_dec(v_numIndices_7862_);
    crate::leanh::lean_dec_ref(v___x_7857_);
    crate::leanh::lean_dec_ref(v_val_7853_);
    crate::leanh::lean_dec_ref(v___x_7851_);
    crate::leanh::lean_dec_ref(v___x_7850_);
    return v_res_7876_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__4(
    mut v_motive_7877_: *mut crate::leanh::LeanObject,
    mut v___x_7878_: *mut crate::leanh::LeanObject,
    mut v___x_7879_: u8,
    mut v___x_7880_: u8,
    mut v___x_7881_: u8,
    mut v_is_7882_: *mut crate::leanh::LeanObject,
    mut v___x_7883_: *mut crate::leanh::LeanObject,
    mut v___x_7884_: *mut crate::leanh::LeanObject,
    mut v___x_7885_: *mut crate::leanh::LeanObject,
    mut v___x_7886_: *mut crate::leanh::LeanObject,
    mut v_params_7887_: *mut crate::leanh::LeanObject,
    mut v___x_7888_: *mut crate::leanh::LeanObject,
    mut v___x_7889_: *mut crate::leanh::LeanObject,
    mut v_heq_7890_: *mut crate::leanh::LeanObject,
    mut v_val_7891_: *mut crate::leanh::LeanObject,
    mut v___x_7892_: *mut crate::leanh::LeanObject,
    mut v_tail_7893_: *mut crate::leanh::LeanObject,
    mut v_alts_7894_: *mut crate::leanh::LeanObject,
    mut v___x_7895_: *mut crate::leanh::LeanObject,
    mut v___x_7896_: *mut crate::leanh::LeanObject,
    mut v___x_7897_: *mut crate::leanh::LeanObject,
    mut v_declName_7898_: *mut crate::leanh::LeanObject,
    mut v_levelParams_7899_: *mut crate::leanh::LeanObject,
    mut v_numIndices_7900_: *mut crate::leanh::LeanObject,
    mut v___x_7901_: *mut crate::leanh::LeanObject,
    mut v_numParams_7902_: *mut crate::leanh::LeanObject,
    mut v_snd_7903_: *mut crate::leanh::LeanObject,
    mut v___x_7904_: *mut crate::leanh::LeanObject,
    mut v___x_7905_: *mut crate::leanh::LeanObject,
    mut v_ism1_x27_7906_: *mut crate::leanh::LeanObject,
    mut v_x_7907_: *mut crate::leanh::LeanObject,
    mut v___y_7908_: *mut crate::leanh::LeanObject,
    mut v___y_7909_: *mut crate::leanh::LeanObject,
    mut v___y_7910_: *mut crate::leanh::LeanObject,
    mut v___y_7911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7913_ = crate::leanh::lean_box((v___x_7879_) as usize);
    v___x_7914_ = crate::leanh::lean_box((v___x_7880_) as usize);
    v___x_7915_ = crate::leanh::lean_box((v___x_7881_) as usize);
    v___f_7916_ = crate::leanh::lean_alloc_closure(
        l_Lean_mkCasesOnSameCtor___lam__3___boxed as *mut core::ffi::c_void,
        35,
        28,
    );
    crate::leanh::lean_closure_set(v___f_7916_, 0, v_motive_7877_);
    crate::leanh::lean_closure_set(v___f_7916_, 1, v___x_7878_);
    crate::leanh::lean_closure_set(v___f_7916_, 2, v___x_7913_);
    crate::leanh::lean_closure_set(v___f_7916_, 3, v___x_7914_);
    crate::leanh::lean_closure_set(v___f_7916_, 4, v___x_7915_);
    crate::leanh::lean_closure_set(v___f_7916_, 5, v_ism1_x27_7906_);
    crate::leanh::lean_closure_set(v___f_7916_, 6, v_is_7882_);
    crate::leanh::lean_closure_set(v___f_7916_, 7, v___x_7883_);
    crate::leanh::lean_closure_set(v___f_7916_, 8, v___x_7884_);
    crate::leanh::lean_closure_set(v___f_7916_, 9, v___x_7885_);
    crate::leanh::lean_closure_set(v___f_7916_, 10, v___x_7886_);
    crate::leanh::lean_closure_set(v___f_7916_, 11, v_params_7887_);
    crate::leanh::lean_closure_set(v___f_7916_, 12, v___x_7888_);
    crate::leanh::lean_closure_set(v___f_7916_, 13, v___x_7889_);
    crate::leanh::lean_closure_set(v___f_7916_, 14, v_heq_7890_);
    crate::leanh::lean_closure_set(v___f_7916_, 15, v_val_7891_);
    crate::leanh::lean_closure_set(v___f_7916_, 16, v___x_7892_);
    crate::leanh::lean_closure_set(v___f_7916_, 17, v_tail_7893_);
    crate::leanh::lean_closure_set(v___f_7916_, 18, v_alts_7894_);
    crate::leanh::lean_closure_set(v___f_7916_, 19, v___x_7895_);
    crate::leanh::lean_closure_set(v___f_7916_, 20, v___x_7896_);
    crate::leanh::lean_closure_set(v___f_7916_, 21, v___x_7897_);
    crate::leanh::lean_closure_set(v___f_7916_, 22, v_declName_7898_);
    crate::leanh::lean_closure_set(v___f_7916_, 23, v_levelParams_7899_);
    crate::leanh::lean_closure_set(v___f_7916_, 24, v_numIndices_7900_);
    crate::leanh::lean_closure_set(v___f_7916_, 25, v___x_7901_);
    crate::leanh::lean_closure_set(v___f_7916_, 26, v_numParams_7902_);
    crate::leanh::lean_closure_set(v___f_7916_, 27, v_snd_7903_);
    v___x_7917_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(
            v___x_7904_,
            v___x_7905_,
            v___f_7916_,
            v___x_7879_,
            v___x_7879_,
            v___y_7908_,
            v___y_7909_,
            v___y_7910_,
            v___y_7911_,
        );
    return v___x_7917_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__4___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_motive_7918_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_7919_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v___x_7920_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_7921_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_7922_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_is_7923_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_7924_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_7925_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_7926_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_7927_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_params_7928_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_7929_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_7930_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_heq_7931_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_val_7932_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___x_7933_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_tail_7934_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_alts_7935_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___x_7936_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___x_7937_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___x_7938_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_declName_7939_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v_levelParams_7940_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v_numIndices_7941_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v___x_7942_: *mut crate::leanh::LeanObject = *_args.add(24);
    let mut v_numParams_7943_: *mut crate::leanh::LeanObject = *_args.add(25);
    let mut v_snd_7944_: *mut crate::leanh::LeanObject = *_args.add(26);
    let mut v___x_7945_: *mut crate::leanh::LeanObject = *_args.add(27);
    let mut v___x_7946_: *mut crate::leanh::LeanObject = *_args.add(28);
    let mut v_ism1_x27_7947_: *mut crate::leanh::LeanObject = *_args.add(29);
    let mut v_x_7948_: *mut crate::leanh::LeanObject = *_args.add(30);
    let mut v___y_7949_: *mut crate::leanh::LeanObject = *_args.add(31);
    let mut v___y_7950_: *mut crate::leanh::LeanObject = *_args.add(32);
    let mut v___y_7951_: *mut crate::leanh::LeanObject = *_args.add(33);
    let mut v___y_7952_: *mut crate::leanh::LeanObject = *_args.add(34);
    let mut v___y_7953_: *mut crate::leanh::LeanObject = *_args.add(35);
    let mut v___x_16060__boxed_7954_: u8 = 0;
    let mut v___x_16061__boxed_7955_: u8 = 0;
    let mut v___x_16062__boxed_7956_: u8 = 0;
    let mut v_res_7957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_16060__boxed_7954_ = (crate::leanh::lean_unbox(v___x_7920_) as u8);
    v___x_16061__boxed_7955_ = (crate::leanh::lean_unbox(v___x_7921_) as u8);
    v___x_16062__boxed_7956_ = (crate::leanh::lean_unbox(v___x_7922_) as u8);
    v_res_7957_ = l_Lean_mkCasesOnSameCtor___lam__4(
        v_motive_7918_,
        v___x_7919_,
        v___x_16060__boxed_7954_,
        v___x_16061__boxed_7955_,
        v___x_16062__boxed_7956_,
        v_is_7923_,
        v___x_7924_,
        v___x_7925_,
        v___x_7926_,
        v___x_7927_,
        v_params_7928_,
        v___x_7929_,
        v___x_7930_,
        v_heq_7931_,
        v_val_7932_,
        v___x_7933_,
        v_tail_7934_,
        v_alts_7935_,
        v___x_7936_,
        v___x_7937_,
        v___x_7938_,
        v_declName_7939_,
        v_levelParams_7940_,
        v_numIndices_7941_,
        v___x_7942_,
        v_numParams_7943_,
        v_snd_7944_,
        v___x_7945_,
        v___x_7946_,
        v_ism1_x27_7947_,
        v_x_7948_,
        v___y_7949_,
        v___y_7950_,
        v___y_7951_,
        v___y_7952_,
    );
    crate::leanh::lean_dec(v___y_7952_);
    crate::leanh::lean_dec_ref(v___y_7951_);
    crate::leanh::lean_dec(v___y_7950_);
    crate::leanh::lean_dec_ref(v___y_7949_);
    crate::leanh::lean_dec_ref(v_x_7948_);
    return v_res_7957_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__5(
    mut v_numIndices_7958_: *mut crate::leanh::LeanObject,
    mut v___x_7959_: *mut crate::leanh::LeanObject,
    mut v_motive_7960_: *mut crate::leanh::LeanObject,
    mut v___x_7961_: *mut crate::leanh::LeanObject,
    mut v___x_7962_: u8,
    mut v___x_7963_: u8,
    mut v___x_7964_: u8,
    mut v_is_7965_: *mut crate::leanh::LeanObject,
    mut v___x_7966_: *mut crate::leanh::LeanObject,
    mut v___x_7967_: *mut crate::leanh::LeanObject,
    mut v___x_7968_: *mut crate::leanh::LeanObject,
    mut v___x_7969_: *mut crate::leanh::LeanObject,
    mut v_params_7970_: *mut crate::leanh::LeanObject,
    mut v___x_7971_: *mut crate::leanh::LeanObject,
    mut v___x_7972_: *mut crate::leanh::LeanObject,
    mut v_heq_7973_: *mut crate::leanh::LeanObject,
    mut v_val_7974_: *mut crate::leanh::LeanObject,
    mut v___x_7975_: *mut crate::leanh::LeanObject,
    mut v_tail_7976_: *mut crate::leanh::LeanObject,
    mut v___x_7977_: *mut crate::leanh::LeanObject,
    mut v___x_7978_: *mut crate::leanh::LeanObject,
    mut v___x_7979_: *mut crate::leanh::LeanObject,
    mut v_declName_7980_: *mut crate::leanh::LeanObject,
    mut v_levelParams_7981_: *mut crate::leanh::LeanObject,
    mut v___x_7982_: *mut crate::leanh::LeanObject,
    mut v_numParams_7983_: *mut crate::leanh::LeanObject,
    mut v_snd_7984_: *mut crate::leanh::LeanObject,
    mut v___x_7985_: *mut crate::leanh::LeanObject,
    mut v_alts_7986_: *mut crate::leanh::LeanObject,
    mut v___y_7987_: *mut crate::leanh::LeanObject,
    mut v___y_7988_: *mut crate::leanh::LeanObject,
    mut v___y_7989_: *mut crate::leanh::LeanObject,
    mut v___y_7990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7992_ = lean_nat_add(v_numIndices_7958_, v___x_7959_);
    v___x_7993_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_7993_, 0, v___x_7992_);
    v___x_7994_ = crate::leanh::lean_box((v___x_7962_) as usize);
    v___x_7995_ = crate::leanh::lean_box((v___x_7963_) as usize);
    v___x_7996_ = crate::leanh::lean_box((v___x_7964_) as usize);
    crate::leanh::lean_inc_ref(v___x_7993_);
    crate::leanh::lean_inc_ref(v___x_7985_);
    v___f_7997_ = crate::leanh::lean_alloc_closure(
        l_Lean_mkCasesOnSameCtor___lam__4___boxed as *mut core::ffi::c_void,
        36,
        29,
    );
    crate::leanh::lean_closure_set(v___f_7997_, 0, v_motive_7960_);
    crate::leanh::lean_closure_set(v___f_7997_, 1, v___x_7961_);
    crate::leanh::lean_closure_set(v___f_7997_, 2, v___x_7994_);
    crate::leanh::lean_closure_set(v___f_7997_, 3, v___x_7995_);
    crate::leanh::lean_closure_set(v___f_7997_, 4, v___x_7996_);
    crate::leanh::lean_closure_set(v___f_7997_, 5, v_is_7965_);
    crate::leanh::lean_closure_set(v___f_7997_, 6, v___x_7966_);
    crate::leanh::lean_closure_set(v___f_7997_, 7, v___x_7967_);
    crate::leanh::lean_closure_set(v___f_7997_, 8, v___x_7968_);
    crate::leanh::lean_closure_set(v___f_7997_, 9, v___x_7969_);
    crate::leanh::lean_closure_set(v___f_7997_, 10, v_params_7970_);
    crate::leanh::lean_closure_set(v___f_7997_, 11, v___x_7971_);
    crate::leanh::lean_closure_set(v___f_7997_, 12, v___x_7972_);
    crate::leanh::lean_closure_set(v___f_7997_, 13, v_heq_7973_);
    crate::leanh::lean_closure_set(v___f_7997_, 14, v_val_7974_);
    crate::leanh::lean_closure_set(v___f_7997_, 15, v___x_7975_);
    crate::leanh::lean_closure_set(v___f_7997_, 16, v_tail_7976_);
    crate::leanh::lean_closure_set(v___f_7997_, 17, v_alts_7986_);
    crate::leanh::lean_closure_set(v___f_7997_, 18, v___x_7977_);
    crate::leanh::lean_closure_set(v___f_7997_, 19, v___x_7978_);
    crate::leanh::lean_closure_set(v___f_7997_, 20, v___x_7979_);
    crate::leanh::lean_closure_set(v___f_7997_, 21, v_declName_7980_);
    crate::leanh::lean_closure_set(v___f_7997_, 22, v_levelParams_7981_);
    crate::leanh::lean_closure_set(v___f_7997_, 23, v_numIndices_7958_);
    crate::leanh::lean_closure_set(v___f_7997_, 24, v___x_7982_);
    crate::leanh::lean_closure_set(v___f_7997_, 25, v_numParams_7983_);
    crate::leanh::lean_closure_set(v___f_7997_, 26, v_snd_7984_);
    crate::leanh::lean_closure_set(v___f_7997_, 27, v___x_7985_);
    crate::leanh::lean_closure_set(v___f_7997_, 28, v___x_7993_);
    v___x_7998_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(
            v___x_7985_,
            v___x_7993_,
            v___f_7997_,
            v___x_7962_,
            v___x_7962_,
            v___y_7987_,
            v___y_7988_,
            v___y_7989_,
            v___y_7990_,
        );
    return v___x_7998_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__5___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_numIndices_7999_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_8000_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_motive_8001_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_8002_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_8003_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_8004_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_8005_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_is_8006_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_8007_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_8008_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_8009_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_8010_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_params_8011_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___x_8012_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___x_8013_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_heq_8014_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_val_8015_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___x_8016_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_tail_8017_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___x_8018_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___x_8019_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___x_8020_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v_declName_8021_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v_levelParams_8022_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v___x_8023_: *mut crate::leanh::LeanObject = *_args.add(24);
    let mut v_numParams_8024_: *mut crate::leanh::LeanObject = *_args.add(25);
    let mut v_snd_8025_: *mut crate::leanh::LeanObject = *_args.add(26);
    let mut v___x_8026_: *mut crate::leanh::LeanObject = *_args.add(27);
    let mut v_alts_8027_: *mut crate::leanh::LeanObject = *_args.add(28);
    let mut v___y_8028_: *mut crate::leanh::LeanObject = *_args.add(29);
    let mut v___y_8029_: *mut crate::leanh::LeanObject = *_args.add(30);
    let mut v___y_8030_: *mut crate::leanh::LeanObject = *_args.add(31);
    let mut v___y_8031_: *mut crate::leanh::LeanObject = *_args.add(32);
    let mut v___y_8032_: *mut crate::leanh::LeanObject = *_args.add(33);
    let mut v___x_16149__boxed_8033_: u8 = 0;
    let mut v___x_16150__boxed_8034_: u8 = 0;
    let mut v___x_16151__boxed_8035_: u8 = 0;
    let mut v_res_8036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_16149__boxed_8033_ = (crate::leanh::lean_unbox(v___x_8003_) as u8);
    v___x_16150__boxed_8034_ = (crate::leanh::lean_unbox(v___x_8004_) as u8);
    v___x_16151__boxed_8035_ = (crate::leanh::lean_unbox(v___x_8005_) as u8);
    v_res_8036_ = l_Lean_mkCasesOnSameCtor___lam__5(
        v_numIndices_7999_,
        v___x_8000_,
        v_motive_8001_,
        v___x_8002_,
        v___x_16149__boxed_8033_,
        v___x_16150__boxed_8034_,
        v___x_16151__boxed_8035_,
        v_is_8006_,
        v___x_8007_,
        v___x_8008_,
        v___x_8009_,
        v___x_8010_,
        v_params_8011_,
        v___x_8012_,
        v___x_8013_,
        v_heq_8014_,
        v_val_8015_,
        v___x_8016_,
        v_tail_8017_,
        v___x_8018_,
        v___x_8019_,
        v___x_8020_,
        v_declName_8021_,
        v_levelParams_8022_,
        v___x_8023_,
        v_numParams_8024_,
        v_snd_8025_,
        v___x_8026_,
        v_alts_8027_,
        v___y_8028_,
        v___y_8029_,
        v___y_8030_,
        v___y_8031_,
    );
    crate::leanh::lean_dec(v___y_8031_);
    crate::leanh::lean_dec_ref(v___y_8030_);
    crate::leanh::lean_dec(v___y_8029_);
    crate::leanh::lean_dec_ref(v___y_8028_);
    crate::leanh::lean_dec(v___x_8000_);
    return v_res_8036_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed(
    mut v_acc_8037_: *mut crate::leanh::LeanObject,
    mut v_declInfos_8038_: *mut crate::leanh::LeanObject,
    mut v_k_8039_: *mut crate::leanh::LeanObject,
    mut v_kind_8040_: *mut crate::leanh::LeanObject,
    mut v_x_8041_: *mut crate::leanh::LeanObject,
    mut v___y_8042_: *mut crate::leanh::LeanObject,
    mut v___y_8043_: *mut crate::leanh::LeanObject,
    mut v___y_8044_: *mut crate::leanh::LeanObject,
    mut v___y_8045_: *mut crate::leanh::LeanObject,
    mut v___y_8046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_8047_: u8 = 0;
    let mut v_res_8048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_8047_ = (crate::leanh::lean_unbox(v_kind_8040_) as u8);
    v_res_8048_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(v_acc_8037_, v_declInfos_8038_, v_k_8039_, v_kind_boxed_8047_, v_x_8041_, v___y_8042_, v___y_8043_, v___y_8044_, v___y_8045_);
    crate::leanh::lean_dec(v___y_8045_);
    crate::leanh::lean_dec_ref(v___y_8044_);
    crate::leanh::lean_dec(v___y_8043_);
    crate::leanh::lean_dec_ref(v___y_8042_);
    return v_res_8048_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(
    mut v_declInfos_8049_: *mut crate::leanh::LeanObject,
    mut v_k_8050_: *mut crate::leanh::LeanObject,
    mut v_kind_8051_: u8,
    mut v_acc_8052_: *mut crate::leanh::LeanObject,
    mut v___y_8053_: *mut crate::leanh::LeanObject,
    mut v___y_8054_: *mut crate::leanh::LeanObject,
    mut v___y_8055_: *mut crate::leanh::LeanObject,
    mut v___y_8056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_8059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_8060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_8061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_8062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_8063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_8075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8078_: u8 = 0;
    let mut v_toFunctor_8079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeq_8080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqLeft_8081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSeqRight_8082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8085_: u8 = 0;
    let mut v___f_8086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8100_: u8 = 0;
    let mut v___x_8101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8104_: u8 = 0;
    let mut v___f_8105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8118_: u8 = 0;
    let mut v___x_8119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8123_: u8 = 0;
    let mut v___x_8125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8127_: u8 = 0;
    let mut v_reuseFailAlloc_8128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8130_: u8 = 0;
    let mut v_unused_8131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8132_: u8 = 0;
    let mut v_unused_8133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8058_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1_once), _init_l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__1);
                v_toApplicative_8059_ = crate::leanh::lean_ctor_get(v___x_8058_, 0);
                v_toFunctor_8060_ = crate::leanh::lean_ctor_get(v_toApplicative_8059_, 0);
                v_toSeq_8061_ = crate::leanh::lean_ctor_get(v_toApplicative_8059_, 2);
                v_toSeqLeft_8062_ = crate::leanh::lean_ctor_get(v_toApplicative_8059_, 3);
                v_toSeqRight_8063_ = crate::leanh::lean_ctor_get(v_toApplicative_8059_, 4);
                v___f_8064_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__2;
                v___f_8065_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__3;
                crate::leanh::lean_inc_ref_n(v_toFunctor_8060_, 2);
                v___f_8066_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_8066_, 0, v_toFunctor_8060_);
                v___f_8067_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_8067_, 0, v_toFunctor_8060_);
                v___x_8068_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8068_, 0, v___f_8066_);
                crate::leanh::lean_ctor_set(v___x_8068_, 1, v___f_8067_);
                crate::leanh::lean_inc(v_toSeqRight_8063_);
                v___f_8069_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_8069_, 0, v_toSeqRight_8063_);
                crate::leanh::lean_inc(v_toSeqLeft_8062_);
                v___f_8070_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_8070_, 0, v_toSeqLeft_8062_);
                crate::leanh::lean_inc(v_toSeq_8061_);
                v___f_8071_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_8071_, 0, v_toSeq_8061_);
                v___x_8072_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8072_, 0, v___x_8068_);
                crate::leanh::lean_ctor_set(v___x_8072_, 1, v___f_8064_);
                crate::leanh::lean_ctor_set(v___x_8072_, 2, v___f_8071_);
                crate::leanh::lean_ctor_set(v___x_8072_, 3, v___f_8070_);
                crate::leanh::lean_ctor_set(v___x_8072_, 4, v___f_8069_);
                v___x_8073_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8073_, 0, v___x_8072_);
                crate::leanh::lean_ctor_set(v___x_8073_, 1, v___f_8065_);
                v___x_8074_ = l_StateRefT_x27_instMonad___redArg(v___x_8073_);
                v_toApplicative_8075_ = crate::leanh::lean_ctor_get(v___x_8074_, 0);
                v_isSharedCheck_8132_ = (!crate::leanh::lean_is_exclusive(v___x_8074_)) as u8;
                if v_isSharedCheck_8132_ == 0 {
                    v_unused_8133_ = crate::leanh::lean_ctor_get(v___x_8074_, 1);
                    crate::leanh::lean_dec(v_unused_8133_);
                    v___x_8077_ = v___x_8074_;
                    v_isShared_8078_ = v_isSharedCheck_8132_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toApplicative_8075_);
                    crate::leanh::lean_dec(v___x_8074_);
                    v___x_8077_ = crate::leanh::lean_box(0);
                    v_isShared_8078_ = v_isSharedCheck_8132_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_8079_ = crate::leanh::lean_ctor_get(v_toApplicative_8075_, 0);
                v_toSeq_8080_ = crate::leanh::lean_ctor_get(v_toApplicative_8075_, 2);
                v_toSeqLeft_8081_ = crate::leanh::lean_ctor_get(v_toApplicative_8075_, 3);
                v_toSeqRight_8082_ = crate::leanh::lean_ctor_get(v_toApplicative_8075_, 4);
                v_isSharedCheck_8130_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_8075_)) as u8;
                if v_isSharedCheck_8130_ == 0 {
                    v_unused_8131_ = crate::leanh::lean_ctor_get(v_toApplicative_8075_, 1);
                    crate::leanh::lean_dec(v_unused_8131_);
                    v___x_8084_ = v_toApplicative_8075_;
                    v_isShared_8085_ = v_isSharedCheck_8130_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toSeqRight_8082_);
                    crate::leanh::lean_inc(v_toSeqLeft_8081_);
                    crate::leanh::lean_inc(v_toSeq_8080_);
                    crate::leanh::lean_inc(v_toFunctor_8079_);
                    crate::leanh::lean_dec(v_toApplicative_8075_);
                    v___x_8084_ = crate::leanh::lean_box(0);
                    v_isShared_8085_ = v_isSharedCheck_8130_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___f_8086_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__4;
                v___f_8087_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___closed__5;
                crate::leanh::lean_inc_ref(v_toFunctor_8079_);
                v___f_8088_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_8088_, 0, v_toFunctor_8079_);
                v___f_8089_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instFunctorOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_8089_, 0, v_toFunctor_8079_);
                v___x_8090_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8090_, 0, v___f_8088_);
                crate::leanh::lean_ctor_set(v___x_8090_, 1, v___f_8089_);
                v___f_8091_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_8091_, 0, v_toSeqRight_8082_);
                v___f_8092_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_8092_, 0, v_toSeqLeft_8081_);
                v___f_8093_ = crate::leanh::lean_alloc_closure(
                    l_ReaderT_instApplicativeOfMonad___redArg___lam__4 as *mut core::ffi::c_void,
                    6,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_8093_, 0, v_toSeq_8080_);
                if v_isShared_8085_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8084_, 4, v___f_8091_);
                    crate::leanh::lean_ctor_set(v___x_8084_, 3, v___f_8092_);
                    crate::leanh::lean_ctor_set(v___x_8084_, 2, v___f_8093_);
                    crate::leanh::lean_ctor_set(v___x_8084_, 1, v___f_8086_);
                    crate::leanh::lean_ctor_set(v___x_8084_, 0, v___x_8090_);
                    v___x_8095_ = v___x_8084_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8129_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8129_, 0, v___x_8090_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8129_, 1, v___f_8086_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8129_, 2, v___f_8093_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8129_, 3, v___f_8092_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8129_, 4, v___f_8091_);
                    v___x_8095_ = v_reuseFailAlloc_8129_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_8078_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_8077_, 1, v___f_8087_);
                    crate::leanh::lean_ctor_set(v___x_8077_, 0, v___x_8095_);
                    v___x_8097_ = v___x_8077_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8128_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8128_, 0, v___x_8095_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8128_, 1, v___f_8087_);
                    v___x_8097_ = v_reuseFailAlloc_8128_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_8098_ = lean_array_get_size(v_acc_8052_);
                v___x_8099_ = lean_array_get_size(v_declInfos_8049_);
                v___x_8100_ = lean_nat_dec_lt(v___x_8098_, v___x_8099_);
                if v___x_8100_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_8097_);
                    crate::leanh::lean_dec_ref(v_declInfos_8049_);
                    crate::leanh::lean_inc(v___y_8056_);
                    crate::leanh::lean_inc_ref(v___y_8055_);
                    crate::leanh::lean_inc(v___y_8054_);
                    crate::leanh::lean_inc_ref(v___y_8053_);
                    v___x_8101_ = crate::leanh::lean_apply_6(
                        v_k_8050_,
                        v_acc_8052_,
                        v___y_8053_,
                        v___y_8054_,
                        v___y_8055_,
                        v___y_8056_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_8101_;
                } else {
                    v___f_8102_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17_spec__22___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                    crate::leanh::lean_closure_set(v___f_8102_, 0, v___x_8097_);
                    v___x_8103_ = crate::leanh::lean_box(0);
                    v___x_8104_ = 0;
                    v___f_8105_ = crate::leanh::lean_alloc_closure(
                        l_Pi_instInhabited___redArg___lam__0 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_8105_, 0, v___f_8102_);
                    v___x_8106_ = crate::leanh::lean_box((v___x_8104_) as usize);
                    v___x_8107_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_8107_, 0, v___x_8106_);
                    crate::leanh::lean_ctor_set(v___x_8107_, 1, v___f_8105_);
                    v___x_8108_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_8108_, 0, v___x_8103_);
                    crate::leanh::lean_ctor_set(v___x_8108_, 1, v___x_8107_);
                    v___x_8109_ = lean_array_get(v___x_8108_, v_declInfos_8049_, v___x_8098_);
                    crate::leanh::lean_dec_ref_known(v___x_8108_, 2);
                    v_snd_8110_ = crate::leanh::lean_ctor_get(v___x_8109_, 1);
                    crate::leanh::lean_inc(v_snd_8110_);
                    v_fst_8111_ = crate::leanh::lean_ctor_get(v___x_8109_, 0);
                    crate::leanh::lean_inc(v_fst_8111_);
                    crate::leanh::lean_dec(v___x_8109_);
                    v_fst_8112_ = crate::leanh::lean_ctor_get(v_snd_8110_, 0);
                    crate::leanh::lean_inc(v_fst_8112_);
                    v_snd_8113_ = crate::leanh::lean_ctor_get(v_snd_8110_, 1);
                    crate::leanh::lean_inc(v_snd_8113_);
                    crate::leanh::lean_dec(v_snd_8110_);
                    crate::leanh::lean_inc(v___y_8056_);
                    crate::leanh::lean_inc_ref(v___y_8055_);
                    crate::leanh::lean_inc(v___y_8054_);
                    crate::leanh::lean_inc_ref(v___y_8053_);
                    crate::leanh::lean_inc_ref(v_acc_8052_);
                    v___x_8114_ = crate::leanh::lean_apply_6(
                        v_snd_8113_,
                        v_acc_8052_,
                        v___y_8053_,
                        v___y_8054_,
                        v___y_8055_,
                        v___y_8056_,
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_8114_) == 0 {
                        v_a_8115_ = crate::leanh::lean_ctor_get(v___x_8114_, 0);
                        crate::leanh::lean_inc(v_a_8115_);
                        crate::leanh::lean_dec_ref_known(v___x_8114_, 1);
                        v___x_8116_ = crate::leanh::lean_box((v_kind_8051_) as usize);
                        v___f_8117_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1___boxed as *mut core::ffi::c_void, 10, 4);
                        crate::leanh::lean_closure_set(v___f_8117_, 0, v_acc_8052_);
                        crate::leanh::lean_closure_set(v___f_8117_, 1, v_declInfos_8049_);
                        crate::leanh::lean_closure_set(v___f_8117_, 2, v_k_8050_);
                        crate::leanh::lean_closure_set(v___f_8117_, 3, v___x_8116_);
                        v___x_8118_ = (crate::leanh::lean_unbox(v_fst_8112_) as u8);
                        crate::leanh::lean_dec(v_fst_8112_);
                        v___x_8119_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v_fst_8111_, v___x_8118_, v_a_8115_, v___f_8117_, v_kind_8051_, v___y_8053_, v___y_8054_, v___y_8055_, v___y_8056_);
                        return v___x_8119_;
                    } else {
                        crate::leanh::lean_dec(v_fst_8112_);
                        crate::leanh::lean_dec(v_fst_8111_);
                        crate::leanh::lean_dec_ref(v_acc_8052_);
                        crate::leanh::lean_dec_ref(v_k_8050_);
                        crate::leanh::lean_dec_ref(v_declInfos_8049_);
                        v_a_8120_ = crate::leanh::lean_ctor_get(v___x_8114_, 0);
                        v_isSharedCheck_8127_ =
                            (!crate::leanh::lean_is_exclusive(v___x_8114_)) as u8;
                        if v_isSharedCheck_8127_ == 0 {
                            v___x_8122_ = v___x_8114_;
                            v_isShared_8123_ = v_isSharedCheck_8127_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_8120_);
                            crate::leanh::lean_dec(v___x_8114_);
                            v___x_8122_ = crate::leanh::lean_box(0);
                            v_isShared_8123_ = v_isSharedCheck_8127_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            5 => {
                if v_isShared_8123_ == 0 {
                    v___x_8125_ = v___x_8122_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8126_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8126_, 0, v_a_8120_);
                    v___x_8125_ = v_reuseFailAlloc_8126_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8125_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___lam__1(
    mut v_acc_8134_: *mut crate::leanh::LeanObject,
    mut v_declInfos_8135_: *mut crate::leanh::LeanObject,
    mut v_k_8136_: *mut crate::leanh::LeanObject,
    mut v_kind_8137_: u8,
    mut v_x_8138_: *mut crate::leanh::LeanObject,
    mut v___y_8139_: *mut crate::leanh::LeanObject,
    mut v___y_8140_: *mut crate::leanh::LeanObject,
    mut v___y_8141_: *mut crate::leanh::LeanObject,
    mut v___y_8142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8144_ = lean_array_push(v_acc_8134_, v_x_8138_);
    v___x_8145_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_8135_, v_k_8136_, v_kind_8137_, v___x_8144_, v___y_8139_, v___y_8140_, v___y_8141_, v___y_8142_);
    return v___x_8145_;
}
pub unsafe fn l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6___boxed(
    mut v_declInfos_8146_: *mut crate::leanh::LeanObject,
    mut v_k_8147_: *mut crate::leanh::LeanObject,
    mut v_kind_8148_: *mut crate::leanh::LeanObject,
    mut v_acc_8149_: *mut crate::leanh::LeanObject,
    mut v___y_8150_: *mut crate::leanh::LeanObject,
    mut v___y_8151_: *mut crate::leanh::LeanObject,
    mut v___y_8152_: *mut crate::leanh::LeanObject,
    mut v___y_8153_: *mut crate::leanh::LeanObject,
    mut v___y_8154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_8155_: u8 = 0;
    let mut v_res_8156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_8155_ = (crate::leanh::lean_unbox(v_kind_8148_) as u8);
    v_res_8156_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_8146_, v_k_8147_, v_kind_boxed_8155_, v_acc_8149_, v___y_8150_, v___y_8151_, v___y_8152_, v___y_8153_);
    crate::leanh::lean_dec(v___y_8153_);
    crate::leanh::lean_dec_ref(v___y_8152_);
    crate::leanh::lean_dec(v___y_8151_);
    crate::leanh::lean_dec_ref(v___y_8150_);
    return v_res_8156_;
}
pub unsafe fn l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(
    mut v_declInfos_8157_: *mut crate::leanh::LeanObject,
    mut v_k_8158_: *mut crate::leanh::LeanObject,
    mut v_kind_8159_: u8,
    mut v___y_8160_: *mut crate::leanh::LeanObject,
    mut v___y_8161_: *mut crate::leanh::LeanObject,
    mut v___y_8162_: *mut crate::leanh::LeanObject,
    mut v___y_8163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8165_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__17___closed__0;
    v___x_8166_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDecls_loop___at___00Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5_spec__6(v_declInfos_8157_, v_k_8158_, v_kind_8159_, v___x_8165_, v___y_8160_, v___y_8161_, v___y_8162_, v___y_8163_);
    return v___x_8166_;
}
pub unsafe fn l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5___boxed(
    mut v_declInfos_8167_: *mut crate::leanh::LeanObject,
    mut v_k_8168_: *mut crate::leanh::LeanObject,
    mut v_kind_8169_: *mut crate::leanh::LeanObject,
    mut v___y_8170_: *mut crate::leanh::LeanObject,
    mut v___y_8171_: *mut crate::leanh::LeanObject,
    mut v___y_8172_: *mut crate::leanh::LeanObject,
    mut v___y_8173_: *mut crate::leanh::LeanObject,
    mut v___y_8174_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_8175_: u8 = 0;
    let mut v_res_8176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_8175_ = (crate::leanh::lean_unbox(v_kind_8169_) as u8);
    v_res_8176_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v_declInfos_8167_, v_k_8168_, v_kind_boxed_8175_, v___y_8170_, v___y_8171_, v___y_8172_, v___y_8173_);
    crate::leanh::lean_dec(v___y_8173_);
    crate::leanh::lean_dec_ref(v___y_8172_);
    crate::leanh::lean_dec(v___y_8171_);
    crate::leanh::lean_dec_ref(v___y_8170_);
    return v_res_8176_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(
    mut v_declInfos_8177_: *mut crate::leanh::LeanObject,
    mut v_k_8178_: *mut crate::leanh::LeanObject,
    mut v_kind_8179_: u8,
    mut v___y_8180_: *mut crate::leanh::LeanObject,
    mut v___y_8181_: *mut crate::leanh::LeanObject,
    mut v___y_8182_: *mut crate::leanh::LeanObject,
    mut v___y_8183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_8185_: usize = 0;
    let mut v___x_8186_: usize = 0;
    let mut v___x_8187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_8185_ = lean_array_size(v_declInfos_8177_);
    v___x_8186_ = 0usize;
    v___x_8187_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__9_spec__16(v_sz_8185_, v___x_8186_, v_declInfos_8177_);
    v___x_8188_ = l_Lean_Meta_withLocalDecls___at___00Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4_spec__5(v___x_8187_, v_k_8178_, v_kind_8179_, v___y_8180_, v___y_8181_, v___y_8182_, v___y_8183_);
    return v___x_8188_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4___boxed(
    mut v_declInfos_8189_: *mut crate::leanh::LeanObject,
    mut v_k_8190_: *mut crate::leanh::LeanObject,
    mut v_kind_8191_: *mut crate::leanh::LeanObject,
    mut v___y_8192_: *mut crate::leanh::LeanObject,
    mut v___y_8193_: *mut crate::leanh::LeanObject,
    mut v___y_8194_: *mut crate::leanh::LeanObject,
    mut v___y_8195_: *mut crate::leanh::LeanObject,
    mut v___y_8196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_8197_: u8 = 0;
    let mut v_res_8198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_8197_ = (crate::leanh::lean_unbox(v_kind_8191_) as u8);
    v_res_8198_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v_declInfos_8189_, v_k_8190_, v_kind_boxed_8197_, v___y_8192_, v___y_8193_, v___y_8194_, v___y_8195_);
    crate::leanh::lean_dec(v___y_8195_);
    crate::leanh::lean_dec_ref(v___y_8194_);
    crate::leanh::lean_dec(v___y_8193_);
    crate::leanh::lean_dec_ref(v___y_8192_);
    return v_res_8198_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(
    mut v_declInfos_8199_: *mut crate::leanh::LeanObject,
    mut v_k_8200_: *mut crate::leanh::LeanObject,
    mut v_kind_8201_: u8,
    mut v___y_8202_: *mut crate::leanh::LeanObject,
    mut v___y_8203_: *mut crate::leanh::LeanObject,
    mut v___y_8204_: *mut crate::leanh::LeanObject,
    mut v___y_8205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_8207_: usize = 0;
    let mut v___x_8208_: usize = 0;
    let mut v___x_8209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_8207_ = lean_array_size(v_declInfos_8199_);
    v___x_8208_ = 0usize;
    v___x_8209_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtorHet_spec__7_spec__8(v_sz_8207_, v___x_8208_, v_declInfos_8199_);
    v___x_8210_ = l_Lean_Meta_withLocalDeclsD___at___00Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4_spec__4(v___x_8209_, v_k_8200_, v_kind_8201_, v___y_8202_, v___y_8203_, v___y_8204_, v___y_8205_);
    return v___x_8210_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4___boxed(
    mut v_declInfos_8211_: *mut crate::leanh::LeanObject,
    mut v_k_8212_: *mut crate::leanh::LeanObject,
    mut v_kind_8213_: *mut crate::leanh::LeanObject,
    mut v___y_8214_: *mut crate::leanh::LeanObject,
    mut v___y_8215_: *mut crate::leanh::LeanObject,
    mut v___y_8216_: *mut crate::leanh::LeanObject,
    mut v___y_8217_: *mut crate::leanh::LeanObject,
    mut v___y_8218_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_kind_boxed_8219_: u8 = 0;
    let mut v_res_8220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_8219_ = (crate::leanh::lean_unbox(v_kind_8213_) as u8);
    v_res_8220_ = l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(
        v_declInfos_8211_,
        v_k_8212_,
        v_kind_boxed_8219_,
        v___y_8214_,
        v___y_8215_,
        v___y_8216_,
        v___y_8217_,
    );
    crate::leanh::lean_dec(v___y_8217_);
    crate::leanh::lean_dec_ref(v___y_8216_);
    crate::leanh::lean_dec(v___y_8215_);
    crate::leanh::lean_dec_ref(v___y_8214_);
    return v_res_8220_;
}
pub unsafe fn _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_8223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8223_ = crate::leanh::lean_box(0);
    v___x_8224_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__0;
    v___x_8225_ = l_Lean_mkConst(v___x_8224_, v___x_8223_);
    return v___x_8225_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(
    mut v_j_8226_: *mut crate::leanh::LeanObject,
    mut v___x_8227_: *mut crate::leanh::LeanObject,
    mut v_motive_8228_: *mut crate::leanh::LeanObject,
    mut v_isZero_8229_: u8,
    mut v___x_8230_: u8,
    mut v___x_8231_: u8,
    mut v___x_8232_: *mut crate::leanh::LeanObject,
    mut v___x_8233_: *mut crate::leanh::LeanObject,
    mut v___x_8234_: *mut crate::leanh::LeanObject,
    mut v_zs12_8235_: *mut crate::leanh::LeanObject,
    mut v_is_8236_: *mut crate::leanh::LeanObject,
    mut v_fields1_8237_: *mut crate::leanh::LeanObject,
    mut v_fields2_8238_: *mut crate::leanh::LeanObject,
    mut v___y_8239_: *mut crate::leanh::LeanObject,
    mut v___y_8240_: *mut crate::leanh::LeanObject,
    mut v___y_8241_: *mut crate::leanh::LeanObject,
    mut v___y_8242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_8245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8248_: u8 = 0;
    let mut v___x_8249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_8254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_8255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8279_: u8 = 0;
    let mut v___x_8280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8286_: u8 = 0;
    let mut v___x_8288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8290_: u8 = 0;
    let mut v_a_8291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8294_: u8 = 0;
    let mut v___x_8296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8298_: u8 = 0;
    let mut v_a_8299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8302_: u8 = 0;
    let mut v___x_8304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8306_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_j_8226_);
                v___x_8264_ = l_Lean_mkNatLit(v_j_8226_);
                v___x_8265_ = l_Lean_Meta_mkEqRefl(
                    v___x_8264_,
                    v___y_8239_,
                    v___y_8240_,
                    v___y_8241_,
                    v___y_8242_,
                );
                if crate::leanh::lean_obj_tag(v___x_8265_) == 0 {
                    v_a_8266_ = crate::leanh::lean_ctor_get(v___x_8265_, 0);
                    crate::leanh::lean_inc(v_a_8266_);
                    crate::leanh::lean_dec_ref_known(v___x_8265_, 1);
                    crate::leanh::lean_inc_ref(v___x_8227_);
                    v___x_8267_ = l_Lean_mkAppN(v___x_8227_, v_fields1_8237_);
                    v___x_8268_ = l_Lean_mkAppN(v___x_8227_, v_fields2_8238_);
                    v___x_8269_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_8270_ = lean_mk_empty_array_with_capacity(v___x_8269_);
                    v___x_8271_ = lean_array_push(v___x_8270_, v___x_8267_);
                    v___x_8272_ = lean_array_push(v___x_8271_, v___x_8268_);
                    v___x_8273_ = lean_array_push(v___x_8272_, v_a_8266_);
                    v___x_8274_ = l_Array_append___redArg(v_is_8236_, v___x_8273_);
                    crate::leanh::lean_dec_ref(v___x_8273_);
                    v___x_8275_ = l_Lean_mkAppN(v_motive_8228_, v___x_8274_);
                    crate::leanh::lean_dec_ref(v___x_8274_);
                    v___x_8276_ = l_Lean_Meta_mkForallFVars(
                        v_zs12_8235_,
                        v___x_8275_,
                        v_isZero_8229_,
                        v___x_8230_,
                        v___x_8230_,
                        v___x_8231_,
                        v___y_8239_,
                        v___y_8240_,
                        v___y_8241_,
                        v___y_8242_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_8276_) == 0 {
                        v_a_8277_ = crate::leanh::lean_ctor_get(v___x_8276_, 0);
                        crate::leanh::lean_inc(v_a_8277_);
                        crate::leanh::lean_dec_ref_known(v___x_8276_, 1);
                        v___x_8278_ = lean_array_get_size(v_zs12_8235_);
                        v___x_8279_ = lean_nat_dec_eq(v___x_8278_, v___x_8232_);
                        if v___x_8279_ == 0 {
                            v_e_8254_ = v_a_8277_;
                            state = 2;
                            continue;
                        } else {
                            v___x_8280_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1_once), _init_l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___closed__1);
                            v___x_8281_ =
                                l_Lean_mkArrow(v___x_8280_, v_a_8277_, v___y_8241_, v___y_8242_);
                            if crate::leanh::lean_obj_tag(v___x_8281_) == 0 {
                                v_a_8282_ = crate::leanh::lean_ctor_get(v___x_8281_, 0);
                                crate::leanh::lean_inc(v_a_8282_);
                                crate::leanh::lean_dec_ref_known(v___x_8281_, 1);
                                v_e_8254_ = v_a_8282_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_8233_);
                                crate::leanh::lean_dec(v___x_8232_);
                                crate::leanh::lean_dec(v_j_8226_);
                                v_a_8283_ = crate::leanh::lean_ctor_get(v___x_8281_, 0);
                                v_isSharedCheck_8290_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_8281_)) as u8;
                                if v_isSharedCheck_8290_ == 0 {
                                    v___x_8285_ = v___x_8281_;
                                    v_isShared_8286_ = v_isSharedCheck_8290_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_8283_);
                                    crate::leanh::lean_dec(v___x_8281_);
                                    v___x_8285_ = crate::leanh::lean_box(0);
                                    v_isShared_8286_ = v_isSharedCheck_8290_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_8233_);
                        crate::leanh::lean_dec(v___x_8232_);
                        crate::leanh::lean_dec(v_j_8226_);
                        v_a_8291_ = crate::leanh::lean_ctor_get(v___x_8276_, 0);
                        v_isSharedCheck_8298_ =
                            (!crate::leanh::lean_is_exclusive(v___x_8276_)) as u8;
                        if v_isSharedCheck_8298_ == 0 {
                            v___x_8293_ = v___x_8276_;
                            v_isShared_8294_ = v_isSharedCheck_8298_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_8291_);
                            crate::leanh::lean_dec(v___x_8276_);
                            v___x_8293_ = crate::leanh::lean_box(0);
                            v_isShared_8294_ = v_isSharedCheck_8298_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_is_8236_);
                    crate::leanh::lean_dec(v___x_8233_);
                    crate::leanh::lean_dec(v___x_8232_);
                    crate::leanh::lean_dec_ref(v_motive_8228_);
                    crate::leanh::lean_dec_ref(v___x_8227_);
                    crate::leanh::lean_dec(v_j_8226_);
                    v_a_8299_ = crate::leanh::lean_ctor_get(v___x_8265_, 0);
                    v_isSharedCheck_8306_ = (!crate::leanh::lean_is_exclusive(v___x_8265_)) as u8;
                    if v_isSharedCheck_8306_ == 0 {
                        v___x_8301_ = v___x_8265_;
                        v_isShared_8302_ = v_isSharedCheck_8306_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8299_);
                        crate::leanh::lean_dec(v___x_8265_);
                        v___x_8301_ = crate::leanh::lean_box(0);
                        v_isShared_8302_ = v_isSharedCheck_8306_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8247_ = lean_array_get_size(v_zs12_8235_);
                v___x_8248_ = lean_nat_dec_eq(v___x_8247_, v___x_8232_);
                v___x_8249_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_8249_, 0, v___x_8247_);
                crate::leanh::lean_ctor_set(v___x_8249_, 1, v___x_8232_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_8249_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    v___x_8248_,
                );
                v___x_8250_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8250_, 0, v___y_8246_);
                crate::leanh::lean_ctor_set(v___x_8250_, 1, v___y_8245_);
                v___x_8251_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8251_, 0, v___x_8250_);
                crate::leanh::lean_ctor_set(v___x_8251_, 1, v___x_8249_);
                v___x_8252_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_8252_, 0, v___x_8251_);
                return v___x_8252_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___x_8233_) == 1 {
                    crate::leanh::lean_dec(v_j_8226_);
                    v_str_8255_ = crate::leanh::lean_ctor_get(v___x_8233_, 1);
                    crate::leanh::lean_inc_ref(v_str_8255_);
                    crate::leanh::lean_dec_ref_known(v___x_8233_, 2);
                    v___x_8256_ = crate::leanh::lean_box(0);
                    v___x_8257_ = l_Lean_Name_str___override(v___x_8256_, v_str_8255_);
                    v___y_8245_ = v_e_8254_;
                    v___y_8246_ = v___x_8257_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_8233_);
                    v___x_8258_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__6___redArg___lam__0___closed__0;
                    v___x_8259_ = lean_nat_add(v_j_8226_, v___x_8234_);
                    crate::leanh::lean_dec(v_j_8226_);
                    v___x_8260_ = l_Nat_reprFast(v___x_8259_);
                    v___x_8261_ = lean_string_append(v___x_8258_, v___x_8260_);
                    crate::leanh::lean_dec_ref(v___x_8260_);
                    v___x_8262_ = crate::leanh::lean_box(0);
                    v___x_8263_ = l_Lean_Name_str___override(v___x_8262_, v___x_8261_);
                    v___y_8245_ = v_e_8254_;
                    v___y_8246_ = v___x_8263_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                if v_isShared_8286_ == 0 {
                    v___x_8288_ = v___x_8285_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8289_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8289_, 0, v_a_8283_);
                    v___x_8288_ = v_reuseFailAlloc_8289_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8288_;
            }
            5 => {
                if v_isShared_8294_ == 0 {
                    v___x_8296_ = v___x_8293_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8297_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8297_, 0, v_a_8291_);
                    v___x_8296_ = v_reuseFailAlloc_8297_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8296_;
            }
            7 => {
                if v_isShared_8302_ == 0 {
                    v___x_8304_ = v___x_8301_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8305_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8305_, 0, v_a_8299_);
                    v___x_8304_ = v_reuseFailAlloc_8305_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_8304_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_j_8307_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_8308_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_motive_8309_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_isZero_8310_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v___x_8311_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_8312_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_8313_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_8314_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_8315_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_zs12_8316_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_is_8317_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_fields1_8318_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_fields2_8319_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_8320_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_8321_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_8322_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_8323_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_8324_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_isZero_boxed_8325_: u8 = 0;
    let mut v___x_16487__boxed_8326_: u8 = 0;
    let mut v___x_16488__boxed_8327_: u8 = 0;
    let mut v_res_8328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isZero_boxed_8325_ = (crate::leanh::lean_unbox(v_isZero_8310_) as u8);
    v___x_16487__boxed_8326_ = (crate::leanh::lean_unbox(v___x_8311_) as u8);
    v___x_16488__boxed_8327_ = (crate::leanh::lean_unbox(v___x_8312_) as u8);
    v_res_8328_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0(
        v_j_8307_,
        v___x_8308_,
        v_motive_8309_,
        v_isZero_boxed_8325_,
        v___x_16487__boxed_8326_,
        v___x_16488__boxed_8327_,
        v___x_8313_,
        v___x_8314_,
        v___x_8315_,
        v_zs12_8316_,
        v_is_8317_,
        v_fields1_8318_,
        v_fields2_8319_,
        v___y_8320_,
        v___y_8321_,
        v___y_8322_,
        v___y_8323_,
    );
    crate::leanh::lean_dec(v___y_8323_);
    crate::leanh::lean_dec_ref(v___y_8322_);
    crate::leanh::lean_dec(v___y_8321_);
    crate::leanh::lean_dec_ref(v___y_8320_);
    crate::leanh::lean_dec_ref(v_fields2_8319_);
    crate::leanh::lean_dec_ref(v_fields1_8318_);
    crate::leanh::lean_dec_ref(v_zs12_8316_);
    crate::leanh::lean_dec(v___x_8315_);
    return v_res_8328_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(
    mut v_tail_8329_: *mut crate::leanh::LeanObject,
    mut v_params_8330_: *mut crate::leanh::LeanObject,
    mut v_motive_8331_: *mut crate::leanh::LeanObject,
    mut v_as_8332_: *mut crate::leanh::LeanObject,
    mut v_i_8333_: *mut crate::leanh::LeanObject,
    mut v_j_8334_: *mut crate::leanh::LeanObject,
    mut v_bs_8335_: *mut crate::leanh::LeanObject,
    mut v___y_8336_: *mut crate::leanh::LeanObject,
    mut v___y_8337_: *mut crate::leanh::LeanObject,
    mut v___y_8338_: *mut crate::leanh::LeanObject,
    mut v___y_8339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_8341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_8342_: u8 = 0;
    let mut v___x_8343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8345_: u8 = 0;
    let mut v___x_8346_: u8 = 0;
    let mut v___x_8347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_8356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8363_: u8 = 0;
    let mut v___x_8365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8367_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_8341_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_8342_ = lean_nat_dec_eq(v_i_8333_, v_zero_8341_);
                if v_isZero_8342_ == 1 {
                    crate::leanh::lean_dec(v_j_8334_);
                    crate::leanh::lean_dec(v_i_8333_);
                    crate::leanh::lean_dec_ref(v_motive_8331_);
                    crate::leanh::lean_dec(v_tail_8329_);
                    v___x_8343_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_8343_, 0, v_bs_8335_);
                    return v___x_8343_;
                } else {
                    v___x_8344_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_8345_ = 1;
                    v___x_8346_ = 1;
                    v___x_8347_ = lean_array_fget_borrowed(v_as_8332_, v_j_8334_);
                    crate::leanh::lean_inc(v_tail_8329_);
                    crate::leanh::lean_inc_n(v___x_8347_, 2);
                    v___x_8348_ = l_Lean_mkConst(v___x_8347_, v_tail_8329_);
                    v___x_8349_ = l_Lean_mkAppN(v___x_8348_, v_params_8330_);
                    v___x_8350_ = crate::leanh::lean_box((v_isZero_8342_) as usize);
                    v___x_8351_ = crate::leanh::lean_box((v___x_8345_) as usize);
                    v___x_8352_ = crate::leanh::lean_box((v___x_8346_) as usize);
                    crate::leanh::lean_inc_ref(v_motive_8331_);
                    crate::leanh::lean_inc_ref(v___x_8349_);
                    crate::leanh::lean_inc(v_j_8334_);
                    v___f_8353_ = crate::leanh::lean_alloc_closure(l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 18, 9);
                    crate::leanh::lean_closure_set(v___f_8353_, 0, v_j_8334_);
                    crate::leanh::lean_closure_set(v___f_8353_, 1, v___x_8349_);
                    crate::leanh::lean_closure_set(v___f_8353_, 2, v_motive_8331_);
                    crate::leanh::lean_closure_set(v___f_8353_, 3, v___x_8350_);
                    crate::leanh::lean_closure_set(v___f_8353_, 4, v___x_8351_);
                    crate::leanh::lean_closure_set(v___f_8353_, 5, v___x_8352_);
                    crate::leanh::lean_closure_set(v___f_8353_, 6, v_zero_8341_);
                    crate::leanh::lean_closure_set(v___f_8353_, 7, v___x_8347_);
                    crate::leanh::lean_closure_set(v___f_8353_, 8, v___x_8344_);
                    v___x_8354_ = l_Lean_Meta_withSharedCtorIndices___redArg(
                        v___x_8349_,
                        v___f_8353_,
                        v___y_8336_,
                        v___y_8337_,
                        v___y_8338_,
                        v___y_8339_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_8354_) == 0 {
                        v_a_8355_ = crate::leanh::lean_ctor_get(v___x_8354_, 0);
                        crate::leanh::lean_inc(v_a_8355_);
                        crate::leanh::lean_dec_ref_known(v___x_8354_, 1);
                        v_n_8356_ = lean_nat_sub(v_i_8333_, v___x_8344_);
                        crate::leanh::lean_dec(v_i_8333_);
                        v___x_8357_ = lean_nat_add(v_j_8334_, v___x_8344_);
                        crate::leanh::lean_dec(v_j_8334_);
                        v___x_8358_ = lean_array_push(v_bs_8335_, v_a_8355_);
                        v_i_8333_ = v_n_8356_;
                        v_j_8334_ = v___x_8357_;
                        v_bs_8335_ = v___x_8358_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_8335_);
                        crate::leanh::lean_dec(v_j_8334_);
                        crate::leanh::lean_dec(v_i_8333_);
                        crate::leanh::lean_dec_ref(v_motive_8331_);
                        crate::leanh::lean_dec(v_tail_8329_);
                        v_a_8360_ = crate::leanh::lean_ctor_get(v___x_8354_, 0);
                        v_isSharedCheck_8367_ =
                            (!crate::leanh::lean_is_exclusive(v___x_8354_)) as u8;
                        if v_isSharedCheck_8367_ == 0 {
                            v___x_8362_ = v___x_8354_;
                            v_isShared_8363_ = v_isSharedCheck_8367_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_8360_);
                            crate::leanh::lean_dec(v___x_8354_);
                            v___x_8362_ = crate::leanh::lean_box(0);
                            v_isShared_8363_ = v_isSharedCheck_8367_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_8363_ == 0 {
                    v___x_8365_ = v___x_8362_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8366_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8366_, 0, v_a_8360_);
                    v___x_8365_ = v_reuseFailAlloc_8366_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8365_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg___boxed(
    mut v_tail_8368_: *mut crate::leanh::LeanObject,
    mut v_params_8369_: *mut crate::leanh::LeanObject,
    mut v_motive_8370_: *mut crate::leanh::LeanObject,
    mut v_as_8371_: *mut crate::leanh::LeanObject,
    mut v_i_8372_: *mut crate::leanh::LeanObject,
    mut v_j_8373_: *mut crate::leanh::LeanObject,
    mut v_bs_8374_: *mut crate::leanh::LeanObject,
    mut v___y_8375_: *mut crate::leanh::LeanObject,
    mut v___y_8376_: *mut crate::leanh::LeanObject,
    mut v___y_8377_: *mut crate::leanh::LeanObject,
    mut v___y_8378_: *mut crate::leanh::LeanObject,
    mut v___y_8379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8380_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(
        v_tail_8368_,
        v_params_8369_,
        v_motive_8370_,
        v_as_8371_,
        v_i_8372_,
        v_j_8373_,
        v_bs_8374_,
        v___y_8375_,
        v___y_8376_,
        v___y_8377_,
        v___y_8378_,
    );
    crate::leanh::lean_dec(v___y_8378_);
    crate::leanh::lean_dec_ref(v___y_8377_);
    crate::leanh::lean_dec(v___y_8376_);
    crate::leanh::lean_dec_ref(v___y_8375_);
    crate::leanh::lean_dec_ref(v_as_8371_);
    crate::leanh::lean_dec_ref(v_params_8369_);
    return v_res_8380_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__6(
    mut v_ctors_8381_: *mut crate::leanh::LeanObject,
    mut v_tail_8382_: *mut crate::leanh::LeanObject,
    mut v_params_8383_: *mut crate::leanh::LeanObject,
    mut v___x_8384_: *mut crate::leanh::LeanObject,
    mut v_numIndices_8385_: *mut crate::leanh::LeanObject,
    mut v___x_8386_: *mut crate::leanh::LeanObject,
    mut v___x_8387_: *mut crate::leanh::LeanObject,
    mut v___x_8388_: u8,
    mut v___x_8389_: u8,
    mut v___x_8390_: u8,
    mut v_is_8391_: *mut crate::leanh::LeanObject,
    mut v___x_8392_: *mut crate::leanh::LeanObject,
    mut v___x_8393_: *mut crate::leanh::LeanObject,
    mut v___x_8394_: *mut crate::leanh::LeanObject,
    mut v___x_8395_: *mut crate::leanh::LeanObject,
    mut v___x_8396_: *mut crate::leanh::LeanObject,
    mut v___x_8397_: *mut crate::leanh::LeanObject,
    mut v_heq_8398_: *mut crate::leanh::LeanObject,
    mut v_val_8399_: *mut crate::leanh::LeanObject,
    mut v___x_8400_: *mut crate::leanh::LeanObject,
    mut v_declName_8401_: *mut crate::leanh::LeanObject,
    mut v_levelParams_8402_: *mut crate::leanh::LeanObject,
    mut v___x_8403_: *mut crate::leanh::LeanObject,
    mut v_numParams_8404_: *mut crate::leanh::LeanObject,
    mut v___x_8405_: *mut crate::leanh::LeanObject,
    mut v_motive_8406_: *mut crate::leanh::LeanObject,
    mut v___y_8407_: *mut crate::leanh::LeanObject,
    mut v___y_8408_: *mut crate::leanh::LeanObject,
    mut v___y_8409_: *mut crate::leanh::LeanObject,
    mut v___y_8410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8424_: u8 = 0;
    let mut v___x_8425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8429_: u8 = 0;
    let mut v___x_8431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8433_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8412_ = lean_array_mk(v_ctors_8381_);
                v___x_8413_ = lean_array_get_size(v___x_8412_);
                v___x_8414_ = lean_mk_empty_array_with_capacity(v___x_8413_);
                crate::leanh::lean_inc(v___x_8384_);
                crate::leanh::lean_inc_ref(v_motive_8406_);
                crate::leanh::lean_inc(v_tail_8382_);
                v___x_8415_ =
                    l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(
                        v_tail_8382_,
                        v_params_8383_,
                        v_motive_8406_,
                        v___x_8412_,
                        v___x_8413_,
                        v___x_8384_,
                        v___x_8414_,
                        v___y_8407_,
                        v___y_8408_,
                        v___y_8409_,
                        v___y_8410_,
                    );
                if crate::leanh::lean_obj_tag(v___x_8415_) == 0 {
                    v_a_8416_ = crate::leanh::lean_ctor_get(v___x_8415_, 0);
                    crate::leanh::lean_inc(v_a_8416_);
                    crate::leanh::lean_dec_ref_known(v___x_8415_, 1);
                    v___x_8417_ = l_Array_unzip___redArg(v_a_8416_);
                    crate::leanh::lean_dec(v_a_8416_);
                    v_fst_8418_ = crate::leanh::lean_ctor_get(v___x_8417_, 0);
                    crate::leanh::lean_inc(v_fst_8418_);
                    v_snd_8419_ = crate::leanh::lean_ctor_get(v___x_8417_, 1);
                    crate::leanh::lean_inc(v_snd_8419_);
                    crate::leanh::lean_dec_ref(v___x_8417_);
                    v___x_8420_ = crate::leanh::lean_box((v___x_8388_) as usize);
                    v___x_8421_ = crate::leanh::lean_box((v___x_8389_) as usize);
                    v___x_8422_ = crate::leanh::lean_box((v___x_8390_) as usize);
                    v___f_8423_ = crate::leanh::lean_alloc_closure(
                        l_Lean_mkCasesOnSameCtor___lam__5___boxed as *mut core::ffi::c_void,
                        34,
                        28,
                    );
                    crate::leanh::lean_closure_set(v___f_8423_, 0, v_numIndices_8385_);
                    crate::leanh::lean_closure_set(v___f_8423_, 1, v___x_8386_);
                    crate::leanh::lean_closure_set(v___f_8423_, 2, v_motive_8406_);
                    crate::leanh::lean_closure_set(v___f_8423_, 3, v___x_8387_);
                    crate::leanh::lean_closure_set(v___f_8423_, 4, v___x_8420_);
                    crate::leanh::lean_closure_set(v___f_8423_, 5, v___x_8421_);
                    crate::leanh::lean_closure_set(v___f_8423_, 6, v___x_8422_);
                    crate::leanh::lean_closure_set(v___f_8423_, 7, v_is_8391_);
                    crate::leanh::lean_closure_set(v___f_8423_, 8, v___x_8392_);
                    crate::leanh::lean_closure_set(v___f_8423_, 9, v___x_8393_);
                    crate::leanh::lean_closure_set(v___f_8423_, 10, v___x_8394_);
                    crate::leanh::lean_closure_set(v___f_8423_, 11, v___x_8395_);
                    crate::leanh::lean_closure_set(v___f_8423_, 12, v_params_8383_);
                    crate::leanh::lean_closure_set(v___f_8423_, 13, v___x_8396_);
                    crate::leanh::lean_closure_set(v___f_8423_, 14, v___x_8397_);
                    crate::leanh::lean_closure_set(v___f_8423_, 15, v_heq_8398_);
                    crate::leanh::lean_closure_set(v___f_8423_, 16, v_val_8399_);
                    crate::leanh::lean_closure_set(v___f_8423_, 17, v___x_8413_);
                    crate::leanh::lean_closure_set(v___f_8423_, 18, v_tail_8382_);
                    crate::leanh::lean_closure_set(v___f_8423_, 19, v___x_8412_);
                    crate::leanh::lean_closure_set(v___f_8423_, 20, v___x_8384_);
                    crate::leanh::lean_closure_set(v___f_8423_, 21, v___x_8400_);
                    crate::leanh::lean_closure_set(v___f_8423_, 22, v_declName_8401_);
                    crate::leanh::lean_closure_set(v___f_8423_, 23, v_levelParams_8402_);
                    crate::leanh::lean_closure_set(v___f_8423_, 24, v___x_8403_);
                    crate::leanh::lean_closure_set(v___f_8423_, 25, v_numParams_8404_);
                    crate::leanh::lean_closure_set(v___f_8423_, 26, v_snd_8419_);
                    crate::leanh::lean_closure_set(v___f_8423_, 27, v___x_8405_);
                    v___x_8424_ = 0;
                    v___x_8425_ =
                        l_Lean_Meta_withLocalDeclsDND___at___00Lean_mkCasesOnSameCtor_spec__4(
                            v_fst_8418_,
                            v___f_8423_,
                            v___x_8424_,
                            v___y_8407_,
                            v___y_8408_,
                            v___y_8409_,
                            v___y_8410_,
                        );
                    return v___x_8425_;
                } else {
                    crate::leanh::lean_dec_ref(v___x_8412_);
                    crate::leanh::lean_dec_ref(v_motive_8406_);
                    crate::leanh::lean_dec_ref(v___x_8405_);
                    crate::leanh::lean_dec(v_numParams_8404_);
                    crate::leanh::lean_dec(v___x_8403_);
                    crate::leanh::lean_dec(v_levelParams_8402_);
                    crate::leanh::lean_dec(v_declName_8401_);
                    crate::leanh::lean_dec_ref(v___x_8400_);
                    crate::leanh::lean_dec_ref(v_val_8399_);
                    crate::leanh::lean_dec_ref(v_heq_8398_);
                    crate::leanh::lean_dec_ref(v___x_8397_);
                    crate::leanh::lean_dec_ref(v___x_8396_);
                    crate::leanh::lean_dec(v___x_8395_);
                    crate::leanh::lean_dec(v___x_8394_);
                    crate::leanh::lean_dec_ref(v___x_8393_);
                    crate::leanh::lean_dec_ref(v___x_8392_);
                    crate::leanh::lean_dec_ref(v_is_8391_);
                    crate::leanh::lean_dec_ref(v___x_8387_);
                    crate::leanh::lean_dec(v___x_8386_);
                    crate::leanh::lean_dec(v_numIndices_8385_);
                    crate::leanh::lean_dec(v___x_8384_);
                    crate::leanh::lean_dec_ref(v_params_8383_);
                    crate::leanh::lean_dec(v_tail_8382_);
                    v_a_8426_ = crate::leanh::lean_ctor_get(v___x_8415_, 0);
                    v_isSharedCheck_8433_ = (!crate::leanh::lean_is_exclusive(v___x_8415_)) as u8;
                    if v_isSharedCheck_8433_ == 0 {
                        v___x_8428_ = v___x_8415_;
                        v_isShared_8429_ = v_isSharedCheck_8433_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8426_);
                        crate::leanh::lean_dec(v___x_8415_);
                        v___x_8428_ = crate::leanh::lean_box(0);
                        v_isShared_8429_ = v_isSharedCheck_8433_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8429_ == 0 {
                    v___x_8431_ = v___x_8428_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8432_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8432_, 0, v_a_8426_);
                    v___x_8431_ = v_reuseFailAlloc_8432_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8431_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__6___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ctors_8434_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_tail_8435_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_params_8436_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v___x_8437_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_numIndices_8438_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_8439_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_8440_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_8441_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_8442_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_8443_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_is_8444_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_8445_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_8446_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___x_8447_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___x_8448_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___x_8449_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___x_8450_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_heq_8451_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_val_8452_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___x_8453_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_declName_8454_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_levelParams_8455_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v___x_8456_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v_numParams_8457_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v___x_8458_: *mut crate::leanh::LeanObject = *_args.add(24);
    let mut v_motive_8459_: *mut crate::leanh::LeanObject = *_args.add(25);
    let mut v___y_8460_: *mut crate::leanh::LeanObject = *_args.add(26);
    let mut v___y_8461_: *mut crate::leanh::LeanObject = *_args.add(27);
    let mut v___y_8462_: *mut crate::leanh::LeanObject = *_args.add(28);
    let mut v___y_8463_: *mut crate::leanh::LeanObject = *_args.add(29);
    let mut v___y_8464_: *mut crate::leanh::LeanObject = *_args.add(30);
    let mut v___x_16721__boxed_8465_: u8 = 0;
    let mut v___x_16722__boxed_8466_: u8 = 0;
    let mut v___x_16723__boxed_8467_: u8 = 0;
    let mut v_res_8468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_16721__boxed_8465_ = (crate::leanh::lean_unbox(v___x_8441_) as u8);
    v___x_16722__boxed_8466_ = (crate::leanh::lean_unbox(v___x_8442_) as u8);
    v___x_16723__boxed_8467_ = (crate::leanh::lean_unbox(v___x_8443_) as u8);
    v_res_8468_ = l_Lean_mkCasesOnSameCtor___lam__6(
        v_ctors_8434_,
        v_tail_8435_,
        v_params_8436_,
        v___x_8437_,
        v_numIndices_8438_,
        v___x_8439_,
        v___x_8440_,
        v___x_16721__boxed_8465_,
        v___x_16722__boxed_8466_,
        v___x_16723__boxed_8467_,
        v_is_8444_,
        v___x_8445_,
        v___x_8446_,
        v___x_8447_,
        v___x_8448_,
        v___x_8449_,
        v___x_8450_,
        v_heq_8451_,
        v_val_8452_,
        v___x_8453_,
        v_declName_8454_,
        v_levelParams_8455_,
        v___x_8456_,
        v_numParams_8457_,
        v___x_8458_,
        v_motive_8459_,
        v___y_8460_,
        v___y_8461_,
        v___y_8462_,
        v___y_8463_,
    );
    crate::leanh::lean_dec(v___y_8463_);
    crate::leanh::lean_dec_ref(v___y_8462_);
    crate::leanh::lean_dec(v___y_8461_);
    crate::leanh::lean_dec_ref(v___y_8460_);
    return v_res_8468_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__7(
    mut v___x_8469_: *mut crate::leanh::LeanObject,
    mut v___x_8470_: *mut crate::leanh::LeanObject,
    mut v_is_8471_: *mut crate::leanh::LeanObject,
    mut v_head_8472_: *mut crate::leanh::LeanObject,
    mut v_ctors_8473_: *mut crate::leanh::LeanObject,
    mut v_tail_8474_: *mut crate::leanh::LeanObject,
    mut v_params_8475_: *mut crate::leanh::LeanObject,
    mut v___x_8476_: *mut crate::leanh::LeanObject,
    mut v_numIndices_8477_: *mut crate::leanh::LeanObject,
    mut v___x_8478_: *mut crate::leanh::LeanObject,
    mut v___x_8479_: *mut crate::leanh::LeanObject,
    mut v___x_8480_: *mut crate::leanh::LeanObject,
    mut v___x_8481_: *mut crate::leanh::LeanObject,
    mut v___x_8482_: *mut crate::leanh::LeanObject,
    mut v_val_8483_: *mut crate::leanh::LeanObject,
    mut v___x_8484_: *mut crate::leanh::LeanObject,
    mut v_declName_8485_: *mut crate::leanh::LeanObject,
    mut v_levelParams_8486_: *mut crate::leanh::LeanObject,
    mut v_numParams_8487_: *mut crate::leanh::LeanObject,
    mut v___x_8488_: *mut crate::leanh::LeanObject,
    mut v_heq_8489_: *mut crate::leanh::LeanObject,
    mut v___y_8490_: *mut crate::leanh::LeanObject,
    mut v___y_8491_: *mut crate::leanh::LeanObject,
    mut v___y_8492_: *mut crate::leanh::LeanObject,
    mut v___y_8493_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8502_: u8 = 0;
    let mut v___x_8503_: u8 = 0;
    let mut v___x_8504_: u8 = 0;
    let mut v___x_8505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8512_: u8 = 0;
    let mut v___x_8513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8517_: u8 = 0;
    let mut v___x_8519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8495_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_8496_ = lean_mk_empty_array_with_capacity(v___x_8495_);
                crate::leanh::lean_inc_ref(v___x_8469_);
                v___x_8497_ = lean_array_push(v___x_8496_, v___x_8469_);
                crate::leanh::lean_inc_ref(v___x_8470_);
                v___x_8498_ = lean_array_push(v___x_8497_, v___x_8470_);
                crate::leanh::lean_inc_ref(v_heq_8489_);
                v___x_8499_ = lean_array_push(v___x_8498_, v_heq_8489_);
                crate::leanh::lean_inc_ref(v_is_8471_);
                v___x_8500_ = l_Array_append___redArg(v_is_8471_, v___x_8499_);
                crate::leanh::lean_dec_ref(v___x_8499_);
                v___x_8501_ = l_Lean_mkSort(v_head_8472_);
                v___x_8502_ = 0;
                v___x_8503_ = 1;
                v___x_8504_ = 1;
                v___x_8505_ = l_Lean_Meta_mkForallFVars(
                    v___x_8500_,
                    v___x_8501_,
                    v___x_8502_,
                    v___x_8503_,
                    v___x_8503_,
                    v___x_8504_,
                    v___y_8490_,
                    v___y_8491_,
                    v___y_8492_,
                    v___y_8493_,
                );
                if crate::leanh::lean_obj_tag(v___x_8505_) == 0 {
                    v_a_8506_ = crate::leanh::lean_ctor_get(v___x_8505_, 0);
                    crate::leanh::lean_inc(v_a_8506_);
                    crate::leanh::lean_dec_ref_known(v___x_8505_, 1);
                    v___x_8507_ = crate::leanh::lean_box((v___x_8502_) as usize);
                    v___x_8508_ = crate::leanh::lean_box((v___x_8503_) as usize);
                    v___x_8509_ = crate::leanh::lean_box((v___x_8504_) as usize);
                    v___f_8510_ = crate::leanh::lean_alloc_closure(
                        l_Lean_mkCasesOnSameCtor___lam__6___boxed as *mut core::ffi::c_void,
                        31,
                        25,
                    );
                    crate::leanh::lean_closure_set(v___f_8510_, 0, v_ctors_8473_);
                    crate::leanh::lean_closure_set(v___f_8510_, 1, v_tail_8474_);
                    crate::leanh::lean_closure_set(v___f_8510_, 2, v_params_8475_);
                    crate::leanh::lean_closure_set(v___f_8510_, 3, v___x_8476_);
                    crate::leanh::lean_closure_set(v___f_8510_, 4, v_numIndices_8477_);
                    crate::leanh::lean_closure_set(v___f_8510_, 5, v___x_8478_);
                    crate::leanh::lean_closure_set(v___f_8510_, 6, v___x_8500_);
                    crate::leanh::lean_closure_set(v___f_8510_, 7, v___x_8507_);
                    crate::leanh::lean_closure_set(v___f_8510_, 8, v___x_8508_);
                    crate::leanh::lean_closure_set(v___f_8510_, 9, v___x_8509_);
                    crate::leanh::lean_closure_set(v___f_8510_, 10, v_is_8471_);
                    crate::leanh::lean_closure_set(v___f_8510_, 11, v___x_8470_);
                    crate::leanh::lean_closure_set(v___f_8510_, 12, v___x_8469_);
                    crate::leanh::lean_closure_set(v___f_8510_, 13, v___x_8479_);
                    crate::leanh::lean_closure_set(v___f_8510_, 14, v___x_8480_);
                    crate::leanh::lean_closure_set(v___f_8510_, 15, v___x_8481_);
                    crate::leanh::lean_closure_set(v___f_8510_, 16, v___x_8482_);
                    crate::leanh::lean_closure_set(v___f_8510_, 17, v_heq_8489_);
                    crate::leanh::lean_closure_set(v___f_8510_, 18, v_val_8483_);
                    crate::leanh::lean_closure_set(v___f_8510_, 19, v___x_8484_);
                    crate::leanh::lean_closure_set(v___f_8510_, 20, v_declName_8485_);
                    crate::leanh::lean_closure_set(v___f_8510_, 21, v_levelParams_8486_);
                    crate::leanh::lean_closure_set(v___f_8510_, 22, v___x_8495_);
                    crate::leanh::lean_closure_set(v___f_8510_, 23, v_numParams_8487_);
                    crate::leanh::lean_closure_set(v___f_8510_, 24, v___x_8488_);
                    v___x_8511_ = l_Lean_mkCasesOnSameCtorHet___lam__3___closed__1;
                    v___x_8512_ = 0;
                    v___x_8513_ = l_Lean_Meta_withLocalDecl___at___00Lean_mkCasesOnSameCtorHet_spec__8___redArg(v___x_8511_, v___x_8504_, v_a_8506_, v___f_8510_, v___x_8512_, v___y_8490_, v___y_8491_, v___y_8492_, v___y_8493_);
                    return v___x_8513_;
                } else {
                    crate::leanh::lean_dec_ref(v___x_8500_);
                    crate::leanh::lean_dec_ref(v_heq_8489_);
                    crate::leanh::lean_dec_ref(v___x_8488_);
                    crate::leanh::lean_dec(v_numParams_8487_);
                    crate::leanh::lean_dec(v_levelParams_8486_);
                    crate::leanh::lean_dec(v_declName_8485_);
                    crate::leanh::lean_dec_ref(v___x_8484_);
                    crate::leanh::lean_dec_ref(v_val_8483_);
                    crate::leanh::lean_dec_ref(v___x_8482_);
                    crate::leanh::lean_dec_ref(v___x_8481_);
                    crate::leanh::lean_dec(v___x_8480_);
                    crate::leanh::lean_dec(v___x_8479_);
                    crate::leanh::lean_dec(v___x_8478_);
                    crate::leanh::lean_dec(v_numIndices_8477_);
                    crate::leanh::lean_dec(v___x_8476_);
                    crate::leanh::lean_dec_ref(v_params_8475_);
                    crate::leanh::lean_dec(v_tail_8474_);
                    crate::leanh::lean_dec(v_ctors_8473_);
                    crate::leanh::lean_dec_ref(v_is_8471_);
                    crate::leanh::lean_dec_ref(v___x_8470_);
                    crate::leanh::lean_dec_ref(v___x_8469_);
                    v_a_8514_ = crate::leanh::lean_ctor_get(v___x_8505_, 0);
                    v_isSharedCheck_8521_ = (!crate::leanh::lean_is_exclusive(v___x_8505_)) as u8;
                    if v_isSharedCheck_8521_ == 0 {
                        v___x_8516_ = v___x_8505_;
                        v_isShared_8517_ = v_isSharedCheck_8521_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8514_);
                        crate::leanh::lean_dec(v___x_8505_);
                        v___x_8516_ = crate::leanh::lean_box(0);
                        v_isShared_8517_ = v_isSharedCheck_8521_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8517_ == 0 {
                    v___x_8519_ = v___x_8516_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8520_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8520_, 0, v_a_8514_);
                    v___x_8519_ = v_reuseFailAlloc_8520_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8519_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__7___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8522_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v___x_8523_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_is_8524_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_head_8525_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_ctors_8526_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_tail_8527_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_params_8528_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_8529_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_numIndices_8530_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_8531_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_8532_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_8533_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___x_8534_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___x_8535_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_val_8536_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___x_8537_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_declName_8538_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_levelParams_8539_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_numParams_8540_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___x_8541_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v_heq_8542_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___y_8543_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v___y_8544_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v___y_8545_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v___y_8546_: *mut crate::leanh::LeanObject = *_args.add(24);
    let mut v___y_8547_: *mut crate::leanh::LeanObject = *_args.add(25);
    let mut v_res_8548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8548_ = l_Lean_mkCasesOnSameCtor___lam__7(
        v___x_8522_,
        v___x_8523_,
        v_is_8524_,
        v_head_8525_,
        v_ctors_8526_,
        v_tail_8527_,
        v_params_8528_,
        v___x_8529_,
        v_numIndices_8530_,
        v___x_8531_,
        v___x_8532_,
        v___x_8533_,
        v___x_8534_,
        v___x_8535_,
        v_val_8536_,
        v___x_8537_,
        v_declName_8538_,
        v_levelParams_8539_,
        v_numParams_8540_,
        v___x_8541_,
        v_heq_8542_,
        v___y_8543_,
        v___y_8544_,
        v___y_8545_,
        v___y_8546_,
    );
    crate::leanh::lean_dec(v___y_8546_);
    crate::leanh::lean_dec_ref(v___y_8545_);
    crate::leanh::lean_dec(v___y_8544_);
    crate::leanh::lean_dec_ref(v___y_8543_);
    return v_res_8548_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__8(
    mut v___x_8549_: *mut crate::leanh::LeanObject,
    mut v_x1_8550_: *mut crate::leanh::LeanObject,
    mut v_indName_8551_: *mut crate::leanh::LeanObject,
    mut v_tail_8552_: *mut crate::leanh::LeanObject,
    mut v_params_8553_: *mut crate::leanh::LeanObject,
    mut v_is_8554_: *mut crate::leanh::LeanObject,
    mut v___x_8555_: *mut crate::leanh::LeanObject,
    mut v_head_8556_: *mut crate::leanh::LeanObject,
    mut v_ctors_8557_: *mut crate::leanh::LeanObject,
    mut v_numIndices_8558_: *mut crate::leanh::LeanObject,
    mut v___x_8559_: *mut crate::leanh::LeanObject,
    mut v___x_8560_: *mut crate::leanh::LeanObject,
    mut v_val_8561_: *mut crate::leanh::LeanObject,
    mut v_declName_8562_: *mut crate::leanh::LeanObject,
    mut v_levelParams_8563_: *mut crate::leanh::LeanObject,
    mut v_numParams_8564_: *mut crate::leanh::LeanObject,
    mut v___x_8565_: *mut crate::leanh::LeanObject,
    mut v_x2_8566_: *mut crate::leanh::LeanObject,
    mut v_x_8567_: *mut crate::leanh::LeanObject,
    mut v___y_8568_: *mut crate::leanh::LeanObject,
    mut v___y_8569_: *mut crate::leanh::LeanObject,
    mut v___y_8570_: *mut crate::leanh::LeanObject,
    mut v___y_8571_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8594_: u8 = 0;
    let mut v___x_8596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8598_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8573_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_8574_ = lean_array_get_borrowed(v___x_8549_, v_x1_8550_, v___x_8573_);
                v___x_8575_ = lean_array_get_borrowed(v___x_8549_, v_x2_8566_, v___x_8573_);
                v___x_8576_ = l_mkCtorIdxName(v_indName_8551_);
                crate::leanh::lean_inc(v_tail_8552_);
                v___x_8577_ = l_Lean_mkConst(v___x_8576_, v_tail_8552_);
                crate::leanh::lean_inc_ref(v_params_8553_);
                v___x_8578_ = l_Array_append___redArg(v_params_8553_, v_is_8554_);
                v___x_8579_ = lean_mk_empty_array_with_capacity(v___x_8555_);
                crate::leanh::lean_inc(v___x_8574_);
                crate::leanh::lean_inc_ref_n(v___x_8579_, 2);
                v___x_8580_ = lean_array_push(v___x_8579_, v___x_8574_);
                crate::leanh::lean_inc_ref(v___x_8578_);
                v___x_8581_ = l_Array_append___redArg(v___x_8578_, v___x_8580_);
                crate::leanh::lean_inc_ref(v___x_8577_);
                v___x_8582_ = l_Lean_mkAppN(v___x_8577_, v___x_8581_);
                crate::leanh::lean_dec_ref(v___x_8581_);
                crate::leanh::lean_inc(v___x_8575_);
                v___x_8583_ = lean_array_push(v___x_8579_, v___x_8575_);
                v___x_8584_ = l_Array_append___redArg(v___x_8578_, v___x_8583_);
                v___x_8585_ = l_Lean_mkAppN(v___x_8577_, v___x_8584_);
                crate::leanh::lean_dec_ref(v___x_8584_);
                v___x_8586_ = l_Lean_Meta_mkEq(
                    v___x_8582_,
                    v___x_8585_,
                    v___y_8568_,
                    v___y_8569_,
                    v___y_8570_,
                    v___y_8571_,
                );
                if crate::leanh::lean_obj_tag(v___x_8586_) == 0 {
                    v_a_8587_ = crate::leanh::lean_ctor_get(v___x_8586_, 0);
                    crate::leanh::lean_inc(v_a_8587_);
                    crate::leanh::lean_dec_ref_known(v___x_8586_, 1);
                    crate::leanh::lean_inc(v___x_8575_);
                    crate::leanh::lean_inc(v___x_8574_);
                    v___f_8588_ = crate::leanh::lean_alloc_closure(
                        l_Lean_mkCasesOnSameCtor___lam__7___boxed as *mut core::ffi::c_void,
                        26,
                        20,
                    );
                    crate::leanh::lean_closure_set(v___f_8588_, 0, v___x_8574_);
                    crate::leanh::lean_closure_set(v___f_8588_, 1, v___x_8575_);
                    crate::leanh::lean_closure_set(v___f_8588_, 2, v_is_8554_);
                    crate::leanh::lean_closure_set(v___f_8588_, 3, v_head_8556_);
                    crate::leanh::lean_closure_set(v___f_8588_, 4, v_ctors_8557_);
                    crate::leanh::lean_closure_set(v___f_8588_, 5, v_tail_8552_);
                    crate::leanh::lean_closure_set(v___f_8588_, 6, v_params_8553_);
                    crate::leanh::lean_closure_set(v___f_8588_, 7, v___x_8573_);
                    crate::leanh::lean_closure_set(v___f_8588_, 8, v_numIndices_8558_);
                    crate::leanh::lean_closure_set(v___f_8588_, 9, v___x_8555_);
                    crate::leanh::lean_closure_set(v___f_8588_, 10, v___x_8559_);
                    crate::leanh::lean_closure_set(v___f_8588_, 11, v___x_8560_);
                    crate::leanh::lean_closure_set(v___f_8588_, 12, v___x_8580_);
                    crate::leanh::lean_closure_set(v___f_8588_, 13, v___x_8583_);
                    crate::leanh::lean_closure_set(v___f_8588_, 14, v_val_8561_);
                    crate::leanh::lean_closure_set(v___f_8588_, 15, v___x_8579_);
                    crate::leanh::lean_closure_set(v___f_8588_, 16, v_declName_8562_);
                    crate::leanh::lean_closure_set(v___f_8588_, 17, v_levelParams_8563_);
                    crate::leanh::lean_closure_set(v___f_8588_, 18, v_numParams_8564_);
                    crate::leanh::lean_closure_set(v___f_8588_, 19, v___x_8565_);
                    v___x_8589_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtorHet_spec__5___redArg___closed__1;
                    v___x_8590_ = l_Lean_Meta_withLocalDeclD___at___00Lean_mkCasesOnSameCtorHet_spec__4___redArg(v___x_8589_, v_a_8587_, v___f_8588_, v___y_8568_, v___y_8569_, v___y_8570_, v___y_8571_);
                    return v___x_8590_;
                } else {
                    crate::leanh::lean_dec_ref(v___x_8583_);
                    crate::leanh::lean_dec_ref(v___x_8580_);
                    crate::leanh::lean_dec_ref(v___x_8579_);
                    crate::leanh::lean_dec_ref(v___x_8565_);
                    crate::leanh::lean_dec(v_numParams_8564_);
                    crate::leanh::lean_dec(v_levelParams_8563_);
                    crate::leanh::lean_dec(v_declName_8562_);
                    crate::leanh::lean_dec_ref(v_val_8561_);
                    crate::leanh::lean_dec(v___x_8560_);
                    crate::leanh::lean_dec(v___x_8559_);
                    crate::leanh::lean_dec(v_numIndices_8558_);
                    crate::leanh::lean_dec(v_ctors_8557_);
                    crate::leanh::lean_dec(v_head_8556_);
                    crate::leanh::lean_dec(v___x_8555_);
                    crate::leanh::lean_dec_ref(v_is_8554_);
                    crate::leanh::lean_dec_ref(v_params_8553_);
                    crate::leanh::lean_dec(v_tail_8552_);
                    v_a_8591_ = crate::leanh::lean_ctor_get(v___x_8586_, 0);
                    v_isSharedCheck_8598_ = (!crate::leanh::lean_is_exclusive(v___x_8586_)) as u8;
                    if v_isSharedCheck_8598_ == 0 {
                        v___x_8593_ = v___x_8586_;
                        v_isShared_8594_ = v_isSharedCheck_8598_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8591_);
                        crate::leanh::lean_dec(v___x_8586_);
                        v___x_8593_ = crate::leanh::lean_box(0);
                        v_isShared_8594_ = v_isSharedCheck_8598_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8594_ == 0 {
                    v___x_8596_ = v___x_8593_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8597_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8597_, 0, v_a_8591_);
                    v___x_8596_ = v_reuseFailAlloc_8597_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8596_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__8___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8599_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_x1_8600_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_indName_8601_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_tail_8602_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_params_8603_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_is_8604_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_8605_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_head_8606_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_ctors_8607_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_numIndices_8608_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_8609_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___x_8610_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_val_8611_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_declName_8612_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_levelParams_8613_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_numParams_8614_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___x_8615_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_x2_8616_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_x_8617_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_8618_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_8619_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___y_8620_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v___y_8621_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v___y_8622_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v_res_8623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8623_ = l_Lean_mkCasesOnSameCtor___lam__8(
        v___x_8599_,
        v_x1_8600_,
        v_indName_8601_,
        v_tail_8602_,
        v_params_8603_,
        v_is_8604_,
        v___x_8605_,
        v_head_8606_,
        v_ctors_8607_,
        v_numIndices_8608_,
        v___x_8609_,
        v___x_8610_,
        v_val_8611_,
        v_declName_8612_,
        v_levelParams_8613_,
        v_numParams_8614_,
        v___x_8615_,
        v_x2_8616_,
        v_x_8617_,
        v___y_8618_,
        v___y_8619_,
        v___y_8620_,
        v___y_8621_,
    );
    crate::leanh::lean_dec(v___y_8621_);
    crate::leanh::lean_dec_ref(v___y_8620_);
    crate::leanh::lean_dec(v___y_8619_);
    crate::leanh::lean_dec_ref(v___y_8618_);
    crate::leanh::lean_dec_ref(v_x_8617_);
    crate::leanh::lean_dec_ref(v_x2_8616_);
    crate::leanh::lean_dec_ref(v_x1_8600_);
    crate::leanh::lean_dec_ref(v___x_8599_);
    return v_res_8623_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__9(
    mut v___x_8624_: *mut crate::leanh::LeanObject,
    mut v_indName_8625_: *mut crate::leanh::LeanObject,
    mut v_tail_8626_: *mut crate::leanh::LeanObject,
    mut v_params_8627_: *mut crate::leanh::LeanObject,
    mut v_is_8628_: *mut crate::leanh::LeanObject,
    mut v___x_8629_: *mut crate::leanh::LeanObject,
    mut v_head_8630_: *mut crate::leanh::LeanObject,
    mut v_ctors_8631_: *mut crate::leanh::LeanObject,
    mut v_numIndices_8632_: *mut crate::leanh::LeanObject,
    mut v___x_8633_: *mut crate::leanh::LeanObject,
    mut v___x_8634_: *mut crate::leanh::LeanObject,
    mut v_val_8635_: *mut crate::leanh::LeanObject,
    mut v_declName_8636_: *mut crate::leanh::LeanObject,
    mut v_levelParams_8637_: *mut crate::leanh::LeanObject,
    mut v_numParams_8638_: *mut crate::leanh::LeanObject,
    mut v___x_8639_: *mut crate::leanh::LeanObject,
    mut v_t_8640_: *mut crate::leanh::LeanObject,
    mut v___x_8641_: *mut crate::leanh::LeanObject,
    mut v_x1_8642_: *mut crate::leanh::LeanObject,
    mut v_x_8643_: *mut crate::leanh::LeanObject,
    mut v___y_8644_: *mut crate::leanh::LeanObject,
    mut v___y_8645_: *mut crate::leanh::LeanObject,
    mut v___y_8646_: *mut crate::leanh::LeanObject,
    mut v___y_8647_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_8649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8650_: u8 = 0;
    let mut v___x_8651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_8649_ = crate::leanh::lean_alloc_closure(
        l_Lean_mkCasesOnSameCtor___lam__8___boxed as *mut core::ffi::c_void,
        24,
        17,
    );
    crate::leanh::lean_closure_set(v___f_8649_, 0, v___x_8624_);
    crate::leanh::lean_closure_set(v___f_8649_, 1, v_x1_8642_);
    crate::leanh::lean_closure_set(v___f_8649_, 2, v_indName_8625_);
    crate::leanh::lean_closure_set(v___f_8649_, 3, v_tail_8626_);
    crate::leanh::lean_closure_set(v___f_8649_, 4, v_params_8627_);
    crate::leanh::lean_closure_set(v___f_8649_, 5, v_is_8628_);
    crate::leanh::lean_closure_set(v___f_8649_, 6, v___x_8629_);
    crate::leanh::lean_closure_set(v___f_8649_, 7, v_head_8630_);
    crate::leanh::lean_closure_set(v___f_8649_, 8, v_ctors_8631_);
    crate::leanh::lean_closure_set(v___f_8649_, 9, v_numIndices_8632_);
    crate::leanh::lean_closure_set(v___f_8649_, 10, v___x_8633_);
    crate::leanh::lean_closure_set(v___f_8649_, 11, v___x_8634_);
    crate::leanh::lean_closure_set(v___f_8649_, 12, v_val_8635_);
    crate::leanh::lean_closure_set(v___f_8649_, 13, v_declName_8636_);
    crate::leanh::lean_closure_set(v___f_8649_, 14, v_levelParams_8637_);
    crate::leanh::lean_closure_set(v___f_8649_, 15, v_numParams_8638_);
    crate::leanh::lean_closure_set(v___f_8649_, 16, v___x_8639_);
    v___x_8650_ = 0;
    v___x_8651_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(
            v_t_8640_,
            v___x_8641_,
            v___f_8649_,
            v___x_8650_,
            v___x_8650_,
            v___y_8644_,
            v___y_8645_,
            v___y_8646_,
            v___y_8647_,
        );
    return v___x_8651_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__9___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8652_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_indName_8653_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_tail_8654_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_params_8655_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_is_8656_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___x_8657_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_head_8658_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_ctors_8659_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_numIndices_8660_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___x_8661_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___x_8662_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_val_8663_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_declName_8664_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_levelParams_8665_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_numParams_8666_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___x_8667_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v_t_8668_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___x_8669_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_x1_8670_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_x_8671_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_8672_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___y_8673_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v___y_8674_: *mut crate::leanh::LeanObject = *_args.add(22);
    let mut v___y_8675_: *mut crate::leanh::LeanObject = *_args.add(23);
    let mut v___y_8676_: *mut crate::leanh::LeanObject = *_args.add(24);
    let mut v_res_8677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8677_ = l_Lean_mkCasesOnSameCtor___lam__9(
        v___x_8652_,
        v_indName_8653_,
        v_tail_8654_,
        v_params_8655_,
        v_is_8656_,
        v___x_8657_,
        v_head_8658_,
        v_ctors_8659_,
        v_numIndices_8660_,
        v___x_8661_,
        v___x_8662_,
        v_val_8663_,
        v_declName_8664_,
        v_levelParams_8665_,
        v_numParams_8666_,
        v___x_8667_,
        v_t_8668_,
        v___x_8669_,
        v_x1_8670_,
        v_x_8671_,
        v___y_8672_,
        v___y_8673_,
        v___y_8674_,
        v___y_8675_,
    );
    crate::leanh::lean_dec(v___y_8675_);
    crate::leanh::lean_dec_ref(v___y_8674_);
    crate::leanh::lean_dec(v___y_8673_);
    crate::leanh::lean_dec_ref(v___y_8672_);
    crate::leanh::lean_dec_ref(v_x_8671_);
    return v_res_8677_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__10(
    mut v___x_8678_: *mut crate::leanh::LeanObject,
    mut v_indName_8679_: *mut crate::leanh::LeanObject,
    mut v_tail_8680_: *mut crate::leanh::LeanObject,
    mut v_params_8681_: *mut crate::leanh::LeanObject,
    mut v_head_8682_: *mut crate::leanh::LeanObject,
    mut v_ctors_8683_: *mut crate::leanh::LeanObject,
    mut v_numIndices_8684_: *mut crate::leanh::LeanObject,
    mut v___x_8685_: *mut crate::leanh::LeanObject,
    mut v___x_8686_: *mut crate::leanh::LeanObject,
    mut v_val_8687_: *mut crate::leanh::LeanObject,
    mut v_declName_8688_: *mut crate::leanh::LeanObject,
    mut v_levelParams_8689_: *mut crate::leanh::LeanObject,
    mut v_numParams_8690_: *mut crate::leanh::LeanObject,
    mut v___x_8691_: *mut crate::leanh::LeanObject,
    mut v_is_8692_: *mut crate::leanh::LeanObject,
    mut v_t_8693_: *mut crate::leanh::LeanObject,
    mut v___y_8694_: *mut crate::leanh::LeanObject,
    mut v___y_8695_: *mut crate::leanh::LeanObject,
    mut v___y_8696_: *mut crate::leanh::LeanObject,
    mut v___y_8697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8702_: u8 = 0;
    let mut v___x_8703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8699_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_8700_ = l_Lean_mkCasesOnSameCtorHet___lam__6___closed__0;
    crate::leanh::lean_inc_ref(v_t_8693_);
    v___f_8701_ = crate::leanh::lean_alloc_closure(
        l_Lean_mkCasesOnSameCtor___lam__9___boxed as *mut core::ffi::c_void,
        25,
        18,
    );
    crate::leanh::lean_closure_set(v___f_8701_, 0, v___x_8678_);
    crate::leanh::lean_closure_set(v___f_8701_, 1, v_indName_8679_);
    crate::leanh::lean_closure_set(v___f_8701_, 2, v_tail_8680_);
    crate::leanh::lean_closure_set(v___f_8701_, 3, v_params_8681_);
    crate::leanh::lean_closure_set(v___f_8701_, 4, v_is_8692_);
    crate::leanh::lean_closure_set(v___f_8701_, 5, v___x_8699_);
    crate::leanh::lean_closure_set(v___f_8701_, 6, v_head_8682_);
    crate::leanh::lean_closure_set(v___f_8701_, 7, v_ctors_8683_);
    crate::leanh::lean_closure_set(v___f_8701_, 8, v_numIndices_8684_);
    crate::leanh::lean_closure_set(v___f_8701_, 9, v___x_8685_);
    crate::leanh::lean_closure_set(v___f_8701_, 10, v___x_8686_);
    crate::leanh::lean_closure_set(v___f_8701_, 11, v_val_8687_);
    crate::leanh::lean_closure_set(v___f_8701_, 12, v_declName_8688_);
    crate::leanh::lean_closure_set(v___f_8701_, 13, v_levelParams_8689_);
    crate::leanh::lean_closure_set(v___f_8701_, 14, v_numParams_8690_);
    crate::leanh::lean_closure_set(v___f_8701_, 15, v___x_8691_);
    crate::leanh::lean_closure_set(v___f_8701_, 16, v_t_8693_);
    crate::leanh::lean_closure_set(v___f_8701_, 17, v___x_8700_);
    v___x_8702_ = 0;
    v___x_8703_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(
            v_t_8693_,
            v___x_8700_,
            v___f_8701_,
            v___x_8702_,
            v___x_8702_,
            v___y_8694_,
            v___y_8695_,
            v___y_8696_,
            v___y_8697_,
        );
    return v___x_8703_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__10___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8704_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_indName_8705_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_tail_8706_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_params_8707_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_head_8708_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_ctors_8709_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_numIndices_8710_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_8711_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___x_8712_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_val_8713_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_declName_8714_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_levelParams_8715_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_numParams_8716_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___x_8717_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v_is_8718_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v_t_8719_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_8720_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_8721_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_8722_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_8723_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_8724_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_res_8725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8725_ = l_Lean_mkCasesOnSameCtor___lam__10(
        v___x_8704_,
        v_indName_8705_,
        v_tail_8706_,
        v_params_8707_,
        v_head_8708_,
        v_ctors_8709_,
        v_numIndices_8710_,
        v___x_8711_,
        v___x_8712_,
        v_val_8713_,
        v_declName_8714_,
        v_levelParams_8715_,
        v_numParams_8716_,
        v___x_8717_,
        v_is_8718_,
        v_t_8719_,
        v___y_8720_,
        v___y_8721_,
        v___y_8722_,
        v___y_8723_,
    );
    crate::leanh::lean_dec(v___y_8723_);
    crate::leanh::lean_dec_ref(v___y_8722_);
    crate::leanh::lean_dec(v___y_8721_);
    crate::leanh::lean_dec_ref(v___y_8720_);
    return v_res_8725_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__11(
    mut v___x_8726_: *mut crate::leanh::LeanObject,
    mut v_indName_8727_: *mut crate::leanh::LeanObject,
    mut v_tail_8728_: *mut crate::leanh::LeanObject,
    mut v_head_8729_: *mut crate::leanh::LeanObject,
    mut v_ctors_8730_: *mut crate::leanh::LeanObject,
    mut v_numIndices_8731_: *mut crate::leanh::LeanObject,
    mut v___x_8732_: *mut crate::leanh::LeanObject,
    mut v___x_8733_: *mut crate::leanh::LeanObject,
    mut v_val_8734_: *mut crate::leanh::LeanObject,
    mut v_declName_8735_: *mut crate::leanh::LeanObject,
    mut v_levelParams_8736_: *mut crate::leanh::LeanObject,
    mut v_numParams_8737_: *mut crate::leanh::LeanObject,
    mut v_params_8738_: *mut crate::leanh::LeanObject,
    mut v_t_8739_: *mut crate::leanh::LeanObject,
    mut v___y_8740_: *mut crate::leanh::LeanObject,
    mut v___y_8741_: *mut crate::leanh::LeanObject,
    mut v___y_8742_: *mut crate::leanh::LeanObject,
    mut v___y_8743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8748_: u8 = 0;
    let mut v___x_8749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8745_ = l_Lean_Expr_bindingBody_x21(v_t_8739_);
    crate::leanh::lean_inc_ref(v___x_8745_);
    crate::leanh::lean_inc(v_numIndices_8731_);
    v___f_8746_ = crate::leanh::lean_alloc_closure(
        l_Lean_mkCasesOnSameCtor___lam__10___boxed as *mut core::ffi::c_void,
        21,
        14,
    );
    crate::leanh::lean_closure_set(v___f_8746_, 0, v___x_8726_);
    crate::leanh::lean_closure_set(v___f_8746_, 1, v_indName_8727_);
    crate::leanh::lean_closure_set(v___f_8746_, 2, v_tail_8728_);
    crate::leanh::lean_closure_set(v___f_8746_, 3, v_params_8738_);
    crate::leanh::lean_closure_set(v___f_8746_, 4, v_head_8729_);
    crate::leanh::lean_closure_set(v___f_8746_, 5, v_ctors_8730_);
    crate::leanh::lean_closure_set(v___f_8746_, 6, v_numIndices_8731_);
    crate::leanh::lean_closure_set(v___f_8746_, 7, v___x_8732_);
    crate::leanh::lean_closure_set(v___f_8746_, 8, v___x_8733_);
    crate::leanh::lean_closure_set(v___f_8746_, 9, v_val_8734_);
    crate::leanh::lean_closure_set(v___f_8746_, 10, v_declName_8735_);
    crate::leanh::lean_closure_set(v___f_8746_, 11, v_levelParams_8736_);
    crate::leanh::lean_closure_set(v___f_8746_, 12, v_numParams_8737_);
    crate::leanh::lean_closure_set(v___f_8746_, 13, v___x_8745_);
    v___x_8747_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_8747_, 0, v_numIndices_8731_);
    v___x_8748_ = 0;
    v___x_8749_ =
        l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(
            v___x_8745_,
            v___x_8747_,
            v___f_8746_,
            v___x_8748_,
            v___x_8748_,
            v___y_8740_,
            v___y_8741_,
            v___y_8742_,
            v___y_8743_,
        );
    return v___x_8749_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___lam__11___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8750_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_indName_8751_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_tail_8752_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_head_8753_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_ctors_8754_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_numIndices_8755_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___x_8756_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___x_8757_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_val_8758_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_declName_8759_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v_levelParams_8760_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v_numParams_8761_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v_params_8762_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v_t_8763_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_8764_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_8765_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_8766_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_8767_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_8768_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_res_8769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8769_ = l_Lean_mkCasesOnSameCtor___lam__11(
        v___x_8750_,
        v_indName_8751_,
        v_tail_8752_,
        v_head_8753_,
        v_ctors_8754_,
        v_numIndices_8755_,
        v___x_8756_,
        v___x_8757_,
        v_val_8758_,
        v_declName_8759_,
        v_levelParams_8760_,
        v_numParams_8761_,
        v_params_8762_,
        v_t_8763_,
        v___y_8764_,
        v___y_8765_,
        v___y_8766_,
        v___y_8767_,
    );
    crate::leanh::lean_dec(v___y_8767_);
    crate::leanh::lean_dec_ref(v___y_8766_);
    crate::leanh::lean_dec(v___y_8765_);
    crate::leanh::lean_dec_ref(v___y_8764_);
    crate::leanh::lean_dec_ref(v_t_8763_);
    return v_res_8769_;
}
pub unsafe fn _init_l_Lean_mkCasesOnSameCtor___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_8774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8774_ = l_Lean_mkCasesOnSameCtorHet___closed__2;
    v___x_8775_ = crate::leanh::lean_unsigned_to_nat(58);
    v___x_8776_ = crate::leanh::lean_unsigned_to_nat(142);
    v___x_8777_ = l_Lean_mkCasesOnSameCtor___closed__2;
    v___x_8778_ = l_Lean_mkCasesOnSameCtorHet___closed__0;
    v___x_8779_ = l_mkPanicMessageWithDecl(
        v___x_8778_,
        v___x_8777_,
        v___x_8776_,
        v___x_8775_,
        v___x_8774_,
    );
    return v___x_8779_;
}
pub unsafe fn _init_l_Lean_mkCasesOnSameCtor___closed__4() -> *mut crate::leanh::LeanObject {
    let mut v___x_8780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8780_ = l_Lean_mkCasesOnSameCtorHet___closed__4;
    v___x_8781_ = crate::leanh::lean_unsigned_to_nat(60);
    v___x_8782_ = crate::leanh::lean_unsigned_to_nat(136);
    v___x_8783_ = l_Lean_mkCasesOnSameCtor___closed__2;
    v___x_8784_ = l_Lean_mkCasesOnSameCtorHet___closed__0;
    v___x_8785_ = l_mkPanicMessageWithDecl(
        v___x_8784_,
        v___x_8783_,
        v___x_8782_,
        v___x_8781_,
        v___x_8780_,
    );
    return v___x_8785_;
}
pub unsafe fn l_Lean_mkCasesOnSameCtor(
    mut v_declName_8786_: *mut crate::leanh::LeanObject,
    mut v_indName_8787_: *mut crate::leanh::LeanObject,
    mut v_a_8788_: *mut crate::leanh::LeanObject,
    mut v_a_8789_: *mut crate::leanh::LeanObject,
    mut v_a_8790_: *mut crate::leanh::LeanObject,
    mut v_a_8791_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8801_: u8 = 0;
    let mut v___x_8802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_8805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_8806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_8809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_8810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_8811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_numIndices_8812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctors_8813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8818_: u8 = 0;
    let mut v___x_8819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8826_: u8 = 0;
    let mut v___x_8828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8830_: u8 = 0;
    let mut v_isSharedCheck_8831_: u8 = 0;
    let mut v_unused_8832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8838_: u8 = 0;
    let mut v___x_8840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8842_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_indName_8787_);
                v___x_8793_ = l_Lean_getConstInfo___at___00Lean_mkCasesOnSameCtorHet_spec__0(
                    v_indName_8787_,
                    v_a_8788_,
                    v_a_8789_,
                    v_a_8790_,
                    v_a_8791_,
                );
                if crate::leanh::lean_obj_tag(v___x_8793_) == 0 {
                    v_a_8794_ = crate::leanh::lean_ctor_get(v___x_8793_, 0);
                    crate::leanh::lean_inc(v_a_8794_);
                    crate::leanh::lean_dec_ref_known(v___x_8793_, 1);
                    if crate::leanh::lean_obj_tag(v_a_8794_) == 5 {
                        v_val_8795_ = crate::leanh::lean_ctor_get(v_a_8794_, 0);
                        crate::leanh::lean_inc_ref(v_val_8795_);
                        crate::leanh::lean_dec_ref_known(v_a_8794_, 1);
                        v___x_8796_ = l_Lean_mkCasesOnSameCtor___closed__1;
                        crate::leanh::lean_inc(v_declName_8786_);
                        v___x_8797_ = l_Lean_Name_append(v_declName_8786_, v___x_8796_);
                        crate::leanh::lean_inc(v_indName_8787_);
                        crate::leanh::lean_inc(v___x_8797_);
                        v___x_8798_ = l_Lean_mkCasesOnSameCtorHet(
                            v___x_8797_,
                            v_indName_8787_,
                            v_a_8788_,
                            v_a_8789_,
                            v_a_8790_,
                            v_a_8791_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_8798_) == 0 {
                            v_isSharedCheck_8831_ =
                                (!crate::leanh::lean_is_exclusive(v___x_8798_)) as u8;
                            if v_isSharedCheck_8831_ == 0 {
                                v_unused_8832_ = crate::leanh::lean_ctor_get(v___x_8798_, 0);
                                crate::leanh::lean_dec(v_unused_8832_);
                                v___x_8800_ = v___x_8798_;
                                v_isShared_8801_ = v_isSharedCheck_8831_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_8798_);
                                v___x_8800_ = crate::leanh::lean_box(0);
                                v_isShared_8801_ = v_isSharedCheck_8831_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_8797_);
                            crate::leanh::lean_dec_ref(v_val_8795_);
                            crate::leanh::lean_dec(v_indName_8787_);
                            crate::leanh::lean_dec(v_declName_8786_);
                            return v___x_8798_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_8794_);
                        crate::leanh::lean_dec(v_indName_8787_);
                        crate::leanh::lean_dec(v_declName_8786_);
                        v___x_8833_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_mkCasesOnSameCtor___closed__4),
                            core::ptr::addr_of_mut!(l_Lean_mkCasesOnSameCtor___closed__4_once),
                            _init_l_Lean_mkCasesOnSameCtor___closed__4,
                        );
                        v___x_8834_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(
                            v___x_8833_,
                            v_a_8788_,
                            v_a_8789_,
                            v_a_8790_,
                            v_a_8791_,
                        );
                        return v___x_8834_;
                    }
                } else {
                    crate::leanh::lean_dec(v_indName_8787_);
                    crate::leanh::lean_dec(v_declName_8786_);
                    v_a_8835_ = crate::leanh::lean_ctor_get(v___x_8793_, 0);
                    v_isSharedCheck_8842_ = (!crate::leanh::lean_is_exclusive(v___x_8793_)) as u8;
                    if v_isSharedCheck_8842_ == 0 {
                        v___x_8837_ = v___x_8793_;
                        v_isShared_8838_ = v_isSharedCheck_8842_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8835_);
                        crate::leanh::lean_dec(v___x_8793_);
                        v___x_8837_ = crate::leanh::lean_box(0);
                        v_isShared_8838_ = v_isSharedCheck_8842_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_indName_8787_);
                v___x_8802_ = l_Lean_mkCasesOnName(v_indName_8787_);
                v___x_8803_ = l_Lean_getConstVal___at___00Lean_mkCasesOnSameCtorHet_spec__1(
                    v___x_8802_,
                    v_a_8788_,
                    v_a_8789_,
                    v_a_8790_,
                    v_a_8791_,
                );
                if crate::leanh::lean_obj_tag(v___x_8803_) == 0 {
                    v_a_8804_ = crate::leanh::lean_ctor_get(v___x_8803_, 0);
                    crate::leanh::lean_inc(v_a_8804_);
                    crate::leanh::lean_dec_ref_known(v___x_8803_, 1);
                    v_levelParams_8805_ = crate::leanh::lean_ctor_get(v_a_8804_, 1);
                    crate::leanh::lean_inc_n(v_levelParams_8805_, 2);
                    v_type_8806_ = crate::leanh::lean_ctor_get(v_a_8804_, 2);
                    crate::leanh::lean_inc_ref(v_type_8806_);
                    crate::leanh::lean_dec(v_a_8804_);
                    v___x_8807_ = crate::leanh::lean_box(0);
                    v___x_8808_ = l_List_mapTR_loop___at___00Lean_mkCasesOnSameCtorHet_spec__2(
                        v_levelParams_8805_,
                        v___x_8807_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_8808_) == 1 {
                        v_head_8809_ = crate::leanh::lean_ctor_get(v___x_8808_, 0);
                        crate::leanh::lean_inc(v_head_8809_);
                        v_tail_8810_ = crate::leanh::lean_ctor_get(v___x_8808_, 1);
                        crate::leanh::lean_inc(v_tail_8810_);
                        v_numParams_8811_ = crate::leanh::lean_ctor_get(v_val_8795_, 1);
                        crate::leanh::lean_inc_n(v_numParams_8811_, 2);
                        v_numIndices_8812_ = crate::leanh::lean_ctor_get(v_val_8795_, 2);
                        crate::leanh::lean_inc(v_numIndices_8812_);
                        v_ctors_8813_ = crate::leanh::lean_ctor_get(v_val_8795_, 4);
                        crate::leanh::lean_inc(v_ctors_8813_);
                        v___x_8814_ = l_Lean_instInhabitedExpr;
                        v___f_8815_ = crate::leanh::lean_alloc_closure(
                            l_Lean_mkCasesOnSameCtor___lam__11___boxed as *mut core::ffi::c_void,
                            19,
                            12,
                        );
                        crate::leanh::lean_closure_set(v___f_8815_, 0, v___x_8814_);
                        crate::leanh::lean_closure_set(v___f_8815_, 1, v_indName_8787_);
                        crate::leanh::lean_closure_set(v___f_8815_, 2, v_tail_8810_);
                        crate::leanh::lean_closure_set(v___f_8815_, 3, v_head_8809_);
                        crate::leanh::lean_closure_set(v___f_8815_, 4, v_ctors_8813_);
                        crate::leanh::lean_closure_set(v___f_8815_, 5, v_numIndices_8812_);
                        crate::leanh::lean_closure_set(v___f_8815_, 6, v___x_8797_);
                        crate::leanh::lean_closure_set(v___f_8815_, 7, v___x_8808_);
                        crate::leanh::lean_closure_set(v___f_8815_, 8, v_val_8795_);
                        crate::leanh::lean_closure_set(v___f_8815_, 9, v_declName_8786_);
                        crate::leanh::lean_closure_set(v___f_8815_, 10, v_levelParams_8805_);
                        crate::leanh::lean_closure_set(v___f_8815_, 11, v_numParams_8811_);
                        if v_isShared_8801_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_8800_, 1);
                            crate::leanh::lean_ctor_set(v___x_8800_, 0, v_numParams_8811_);
                            v___x_8817_ = v___x_8800_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_8820_ =
                                crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_8820_,
                                0,
                                v_numParams_8811_,
                            );
                            v___x_8817_ = v_reuseFailAlloc_8820_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_8808_);
                        crate::leanh::lean_dec_ref(v_type_8806_);
                        crate::leanh::lean_dec(v_levelParams_8805_);
                        crate::leanh::lean_del_object(v___x_8800_);
                        crate::leanh::lean_dec(v___x_8797_);
                        crate::leanh::lean_dec_ref(v_val_8795_);
                        crate::leanh::lean_dec(v_indName_8787_);
                        crate::leanh::lean_dec(v_declName_8786_);
                        v___x_8821_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_mkCasesOnSameCtor___closed__3),
                            core::ptr::addr_of_mut!(l_Lean_mkCasesOnSameCtor___closed__3_once),
                            _init_l_Lean_mkCasesOnSameCtor___closed__3,
                        );
                        v___x_8822_ = l_panic___at___00Lean_mkCasesOnSameCtorHet_spec__14(
                            v___x_8821_,
                            v_a_8788_,
                            v_a_8789_,
                            v_a_8790_,
                            v_a_8791_,
                        );
                        return v___x_8822_;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_8800_);
                    crate::leanh::lean_dec(v___x_8797_);
                    crate::leanh::lean_dec_ref(v_val_8795_);
                    crate::leanh::lean_dec(v_indName_8787_);
                    crate::leanh::lean_dec(v_declName_8786_);
                    v_a_8823_ = crate::leanh::lean_ctor_get(v___x_8803_, 0);
                    v_isSharedCheck_8830_ = (!crate::leanh::lean_is_exclusive(v___x_8803_)) as u8;
                    if v_isSharedCheck_8830_ == 0 {
                        v___x_8825_ = v___x_8803_;
                        v_isShared_8826_ = v_isSharedCheck_8830_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_8823_);
                        crate::leanh::lean_dec(v___x_8803_);
                        v___x_8825_ = crate::leanh::lean_box(0);
                        v_isShared_8826_ = v_isSharedCheck_8830_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_8818_ = 0;
                v___x_8819_ = l_Lean_Meta_forallBoundedTelescope___at___00Lean_mkCasesOnSameCtorHet_spec__9___redArg(v_type_8806_, v___x_8817_, v___f_8815_, v___x_8818_, v___x_8818_, v_a_8788_, v_a_8789_, v_a_8790_, v_a_8791_);
                return v___x_8819_;
            }
            3 => {
                if v_isShared_8826_ == 0 {
                    v___x_8828_ = v___x_8825_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8829_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8829_, 0, v_a_8823_);
                    v___x_8828_ = v_reuseFailAlloc_8829_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8828_;
            }
            5 => {
                if v_isShared_8838_ == 0 {
                    v___x_8840_ = v___x_8837_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8841_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_8841_, 0, v_a_8835_);
                    v___x_8840_ = v_reuseFailAlloc_8841_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_8840_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkCasesOnSameCtor___boxed(
    mut v_declName_8843_: *mut crate::leanh::LeanObject,
    mut v_indName_8844_: *mut crate::leanh::LeanObject,
    mut v_a_8845_: *mut crate::leanh::LeanObject,
    mut v_a_8846_: *mut crate::leanh::LeanObject,
    mut v_a_8847_: *mut crate::leanh::LeanObject,
    mut v_a_8848_: *mut crate::leanh::LeanObject,
    mut v_a_8849_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8850_ = l_Lean_mkCasesOnSameCtor(
        v_declName_8843_,
        v_indName_8844_,
        v_a_8845_,
        v_a_8846_,
        v_a_8847_,
        v_a_8848_,
    );
    crate::leanh::lean_dec(v_a_8848_);
    crate::leanh::lean_dec_ref(v_a_8847_);
    crate::leanh::lean_dec(v_a_8846_);
    crate::leanh::lean_dec_ref(v_a_8845_);
    return v_res_8850_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0(
    mut v_tail_8851_: *mut crate::leanh::LeanObject,
    mut v_params_8852_: *mut crate::leanh::LeanObject,
    mut v_motive_8853_: *mut crate::leanh::LeanObject,
    mut v_as_8854_: *mut crate::leanh::LeanObject,
    mut v_i_8855_: *mut crate::leanh::LeanObject,
    mut v_j_8856_: *mut crate::leanh::LeanObject,
    mut v_inv_8857_: *mut crate::leanh::LeanObject,
    mut v_bs_8858_: *mut crate::leanh::LeanObject,
    mut v___y_8859_: *mut crate::leanh::LeanObject,
    mut v___y_8860_: *mut crate::leanh::LeanObject,
    mut v___y_8861_: *mut crate::leanh::LeanObject,
    mut v___y_8862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8864_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___redArg(
        v_tail_8851_,
        v_params_8852_,
        v_motive_8853_,
        v_as_8854_,
        v_i_8855_,
        v_j_8856_,
        v_bs_8858_,
        v___y_8859_,
        v___y_8860_,
        v___y_8861_,
        v___y_8862_,
    );
    return v___x_8864_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0___boxed(
    mut v_tail_8865_: *mut crate::leanh::LeanObject,
    mut v_params_8866_: *mut crate::leanh::LeanObject,
    mut v_motive_8867_: *mut crate::leanh::LeanObject,
    mut v_as_8868_: *mut crate::leanh::LeanObject,
    mut v_i_8869_: *mut crate::leanh::LeanObject,
    mut v_j_8870_: *mut crate::leanh::LeanObject,
    mut v_inv_8871_: *mut crate::leanh::LeanObject,
    mut v_bs_8872_: *mut crate::leanh::LeanObject,
    mut v___y_8873_: *mut crate::leanh::LeanObject,
    mut v___y_8874_: *mut crate::leanh::LeanObject,
    mut v___y_8875_: *mut crate::leanh::LeanObject,
    mut v___y_8876_: *mut crate::leanh::LeanObject,
    mut v___y_8877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8878_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__0(
        v_tail_8865_,
        v_params_8866_,
        v_motive_8867_,
        v_as_8868_,
        v_i_8869_,
        v_j_8870_,
        v_inv_8871_,
        v_bs_8872_,
        v___y_8873_,
        v___y_8874_,
        v___y_8875_,
        v___y_8876_,
    );
    crate::leanh::lean_dec(v___y_8876_);
    crate::leanh::lean_dec_ref(v___y_8875_);
    crate::leanh::lean_dec(v___y_8874_);
    crate::leanh::lean_dec_ref(v___y_8873_);
    crate::leanh::lean_dec_ref(v_as_8868_);
    crate::leanh::lean_dec_ref(v_params_8866_);
    return v_res_8878_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2(
    mut v_tail_8879_: *mut crate::leanh::LeanObject,
    mut v_params_8880_: *mut crate::leanh::LeanObject,
    mut v_a_8881_: *mut crate::leanh::LeanObject,
    mut v_snd_8882_: *mut crate::leanh::LeanObject,
    mut v_alts_8883_: *mut crate::leanh::LeanObject,
    mut v_as_8884_: *mut crate::leanh::LeanObject,
    mut v_i_8885_: *mut crate::leanh::LeanObject,
    mut v_j_8886_: *mut crate::leanh::LeanObject,
    mut v_inv_8887_: *mut crate::leanh::LeanObject,
    mut v_bs_8888_: *mut crate::leanh::LeanObject,
    mut v___y_8889_: *mut crate::leanh::LeanObject,
    mut v___y_8890_: *mut crate::leanh::LeanObject,
    mut v___y_8891_: *mut crate::leanh::LeanObject,
    mut v___y_8892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_8894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_8894_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___redArg(
        v_tail_8879_,
        v_params_8880_,
        v_a_8881_,
        v_snd_8882_,
        v_alts_8883_,
        v_as_8884_,
        v_i_8885_,
        v_j_8886_,
        v_bs_8888_,
        v___y_8889_,
        v___y_8890_,
        v___y_8891_,
        v___y_8892_,
    );
    return v___x_8894_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2___boxed(
    mut v_tail_8895_: *mut crate::leanh::LeanObject,
    mut v_params_8896_: *mut crate::leanh::LeanObject,
    mut v_a_8897_: *mut crate::leanh::LeanObject,
    mut v_snd_8898_: *mut crate::leanh::LeanObject,
    mut v_alts_8899_: *mut crate::leanh::LeanObject,
    mut v_as_8900_: *mut crate::leanh::LeanObject,
    mut v_i_8901_: *mut crate::leanh::LeanObject,
    mut v_j_8902_: *mut crate::leanh::LeanObject,
    mut v_inv_8903_: *mut crate::leanh::LeanObject,
    mut v_bs_8904_: *mut crate::leanh::LeanObject,
    mut v___y_8905_: *mut crate::leanh::LeanObject,
    mut v___y_8906_: *mut crate::leanh::LeanObject,
    mut v___y_8907_: *mut crate::leanh::LeanObject,
    mut v___y_8908_: *mut crate::leanh::LeanObject,
    mut v___y_8909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_8910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_8910_ = l_Array_mapFinIdxM_map___at___00Lean_mkCasesOnSameCtor_spec__2(
        v_tail_8895_,
        v_params_8896_,
        v_a_8897_,
        v_snd_8898_,
        v_alts_8899_,
        v_as_8900_,
        v_i_8901_,
        v_j_8902_,
        v_inv_8903_,
        v_bs_8904_,
        v___y_8905_,
        v___y_8906_,
        v___y_8907_,
        v___y_8908_,
    );
    crate::leanh::lean_dec(v___y_8908_);
    crate::leanh::lean_dec_ref(v___y_8907_);
    crate::leanh::lean_dec(v___y_8906_);
    crate::leanh::lean_dec_ref(v___y_8905_);
    crate::leanh::lean_dec_ref(v_as_8900_);
    crate::leanh::lean_dec_ref(v_params_8896_);
    return v_res_8910_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Constructions_CasesOnSameCtor(
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
    res = runtime_initialize_Lean_Meta_CompletionName(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_CtorElim(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_App(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_SameCtorUtils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Constructions_CasesOnSameCtor(
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
pub unsafe fn initialize_Lean_Meta_Constructions_CasesOnSameCtor(
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
    res = initialize_Lean_Meta_CompletionName(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Constructions_CtorIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Constructions_CtorElim(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_App(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_SameCtorUtils(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Constructions_CasesOnSameCtor(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Constructions_CasesOnSameCtor(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Constructions_CasesOnSameCtor(builtin);
}

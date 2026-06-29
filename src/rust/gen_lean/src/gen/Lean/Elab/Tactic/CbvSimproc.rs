// Lean compiler output
// Module: Lean.Elab.Tactic.CbvSimproc
// Imports: Init.CbvSimproc Lean.Meta.Tactic.Cbv.CbvSimproc Lean.Elab.Command
use crate::r#gen::Init::CbvSimproc::{
    initialize_Init_CbvSimproc, runtime_initialize_Init_CbvSimproc,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Syntax_getArg,
    l_Lean_Syntax_isOfKind, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Compiler::InitAttr::l_Lean_declareBuiltin;
use crate::r#gen::Lean::CoreM::l_Lean_Core_mkFreshUserName;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::Elab::Command::{
    initialize_Lean_Elab_Command, l_Lean_Elab_Command_commandElabAttribute,
    l_Lean_Elab_Command_liftTermElabM___redArg, runtime_initialize_Lean_Elab_Command,
};
use crate::r#gen::Lean::Elab::Exception::l_Lean_Elab_unsupportedSyntaxExceptionId;
use crate::r#gen::Lean::Elab::SyntheticMVars::l_Lean_Elab_Term_synthesizeSyntheticMVars;
use crate::r#gen::Lean::Elab::Term::TermElabM::{
    l_Lean_Elab_Term_TermElabM_run___redArg, l_Lean_Elab_Term_elabTerm,
};
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_lit___override, l_Lean_mkApp3, l_Lean_mkAppB,
    l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofName,
    l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AbstractMVars::l_Lean_Meta_abstractMVars;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp, l_Lean_Meta_mkForallFVars,
    l_Lean_Meta_mkFreshExprMVar,
};
use crate::r#gen::Lean::Meta::Sym::Pattern::l_Lean_Meta_Sym_mkPatternFromExpr;
use crate::r#gen::Lean::Meta::Sym::Simp::DiscrTree::l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys;
use crate::r#gen::Lean::Meta::Tactic::Cbv::CbvSimproc::{
    initialize_Lean_Meta_Tactic_Cbv_CbvSimproc, l_Lean_Meta_Tactic_Cbv_registerCbvSimproc,
    runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ReservedNameAction::l_Lean_realizeGlobalConstNoOverload;
use crate::r#gen::Lean::ToExpr::l___private_Lean_ToExpr_0__Lean_Name_toExprAux;
use crate::ffi::{
    lean_array_get, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_string_dec_eq,
};
use crate::ffi::lean_st_ref_get;
pub static l_Lean_Elab_elabCbvSimprocPattern___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_elabCbvSimprocPattern___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_elabCbvSimprocPattern___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabCbvSimprocPattern___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_elabCbvSimprocPattern___closed__1_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_elabCbvSimprocPattern___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabCbvSimprocPattern___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_elabCbvSimprocPattern___closed__2_value: crate::leanh::LeanCtorObject<10> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8
                + 16) as u16,
            other: 8,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_elabCbvSimprocPattern___closed__0_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_elabCbvSimprocPattern___closed__1_value)
                as *mut crate::leanh::LeanObject,
            16843009 as *mut crate::leanh::LeanObject,
            65537 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_elabCbvSimprocPattern___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabCbvSimprocPattern___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_elabCbvSimprocPattern___closed__3_value: crate::leanh::LeanCtorObject<7> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7
                + 0) as u16,
            other: 7,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_elabCbvSimprocPattern___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabCbvSimprocPattern___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_mkSimprocPatternFromExpr___closed__0_value: crate::leanh::LeanClosureObject<
    1,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_mkSimprocPatternFromExpr___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 1,
    m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Elab_mkSimprocPatternFromExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkSimprocPatternFromExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value: crate::leanh::LeanStringObject<24> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value: crate::leanh::LeanStringObject<79> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value: crate::leanh::LeanStringObject<23> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value: crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<19> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__2_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkCbvSimprocType___closed__0_value: crate::leanh::LeanStringObject<52> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 52,
        m_capacity: 52,
        m_length: 51,
        m_data: [
            85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 121, 112, 101, 32, 102, 111,
            114, 32, 99, 98, 118, 32, 115, 105, 109, 112, 114, 111, 99, 32, 112, 97, 116, 116, 101,
            114, 110, 58, 32, 69, 120, 112, 101, 99, 116, 101, 100, 32, 96, 0,
        ],
    };
static mut l_Lean_Elab_checkCbvSimprocType___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_checkCbvSimprocType___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkCbvSimprocType___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkCbvSimprocType___closed__2_value: crate::leanh::LeanStringObject<5> =
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
static mut l_Lean_Elab_checkCbvSimprocType___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_checkCbvSimprocType___closed__3_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [77, 101, 116, 97, 0],
    };
static mut l_Lean_Elab_checkCbvSimprocType___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_checkCbvSimprocType___closed__4_value: crate::leanh::LeanStringObject<4> =
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
        m_data: [83, 121, 109, 0],
    };
static mut l_Lean_Elab_checkCbvSimprocType___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_checkCbvSimprocType___closed__5_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [83, 105, 109, 112, 0],
    };
static mut l_Lean_Elab_checkCbvSimprocType___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_checkCbvSimprocType___closed__6_value: crate::leanh::LeanStringObject<8> =
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
        m_data: [83, 105, 109, 112, 114, 111, 99, 0],
    };
static mut l_Lean_Elab_checkCbvSimprocType___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__6_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value)
                as *mut crate::leanh::LeanObject,
            11948124481539785030 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value)
                as *mut crate::leanh::LeanObject,
            15449383196166861506 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__4_value)
                as *mut crate::leanh::LeanObject,
            4034176598647545331 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_3: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__5_value)
                as *mut crate::leanh::LeanObject,
            13806531830123099675 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_checkCbvSimprocType___closed__7_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_3)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__6_value)
                as *mut crate::leanh::LeanObject,
            4585357269266081267 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_checkCbvSimprocType___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_checkCbvSimprocType___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkCbvSimprocType___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_checkCbvSimprocType___closed__9_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkCbvSimprocType___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkCbvSimprocType___closed__10_value: crate::leanh::LeanStringObject<9> =
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
        m_data: [96, 44, 32, 98, 117, 116, 32, 96, 0],
    };
static mut l_Lean_Elab_checkCbvSimprocType___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__10_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_checkCbvSimprocType___closed__11_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkCbvSimprocType___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_checkCbvSimprocType___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkCbvSimprocType___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkCbvSimprocType___closed__13_value: crate::leanh::LeanStringObject<11> =
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
        m_data: [96, 32, 104, 97, 115, 32, 116, 121, 112, 101, 0],
    };
static mut l_Lean_Elab_checkCbvSimprocType___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_checkCbvSimprocType___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkCbvSimprocType___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabCbvSimprocPattern___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabCbvSimprocPattern___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPattern___closed__1_value:
    crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        99, 98, 118, 83, 105, 109, 112, 114, 111, 99, 80, 97, 116, 116, 101, 114, 110, 0,
    ],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPattern___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__1_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__1_value)
            as *mut crate::leanh::LeanObject,
        5000477209128750040 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__1_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__2_value: crate::leanh::LeanStringObject<22> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [101, 108, 97, 98, 67, 98, 118, 83, 105, 109, 112, 114, 111, 99, 80, 97, 116, 116, 101, 114, 110, 0]};
static mut l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__1_value) as *mut crate::leanh::LeanObject,16981400742628996529 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__2_value) as *mut crate::leanh::LeanObject,14237717666078075311 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [68, 105, 115, 99, 114, 84, 114, 101, 101, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [75, 101, 121, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__2_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 116, 97, 114, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,12558998168795833107 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,6571394212498793888 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__2_value) as *mut crate::leanh::LeanObject,4525596147727532808 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__5_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 116, 104, 101, 114, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,12558998168795833107 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,6571394212498793888 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__5_value) as *mut crate::leanh::LeanObject,11989153488816012938 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__8_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [108, 105, 116, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__8_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,12558998168795833107 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,6571394212498793888 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__8_value) as *mut crate::leanh::LeanObject,15074539318474479562 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__11_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [76, 105, 116, 101, 114, 97, 108, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__12_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [110, 97, 116, 86, 97, 108, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__12_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__11_value) as *mut crate::leanh::LeanObject,7001815944269665831 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__12_value) as *mut crate::leanh::LeanObject,9295767770006931264 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__15_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 116, 114, 86, 97, 108, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__15_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__11_value) as *mut crate::leanh::LeanObject,7001815944269665831 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__15_value) as *mut crate::leanh::LeanObject,2005404019190257220 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__18_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [102, 118, 97, 114, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__18_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,12558998168795833107 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,6571394212498793888 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__18_value) as *mut crate::leanh::LeanObject,3087321959384269759 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__21_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [70, 86, 97, 114, 73, 100, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__21_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__22_value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__22: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__22_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__21_value) as *mut crate::leanh::LeanObject,6212595679582900358 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__22_value) as *mut crate::leanh::LeanObject,6968149084986791158 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__25_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 111, 110, 115, 116, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__25: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__25_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,12558998168795833107 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,6571394212498793888 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__25_value) as *mut crate::leanh::LeanObject,17383108283035838098 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__28_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 114, 114, 111, 119, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__28: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__28_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,12558998168795833107 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,6571394212498793888 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__28_value) as *mut crate::leanh::LeanObject,8457098344818307929 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__31_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 114, 111, 106, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__31: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__31_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value) as *mut crate::leanh::LeanObject,15449383196166861506 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,12558998168795833107 as *mut crate::leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut crate::leanh::LeanObject,6571394212498793888 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__31_value) as *mut crate::leanh::LeanObject,12263618261203284320 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__1_value:
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
    m_data: [67, 98, 118, 0],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<26> = crate::leanh::LeanStringObject {
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
        114, 101, 103, 105, 115, 116, 101, 114, 66, 117, 105, 108, 116, 105, 110, 67, 98, 118, 83,
        105, 109, 112, 114, 111, 99, 0,
    ],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 105, 115, 116, 0],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__4_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [116, 111, 65, 114, 114, 97, 121, 0],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__4_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5_value_aux_0:
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
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        9582258842178272501 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__4_value
        ) as *mut crate::leanh::LeanObject,
        8414467900391110369 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__8_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [100, 101, 99, 108, 97, 114, 101, 0],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__8:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__8_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__9_value:
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
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__8_value
        ) as *mut crate::leanh::LeanObject,
        13812150225987229964 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__9:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__9_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__10_value:
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
    m_data: [110, 105, 108, 0],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__10:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__10_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11_value_aux_0:
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
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        9582258842178272501 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__10_value
        ) as *mut crate::leanh::LeanObject,
        18135193680607614554 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__13_value:
    crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [99, 111, 110, 115, 0],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__13:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__13_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14_value_aux_0:
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
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3_value
        ) as *mut crate::leanh::LeanObject,
        9582258842178272501 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__13_value
        ) as *mut crate::leanh::LeanObject,
        8614124190858717794 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__0_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
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
        99, 98, 118, 83, 105, 109, 112, 114, 111, 99, 80, 97, 116, 116, 101, 114, 110, 66, 117,
        105, 108, 116, 105, 110, 0,
    ],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value)
            as *mut crate::leanh::LeanObject,
        11948124481539785030 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value_aux_0
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__0_value)
            as *mut crate::leanh::LeanObject,
        8018486133748762727 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__0_value)
            as *mut crate::leanh::LeanObject,
        2235975067317863979 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__0_value: crate::leanh::LeanStringObject<29> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [101, 108, 97, 98, 67, 98, 118, 83, 105, 109, 112, 114, 111, 99, 80, 97, 116, 116, 101, 114, 110, 66, 117, 105, 108, 116, 105, 110, 0]};
static mut l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__0_value) as *mut crate::leanh::LeanObject,11510100434945111860 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__1_value) as *mut crate::leanh::LeanObject,16981400742628996529 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__0_value) as *mut crate::leanh::LeanObject,8968079526420962855 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Elab_elabCbvSimprocPattern___lam__0(
    mut v_x_1134_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1135_: u8 = 0;
    v___x_1135_ = 0;
    return v___x_1135_;
}
pub unsafe fn l_Lean_Elab_elabCbvSimprocPattern___lam__0___boxed(
    mut v_x_1136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1137_: u8 = 0;
    let mut v_r_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1137_ = l_Lean_Elab_elabCbvSimprocPattern___lam__0(v_x_1136_);
    crate::leanh::lean_dec(v_x_1136_);
    v_r_1138_ = crate::leanh::lean_box((v_res_1137_) as usize);
    return v_r_1138_;
}
pub unsafe fn l_Lean_Elab_elabCbvSimprocPattern___lam__1(
    mut v_stx_1139_: *mut crate::leanh::LeanObject,
    mut v___x_1140_: *mut crate::leanh::LeanObject,
    mut v___x_1141_: u8,
    mut v___y_1142_: *mut crate::leanh::LeanObject,
    mut v___y_1143_: *mut crate::leanh::LeanObject,
    mut v___y_1144_: *mut crate::leanh::LeanObject,
    mut v___y_1145_: *mut crate::leanh::LeanObject,
    mut v___y_1146_: *mut crate::leanh::LeanObject,
    mut v___y_1147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: u8 = 0;
    let mut v___x_1152_: u8 = 0;
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1156_: u8 = 0;
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1160_: u8 = 0;
    let mut v_unused_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1165_: u8 = 0;
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1169_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1149_ = l_Lean_Elab_Term_elabTerm(
                    v_stx_1139_,
                    v___x_1140_,
                    v___x_1141_,
                    v___x_1141_,
                    v___y_1142_,
                    v___y_1143_,
                    v___y_1144_,
                    v___y_1145_,
                    v___y_1146_,
                    v___y_1147_,
                );
                if crate::leanh::lean_obj_tag(v___x_1149_) == 0 {
                    v_a_1150_ = crate::leanh::lean_ctor_get(v___x_1149_, 0);
                    crate::leanh::lean_inc(v_a_1150_);
                    crate::leanh::lean_dec_ref_known(v___x_1149_, 1);
                    v___x_1151_ = 0;
                    v___x_1152_ = 0;
                    v___x_1153_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(
                        v___x_1151_,
                        v___x_1152_,
                        v___y_1142_,
                        v___y_1143_,
                        v___y_1144_,
                        v___y_1145_,
                        v___y_1146_,
                        v___y_1147_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1153_) == 0 {
                        v_isSharedCheck_1160_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1153_)) as u8;
                        if v_isSharedCheck_1160_ == 0 {
                            v_unused_1161_ = crate::leanh::lean_ctor_get(v___x_1153_, 0);
                            crate::leanh::lean_dec(v_unused_1161_);
                            v___x_1155_ = v___x_1153_;
                            v_isShared_1156_ = v_isSharedCheck_1160_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_1153_);
                            v___x_1155_ = crate::leanh::lean_box(0);
                            v_isShared_1156_ = v_isSharedCheck_1160_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1150_);
                        v_a_1162_ = crate::leanh::lean_ctor_get(v___x_1153_, 0);
                        v_isSharedCheck_1169_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1153_)) as u8;
                        if v_isSharedCheck_1169_ == 0 {
                            v___x_1164_ = v___x_1153_;
                            v_isShared_1165_ = v_isSharedCheck_1169_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1162_);
                            crate::leanh::lean_dec(v___x_1153_);
                            v___x_1164_ = crate::leanh::lean_box(0);
                            v_isShared_1165_ = v_isSharedCheck_1169_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    return v___x_1149_;
                }
            }
            1 => {
                if v_isShared_1156_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1155_, 0, v_a_1150_);
                    v___x_1158_ = v___x_1155_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1159_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1150_);
                    v___x_1158_ = v_reuseFailAlloc_1159_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1158_;
            }
            3 => {
                if v_isShared_1165_ == 0 {
                    v___x_1167_ = v___x_1164_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1168_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
                    v___x_1167_ = v_reuseFailAlloc_1168_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1167_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_elabCbvSimprocPattern___lam__1___boxed(
    mut v_stx_1170_: *mut crate::leanh::LeanObject,
    mut v___x_1171_: *mut crate::leanh::LeanObject,
    mut v___x_1172_: *mut crate::leanh::LeanObject,
    mut v___y_1173_: *mut crate::leanh::LeanObject,
    mut v___y_1174_: *mut crate::leanh::LeanObject,
    mut v___y_1175_: *mut crate::leanh::LeanObject,
    mut v___y_1176_: *mut crate::leanh::LeanObject,
    mut v___y_1177_: *mut crate::leanh::LeanObject,
    mut v___y_1178_: *mut crate::leanh::LeanObject,
    mut v___y_1179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_356__boxed_1180_: u8 = 0;
    let mut v_res_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_356__boxed_1180_ = (crate::leanh::lean_unbox(v___x_1172_) as u8);
    v_res_1181_ = l_Lean_Elab_elabCbvSimprocPattern___lam__1(
        v_stx_1170_,
        v___x_1171_,
        v___x_356__boxed_1180_,
        v___y_1173_,
        v___y_1174_,
        v___y_1175_,
        v___y_1176_,
        v___y_1177_,
        v___y_1178_,
    );
    crate::leanh::lean_dec(v___y_1178_);
    crate::leanh::lean_dec_ref(v___y_1177_);
    crate::leanh::lean_dec(v___y_1176_);
    crate::leanh::lean_dec_ref(v___y_1175_);
    crate::leanh::lean_dec(v___y_1174_);
    crate::leanh::lean_dec_ref(v___y_1173_);
    return v_res_1181_;
}
pub unsafe fn l_Lean_Elab_elabCbvSimprocPattern(
    mut v_stx_1196_: *mut crate::leanh::LeanObject,
    mut v_a_1197_: *mut crate::leanh::LeanObject,
    mut v_a_1198_: *mut crate::leanh::LeanObject,
    mut v_a_1199_: *mut crate::leanh::LeanObject,
    mut v_a_1200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: u8 = 0;
    let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_go_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1212_: u8 = 0;
    let mut v_fst_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1217_: u8 = 0;
    let mut v_a_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1221_: u8 = 0;
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1202_ = crate::leanh::lean_box(0);
                v___x_1203_ = 1;
                v___x_1204_ = crate::leanh::lean_box((v___x_1203_) as usize);
                v_go_1205_ = crate::leanh::lean_alloc_closure(
                    l_Lean_Elab_elabCbvSimprocPattern___lam__1___boxed as *mut core::ffi::c_void,
                    10,
                    3,
                );
                crate::leanh::lean_closure_set(v_go_1205_, 0, v_stx_1196_);
                crate::leanh::lean_closure_set(v_go_1205_, 1, v___x_1202_);
                crate::leanh::lean_closure_set(v_go_1205_, 2, v___x_1204_);
                v___x_1206_ = l_Lean_Elab_elabCbvSimprocPattern___closed__2;
                v___x_1207_ = l_Lean_Elab_elabCbvSimprocPattern___closed__3;
                v___x_1208_ = l_Lean_Elab_Term_TermElabM_run___redArg(
                    v_go_1205_,
                    v___x_1206_,
                    v___x_1207_,
                    v_a_1197_,
                    v_a_1198_,
                    v_a_1199_,
                    v_a_1200_,
                );
                if crate::leanh::lean_obj_tag(v___x_1208_) == 0 {
                    v_a_1209_ = crate::leanh::lean_ctor_get(v___x_1208_, 0);
                    v_isSharedCheck_1217_ = (!crate::leanh::lean_is_exclusive(v___x_1208_)) as u8;
                    if v_isSharedCheck_1217_ == 0 {
                        v___x_1211_ = v___x_1208_;
                        v_isShared_1212_ = v_isSharedCheck_1217_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1209_);
                        crate::leanh::lean_dec(v___x_1208_);
                        v___x_1211_ = crate::leanh::lean_box(0);
                        v_isShared_1212_ = v_isSharedCheck_1217_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1218_ = crate::leanh::lean_ctor_get(v___x_1208_, 0);
                    v_isSharedCheck_1225_ = (!crate::leanh::lean_is_exclusive(v___x_1208_)) as u8;
                    if v_isSharedCheck_1225_ == 0 {
                        v___x_1220_ = v___x_1208_;
                        v_isShared_1221_ = v_isSharedCheck_1225_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1218_);
                        crate::leanh::lean_dec(v___x_1208_);
                        v___x_1220_ = crate::leanh::lean_box(0);
                        v_isShared_1221_ = v_isSharedCheck_1225_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1213_ = crate::leanh::lean_ctor_get(v_a_1209_, 0);
                crate::leanh::lean_inc(v_fst_1213_);
                crate::leanh::lean_dec(v_a_1209_);
                if v_isShared_1212_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1211_, 0, v_fst_1213_);
                    v___x_1215_ = v___x_1211_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1216_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_fst_1213_);
                    v___x_1215_ = v_reuseFailAlloc_1216_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1215_;
            }
            3 => {
                if v_isShared_1221_ == 0 {
                    v___x_1223_ = v___x_1220_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1224_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
                    v___x_1223_ = v_reuseFailAlloc_1224_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1223_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_elabCbvSimprocPattern___boxed(
    mut v_stx_1226_: *mut crate::leanh::LeanObject,
    mut v_a_1227_: *mut crate::leanh::LeanObject,
    mut v_a_1228_: *mut crate::leanh::LeanObject,
    mut v_a_1229_: *mut crate::leanh::LeanObject,
    mut v_a_1230_: *mut crate::leanh::LeanObject,
    mut v_a_1231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1232_ =
        l_Lean_Elab_elabCbvSimprocPattern(v_stx_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
    crate::leanh::lean_dec(v_a_1230_);
    crate::leanh::lean_dec_ref(v_a_1229_);
    crate::leanh::lean_dec(v_a_1228_);
    crate::leanh::lean_dec_ref(v_a_1227_);
    return v_res_1232_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg___lam__0(
    mut v_k_1233_: *mut crate::leanh::LeanObject,
    mut v_b_1234_: *mut crate::leanh::LeanObject,
    mut v_c_1235_: *mut crate::leanh::LeanObject,
    mut v___y_1236_: *mut crate::leanh::LeanObject,
    mut v___y_1237_: *mut crate::leanh::LeanObject,
    mut v___y_1238_: *mut crate::leanh::LeanObject,
    mut v___y_1239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1239_);
    crate::leanh::lean_inc_ref(v___y_1238_);
    crate::leanh::lean_inc(v___y_1237_);
    crate::leanh::lean_inc_ref(v___y_1236_);
    v___x_1241_ = crate::leanh::lean_apply_7(
        v_k_1233_,
        v_b_1234_,
        v_c_1235_,
        v___y_1236_,
        v___y_1237_,
        v___y_1238_,
        v___y_1239_,
        crate::leanh::lean_box(0),
    );
    return v___x_1241_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg___lam__0___boxed(
    mut v_k_1242_: *mut crate::leanh::LeanObject,
    mut v_b_1243_: *mut crate::leanh::LeanObject,
    mut v_c_1244_: *mut crate::leanh::LeanObject,
    mut v___y_1245_: *mut crate::leanh::LeanObject,
    mut v___y_1246_: *mut crate::leanh::LeanObject,
    mut v___y_1247_: *mut crate::leanh::LeanObject,
    mut v___y_1248_: *mut crate::leanh::LeanObject,
    mut v___y_1249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1250_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg___lam__0(v_k_1242_, v_b_1243_, v_c_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
    crate::leanh::lean_dec(v___y_1248_);
    crate::leanh::lean_dec_ref(v___y_1247_);
    crate::leanh::lean_dec(v___y_1246_);
    crate::leanh::lean_dec_ref(v___y_1245_);
    return v_res_1250_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg(
    mut v_e_1251_: *mut crate::leanh::LeanObject,
    mut v_k_1252_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1253_: u8,
    mut v___y_1254_: *mut crate::leanh::LeanObject,
    mut v___y_1255_: *mut crate::leanh::LeanObject,
    mut v___y_1256_: *mut crate::leanh::LeanObject,
    mut v___y_1257_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: u8 = 0;
    let mut v___x_1261_: u8 = 0;
    let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1267_: u8 = 0;
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1271_: u8 = 0;
    let mut v_a_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1275_: u8 = 0;
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1279_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1259_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                crate::leanh::lean_closure_set(v___f_1259_, 0, v_k_1252_);
                v___x_1260_ = 1;
                v___x_1261_ = 0;
                v___x_1262_ = crate::leanh::lean_box(0);
                v___x_1263_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    crate::leanh::lean_box(0),
                    v_e_1251_,
                    v___x_1260_,
                    v___x_1261_,
                    v___x_1260_,
                    v___x_1261_,
                    v___x_1262_,
                    v___f_1259_,
                    v_cleanupAnnotations_1253_,
                    v___y_1254_,
                    v___y_1255_,
                    v___y_1256_,
                    v___y_1257_,
                );
                if crate::leanh::lean_obj_tag(v___x_1263_) == 0 {
                    v_a_1264_ = crate::leanh::lean_ctor_get(v___x_1263_, 0);
                    v_isSharedCheck_1271_ = (!crate::leanh::lean_is_exclusive(v___x_1263_)) as u8;
                    if v_isSharedCheck_1271_ == 0 {
                        v___x_1266_ = v___x_1263_;
                        v_isShared_1267_ = v_isSharedCheck_1271_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1264_);
                        crate::leanh::lean_dec(v___x_1263_);
                        v___x_1266_ = crate::leanh::lean_box(0);
                        v_isShared_1267_ = v_isSharedCheck_1271_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1272_ = crate::leanh::lean_ctor_get(v___x_1263_, 0);
                    v_isSharedCheck_1279_ = (!crate::leanh::lean_is_exclusive(v___x_1263_)) as u8;
                    if v_isSharedCheck_1279_ == 0 {
                        v___x_1274_ = v___x_1263_;
                        v_isShared_1275_ = v_isSharedCheck_1279_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1272_);
                        crate::leanh::lean_dec(v___x_1263_);
                        v___x_1274_ = crate::leanh::lean_box(0);
                        v_isShared_1275_ = v_isSharedCheck_1279_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1267_ == 0 {
                    v___x_1269_ = v___x_1266_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1270_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
                    v___x_1269_ = v_reuseFailAlloc_1270_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1269_;
            }
            3 => {
                if v_isShared_1275_ == 0 {
                    v___x_1277_ = v___x_1274_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1278_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
                    v___x_1277_ = v_reuseFailAlloc_1278_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1277_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg___boxed(
    mut v_e_1280_: *mut crate::leanh::LeanObject,
    mut v_k_1281_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1282_: *mut crate::leanh::LeanObject,
    mut v___y_1283_: *mut crate::leanh::LeanObject,
    mut v___y_1284_: *mut crate::leanh::LeanObject,
    mut v___y_1285_: *mut crate::leanh::LeanObject,
    mut v___y_1286_: *mut crate::leanh::LeanObject,
    mut v___y_1287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1288_: u8 = 0;
    let mut v_res_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1288_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1282_) as u8);
    v_res_1289_ =
        l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg(
            v_e_1280_,
            v_k_1281_,
            v_cleanupAnnotations_boxed_1288_,
            v___y_1283_,
            v___y_1284_,
            v___y_1285_,
            v___y_1286_,
        );
    crate::leanh::lean_dec(v___y_1286_);
    crate::leanh::lean_dec_ref(v___y_1285_);
    crate::leanh::lean_dec(v___y_1284_);
    crate::leanh::lean_dec_ref(v___y_1283_);
    return v_res_1289_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0(
    mut v_00_u03b1_1290_: *mut crate::leanh::LeanObject,
    mut v_e_1291_: *mut crate::leanh::LeanObject,
    mut v_k_1292_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1293_: u8,
    mut v___y_1294_: *mut crate::leanh::LeanObject,
    mut v___y_1295_: *mut crate::leanh::LeanObject,
    mut v___y_1296_: *mut crate::leanh::LeanObject,
    mut v___y_1297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1299_ =
        l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg(
            v_e_1291_,
            v_k_1292_,
            v_cleanupAnnotations_1293_,
            v___y_1294_,
            v___y_1295_,
            v___y_1296_,
            v___y_1297_,
        );
    return v___x_1299_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___boxed(
    mut v_00_u03b1_1300_: *mut crate::leanh::LeanObject,
    mut v_e_1301_: *mut crate::leanh::LeanObject,
    mut v_k_1302_: *mut crate::leanh::LeanObject,
    mut v_cleanupAnnotations_1303_: *mut crate::leanh::LeanObject,
    mut v___y_1304_: *mut crate::leanh::LeanObject,
    mut v___y_1305_: *mut crate::leanh::LeanObject,
    mut v___y_1306_: *mut crate::leanh::LeanObject,
    mut v___y_1307_: *mut crate::leanh::LeanObject,
    mut v___y_1308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1309_: u8 = 0;
    let mut v_res_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1309_ = (crate::leanh::lean_unbox(v_cleanupAnnotations_1303_) as u8);
    v_res_1310_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0(
        v_00_u03b1_1300_,
        v_e_1301_,
        v_k_1302_,
        v_cleanupAnnotations_boxed_1309_,
        v___y_1304_,
        v___y_1305_,
        v___y_1306_,
        v___y_1307_,
    );
    crate::leanh::lean_dec(v___y_1307_);
    crate::leanh::lean_dec_ref(v___y_1306_);
    crate::leanh::lean_dec(v___y_1305_);
    crate::leanh::lean_dec_ref(v___y_1304_);
    return v_res_1310_;
}
pub unsafe fn l_Lean_Elab_mkSimprocPatternFromExpr___lam__0(
    mut v___x_1311_: u8,
    mut v_args_1312_: *mut crate::leanh::LeanObject,
    mut v_body_1313_: *mut crate::leanh::LeanObject,
    mut v___y_1314_: *mut crate::leanh::LeanObject,
    mut v___y_1315_: *mut crate::leanh::LeanObject,
    mut v___y_1316_: *mut crate::leanh::LeanObject,
    mut v___y_1317_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1319_: u8 = 0;
    let mut v___x_1320_: u8 = 0;
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1319_ = 0;
    v___x_1320_ = 1;
    v___x_1321_ = l_Lean_Meta_mkForallFVars(
        v_args_1312_,
        v_body_1313_,
        v___x_1319_,
        v___x_1311_,
        v___x_1311_,
        v___x_1320_,
        v___y_1314_,
        v___y_1315_,
        v___y_1316_,
        v___y_1317_,
    );
    return v___x_1321_;
}
pub unsafe fn l_Lean_Elab_mkSimprocPatternFromExpr___lam__0___boxed(
    mut v___x_1322_: *mut crate::leanh::LeanObject,
    mut v_args_1323_: *mut crate::leanh::LeanObject,
    mut v_body_1324_: *mut crate::leanh::LeanObject,
    mut v___y_1325_: *mut crate::leanh::LeanObject,
    mut v___y_1326_: *mut crate::leanh::LeanObject,
    mut v___y_1327_: *mut crate::leanh::LeanObject,
    mut v___y_1328_: *mut crate::leanh::LeanObject,
    mut v___y_1329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_637__boxed_1330_: u8 = 0;
    let mut v_res_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_637__boxed_1330_ = (crate::leanh::lean_unbox(v___x_1322_) as u8);
    v_res_1331_ = l_Lean_Elab_mkSimprocPatternFromExpr___lam__0(
        v___x_637__boxed_1330_,
        v_args_1323_,
        v_body_1324_,
        v___y_1325_,
        v___y_1326_,
        v___y_1327_,
        v___y_1328_,
    );
    crate::leanh::lean_dec(v___y_1328_);
    crate::leanh::lean_dec_ref(v___y_1327_);
    crate::leanh::lean_dec(v___y_1326_);
    crate::leanh::lean_dec_ref(v___y_1325_);
    crate::leanh::lean_dec_ref(v_args_1323_);
    return v_res_1331_;
}
pub unsafe fn l_Lean_Elab_mkSimprocPatternFromExpr(
    mut v_e_1335_: *mut crate::leanh::LeanObject,
    mut v_a_1336_: *mut crate::leanh::LeanObject,
    mut v_a_1337_: *mut crate::leanh::LeanObject,
    mut v_a_1338_: *mut crate::leanh::LeanObject,
    mut v_a_1339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1341_: u8 = 0;
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramNames_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: u8 = 0;
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: u8 = 0;
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1361_: u8 = 0;
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1365_: u8 = 0;
    let mut v_a_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v___x_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1373_: u8 = 0;
    let mut v_a_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1377_: u8 = 0;
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1341_ = 1;
                v___x_1342_ = l_Lean_Meta_abstractMVars(
                    v_e_1335_,
                    v___x_1341_,
                    v_a_1336_,
                    v_a_1337_,
                    v_a_1338_,
                    v_a_1339_,
                );
                if crate::leanh::lean_obj_tag(v___x_1342_) == 0 {
                    v_a_1343_ = crate::leanh::lean_ctor_get(v___x_1342_, 0);
                    crate::leanh::lean_inc(v_a_1343_);
                    crate::leanh::lean_dec_ref_known(v___x_1342_, 1);
                    v_paramNames_1344_ = crate::leanh::lean_ctor_get(v_a_1343_, 0);
                    crate::leanh::lean_inc_ref(v_paramNames_1344_);
                    v_expr_1345_ = crate::leanh::lean_ctor_get(v_a_1343_, 2);
                    crate::leanh::lean_inc_ref(v_expr_1345_);
                    crate::leanh::lean_dec(v_a_1343_);
                    v___f_1346_ = l_Lean_Elab_mkSimprocPatternFromExpr___closed__0;
                    v___x_1347_ = 0;
                    v___x_1348_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg(v_expr_1345_, v___f_1346_, v___x_1347_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
                    if crate::leanh::lean_obj_tag(v___x_1348_) == 0 {
                        v_a_1349_ = crate::leanh::lean_ctor_get(v___x_1348_, 0);
                        crate::leanh::lean_inc(v_a_1349_);
                        crate::leanh::lean_dec_ref_known(v___x_1348_, 1);
                        v___x_1350_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1350_, 0, v_a_1349_);
                        v___x_1351_ = 0;
                        v___x_1352_ = crate::leanh::lean_box(0);
                        v___x_1353_ = l_Lean_Meta_mkFreshExprMVar(
                            v___x_1350_,
                            v___x_1351_,
                            v___x_1352_,
                            v_a_1336_,
                            v_a_1337_,
                            v_a_1338_,
                            v_a_1339_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1353_) == 0 {
                            v_a_1354_ = crate::leanh::lean_ctor_get(v___x_1353_, 0);
                            crate::leanh::lean_inc(v_a_1354_);
                            crate::leanh::lean_dec_ref_known(v___x_1353_, 1);
                            v___x_1355_ = lean_array_to_list(v_paramNames_1344_);
                            v___x_1356_ = crate::leanh::lean_box(0);
                            v___x_1357_ = l_Lean_Meta_Sym_mkPatternFromExpr(
                                v_a_1354_,
                                v___x_1355_,
                                v___x_1356_,
                                v_a_1336_,
                                v_a_1337_,
                                v_a_1338_,
                                v_a_1339_,
                            );
                            return v___x_1357_;
                        } else {
                            crate::leanh::lean_dec_ref(v_paramNames_1344_);
                            v_a_1358_ = crate::leanh::lean_ctor_get(v___x_1353_, 0);
                            v_isSharedCheck_1365_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1353_)) as u8;
                            if v_isSharedCheck_1365_ == 0 {
                                v___x_1360_ = v___x_1353_;
                                v_isShared_1361_ = v_isSharedCheck_1365_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1358_);
                                crate::leanh::lean_dec(v___x_1353_);
                                v___x_1360_ = crate::leanh::lean_box(0);
                                v_isShared_1361_ = v_isSharedCheck_1365_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_paramNames_1344_);
                        v_a_1366_ = crate::leanh::lean_ctor_get(v___x_1348_, 0);
                        v_isSharedCheck_1373_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1348_)) as u8;
                        if v_isSharedCheck_1373_ == 0 {
                            v___x_1368_ = v___x_1348_;
                            v_isShared_1369_ = v_isSharedCheck_1373_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1366_);
                            crate::leanh::lean_dec(v___x_1348_);
                            v___x_1368_ = crate::leanh::lean_box(0);
                            v_isShared_1369_ = v_isSharedCheck_1373_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_1374_ = crate::leanh::lean_ctor_get(v___x_1342_, 0);
                    v_isSharedCheck_1381_ = (!crate::leanh::lean_is_exclusive(v___x_1342_)) as u8;
                    if v_isSharedCheck_1381_ == 0 {
                        v___x_1376_ = v___x_1342_;
                        v_isShared_1377_ = v_isSharedCheck_1381_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1374_);
                        crate::leanh::lean_dec(v___x_1342_);
                        v___x_1376_ = crate::leanh::lean_box(0);
                        v_isShared_1377_ = v_isSharedCheck_1381_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1361_ == 0 {
                    v___x_1363_ = v___x_1360_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1364_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
                    v___x_1363_ = v_reuseFailAlloc_1364_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1363_;
            }
            3 => {
                if v_isShared_1369_ == 0 {
                    v___x_1371_ = v___x_1368_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1372_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
                    v___x_1371_ = v_reuseFailAlloc_1372_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1371_;
            }
            5 => {
                if v_isShared_1377_ == 0 {
                    v___x_1379_ = v___x_1376_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1380_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
                    v___x_1379_ = v_reuseFailAlloc_1380_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1379_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_mkSimprocPatternFromExpr___boxed(
    mut v_e_1382_: *mut crate::leanh::LeanObject,
    mut v_a_1383_: *mut crate::leanh::LeanObject,
    mut v_a_1384_: *mut crate::leanh::LeanObject,
    mut v_a_1385_: *mut crate::leanh::LeanObject,
    mut v_a_1386_: *mut crate::leanh::LeanObject,
    mut v_a_1387_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1388_ =
        l_Lean_Elab_mkSimprocPatternFromExpr(v_e_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_);
    crate::leanh::lean_dec(v_a_1386_);
    crate::leanh::lean_dec_ref(v_a_1385_);
    crate::leanh::lean_dec(v_a_1384_);
    crate::leanh::lean_dec_ref(v_a_1383_);
    return v_res_1388_;
}
pub unsafe fn l_Lean_Elab_elabCbvSimprocKeys(
    mut v_stx_1389_: *mut crate::leanh::LeanObject,
    mut v_a_1390_: *mut crate::leanh::LeanObject,
    mut v_a_1391_: *mut crate::leanh::LeanObject,
    mut v_a_1392_: *mut crate::leanh::LeanObject,
    mut v_a_1393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1401_: u8 = 0;
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1406_: u8 = 0;
    let mut v_a_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1410_: u8 = 0;
    let mut v___x_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1414_: u8 = 0;
    let mut v_a_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1418_: u8 = 0;
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1422_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1395_ = l_Lean_Elab_elabCbvSimprocPattern(
                    v_stx_1389_,
                    v_a_1390_,
                    v_a_1391_,
                    v_a_1392_,
                    v_a_1393_,
                );
                if crate::leanh::lean_obj_tag(v___x_1395_) == 0 {
                    v_a_1396_ = crate::leanh::lean_ctor_get(v___x_1395_, 0);
                    crate::leanh::lean_inc(v_a_1396_);
                    crate::leanh::lean_dec_ref_known(v___x_1395_, 1);
                    v___x_1397_ = l_Lean_Elab_mkSimprocPatternFromExpr(
                        v_a_1396_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1397_) == 0 {
                        v_a_1398_ = crate::leanh::lean_ctor_get(v___x_1397_, 0);
                        v_isSharedCheck_1406_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1397_)) as u8;
                        if v_isSharedCheck_1406_ == 0 {
                            v___x_1400_ = v___x_1397_;
                            v_isShared_1401_ = v_isSharedCheck_1406_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1398_);
                            crate::leanh::lean_dec(v___x_1397_);
                            v___x_1400_ = crate::leanh::lean_box(0);
                            v_isShared_1401_ = v_isSharedCheck_1406_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1407_ = crate::leanh::lean_ctor_get(v___x_1397_, 0);
                        v_isSharedCheck_1414_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1397_)) as u8;
                        if v_isSharedCheck_1414_ == 0 {
                            v___x_1409_ = v___x_1397_;
                            v_isShared_1410_ = v_isSharedCheck_1414_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1407_);
                            crate::leanh::lean_dec(v___x_1397_);
                            v___x_1409_ = crate::leanh::lean_box(0);
                            v_isShared_1410_ = v_isSharedCheck_1414_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_1415_ = crate::leanh::lean_ctor_get(v___x_1395_, 0);
                    v_isSharedCheck_1422_ = (!crate::leanh::lean_is_exclusive(v___x_1395_)) as u8;
                    if v_isSharedCheck_1422_ == 0 {
                        v___x_1417_ = v___x_1395_;
                        v_isShared_1418_ = v_isSharedCheck_1422_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1415_);
                        crate::leanh::lean_dec(v___x_1395_);
                        v___x_1417_ = crate::leanh::lean_box(0);
                        v_isShared_1418_ = v_isSharedCheck_1422_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1402_ = l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(v_a_1398_);
                if v_isShared_1401_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1400_, 0, v___x_1402_);
                    v___x_1404_ = v___x_1400_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1405_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
                    v___x_1404_ = v_reuseFailAlloc_1405_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1404_;
            }
            3 => {
                if v_isShared_1410_ == 0 {
                    v___x_1412_ = v___x_1409_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1413_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
                    v___x_1412_ = v_reuseFailAlloc_1413_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1412_;
            }
            5 => {
                if v_isShared_1418_ == 0 {
                    v___x_1420_ = v___x_1417_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1421_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
                    v___x_1420_ = v_reuseFailAlloc_1421_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1420_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_elabCbvSimprocKeys___boxed(
    mut v_stx_1423_: *mut crate::leanh::LeanObject,
    mut v_a_1424_: *mut crate::leanh::LeanObject,
    mut v_a_1425_: *mut crate::leanh::LeanObject,
    mut v_a_1426_: *mut crate::leanh::LeanObject,
    mut v_a_1427_: *mut crate::leanh::LeanObject,
    mut v_a_1428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1429_ =
        l_Lean_Elab_elabCbvSimprocKeys(v_stx_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
    crate::leanh::lean_dec(v_a_1427_);
    crate::leanh::lean_dec_ref(v_a_1426_);
    crate::leanh::lean_dec(v_a_1425_);
    crate::leanh::lean_dec_ref(v_a_1424_);
    return v_res_1429_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1430_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1430_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1431_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0);
    v___x_1432_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1432_, 0, v___x_1431_);
    return v___x_1432_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1433_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1);
    v___x_1434_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1435_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1435_, 0, v___x_1434_);
    crate::leanh::lean_ctor_set(v___x_1435_, 1, v___x_1434_);
    crate::leanh::lean_ctor_set(v___x_1435_, 2, v___x_1434_);
    crate::leanh::lean_ctor_set(v___x_1435_, 3, v___x_1434_);
    crate::leanh::lean_ctor_set(v___x_1435_, 4, v___x_1433_);
    crate::leanh::lean_ctor_set(v___x_1435_, 5, v___x_1433_);
    crate::leanh::lean_ctor_set(v___x_1435_, 6, v___x_1433_);
    crate::leanh::lean_ctor_set(v___x_1435_, 7, v___x_1433_);
    crate::leanh::lean_ctor_set(v___x_1435_, 8, v___x_1433_);
    crate::leanh::lean_ctor_set(v___x_1435_, 9, v___x_1433_);
    return v___x_1435_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1436_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1437_ = lean_mk_empty_array_with_capacity(v___x_1436_);
    v___x_1438_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1438_, 0, v___x_1437_);
    return v___x_1438_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1439_: usize = 0;
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1439_ = 5usize;
    v___x_1440_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1441_ = crate::leanh::lean_unsigned_to_nat(32);
    v___x_1442_ = lean_mk_empty_array_with_capacity(v___x_1441_);
    v___x_1443_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3);
    v___x_1444_ = crate::leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    crate::leanh::lean_ctor_set(v___x_1444_, 0, v___x_1443_);
    crate::leanh::lean_ctor_set(v___x_1444_, 1, v___x_1442_);
    crate::leanh::lean_ctor_set(v___x_1444_, 2, v___x_1440_);
    crate::leanh::lean_ctor_set(v___x_1444_, 3, v___x_1440_);
    crate::leanh::lean_ctor_set_usize(v___x_1444_, 4, v___x_1439_);
    return v___x_1444_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1445_ = crate::leanh::lean_box(1);
    v___x_1446_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4);
    v___x_1447_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1);
    v___x_1448_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1448_, 0, v___x_1447_);
    crate::leanh::lean_ctor_set(v___x_1448_, 1, v___x_1446_);
    crate::leanh::lean_ctor_set(v___x_1448_, 2, v___x_1445_);
    return v___x_1448_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2(
    mut v_msgData_1449_: *mut crate::leanh::LeanObject,
    mut v___y_1450_: *mut crate::leanh::LeanObject,
    mut v___y_1451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1453_ = lean_st_ref_get(v___y_1451_);
    v_env_1454_ = crate::leanh::lean_ctor_get(v___x_1453_, 0);
    crate::leanh::lean_inc_ref(v_env_1454_);
    crate::leanh::lean_dec(v___x_1453_);
    v_options_1455_ = crate::leanh::lean_ctor_get(v___y_1450_, 2);
    v___x_1456_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2);
    v___x_1457_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5);
    crate::leanh::lean_inc_ref(v_options_1455_);
    v___x_1458_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1458_, 0, v_env_1454_);
    crate::leanh::lean_ctor_set(v___x_1458_, 1, v___x_1456_);
    crate::leanh::lean_ctor_set(v___x_1458_, 2, v___x_1457_);
    crate::leanh::lean_ctor_set(v___x_1458_, 3, v_options_1455_);
    v___x_1459_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1459_, 0, v___x_1458_);
    crate::leanh::lean_ctor_set(v___x_1459_, 1, v_msgData_1449_);
    v___x_1460_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1460_, 0, v___x_1459_);
    return v___x_1460_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___boxed(
    mut v_msgData_1461_: *mut crate::leanh::LeanObject,
    mut v___y_1462_: *mut crate::leanh::LeanObject,
    mut v___y_1463_: *mut crate::leanh::LeanObject,
    mut v___y_1464_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1465_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2(v_msgData_1461_, v___y_1462_, v___y_1463_);
    crate::leanh::lean_dec(v___y_1463_);
    crate::leanh::lean_dec_ref(v___y_1462_);
    return v_res_1465_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(
    mut v_msg_1466_: *mut crate::leanh::LeanObject,
    mut v___y_1467_: *mut crate::leanh::LeanObject,
    mut v___y_1468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1475_: u8 = 0;
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1470_ = crate::leanh::lean_ctor_get(v___y_1467_, 5);
                v___x_1471_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2(v_msg_1466_, v___y_1467_, v___y_1468_);
                v_a_1472_ = crate::leanh::lean_ctor_get(v___x_1471_, 0);
                v_isSharedCheck_1480_ = (!crate::leanh::lean_is_exclusive(v___x_1471_)) as u8;
                if v_isSharedCheck_1480_ == 0 {
                    v___x_1474_ = v___x_1471_;
                    v_isShared_1475_ = v_isSharedCheck_1480_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1472_);
                    crate::leanh::lean_dec(v___x_1471_);
                    v___x_1474_ = crate::leanh::lean_box(0);
                    v_isShared_1475_ = v_isSharedCheck_1480_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_1470_);
                v___x_1476_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1476_, 0, v_ref_1470_);
                crate::leanh::lean_ctor_set(v___x_1476_, 1, v_a_1472_);
                if v_isShared_1475_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1474_, 1);
                    crate::leanh::lean_ctor_set(v___x_1474_, 0, v___x_1476_);
                    v___x_1478_ = v___x_1474_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1479_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
                    v___x_1478_ = v_reuseFailAlloc_1479_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1478_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg___boxed(
    mut v_msg_1481_: *mut crate::leanh::LeanObject,
    mut v___y_1482_: *mut crate::leanh::LeanObject,
    mut v___y_1483_: *mut crate::leanh::LeanObject,
    mut v___y_1484_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1485_ = l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(
        v_msg_1481_,
        v___y_1482_,
        v___y_1483_,
    );
    crate::leanh::lean_dec(v___y_1483_);
    crate::leanh::lean_dec_ref(v___y_1482_);
    return v_res_1485_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1487_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0;
    v___x_1488_ = l_Lean_stringToMessageData(v___x_1487_);
    return v___x_1488_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1490_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2;
    v___x_1491_ = l_Lean_stringToMessageData(v___x_1490_);
    return v___x_1491_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1493_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4;
    v___x_1494_ = l_Lean_stringToMessageData(v___x_1493_);
    return v___x_1494_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1496_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6;
    v___x_1497_ = l_Lean_stringToMessageData(v___x_1496_);
    return v___x_1497_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1499_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8;
    v___x_1500_ = l_Lean_stringToMessageData(v___x_1499_);
    return v___x_1500_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1502_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10;
    v___x_1503_ = l_Lean_stringToMessageData(v___x_1502_);
    return v___x_1503_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1505_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12;
    v___x_1506_ = l_Lean_stringToMessageData(v___x_1505_);
    return v___x_1506_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(
    mut v_msg_1507_: *mut crate::leanh::LeanObject,
    mut v_declHint_1508_: *mut crate::leanh::LeanObject,
    mut v___y_1509_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: u8 = 0;
    let mut v_isExporting_1514_: u8 = 0;
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: u8 = 0;
    let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1536_: u8 = 0;
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: u8 = 0;
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1568_: u8 = 0;
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1511_ = lean_st_ref_get(v___y_1509_);
                v_env_1512_ = crate::leanh::lean_ctor_get(v___x_1511_, 0);
                crate::leanh::lean_inc_ref(v_env_1512_);
                crate::leanh::lean_dec(v___x_1511_);
                v___x_1513_ = l_Lean_Name_isAnonymous(v_declHint_1508_);
                if v___x_1513_ == 0 {
                    v_isExporting_1514_ = crate::leanh::lean_ctor_get_uint8(
                        v_env_1512_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1514_ == 0 {
                        crate::leanh::lean_dec_ref(v_env_1512_);
                        crate::leanh::lean_dec(v_declHint_1508_);
                        v___x_1515_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1515_, 0, v_msg_1507_);
                        return v___x_1515_;
                    } else {
                        crate::leanh::lean_inc_ref(v_env_1512_);
                        v___x_1516_ = l_Lean_Environment_setExporting(v_env_1512_, v___x_1513_);
                        crate::leanh::lean_inc(v_declHint_1508_);
                        crate::leanh::lean_inc_ref(v___x_1516_);
                        v___x_1517_ = l_Lean_Environment_contains(
                            v___x_1516_,
                            v_declHint_1508_,
                            v_isExporting_1514_,
                        );
                        if v___x_1517_ == 0 {
                            crate::leanh::lean_dec_ref(v___x_1516_);
                            crate::leanh::lean_dec_ref(v_env_1512_);
                            crate::leanh::lean_dec(v_declHint_1508_);
                            v___x_1518_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1518_, 0, v_msg_1507_);
                            return v___x_1518_;
                        } else {
                            v___x_1519_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2);
                            v___x_1520_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5);
                            v___x_1521_ = l_Lean_Options_empty;
                            v___x_1522_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1522_, 0, v___x_1516_);
                            crate::leanh::lean_ctor_set(v___x_1522_, 1, v___x_1519_);
                            crate::leanh::lean_ctor_set(v___x_1522_, 2, v___x_1520_);
                            crate::leanh::lean_ctor_set(v___x_1522_, 3, v___x_1521_);
                            crate::leanh::lean_inc(v_declHint_1508_);
                            v___x_1523_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1508_, v___x_1513_);
                            v_c_1524_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_c_1524_, 0, v___x_1522_);
                            crate::leanh::lean_ctor_set(v_c_1524_, 1, v___x_1523_);
                            v___x_1525_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1512_,
                                v_declHint_1508_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1525_) == 0 {
                                crate::leanh::lean_dec_ref(v_env_1512_);
                                crate::leanh::lean_dec(v_declHint_1508_);
                                v___x_1526_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
                                v___x_1527_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1527_, 0, v___x_1526_);
                                crate::leanh::lean_ctor_set(v___x_1527_, 1, v_c_1524_);
                                v___x_1528_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
                                v___x_1529_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1529_, 0, v___x_1527_);
                                crate::leanh::lean_ctor_set(v___x_1529_, 1, v___x_1528_);
                                v___x_1530_ = l_Lean_MessageData_note(v___x_1529_);
                                v___x_1531_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1531_, 0, v_msg_1507_);
                                crate::leanh::lean_ctor_set(v___x_1531_, 1, v___x_1530_);
                                v___x_1532_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1532_, 0, v___x_1531_);
                                return v___x_1532_;
                            } else {
                                v_val_1533_ = crate::leanh::lean_ctor_get(v___x_1525_, 0);
                                v_isSharedCheck_1568_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1525_)) as u8;
                                if v_isSharedCheck_1568_ == 0 {
                                    v___x_1535_ = v___x_1525_;
                                    v_isShared_1536_ = v_isSharedCheck_1568_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_val_1533_);
                                    crate::leanh::lean_dec(v___x_1525_);
                                    v___x_1535_ = crate::leanh::lean_box(0);
                                    v_isShared_1536_ = v_isSharedCheck_1568_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_env_1512_);
                    crate::leanh::lean_dec(v_declHint_1508_);
                    v___x_1569_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1569_, 0, v_msg_1507_);
                    return v___x_1569_;
                }
            }
            1 => {
                v___x_1537_ = crate::leanh::lean_box(0);
                v___x_1538_ = l_Lean_Environment_header(v_env_1512_);
                crate::leanh::lean_dec_ref(v_env_1512_);
                v___x_1539_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1538_);
                v_mod_1540_ = lean_array_get(v___x_1537_, v___x_1539_, v_val_1533_);
                crate::leanh::lean_dec(v_val_1533_);
                crate::leanh::lean_dec_ref(v___x_1539_);
                v___x_1541_ = l_Lean_isPrivateName(v_declHint_1508_);
                crate::leanh::lean_dec(v_declHint_1508_);
                if v___x_1541_ == 0 {
                    v___x_1542_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
                    v___x_1543_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1543_, 0, v___x_1542_);
                    crate::leanh::lean_ctor_set(v___x_1543_, 1, v_c_1524_);
                    v___x_1544_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
                    v___x_1545_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1545_, 0, v___x_1543_);
                    crate::leanh::lean_ctor_set(v___x_1545_, 1, v___x_1544_);
                    v___x_1546_ = l_Lean_MessageData_ofName(v_mod_1540_);
                    v___x_1547_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1547_, 0, v___x_1545_);
                    crate::leanh::lean_ctor_set(v___x_1547_, 1, v___x_1546_);
                    v___x_1548_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
                    v___x_1549_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1549_, 0, v___x_1547_);
                    crate::leanh::lean_ctor_set(v___x_1549_, 1, v___x_1548_);
                    v___x_1550_ = l_Lean_MessageData_note(v___x_1549_);
                    v___x_1551_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1551_, 0, v_msg_1507_);
                    crate::leanh::lean_ctor_set(v___x_1551_, 1, v___x_1550_);
                    if v_isShared_1536_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1535_, 0);
                        crate::leanh::lean_ctor_set(v___x_1535_, 0, v___x_1551_);
                        v___x_1553_ = v___x_1535_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1554_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
                        v___x_1553_ = v_reuseFailAlloc_1554_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1555_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
                    v___x_1556_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1556_, 0, v___x_1555_);
                    crate::leanh::lean_ctor_set(v___x_1556_, 1, v_c_1524_);
                    v___x_1557_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
                    v___x_1558_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1558_, 0, v___x_1556_);
                    crate::leanh::lean_ctor_set(v___x_1558_, 1, v___x_1557_);
                    v___x_1559_ = l_Lean_MessageData_ofName(v_mod_1540_);
                    v___x_1560_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1560_, 0, v___x_1558_);
                    crate::leanh::lean_ctor_set(v___x_1560_, 1, v___x_1559_);
                    v___x_1561_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
                    v___x_1562_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1562_, 0, v___x_1560_);
                    crate::leanh::lean_ctor_set(v___x_1562_, 1, v___x_1561_);
                    v___x_1563_ = l_Lean_MessageData_note(v___x_1562_);
                    v___x_1564_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1564_, 0, v_msg_1507_);
                    crate::leanh::lean_ctor_set(v___x_1564_, 1, v___x_1563_);
                    if v_isShared_1536_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1535_, 0);
                        crate::leanh::lean_ctor_set(v___x_1535_, 0, v___x_1564_);
                        v___x_1566_ = v___x_1535_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1567_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
                        v___x_1566_ = v_reuseFailAlloc_1567_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1553_;
            }
            3 => {
                return v___x_1566_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(
    mut v_msg_1570_: *mut crate::leanh::LeanObject,
    mut v_declHint_1571_: *mut crate::leanh::LeanObject,
    mut v___y_1572_: *mut crate::leanh::LeanObject,
    mut v___y_1573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1574_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1570_, v_declHint_1571_, v___y_1572_);
    crate::leanh::lean_dec(v___y_1572_);
    return v_res_1574_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(
    mut v_msg_1575_: *mut crate::leanh::LeanObject,
    mut v_declHint_1576_: *mut crate::leanh::LeanObject,
    mut v___y_1577_: *mut crate::leanh::LeanObject,
    mut v___y_1578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1584_: u8 = 0;
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1590_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1580_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1575_, v_declHint_1576_, v___y_1578_);
                v_a_1581_ = crate::leanh::lean_ctor_get(v___x_1580_, 0);
                v_isSharedCheck_1590_ = (!crate::leanh::lean_is_exclusive(v___x_1580_)) as u8;
                if v_isSharedCheck_1590_ == 0 {
                    v___x_1583_ = v___x_1580_;
                    v_isShared_1584_ = v_isSharedCheck_1590_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_1581_);
                    crate::leanh::lean_dec(v___x_1580_);
                    v___x_1583_ = crate::leanh::lean_box(0);
                    v_isShared_1584_ = v_isSharedCheck_1590_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1585_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1586_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1586_, 0, v___x_1585_);
                crate::leanh::lean_ctor_set(v___x_1586_, 1, v_a_1581_);
                if v_isShared_1584_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1583_, 0, v___x_1586_);
                    v___x_1588_ = v___x_1583_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1589_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
                    v___x_1588_ = v_reuseFailAlloc_1589_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1588_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(
    mut v_msg_1591_: *mut crate::leanh::LeanObject,
    mut v_declHint_1592_: *mut crate::leanh::LeanObject,
    mut v___y_1593_: *mut crate::leanh::LeanObject,
    mut v___y_1594_: *mut crate::leanh::LeanObject,
    mut v___y_1595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1596_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1591_, v_declHint_1592_, v___y_1593_, v___y_1594_);
    crate::leanh::lean_dec(v___y_1594_);
    crate::leanh::lean_dec_ref(v___y_1593_);
    return v_res_1596_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(
    mut v_ref_1597_: *mut crate::leanh::LeanObject,
    mut v_msg_1598_: *mut crate::leanh::LeanObject,
    mut v___y_1599_: *mut crate::leanh::LeanObject,
    mut v___y_1600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fileName_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1614_: u8 = 0;
    let mut v_cancelTk_x3f_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1616_: u8 = 0;
    let mut v_inheritedTraceOptions_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1602_ = crate::leanh::lean_ctor_get(v___y_1599_, 0);
    v_fileMap_1603_ = crate::leanh::lean_ctor_get(v___y_1599_, 1);
    v_options_1604_ = crate::leanh::lean_ctor_get(v___y_1599_, 2);
    v_currRecDepth_1605_ = crate::leanh::lean_ctor_get(v___y_1599_, 3);
    v_maxRecDepth_1606_ = crate::leanh::lean_ctor_get(v___y_1599_, 4);
    v_ref_1607_ = crate::leanh::lean_ctor_get(v___y_1599_, 5);
    v_currNamespace_1608_ = crate::leanh::lean_ctor_get(v___y_1599_, 6);
    v_openDecls_1609_ = crate::leanh::lean_ctor_get(v___y_1599_, 7);
    v_initHeartbeats_1610_ = crate::leanh::lean_ctor_get(v___y_1599_, 8);
    v_maxHeartbeats_1611_ = crate::leanh::lean_ctor_get(v___y_1599_, 9);
    v_quotContext_1612_ = crate::leanh::lean_ctor_get(v___y_1599_, 10);
    v_currMacroScope_1613_ = crate::leanh::lean_ctor_get(v___y_1599_, 11);
    v_diag_1614_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1599_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1615_ = crate::leanh::lean_ctor_get(v___y_1599_, 12);
    v_suppressElabErrors_1616_ = crate::leanh::lean_ctor_get_uint8(
        v___y_1599_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1617_ = crate::leanh::lean_ctor_get(v___y_1599_, 13);
    v_ref_1618_ = l_Lean_replaceRef(v_ref_1597_, v_ref_1607_);
    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_1617_);
    crate::leanh::lean_inc(v_cancelTk_x3f_1615_);
    crate::leanh::lean_inc(v_currMacroScope_1613_);
    crate::leanh::lean_inc(v_quotContext_1612_);
    crate::leanh::lean_inc(v_maxHeartbeats_1611_);
    crate::leanh::lean_inc(v_initHeartbeats_1610_);
    crate::leanh::lean_inc(v_openDecls_1609_);
    crate::leanh::lean_inc(v_currNamespace_1608_);
    crate::leanh::lean_inc(v_maxRecDepth_1606_);
    crate::leanh::lean_inc(v_currRecDepth_1605_);
    crate::leanh::lean_inc_ref(v_options_1604_);
    crate::leanh::lean_inc_ref(v_fileMap_1603_);
    crate::leanh::lean_inc_ref(v_fileName_1602_);
    v___x_1619_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
    crate::leanh::lean_ctor_set(v___x_1619_, 0, v_fileName_1602_);
    crate::leanh::lean_ctor_set(v___x_1619_, 1, v_fileMap_1603_);
    crate::leanh::lean_ctor_set(v___x_1619_, 2, v_options_1604_);
    crate::leanh::lean_ctor_set(v___x_1619_, 3, v_currRecDepth_1605_);
    crate::leanh::lean_ctor_set(v___x_1619_, 4, v_maxRecDepth_1606_);
    crate::leanh::lean_ctor_set(v___x_1619_, 5, v_ref_1618_);
    crate::leanh::lean_ctor_set(v___x_1619_, 6, v_currNamespace_1608_);
    crate::leanh::lean_ctor_set(v___x_1619_, 7, v_openDecls_1609_);
    crate::leanh::lean_ctor_set(v___x_1619_, 8, v_initHeartbeats_1610_);
    crate::leanh::lean_ctor_set(v___x_1619_, 9, v_maxHeartbeats_1611_);
    crate::leanh::lean_ctor_set(v___x_1619_, 10, v_quotContext_1612_);
    crate::leanh::lean_ctor_set(v___x_1619_, 11, v_currMacroScope_1613_);
    crate::leanh::lean_ctor_set(v___x_1619_, 12, v_cancelTk_x3f_1615_);
    crate::leanh::lean_ctor_set(v___x_1619_, 13, v_inheritedTraceOptions_1617_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1619_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
        v_diag_1614_,
    );
    crate::leanh::lean_ctor_set_uint8(
        v___x_1619_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1616_,
    );
    v___x_1620_ = l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(
        v_msg_1598_,
        v___x_1619_,
        v___y_1600_,
    );
    crate::leanh::lean_dec_ref_known(v___x_1619_, 14);
    return v___x_1620_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(
    mut v_ref_1621_: *mut crate::leanh::LeanObject,
    mut v_msg_1622_: *mut crate::leanh::LeanObject,
    mut v___y_1623_: *mut crate::leanh::LeanObject,
    mut v___y_1624_: *mut crate::leanh::LeanObject,
    mut v___y_1625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1626_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1621_, v_msg_1622_, v___y_1623_, v___y_1624_);
    crate::leanh::lean_dec(v___y_1624_);
    crate::leanh::lean_dec_ref(v___y_1623_);
    crate::leanh::lean_dec(v_ref_1621_);
    return v_res_1626_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_ref_1627_: *mut crate::leanh::LeanObject,
    mut v_msg_1628_: *mut crate::leanh::LeanObject,
    mut v_declHint_1629_: *mut crate::leanh::LeanObject,
    mut v___y_1630_: *mut crate::leanh::LeanObject,
    mut v___y_1631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1633_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1628_, v_declHint_1629_, v___y_1630_, v___y_1631_);
    v_a_1634_ = crate::leanh::lean_ctor_get(v___x_1633_, 0);
    crate::leanh::lean_inc(v_a_1634_);
    crate::leanh::lean_dec_ref(v___x_1633_);
    v___x_1635_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1627_, v_a_1634_, v___y_1630_, v___y_1631_);
    return v___x_1635_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_ref_1636_: *mut crate::leanh::LeanObject,
    mut v_msg_1637_: *mut crate::leanh::LeanObject,
    mut v_declHint_1638_: *mut crate::leanh::LeanObject,
    mut v___y_1639_: *mut crate::leanh::LeanObject,
    mut v___y_1640_: *mut crate::leanh::LeanObject,
    mut v___y_1641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1642_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1636_, v_msg_1637_, v_declHint_1638_, v___y_1639_, v___y_1640_);
    crate::leanh::lean_dec(v___y_1640_);
    crate::leanh::lean_dec_ref(v___y_1639_);
    crate::leanh::lean_dec(v_ref_1636_);
    return v_res_1642_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1644_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_1645_ = l_Lean_stringToMessageData(v___x_1644_);
    return v___x_1645_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1647_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_1648_ = l_Lean_stringToMessageData(v___x_1647_);
    return v___x_1648_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg(
    mut v_ref_1649_: *mut crate::leanh::LeanObject,
    mut v_constName_1650_: *mut crate::leanh::LeanObject,
    mut v___y_1651_: *mut crate::leanh::LeanObject,
    mut v___y_1652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: u8 = 0;
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1654_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_1655_ = 0;
    crate::leanh::lean_inc(v_constName_1650_);
    v___x_1656_ = l_Lean_MessageData_ofConstName(v_constName_1650_, v___x_1655_);
    v___x_1657_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1657_, 0, v___x_1654_);
    crate::leanh::lean_ctor_set(v___x_1657_, 1, v___x_1656_);
    v___x_1658_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_1659_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1659_, 0, v___x_1657_);
    crate::leanh::lean_ctor_set(v___x_1659_, 1, v___x_1658_);
    v___x_1660_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1649_, v___x_1659_, v_constName_1650_, v___y_1651_, v___y_1652_);
    return v___x_1660_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_1661_: *mut crate::leanh::LeanObject,
    mut v_constName_1662_: *mut crate::leanh::LeanObject,
    mut v___y_1663_: *mut crate::leanh::LeanObject,
    mut v___y_1664_: *mut crate::leanh::LeanObject,
    mut v___y_1665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1666_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg(v_ref_1661_, v_constName_1662_, v___y_1663_, v___y_1664_);
    crate::leanh::lean_dec(v___y_1664_);
    crate::leanh::lean_dec_ref(v___y_1663_);
    crate::leanh::lean_dec(v_ref_1661_);
    return v_res_1666_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg(
    mut v_constName_1667_: *mut crate::leanh::LeanObject,
    mut v___y_1668_: *mut crate::leanh::LeanObject,
    mut v___y_1669_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ref_1671_ = crate::leanh::lean_ctor_get(v___y_1668_, 5);
    v___x_1672_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg(v_ref_1671_, v_constName_1667_, v___y_1668_, v___y_1669_);
    return v___x_1672_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg___boxed(
    mut v_constName_1673_: *mut crate::leanh::LeanObject,
    mut v___y_1674_: *mut crate::leanh::LeanObject,
    mut v___y_1675_: *mut crate::leanh::LeanObject,
    mut v___y_1676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1677_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg(v_constName_1673_, v___y_1674_, v___y_1675_);
    crate::leanh::lean_dec(v___y_1675_);
    crate::leanh::lean_dec_ref(v___y_1674_);
    return v_res_1677_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0(
    mut v_constName_1678_: *mut crate::leanh::LeanObject,
    mut v___y_1679_: *mut crate::leanh::LeanObject,
    mut v___y_1680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: u8 = 0;
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1690_: u8 = 0;
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1682_ = lean_st_ref_get(v___y_1680_);
                v_env_1683_ = crate::leanh::lean_ctor_get(v___x_1682_, 0);
                crate::leanh::lean_inc_ref(v_env_1683_);
                crate::leanh::lean_dec(v___x_1682_);
                v___x_1684_ = 0;
                crate::leanh::lean_inc(v_constName_1678_);
                v___x_1685_ =
                    l_Lean_Environment_find_x3f(v_env_1683_, v_constName_1678_, v___x_1684_);
                if crate::leanh::lean_obj_tag(v___x_1685_) == 0 {
                    v___x_1686_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg(v_constName_1678_, v___y_1679_, v___y_1680_);
                    return v___x_1686_;
                } else {
                    crate::leanh::lean_dec(v_constName_1678_);
                    v_val_1687_ = crate::leanh::lean_ctor_get(v___x_1685_, 0);
                    v_isSharedCheck_1694_ = (!crate::leanh::lean_is_exclusive(v___x_1685_)) as u8;
                    if v_isSharedCheck_1694_ == 0 {
                        v___x_1689_ = v___x_1685_;
                        v_isShared_1690_ = v_isSharedCheck_1694_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1687_);
                        crate::leanh::lean_dec(v___x_1685_);
                        v___x_1689_ = crate::leanh::lean_box(0);
                        v_isShared_1690_ = v_isSharedCheck_1694_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1690_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1689_, 0);
                    v___x_1692_ = v___x_1689_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1693_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_val_1687_);
                    v___x_1692_ = v_reuseFailAlloc_1693_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1692_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0___boxed(
    mut v_constName_1695_: *mut crate::leanh::LeanObject,
    mut v___y_1696_: *mut crate::leanh::LeanObject,
    mut v___y_1697_: *mut crate::leanh::LeanObject,
    mut v___y_1698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1699_ = l_Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0(
        v_constName_1695_,
        v___y_1696_,
        v___y_1697_,
    );
    crate::leanh::lean_dec(v___y_1697_);
    crate::leanh::lean_dec_ref(v___y_1696_);
    return v_res_1699_;
}
pub unsafe fn _init_l_Lean_Elab_checkCbvSimprocType___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1701_ = l_Lean_Elab_checkCbvSimprocType___closed__0;
    v___x_1702_ = l_Lean_stringToMessageData(v___x_1701_);
    return v___x_1702_;
}
pub unsafe fn _init_l_Lean_Elab_checkCbvSimprocType___closed__8() -> *mut crate::leanh::LeanObject {
    let mut v___x_1714_: u8 = 0;
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1714_ = 0;
    v___x_1715_ = l_Lean_Elab_checkCbvSimprocType___closed__7;
    v___x_1716_ = l_Lean_MessageData_ofConstName(v___x_1715_, v___x_1714_);
    return v___x_1716_;
}
pub unsafe fn _init_l_Lean_Elab_checkCbvSimprocType___closed__9() -> *mut crate::leanh::LeanObject {
    let mut v___x_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1717_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__8_once),
        _init_l_Lean_Elab_checkCbvSimprocType___closed__8,
    );
    v___x_1718_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__1_once),
        _init_l_Lean_Elab_checkCbvSimprocType___closed__1,
    );
    v___x_1719_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1719_, 0, v___x_1718_);
    crate::leanh::lean_ctor_set(v___x_1719_, 1, v___x_1717_);
    return v___x_1719_;
}
pub unsafe fn _init_l_Lean_Elab_checkCbvSimprocType___closed__11() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1721_ = l_Lean_Elab_checkCbvSimprocType___closed__10;
    v___x_1722_ = l_Lean_stringToMessageData(v___x_1721_);
    return v___x_1722_;
}
pub unsafe fn _init_l_Lean_Elab_checkCbvSimprocType___closed__12() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1723_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__11_once),
        _init_l_Lean_Elab_checkCbvSimprocType___closed__11,
    );
    v___x_1724_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__9_once),
        _init_l_Lean_Elab_checkCbvSimprocType___closed__9,
    );
    v___x_1725_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1725_, 0, v___x_1724_);
    crate::leanh::lean_ctor_set(v___x_1725_, 1, v___x_1723_);
    return v___x_1725_;
}
pub unsafe fn _init_l_Lean_Elab_checkCbvSimprocType___closed__14() -> *mut crate::leanh::LeanObject
{
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1727_ = l_Lean_Elab_checkCbvSimprocType___closed__13;
    v___x_1728_ = l_Lean_stringToMessageData(v___x_1727_);
    return v___x_1728_;
}
pub unsafe fn l_Lean_Elab_checkCbvSimprocType(
    mut v_declName_1729_: *mut crate::leanh::LeanObject,
    mut v_a_1730_: *mut crate::leanh::LeanObject,
    mut v_a_1731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1737_: u8 = 0;
    let mut v___y_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: u8 = 0;
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: u8 = 0;
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: u8 = 0;
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: u8 = 0;
    let mut v___x_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1776_: u8 = 0;
    let mut v_a_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1780_: u8 = 0;
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1784_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_declName_1729_);
                v___x_1733_ = l_Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0(
                    v_declName_1729_,
                    v_a_1730_,
                    v_a_1731_,
                );
                if crate::leanh::lean_obj_tag(v___x_1733_) == 0 {
                    v_a_1734_ = crate::leanh::lean_ctor_get(v___x_1733_, 0);
                    v_isSharedCheck_1776_ = (!crate::leanh::lean_is_exclusive(v___x_1733_)) as u8;
                    if v_isSharedCheck_1776_ == 0 {
                        v___x_1736_ = v___x_1733_;
                        v_isShared_1737_ = v_isSharedCheck_1776_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1734_);
                        crate::leanh::lean_dec(v___x_1733_);
                        v___x_1736_ = crate::leanh::lean_box(0);
                        v_isShared_1737_ = v_isSharedCheck_1776_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_declName_1729_);
                    v_a_1777_ = crate::leanh::lean_ctor_get(v___x_1733_, 0);
                    v_isSharedCheck_1784_ = (!crate::leanh::lean_is_exclusive(v___x_1733_)) as u8;
                    if v_isSharedCheck_1784_ == 0 {
                        v___x_1779_ = v___x_1733_;
                        v_isShared_1780_ = v_isSharedCheck_1784_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1777_);
                        crate::leanh::lean_dec(v___x_1733_);
                        v___x_1779_ = crate::leanh::lean_box(0);
                        v_isShared_1780_ = v_isSharedCheck_1784_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1750_ = l_Lean_ConstantInfo_type(v_a_1734_);
                if crate::leanh::lean_obj_tag(v___x_1750_) == 4 {
                    v_declName_1751_ = crate::leanh::lean_ctor_get(v___x_1750_, 0);
                    crate::leanh::lean_inc(v_declName_1751_);
                    crate::leanh::lean_dec_ref_known(v___x_1750_, 2);
                    if crate::leanh::lean_obj_tag(v_declName_1751_) == 1 {
                        v_pre_1752_ = crate::leanh::lean_ctor_get(v_declName_1751_, 0);
                        crate::leanh::lean_inc(v_pre_1752_);
                        if crate::leanh::lean_obj_tag(v_pre_1752_) == 1 {
                            v_pre_1753_ = crate::leanh::lean_ctor_get(v_pre_1752_, 0);
                            crate::leanh::lean_inc(v_pre_1753_);
                            if crate::leanh::lean_obj_tag(v_pre_1753_) == 1 {
                                v_pre_1754_ = crate::leanh::lean_ctor_get(v_pre_1753_, 0);
                                crate::leanh::lean_inc(v_pre_1754_);
                                if crate::leanh::lean_obj_tag(v_pre_1754_) == 1 {
                                    v_pre_1755_ = crate::leanh::lean_ctor_get(v_pre_1754_, 0);
                                    crate::leanh::lean_inc(v_pre_1755_);
                                    if crate::leanh::lean_obj_tag(v_pre_1755_) == 1 {
                                        v_pre_1756_ = crate::leanh::lean_ctor_get(v_pre_1755_, 0);
                                        if crate::leanh::lean_obj_tag(v_pre_1756_) == 0 {
                                            v_str_1757_ =
                                                crate::leanh::lean_ctor_get(v_declName_1751_, 1);
                                            crate::leanh::lean_inc_ref(v_str_1757_);
                                            crate::leanh::lean_dec_ref_known(v_declName_1751_, 2);
                                            v_str_1758_ =
                                                crate::leanh::lean_ctor_get(v_pre_1752_, 1);
                                            crate::leanh::lean_inc_ref(v_str_1758_);
                                            crate::leanh::lean_dec_ref_known(v_pre_1752_, 2);
                                            v_str_1759_ =
                                                crate::leanh::lean_ctor_get(v_pre_1753_, 1);
                                            crate::leanh::lean_inc_ref(v_str_1759_);
                                            crate::leanh::lean_dec_ref_known(v_pre_1753_, 2);
                                            v_str_1760_ =
                                                crate::leanh::lean_ctor_get(v_pre_1754_, 1);
                                            crate::leanh::lean_inc_ref(v_str_1760_);
                                            crate::leanh::lean_dec_ref_known(v_pre_1754_, 2);
                                            v_str_1761_ =
                                                crate::leanh::lean_ctor_get(v_pre_1755_, 1);
                                            crate::leanh::lean_inc_ref(v_str_1761_);
                                            crate::leanh::lean_dec_ref_known(v_pre_1755_, 2);
                                            v___x_1762_ =
                                                l_Lean_Elab_checkCbvSimprocType___closed__2;
                                            v___x_1763_ =
                                                lean_string_dec_eq(v_str_1761_, v___x_1762_);
                                            crate::leanh::lean_dec_ref(v_str_1761_);
                                            if v___x_1763_ == 0 {
                                                crate::leanh::lean_dec_ref(v_str_1760_);
                                                crate::leanh::lean_dec_ref(v_str_1759_);
                                                crate::leanh::lean_dec_ref(v_str_1758_);
                                                crate::leanh::lean_dec_ref(v_str_1757_);
                                                crate::leanh::lean_del_object(v___x_1736_);
                                                v___y_1739_ = v_a_1730_;
                                                v___y_1740_ = v_a_1731_;
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_1764_ =
                                                    l_Lean_Elab_checkCbvSimprocType___closed__3;
                                                v___x_1765_ =
                                                    lean_string_dec_eq(v_str_1760_, v___x_1764_);
                                                crate::leanh::lean_dec_ref(v_str_1760_);
                                                if v___x_1765_ == 0 {
                                                    crate::leanh::lean_dec_ref(v_str_1759_);
                                                    crate::leanh::lean_dec_ref(v_str_1758_);
                                                    crate::leanh::lean_dec_ref(v_str_1757_);
                                                    crate::leanh::lean_del_object(v___x_1736_);
                                                    v___y_1739_ = v_a_1730_;
                                                    v___y_1740_ = v_a_1731_;
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    v___x_1766_ =
                                                        l_Lean_Elab_checkCbvSimprocType___closed__4;
                                                    v___x_1767_ = lean_string_dec_eq(
                                                        v_str_1759_,
                                                        v___x_1766_,
                                                    );
                                                    crate::leanh::lean_dec_ref(v_str_1759_);
                                                    if v___x_1767_ == 0 {
                                                        crate::leanh::lean_dec_ref(v_str_1758_);
                                                        crate::leanh::lean_dec_ref(v_str_1757_);
                                                        crate::leanh::lean_del_object(v___x_1736_);
                                                        v___y_1739_ = v_a_1730_;
                                                        v___y_1740_ = v_a_1731_;
                                                        state = 2;
                                                        continue;
                                                    } else {
                                                        v___x_1768_ = l_Lean_Elab_checkCbvSimprocType___closed__5;
                                                        v___x_1769_ = lean_string_dec_eq(
                                                            v_str_1758_,
                                                            v___x_1768_,
                                                        );
                                                        crate::leanh::lean_dec_ref(v_str_1758_);
                                                        if v___x_1769_ == 0 {
                                                            crate::leanh::lean_dec_ref(v_str_1757_);
                                                            crate::leanh::lean_del_object(
                                                                v___x_1736_,
                                                            );
                                                            v___y_1739_ = v_a_1730_;
                                                            v___y_1740_ = v_a_1731_;
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            v___x_1770_ = l_Lean_Elab_checkCbvSimprocType___closed__6;
                                                            v___x_1771_ = lean_string_dec_eq(
                                                                v_str_1757_,
                                                                v___x_1770_,
                                                            );
                                                            crate::leanh::lean_dec_ref(v_str_1757_);
                                                            if v___x_1771_ == 0 {
                                                                crate::leanh::lean_del_object(
                                                                    v___x_1736_,
                                                                );
                                                                v___y_1739_ = v_a_1730_;
                                                                v___y_1740_ = v_a_1731_;
                                                                state = 2;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_dec(v_a_1734_);
                                                                crate::leanh::lean_dec(
                                                                    v_declName_1729_,
                                                                );
                                                                v___x_1772_ =
                                                                    crate::leanh::lean_box(0);
                                                                if v_isShared_1737_ == 0 {
                                                                    crate::leanh::lean_ctor_set(
                                                                        v___x_1736_,
                                                                        0,
                                                                        v___x_1772_,
                                                                    );
                                                                    v___x_1774_ = v___x_1736_;
                                                                    state = 3;
                                                                    continue;
                                                                } else {
                                                                    v_reuseFailAlloc_1775_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                    crate::leanh::lean_ctor_set(
                                                                        v_reuseFailAlloc_1775_,
                                                                        0,
                                                                        v___x_1772_,
                                                                    );
                                                                    v___x_1774_ =
                                                                        v_reuseFailAlloc_1775_;
                                                                    state = 3;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref_known(v_pre_1755_, 2);
                                            crate::leanh::lean_dec_ref_known(v_pre_1754_, 2);
                                            crate::leanh::lean_dec_ref_known(v_pre_1753_, 2);
                                            crate::leanh::lean_dec_ref_known(v_pre_1752_, 2);
                                            crate::leanh::lean_dec_ref_known(v_declName_1751_, 2);
                                            crate::leanh::lean_del_object(v___x_1736_);
                                            v___y_1739_ = v_a_1730_;
                                            v___y_1740_ = v_a_1731_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v_pre_1754_, 2);
                                        crate::leanh::lean_dec(v_pre_1755_);
                                        crate::leanh::lean_dec_ref_known(v_pre_1753_, 2);
                                        crate::leanh::lean_dec_ref_known(v_pre_1752_, 2);
                                        crate::leanh::lean_dec_ref_known(v_declName_1751_, 2);
                                        crate::leanh::lean_del_object(v___x_1736_);
                                        v___y_1739_ = v_a_1730_;
                                        v___y_1740_ = v_a_1731_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_pre_1754_);
                                    crate::leanh::lean_dec_ref_known(v_pre_1753_, 2);
                                    crate::leanh::lean_dec_ref_known(v_pre_1752_, 2);
                                    crate::leanh::lean_dec_ref_known(v_declName_1751_, 2);
                                    crate::leanh::lean_del_object(v___x_1736_);
                                    v___y_1739_ = v_a_1730_;
                                    v___y_1740_ = v_a_1731_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_pre_1752_, 2);
                                crate::leanh::lean_dec(v_pre_1753_);
                                crate::leanh::lean_dec_ref_known(v_declName_1751_, 2);
                                crate::leanh::lean_del_object(v___x_1736_);
                                v___y_1739_ = v_a_1730_;
                                v___y_1740_ = v_a_1731_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_declName_1751_, 2);
                            crate::leanh::lean_dec(v_pre_1752_);
                            crate::leanh::lean_del_object(v___x_1736_);
                            v___y_1739_ = v_a_1730_;
                            v___y_1740_ = v_a_1731_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_1751_);
                        crate::leanh::lean_del_object(v___x_1736_);
                        v___y_1739_ = v_a_1730_;
                        v___y_1740_ = v_a_1731_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1750_);
                    crate::leanh::lean_del_object(v___x_1736_);
                    v___y_1739_ = v_a_1730_;
                    v___y_1740_ = v_a_1731_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1741_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__12),
                    core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__12_once),
                    _init_l_Lean_Elab_checkCbvSimprocType___closed__12,
                );
                v___x_1742_ = l_Lean_MessageData_ofName(v_declName_1729_);
                v___x_1743_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1743_, 0, v___x_1741_);
                crate::leanh::lean_ctor_set(v___x_1743_, 1, v___x_1742_);
                v___x_1744_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__14),
                    core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__14_once),
                    _init_l_Lean_Elab_checkCbvSimprocType___closed__14,
                );
                v___x_1745_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1745_, 0, v___x_1743_);
                crate::leanh::lean_ctor_set(v___x_1745_, 1, v___x_1744_);
                v___x_1746_ = l_Lean_ConstantInfo_type(v_a_1734_);
                crate::leanh::lean_dec(v_a_1734_);
                v___x_1747_ = l_Lean_indentExpr(v___x_1746_);
                v___x_1748_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1748_, 0, v___x_1745_);
                crate::leanh::lean_ctor_set(v___x_1748_, 1, v___x_1747_);
                v___x_1749_ =
                    l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(
                        v___x_1748_,
                        v___y_1739_,
                        v___y_1740_,
                    );
                return v___x_1749_;
            }
            3 => {
                return v___x_1774_;
            }
            4 => {
                if v_isShared_1780_ == 0 {
                    v___x_1782_ = v___x_1779_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1783_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
                    v___x_1782_ = v_reuseFailAlloc_1783_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1782_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_checkCbvSimprocType___boxed(
    mut v_declName_1785_: *mut crate::leanh::LeanObject,
    mut v_a_1786_: *mut crate::leanh::LeanObject,
    mut v_a_1787_: *mut crate::leanh::LeanObject,
    mut v_a_1788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1789_ = l_Lean_Elab_checkCbvSimprocType(v_declName_1785_, v_a_1786_, v_a_1787_);
    crate::leanh::lean_dec(v_a_1787_);
    crate::leanh::lean_dec_ref(v_a_1786_);
    return v_res_1789_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1(
    mut v_00_u03b1_1790_: *mut crate::leanh::LeanObject,
    mut v_msg_1791_: *mut crate::leanh::LeanObject,
    mut v___y_1792_: *mut crate::leanh::LeanObject,
    mut v___y_1793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1795_ = l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(
        v_msg_1791_,
        v___y_1792_,
        v___y_1793_,
    );
    return v___x_1795_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___boxed(
    mut v_00_u03b1_1796_: *mut crate::leanh::LeanObject,
    mut v_msg_1797_: *mut crate::leanh::LeanObject,
    mut v___y_1798_: *mut crate::leanh::LeanObject,
    mut v___y_1799_: *mut crate::leanh::LeanObject,
    mut v___y_1800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1801_ = l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1(
        v_00_u03b1_1796_,
        v_msg_1797_,
        v___y_1798_,
        v___y_1799_,
    );
    crate::leanh::lean_dec(v___y_1799_);
    crate::leanh::lean_dec_ref(v___y_1798_);
    return v_res_1801_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0(
    mut v_00_u03b1_1802_: *mut crate::leanh::LeanObject,
    mut v_constName_1803_: *mut crate::leanh::LeanObject,
    mut v___y_1804_: *mut crate::leanh::LeanObject,
    mut v___y_1805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1807_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg(v_constName_1803_, v___y_1804_, v___y_1805_);
    return v___x_1807_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___boxed(
    mut v_00_u03b1_1808_: *mut crate::leanh::LeanObject,
    mut v_constName_1809_: *mut crate::leanh::LeanObject,
    mut v___y_1810_: *mut crate::leanh::LeanObject,
    mut v___y_1811_: *mut crate::leanh::LeanObject,
    mut v___y_1812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1813_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0(v_00_u03b1_1808_, v_constName_1809_, v___y_1810_, v___y_1811_);
    crate::leanh::lean_dec(v___y_1811_);
    crate::leanh::lean_dec_ref(v___y_1810_);
    return v_res_1813_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1(
    mut v_00_u03b1_1814_: *mut crate::leanh::LeanObject,
    mut v_ref_1815_: *mut crate::leanh::LeanObject,
    mut v_constName_1816_: *mut crate::leanh::LeanObject,
    mut v___y_1817_: *mut crate::leanh::LeanObject,
    mut v___y_1818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1820_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg(v_ref_1815_, v_constName_1816_, v___y_1817_, v___y_1818_);
    return v___x_1820_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_1821_: *mut crate::leanh::LeanObject,
    mut v_ref_1822_: *mut crate::leanh::LeanObject,
    mut v_constName_1823_: *mut crate::leanh::LeanObject,
    mut v___y_1824_: *mut crate::leanh::LeanObject,
    mut v___y_1825_: *mut crate::leanh::LeanObject,
    mut v___y_1826_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1827_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1(v_00_u03b1_1821_, v_ref_1822_, v_constName_1823_, v___y_1824_, v___y_1825_);
    crate::leanh::lean_dec(v___y_1825_);
    crate::leanh::lean_dec_ref(v___y_1824_);
    crate::leanh::lean_dec(v_ref_1822_);
    return v_res_1827_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_1828_: *mut crate::leanh::LeanObject,
    mut v_ref_1829_: *mut crate::leanh::LeanObject,
    mut v_msg_1830_: *mut crate::leanh::LeanObject,
    mut v_declHint_1831_: *mut crate::leanh::LeanObject,
    mut v___y_1832_: *mut crate::leanh::LeanObject,
    mut v___y_1833_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1835_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1829_, v_msg_1830_, v_declHint_1831_, v___y_1832_, v___y_1833_);
    return v___x_1835_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b1_1836_: *mut crate::leanh::LeanObject,
    mut v_ref_1837_: *mut crate::leanh::LeanObject,
    mut v_msg_1838_: *mut crate::leanh::LeanObject,
    mut v_declHint_1839_: *mut crate::leanh::LeanObject,
    mut v___y_1840_: *mut crate::leanh::LeanObject,
    mut v___y_1841_: *mut crate::leanh::LeanObject,
    mut v___y_1842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1843_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1836_, v_ref_1837_, v_msg_1838_, v_declHint_1839_, v___y_1840_, v___y_1841_);
    crate::leanh::lean_dec(v___y_1841_);
    crate::leanh::lean_dec_ref(v___y_1840_);
    crate::leanh::lean_dec(v_ref_1837_);
    return v_res_1843_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(
    mut v_msg_1844_: *mut crate::leanh::LeanObject,
    mut v_declHint_1845_: *mut crate::leanh::LeanObject,
    mut v___y_1846_: *mut crate::leanh::LeanObject,
    mut v___y_1847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1849_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1844_, v_declHint_1845_, v___y_1847_);
    return v___x_1849_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(
    mut v_msg_1850_: *mut crate::leanh::LeanObject,
    mut v_declHint_1851_: *mut crate::leanh::LeanObject,
    mut v___y_1852_: *mut crate::leanh::LeanObject,
    mut v___y_1853_: *mut crate::leanh::LeanObject,
    mut v___y_1854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1855_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1850_, v_declHint_1851_, v___y_1852_, v___y_1853_);
    crate::leanh::lean_dec(v___y_1853_);
    crate::leanh::lean_dec_ref(v___y_1852_);
    return v_res_1855_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6(
    mut v_00_u03b1_1856_: *mut crate::leanh::LeanObject,
    mut v_ref_1857_: *mut crate::leanh::LeanObject,
    mut v_msg_1858_: *mut crate::leanh::LeanObject,
    mut v___y_1859_: *mut crate::leanh::LeanObject,
    mut v___y_1860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1862_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1857_, v_msg_1858_, v___y_1859_, v___y_1860_);
    return v___x_1862_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(
    mut v_00_u03b1_1863_: *mut crate::leanh::LeanObject,
    mut v_ref_1864_: *mut crate::leanh::LeanObject,
    mut v_msg_1865_: *mut crate::leanh::LeanObject,
    mut v___y_1866_: *mut crate::leanh::LeanObject,
    mut v___y_1867_: *mut crate::leanh::LeanObject,
    mut v___y_1868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1869_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_1863_, v_ref_1864_, v_msg_1865_, v___y_1866_, v___y_1867_);
    crate::leanh::lean_dec(v___y_1867_);
    crate::leanh::lean_dec_ref(v___y_1866_);
    crate::leanh::lean_dec(v_ref_1864_);
    return v_res_1869_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1870_ = crate::leanh::lean_box(0);
    v___x_1871_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1872_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1872_, 0, v___x_1871_);
    crate::leanh::lean_ctor_set(v___x_1872_, 1, v___x_1870_);
    return v___x_1872_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1874_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0);
    v___x_1875_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1875_, 0, v___x_1874_);
    return v___x_1875_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___boxed(
    mut v___y_1876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1877_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg();
    return v_res_1877_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0(
    mut v_00_u03b1_1878_: *mut crate::leanh::LeanObject,
    mut v___y_1879_: *mut crate::leanh::LeanObject,
    mut v___y_1880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1882_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg();
    return v___x_1882_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___boxed(
    mut v_00_u03b1_1883_: *mut crate::leanh::LeanObject,
    mut v___y_1884_: *mut crate::leanh::LeanObject,
    mut v___y_1885_: *mut crate::leanh::LeanObject,
    mut v___y_1886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1887_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0(
            v_00_u03b1_1883_,
            v___y_1884_,
            v___y_1885_,
        );
    crate::leanh::lean_dec(v___y_1885_);
    crate::leanh::lean_dec_ref(v___y_1884_);
    return v_res_1887_;
}
pub unsafe fn l_Lean_Elab_Command_elabCbvSimprocPattern___lam__0(
    mut v___x_1888_: *mut crate::leanh::LeanObject,
    mut v___x_1889_: *mut crate::leanh::LeanObject,
    mut v___y_1890_: *mut crate::leanh::LeanObject,
    mut v___y_1891_: *mut crate::leanh::LeanObject,
    mut v___y_1892_: *mut crate::leanh::LeanObject,
    mut v___y_1893_: *mut crate::leanh::LeanObject,
    mut v___y_1894_: *mut crate::leanh::LeanObject,
    mut v___y_1895_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1906_: u8 = 0;
    let mut v___x_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1910_: u8 = 0;
    let mut v_a_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1914_: u8 = 0;
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1918_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1897_ =
                    l_Lean_realizeGlobalConstNoOverload(v___x_1888_, v___y_1894_, v___y_1895_);
                if crate::leanh::lean_obj_tag(v___x_1897_) == 0 {
                    v_a_1898_ = crate::leanh::lean_ctor_get(v___x_1897_, 0);
                    crate::leanh::lean_inc_n(v_a_1898_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1897_, 1);
                    v___x_1899_ =
                        l_Lean_Elab_checkCbvSimprocType(v_a_1898_, v___y_1894_, v___y_1895_);
                    if crate::leanh::lean_obj_tag(v___x_1899_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_1899_, 1);
                        v___x_1900_ = l_Lean_Elab_elabCbvSimprocKeys(
                            v___x_1889_,
                            v___y_1892_,
                            v___y_1893_,
                            v___y_1894_,
                            v___y_1895_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1900_) == 0 {
                            v_a_1901_ = crate::leanh::lean_ctor_get(v___x_1900_, 0);
                            crate::leanh::lean_inc(v_a_1901_);
                            crate::leanh::lean_dec_ref_known(v___x_1900_, 1);
                            v___x_1902_ = l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(
                                v_a_1898_,
                                v_a_1901_,
                                v___y_1894_,
                                v___y_1895_,
                            );
                            return v___x_1902_;
                        } else {
                            crate::leanh::lean_dec(v_a_1898_);
                            v_a_1903_ = crate::leanh::lean_ctor_get(v___x_1900_, 0);
                            v_isSharedCheck_1910_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1900_)) as u8;
                            if v_isSharedCheck_1910_ == 0 {
                                v___x_1905_ = v___x_1900_;
                                v_isShared_1906_ = v_isSharedCheck_1910_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1903_);
                                crate::leanh::lean_dec(v___x_1900_);
                                v___x_1905_ = crate::leanh::lean_box(0);
                                v_isShared_1906_ = v_isSharedCheck_1910_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1898_);
                        crate::leanh::lean_dec(v___x_1889_);
                        return v___x_1899_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1889_);
                    v_a_1911_ = crate::leanh::lean_ctor_get(v___x_1897_, 0);
                    v_isSharedCheck_1918_ = (!crate::leanh::lean_is_exclusive(v___x_1897_)) as u8;
                    if v_isSharedCheck_1918_ == 0 {
                        v___x_1913_ = v___x_1897_;
                        v_isShared_1914_ = v_isSharedCheck_1918_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1911_);
                        crate::leanh::lean_dec(v___x_1897_);
                        v___x_1913_ = crate::leanh::lean_box(0);
                        v_isShared_1914_ = v_isSharedCheck_1918_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1906_ == 0 {
                    v___x_1908_ = v___x_1905_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1909_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
                    v___x_1908_ = v_reuseFailAlloc_1909_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1908_;
            }
            3 => {
                if v_isShared_1914_ == 0 {
                    v___x_1916_ = v___x_1913_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1917_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
                    v___x_1916_ = v_reuseFailAlloc_1917_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1916_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabCbvSimprocPattern___lam__0___boxed(
    mut v___x_1919_: *mut crate::leanh::LeanObject,
    mut v___x_1920_: *mut crate::leanh::LeanObject,
    mut v___y_1921_: *mut crate::leanh::LeanObject,
    mut v___y_1922_: *mut crate::leanh::LeanObject,
    mut v___y_1923_: *mut crate::leanh::LeanObject,
    mut v___y_1924_: *mut crate::leanh::LeanObject,
    mut v___y_1925_: *mut crate::leanh::LeanObject,
    mut v___y_1926_: *mut crate::leanh::LeanObject,
    mut v___y_1927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1928_ = l_Lean_Elab_Command_elabCbvSimprocPattern___lam__0(
        v___x_1919_,
        v___x_1920_,
        v___y_1921_,
        v___y_1922_,
        v___y_1923_,
        v___y_1924_,
        v___y_1925_,
        v___y_1926_,
    );
    crate::leanh::lean_dec(v___y_1926_);
    crate::leanh::lean_dec_ref(v___y_1925_);
    crate::leanh::lean_dec(v___y_1924_);
    crate::leanh::lean_dec_ref(v___y_1923_);
    crate::leanh::lean_dec(v___y_1922_);
    crate::leanh::lean_dec_ref(v___y_1921_);
    return v_res_1928_;
}
pub unsafe fn l_Lean_Elab_Command_elabCbvSimprocPattern(
    mut v_stx_1935_: *mut crate::leanh::LeanObject,
    mut v_a_1936_: *mut crate::leanh::LeanObject,
    mut v_a_1937_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: u8 = 0;
    v___x_1939_ = l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2;
    crate::leanh::lean_inc(v_stx_1935_);
    v___x_1940_ = l_Lean_Syntax_isOfKind(v_stx_1935_, v___x_1939_);
    if v___x_1940_ == 0 {
        let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_1935_);
        v___x_1941_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg();
        return v___x_1941_;
    } else {
        let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1942_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1943_ = l_Lean_Syntax_getArg(v_stx_1935_, v___x_1942_);
        v___x_1944_ = crate::leanh::lean_unsigned_to_nat(3);
        v___x_1945_ = l_Lean_Syntax_getArg(v_stx_1935_, v___x_1944_);
        crate::leanh::lean_dec(v_stx_1935_);
        v___f_1946_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_Command_elabCbvSimprocPattern___lam__0___boxed as *mut core::ffi::c_void,
            9,
            2,
        );
        crate::leanh::lean_closure_set(v___f_1946_, 0, v___x_1945_);
        crate::leanh::lean_closure_set(v___f_1946_, 1, v___x_1943_);
        v___x_1947_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_1946_, v_a_1936_, v_a_1937_);
        return v___x_1947_;
    }
}
pub unsafe fn l_Lean_Elab_Command_elabCbvSimprocPattern___boxed(
    mut v_stx_1948_: *mut crate::leanh::LeanObject,
    mut v_a_1949_: *mut crate::leanh::LeanObject,
    mut v_a_1950_: *mut crate::leanh::LeanObject,
    mut v_a_1951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1952_ = l_Lean_Elab_Command_elabCbvSimprocPattern(v_stx_1948_, v_a_1949_, v_a_1950_);
    crate::leanh::lean_dec(v_a_1950_);
    crate::leanh::lean_dec_ref(v_a_1949_);
    return v_res_1952_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1962_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_1963_ = l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2;
    v___x_1964_ = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3;
    v___x_1965_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Command_elabCbvSimprocPattern___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_1966_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1962_,
        v___x_1963_,
        v___x_1964_,
        v___x_1965_,
    );
    return v___x_1966_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___boxed(
    mut v_a_1967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1968_ = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1();
    return v_res_1968_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1978_ = crate::leanh::lean_box(0);
    v___x_1979_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3;
    v___x_1980_ = l_Lean_mkConst(v___x_1979_, v___x_1978_);
    return v___x_1980_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1988_ = crate::leanh::lean_box(0);
    v___x_1989_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6;
    v___x_1990_ = l_Lean_mkConst(v___x_1989_, v___x_1988_);
    return v___x_1990_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1998_ = crate::leanh::lean_box(0);
    v___x_1999_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9;
    v___x_2000_ = l_Lean_mkConst(v___x_1999_, v___x_1998_);
    return v___x_2000_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2007_ = crate::leanh::lean_box(0);
    v___x_2008_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13;
    v___x_2009_ = l_Lean_mkConst(v___x_2008_, v___x_2007_);
    return v___x_2009_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2015_ = crate::leanh::lean_box(0);
    v___x_2016_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16;
    v___x_2017_ = l_Lean_mkConst(v___x_2016_, v___x_2015_);
    return v___x_2017_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2025_ = crate::leanh::lean_box(0);
    v___x_2026_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19;
    v___x_2027_ = l_Lean_mkConst(v___x_2026_, v___x_2025_);
    return v___x_2027_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2034_ = crate::leanh::lean_box(0);
    v___x_2035_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23;
    v___x_2036_ = l_Lean_mkConst(v___x_2035_, v___x_2034_);
    return v___x_2036_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2044_ = crate::leanh::lean_box(0);
    v___x_2045_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26;
    v___x_2046_ = l_Lean_mkConst(v___x_2045_, v___x_2044_);
    return v___x_2046_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2054_ = crate::leanh::lean_box(0);
    v___x_2055_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29;
    v___x_2056_ = l_Lean_mkConst(v___x_2055_, v___x_2054_);
    return v___x_2056_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2064_ = crate::leanh::lean_box(0);
    v___x_2065_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32;
    v___x_2066_ = l_Lean_mkConst(v___x_2065_, v___x_2064_);
    return v___x_2066_;
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0(
    mut v_nilFn_2067_: *mut crate::leanh::LeanObject,
    mut v_consFn_2068_: *mut crate::leanh::LeanObject,
    mut v_x_2069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2069_) == 0 {
                    crate::leanh::lean_dec_ref(v_consFn_2068_);
                    crate::leanh::lean_inc_ref(v_nilFn_2067_);
                    return v_nilFn_2067_;
                } else {
                    v_head_2070_ = crate::leanh::lean_ctor_get(v_x_2069_, 0);
                    crate::leanh::lean_inc(v_head_2070_);
                    v_tail_2071_ = crate::leanh::lean_ctor_get(v_x_2069_, 1);
                    crate::leanh::lean_inc(v_tail_2071_);
                    crate::leanh::lean_dec_ref_known(v_x_2069_, 2);
                    match crate::leanh::lean_obj_tag(v_head_2070_) {
                        0 => {
                            v___x_2076_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4);
                            v___y_2073_ = v___x_2076_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v___x_2077_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7);
                            v___y_2073_ = v___x_2077_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            v_a_2078_ = crate::leanh::lean_ctor_get(v_head_2070_, 0);
                            crate::leanh::lean_inc_ref(v_a_2078_);
                            crate::leanh::lean_dec_ref_known(v_head_2070_, 1);
                            v___x_2079_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10);
                            if crate::leanh::lean_obj_tag(v_a_2078_) == 0 {
                                v___x_2080_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14);
                                v___x_2081_ = l_Lean_Expr_lit___override(v_a_2078_);
                                v___x_2082_ = l_Lean_Expr_app___override(v___x_2080_, v___x_2081_);
                                v___x_2083_ = l_Lean_Expr_app___override(v___x_2079_, v___x_2082_);
                                v___y_2073_ = v___x_2083_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2084_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17);
                                v___x_2085_ = l_Lean_Expr_lit___override(v_a_2078_);
                                v___x_2086_ = l_Lean_Expr_app___override(v___x_2084_, v___x_2085_);
                                v___x_2087_ = l_Lean_Expr_app___override(v___x_2079_, v___x_2086_);
                                v___y_2073_ = v___x_2087_;
                                state = 1;
                                continue;
                            }
                        }
                        3 => {
                            v_a_2088_ = crate::leanh::lean_ctor_get(v_head_2070_, 0);
                            crate::leanh::lean_inc(v_a_2088_);
                            v_a_2089_ = crate::leanh::lean_ctor_get(v_head_2070_, 1);
                            crate::leanh::lean_inc(v_a_2089_);
                            crate::leanh::lean_dec_ref_known(v_head_2070_, 2);
                            v___x_2090_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20);
                            v___x_2091_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24);
                            v___x_2092_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_2088_);
                            v___x_2093_ = l_Lean_Expr_app___override(v___x_2091_, v___x_2092_);
                            v___x_2094_ = l_Lean_mkNatLit(v_a_2089_);
                            v___x_2095_ = l_Lean_mkAppB(v___x_2090_, v___x_2093_, v___x_2094_);
                            v___y_2073_ = v___x_2095_;
                            state = 1;
                            continue;
                        }
                        4 => {
                            v_a_2096_ = crate::leanh::lean_ctor_get(v_head_2070_, 0);
                            crate::leanh::lean_inc(v_a_2096_);
                            v_a_2097_ = crate::leanh::lean_ctor_get(v_head_2070_, 1);
                            crate::leanh::lean_inc(v_a_2097_);
                            crate::leanh::lean_dec_ref_known(v_head_2070_, 2);
                            v___x_2098_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27);
                            v___x_2099_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_2096_);
                            v___x_2100_ = l_Lean_mkNatLit(v_a_2097_);
                            v___x_2101_ = l_Lean_mkAppB(v___x_2098_, v___x_2099_, v___x_2100_);
                            v___y_2073_ = v___x_2101_;
                            state = 1;
                            continue;
                        }
                        5 => {
                            v___x_2102_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30);
                            v___y_2073_ = v___x_2102_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_a_2103_ = crate::leanh::lean_ctor_get(v_head_2070_, 0);
                            crate::leanh::lean_inc(v_a_2103_);
                            v_a_2104_ = crate::leanh::lean_ctor_get(v_head_2070_, 1);
                            crate::leanh::lean_inc(v_a_2104_);
                            v_a_2105_ = crate::leanh::lean_ctor_get(v_head_2070_, 2);
                            crate::leanh::lean_inc(v_a_2105_);
                            crate::leanh::lean_dec_ref_known(v_head_2070_, 3);
                            v___x_2106_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33);
                            v___x_2107_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_2103_);
                            v___x_2108_ = l_Lean_mkNatLit(v_a_2104_);
                            v___x_2109_ = l_Lean_mkNatLit(v_a_2105_);
                            v___x_2110_ =
                                l_Lean_mkApp3(v___x_2106_, v___x_2107_, v___x_2108_, v___x_2109_);
                            v___y_2073_ = v___x_2110_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_consFn_2068_);
                v___x_2074_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0(v_nilFn_2067_, v_consFn_2068_, v_tail_2071_);
                v___x_2075_ = l_Lean_mkAppB(v_consFn_2068_, v___y_2073_, v___x_2074_);
                return v___x_2075_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___boxed(
    mut v_nilFn_2111_: *mut crate::leanh::LeanObject,
    mut v_consFn_2112_: *mut crate::leanh::LeanObject,
    mut v_x_2113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2114_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0(v_nilFn_2111_, v_consFn_2112_, v_x_2113_);
    crate::leanh::lean_dec_ref(v_nilFn_2111_);
    return v_res_2114_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2126_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6;
    v___x_2127_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5;
    v___x_2128_ = l_Lean_mkConst(v___x_2127_, v___x_2126_);
    return v___x_2128_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2136_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6;
    v___x_2137_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11;
    v___x_2138_ = l_Lean_mkConst(v___x_2137_, v___x_2136_);
    return v___x_2138_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2143_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6;
    v___x_2144_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14;
    v___x_2145_ = l_Lean_mkConst(v___x_2144_, v___x_2143_);
    return v___x_2145_;
}
pub unsafe fn l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0(
    mut v___x_2146_: *mut crate::leanh::LeanObject,
    mut v___x_2147_: *mut crate::leanh::LeanObject,
    mut v___x_2148_: *mut crate::leanh::LeanObject,
    mut v___x_2149_: *mut crate::leanh::LeanObject,
    mut v___y_2150_: *mut crate::leanh::LeanObject,
    mut v___y_2151_: *mut crate::leanh::LeanObject,
    mut v___y_2152_: *mut crate::leanh::LeanObject,
    mut v___y_2153_: *mut crate::leanh::LeanObject,
    mut v___y_2154_: *mut crate::leanh::LeanObject,
    mut v___y_2155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nil_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cons_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2196_: u8 = 0;
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2200_: u8 = 0;
    let mut v_a_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2204_: u8 = 0;
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2208_: u8 = 0;
    let mut v_a_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2212_: u8 = 0;
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2216_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2157_ =
                    l_Lean_realizeGlobalConstNoOverload(v___x_2146_, v___y_2154_, v___y_2155_);
                if crate::leanh::lean_obj_tag(v___x_2157_) == 0 {
                    v_a_2158_ = crate::leanh::lean_ctor_get(v___x_2157_, 0);
                    crate::leanh::lean_inc_n(v_a_2158_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2157_, 1);
                    v___x_2159_ =
                        l_Lean_Elab_checkCbvSimprocType(v_a_2158_, v___y_2154_, v___y_2155_);
                    if crate::leanh::lean_obj_tag(v___x_2159_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2159_, 1);
                        v___x_2160_ = l_Lean_Elab_elabCbvSimprocKeys(
                            v___x_2147_,
                            v___y_2152_,
                            v___y_2153_,
                            v___y_2154_,
                            v___y_2155_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2160_) == 0 {
                            v_a_2161_ = crate::leanh::lean_ctor_get(v___x_2160_, 0);
                            crate::leanh::lean_inc(v_a_2161_);
                            crate::leanh::lean_dec_ref_known(v___x_2160_, 1);
                            v___x_2162_ = l_Lean_Elab_checkCbvSimprocType___closed__3;
                            v___x_2163_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__0;
                            v___x_2164_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__1;
                            v___x_2165_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__2;
                            crate::leanh::lean_inc_ref(v___x_2148_);
                            v___x_2166_ = l_Lean_Name_mkStr5(
                                v___x_2148_,
                                v___x_2162_,
                                v___x_2163_,
                                v___x_2164_,
                                v___x_2165_,
                            );
                            v___x_2167_ = crate::leanh::lean_box(0);
                            v___x_2168_ = l_Lean_mkConst(v___x_2166_, v___x_2167_);
                            crate::leanh::lean_inc_n(v_a_2158_, 2);
                            v___x_2169_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_2158_);
                            v___x_2170_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0;
                            v___x_2171_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1;
                            v___x_2172_ = l_Lean_Name_mkStr4(
                                v___x_2148_,
                                v___x_2162_,
                                v___x_2170_,
                                v___x_2171_,
                            );
                            v___x_2173_ = l_Lean_mkConst(v___x_2172_, v___x_2167_);
                            v___x_2174_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7_once), _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7);
                            v___x_2175_ = l_Lean_mkConst(v_a_2158_, v___x_2167_);
                            v___x_2176_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__9;
                            v___x_2177_ = l_Lean_Name_append(v_a_2158_, v___x_2176_);
                            v___x_2178_ =
                                l_Lean_Core_mkFreshUserName(v___x_2177_, v___y_2154_, v___y_2155_);
                            if crate::leanh::lean_obj_tag(v___x_2178_) == 0 {
                                v_a_2179_ = crate::leanh::lean_ctor_get(v___x_2178_, 0);
                                crate::leanh::lean_inc(v_a_2179_);
                                crate::leanh::lean_dec_ref_known(v___x_2178_, 1);
                                v___x_2180_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12), core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12_once), _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12);
                                crate::leanh::lean_inc_ref_n(v___x_2173_, 2);
                                v_nil_2181_ = l_Lean_Expr_app___override(v___x_2180_, v___x_2173_);
                                v___x_2182_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15), core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15_once), _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15);
                                v_cons_2183_ = l_Lean_Expr_app___override(v___x_2182_, v___x_2173_);
                                v___x_2184_ = lean_array_to_list(v_a_2161_);
                                v___x_2185_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0(v_nil_2181_, v_cons_2183_, v___x_2184_);
                                crate::leanh::lean_dec_ref(v_nil_2181_);
                                v___x_2186_ = l_Lean_mkAppB(v___x_2174_, v___x_2173_, v___x_2185_);
                                v___x_2187_ = lean_mk_empty_array_with_capacity(v___x_2149_);
                                v___x_2188_ = lean_array_push(v___x_2187_, v___x_2169_);
                                v___x_2189_ = lean_array_push(v___x_2188_, v___x_2186_);
                                v___x_2190_ = lean_array_push(v___x_2189_, v___x_2175_);
                                v___x_2191_ = l_Lean_mkAppN(v___x_2168_, v___x_2190_);
                                crate::leanh::lean_dec_ref(v___x_2190_);
                                v___x_2192_ = l_Lean_declareBuiltin(
                                    v_a_2179_,
                                    v___x_2191_,
                                    v___y_2154_,
                                    v___y_2155_,
                                );
                                return v___x_2192_;
                            } else {
                                crate::leanh::lean_dec_ref(v___x_2175_);
                                crate::leanh::lean_dec_ref(v___x_2173_);
                                crate::leanh::lean_dec_ref(v___x_2169_);
                                crate::leanh::lean_dec_ref(v___x_2168_);
                                crate::leanh::lean_dec(v_a_2161_);
                                v_a_2193_ = crate::leanh::lean_ctor_get(v___x_2178_, 0);
                                v_isSharedCheck_2200_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2178_)) as u8;
                                if v_isSharedCheck_2200_ == 0 {
                                    v___x_2195_ = v___x_2178_;
                                    v_isShared_2196_ = v_isSharedCheck_2200_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2193_);
                                    crate::leanh::lean_dec(v___x_2178_);
                                    v___x_2195_ = crate::leanh::lean_box(0);
                                    v_isShared_2196_ = v_isSharedCheck_2200_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2158_);
                            crate::leanh::lean_dec_ref(v___x_2148_);
                            v_a_2201_ = crate::leanh::lean_ctor_get(v___x_2160_, 0);
                            v_isSharedCheck_2208_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2160_)) as u8;
                            if v_isSharedCheck_2208_ == 0 {
                                v___x_2203_ = v___x_2160_;
                                v_isShared_2204_ = v_isSharedCheck_2208_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2201_);
                                crate::leanh::lean_dec(v___x_2160_);
                                v___x_2203_ = crate::leanh::lean_box(0);
                                v_isShared_2204_ = v_isSharedCheck_2208_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2158_);
                        crate::leanh::lean_dec_ref(v___x_2148_);
                        crate::leanh::lean_dec(v___x_2147_);
                        return v___x_2159_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2148_);
                    crate::leanh::lean_dec(v___x_2147_);
                    v_a_2209_ = crate::leanh::lean_ctor_get(v___x_2157_, 0);
                    v_isSharedCheck_2216_ = (!crate::leanh::lean_is_exclusive(v___x_2157_)) as u8;
                    if v_isSharedCheck_2216_ == 0 {
                        v___x_2211_ = v___x_2157_;
                        v_isShared_2212_ = v_isSharedCheck_2216_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2209_);
                        crate::leanh::lean_dec(v___x_2157_);
                        v___x_2211_ = crate::leanh::lean_box(0);
                        v_isShared_2212_ = v_isSharedCheck_2216_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2196_ == 0 {
                    v___x_2198_ = v___x_2195_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2199_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
                    v___x_2198_ = v_reuseFailAlloc_2199_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2198_;
            }
            3 => {
                if v_isShared_2204_ == 0 {
                    v___x_2206_ = v___x_2203_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2207_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
                    v___x_2206_ = v_reuseFailAlloc_2207_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2206_;
            }
            5 => {
                if v_isShared_2212_ == 0 {
                    v___x_2214_ = v___x_2211_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2215_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
                    v___x_2214_ = v_reuseFailAlloc_2215_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2214_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___boxed(
    mut v___x_2217_: *mut crate::leanh::LeanObject,
    mut v___x_2218_: *mut crate::leanh::LeanObject,
    mut v___x_2219_: *mut crate::leanh::LeanObject,
    mut v___x_2220_: *mut crate::leanh::LeanObject,
    mut v___y_2221_: *mut crate::leanh::LeanObject,
    mut v___y_2222_: *mut crate::leanh::LeanObject,
    mut v___y_2223_: *mut crate::leanh::LeanObject,
    mut v___y_2224_: *mut crate::leanh::LeanObject,
    mut v___y_2225_: *mut crate::leanh::LeanObject,
    mut v___y_2226_: *mut crate::leanh::LeanObject,
    mut v___y_2227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2228_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0(
        v___x_2217_,
        v___x_2218_,
        v___x_2219_,
        v___x_2220_,
        v___y_2221_,
        v___y_2222_,
        v___y_2223_,
        v___y_2224_,
        v___y_2225_,
        v___y_2226_,
    );
    crate::leanh::lean_dec(v___y_2226_);
    crate::leanh::lean_dec_ref(v___y_2225_);
    crate::leanh::lean_dec(v___y_2224_);
    crate::leanh::lean_dec_ref(v___y_2223_);
    crate::leanh::lean_dec(v___y_2222_);
    crate::leanh::lean_dec_ref(v___y_2221_);
    crate::leanh::lean_dec(v___x_2220_);
    return v_res_2228_;
}
pub unsafe fn l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin(
    mut v_stx_2234_: *mut crate::leanh::LeanObject,
    mut v_a_2235_: *mut crate::leanh::LeanObject,
    mut v_a_2236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: u8 = 0;
    v___x_2238_ = l_Lean_Elab_checkCbvSimprocType___closed__2;
    v___x_2239_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1;
    crate::leanh::lean_inc(v_stx_2234_);
    v___x_2240_ = l_Lean_Syntax_isOfKind(v_stx_2234_, v___x_2239_);
    if v___x_2240_ == 0 {
        let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_stx_2234_);
        v___x_2241_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg();
        return v___x_2241_;
    } else {
        let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2242_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_2243_ = l_Lean_Syntax_getArg(v_stx_2234_, v___x_2242_);
        v___x_2244_ = crate::leanh::lean_unsigned_to_nat(3);
        v___x_2245_ = l_Lean_Syntax_getArg(v_stx_2234_, v___x_2244_);
        crate::leanh::lean_dec(v_stx_2234_);
        v___f_2246_ = crate::leanh::lean_alloc_closure(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___boxed
                as *mut core::ffi::c_void,
            11,
            4,
        );
        crate::leanh::lean_closure_set(v___f_2246_, 0, v___x_2245_);
        crate::leanh::lean_closure_set(v___f_2246_, 1, v___x_2243_);
        crate::leanh::lean_closure_set(v___f_2246_, 2, v___x_2238_);
        crate::leanh::lean_closure_set(v___f_2246_, 3, v___x_2244_);
        v___x_2247_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2246_, v_a_2235_, v_a_2236_);
        return v___x_2247_;
    }
}
pub unsafe fn l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___boxed(
    mut v_stx_2248_: *mut crate::leanh::LeanObject,
    mut v_a_2249_: *mut crate::leanh::LeanObject,
    mut v_a_2250_: *mut crate::leanh::LeanObject,
    mut v_a_2251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2252_ =
        l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin(v_stx_2248_, v_a_2249_, v_a_2250_);
    crate::leanh::lean_dec(v_a_2250_);
    crate::leanh::lean_dec_ref(v_a_2249_);
    return v_res_2252_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2260_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_2261_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1;
    v___x_2262_ = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1;
    v___x_2263_ = crate::leanh::lean_alloc_closure(
        l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_2264_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2260_,
        v___x_2261_,
        v___x_2262_,
        v___x_2263_,
    );
    return v___x_2264_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___boxed(
    mut v_a_2265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2266_ = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1();
    return v_res_2266_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_CbvSimproc(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_CbvSimproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_CbvSimproc(
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
pub unsafe fn initialize_Lean_Elab_Tactic_CbvSimproc(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_CbvSimproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_CbvSimproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_CbvSimproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_CbvSimproc(builtin);
}

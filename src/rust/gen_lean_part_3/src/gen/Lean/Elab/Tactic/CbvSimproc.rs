// Lean compiler output
// Module: Lean.Elab.Tactic.CbvSimproc
// Imports: Init.CbvSimproc Lean.Meta.Tactic.Cbv.CbvSimproc Lean.Elab.Command
use crate::ffi::{
    lean_array_get, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_st_ref_get, lean_string_dec_eq,
};
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
pub static l_Lean_Elab_elabCbvSimprocPattern___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_elabCbvSimprocPattern___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_elabCbvSimprocPattern___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabCbvSimprocPattern___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_elabCbvSimprocPattern___closed__1_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Elab_elabCbvSimprocPattern___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabCbvSimprocPattern___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_elabCbvSimprocPattern___closed__2_value: leanh::LeanCtorObject<10> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 8
                + 16) as u16,
            other: 8,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_elabCbvSimprocPattern___closed__0_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_elabCbvSimprocPattern___closed__1_value)
                as *mut leanh::LeanObject,
            16843009 as *mut leanh::LeanObject,
            65537 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_elabCbvSimprocPattern___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabCbvSimprocPattern___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_elabCbvSimprocPattern___closed__3_value: leanh::LeanCtorObject<7> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 7
                + 0) as u16,
            other: 7,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_elabCbvSimprocPattern___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabCbvSimprocPattern___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_mkSimprocPatternFromExpr___closed__0_value: leanh::LeanClosureObject<
    1,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_mkSimprocPatternFromExpr___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 1,
    m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Elab_mkSimprocPatternFromExpr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkSimprocPatternFromExpr___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkCbvSimprocType___closed__0_value: leanh::LeanStringObject<52> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_checkCbvSimprocType___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_checkCbvSimprocType___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkCbvSimprocType___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkCbvSimprocType___closed__2_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_checkCbvSimprocType___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_checkCbvSimprocType___closed__3_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_checkCbvSimprocType___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_checkCbvSimprocType___closed__4_value: leanh::LeanStringObject<4> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_checkCbvSimprocType___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_checkCbvSimprocType___closed__5_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_checkCbvSimprocType___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_checkCbvSimprocType___closed__6_value: leanh::LeanStringObject<8> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_checkCbvSimprocType___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__6_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value)
                as *mut leanh::LeanObject,
            11948124481539785030 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value)
                as *mut leanh::LeanObject,
            15449383196166861506 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_2: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__4_value)
                as *mut leanh::LeanObject,
            4034176598647545331 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_3: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__5_value)
                as *mut leanh::LeanObject,
            13806531830123099675 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Elab_checkCbvSimprocType___closed__7_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_3)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__6_value)
                as *mut leanh::LeanObject,
            4585357269266081267 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Elab_checkCbvSimprocType___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_checkCbvSimprocType___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkCbvSimprocType___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_checkCbvSimprocType___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkCbvSimprocType___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkCbvSimprocType___closed__10_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_checkCbvSimprocType___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_checkCbvSimprocType___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkCbvSimprocType___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_checkCbvSimprocType___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkCbvSimprocType___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_checkCbvSimprocType___closed__13_value: leanh::LeanStringObject<11> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_checkCbvSimprocType___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__13_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_checkCbvSimprocType___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_checkCbvSimprocType___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabCbvSimprocPattern___closed__0_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_elabCbvSimprocPattern___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPattern___closed__1_value:
    leanh::LeanStringObject<18> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
static mut l_Lean_Elab_Command_elabCbvSimprocPattern___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__0_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__1_value)
            as *mut leanh::LeanObject,
        5000477209128750040 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__1_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__2_value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [101, 108, 97, 98, 67, 98, 118, 83, 105, 109, 112, 114, 111, 99, 80, 97, 116, 116, 101, 114, 110, 0]};
static mut l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__1_value) as *mut leanh::LeanObject,16981400742628996529 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__2_value) as *mut leanh::LeanObject,14237717666078075311 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [68, 105, 115, 99, 114, 84, 114, 101, 101, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [75, 101, 121, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__2_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 116, 97, 114, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut leanh::LeanObject,12558998168795833107 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut leanh::LeanObject,6571394212498793888 as *mut leanh::LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__2_value) as *mut leanh::LeanObject,4525596147727532808 as *mut leanh::LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__5_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 116, 104, 101, 114, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__5_value) as *mut leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut leanh::LeanObject,12558998168795833107 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut leanh::LeanObject,6571394212498793888 as *mut leanh::LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__5_value) as *mut leanh::LeanObject,11989153488816012938 as *mut leanh::LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__8_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [108, 105, 116, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__8_value) as *mut leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut leanh::LeanObject,12558998168795833107 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut leanh::LeanObject,6571394212498793888 as *mut leanh::LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__8_value) as *mut leanh::LeanObject,15074539318474479562 as *mut leanh::LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__11_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [76, 105, 116, 101, 114, 97, 108, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__12_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [110, 97, 116, 86, 97, 108, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__12_value) as *mut leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__11_value) as *mut leanh::LeanObject,7001815944269665831 as *mut leanh::LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__12_value) as *mut leanh::LeanObject,9295767770006931264 as *mut leanh::LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__15_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 116, 114, 86, 97, 108, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__15_value) as *mut leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__11_value) as *mut leanh::LeanObject,7001815944269665831 as *mut leanh::LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__15_value) as *mut leanh::LeanObject,2005404019190257220 as *mut leanh::LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__18_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [102, 118, 97, 114, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__18_value) as *mut leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut leanh::LeanObject,12558998168795833107 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut leanh::LeanObject,6571394212498793888 as *mut leanh::LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__18_value) as *mut leanh::LeanObject,3087321959384269759 as *mut leanh::LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__21_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [70, 86, 97, 114, 73, 100, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__21_value) as *mut leanh::LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__22_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__22_value) as *mut leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__21_value) as *mut leanh::LeanObject,6212595679582900358 as *mut leanh::LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__22_value) as *mut leanh::LeanObject,6968149084986791158 as *mut leanh::LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__25_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 111, 110, 115, 116, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__25_value) as *mut leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut leanh::LeanObject,12558998168795833107 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut leanh::LeanObject,6571394212498793888 as *mut leanh::LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__25_value) as *mut leanh::LeanObject,17383108283035838098 as *mut leanh::LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__28_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 114, 114, 111, 119, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__28_value) as *mut leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut leanh::LeanObject,12558998168795833107 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut leanh::LeanObject,6571394212498793888 as *mut leanh::LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__28_value) as *mut leanh::LeanObject,8457098344818307929 as *mut leanh::LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__31_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 114, 111, 106, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__31_value) as *mut leanh::LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut leanh::LeanObject,12558998168795833107 as *mut leanh::LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut leanh::LeanObject,6571394212498793888 as *mut leanh::LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__31_value) as *mut leanh::LeanObject,12263618261203284320 as *mut leanh::LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value) as *mut leanh::LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__0_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__1_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__2_value:
    leanh::LeanStringObject<26> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__4_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__4_value
) as *mut leanh::LeanObject;
static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3_value
        ) as *mut leanh::LeanObject,
        9582258842178272501 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__4_value
        ) as *mut leanh::LeanObject,
        8414467900391110369 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__8_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__8_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__9_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__8_value
        ) as *mut leanh::LeanObject,
        13812150225987229964 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__9_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__10_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__10_value
) as *mut leanh::LeanObject;
static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3_value
        ) as *mut leanh::LeanObject,
        9582258842178272501 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__10_value
        ) as *mut leanh::LeanObject,
        18135193680607614554 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__13_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__13_value
) as *mut leanh::LeanObject;
static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3_value
        ) as *mut leanh::LeanObject,
        9582258842178272501 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__13_value
        ) as *mut leanh::LeanObject,
        8614124190858717794 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14_value
) as *mut leanh::LeanObject;
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__0_value:
    leanh::LeanStringObject<25> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
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
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__0_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__0_value)
            as *mut leanh::LeanObject,
        2235975067317863979 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__0_value: leanh::LeanStringObject<29> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [101, 108, 97, 98, 67, 98, 118, 83, 105, 109, 112, 114, 111, 99, 80, 97, 116, 116, 101, 114, 110, 66, 117, 105, 108, 116, 105, 110, 0]};
static mut l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__0_value) as *mut leanh::LeanObject,11510100434945111860 as *mut leanh::LeanObject] };
static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__1_value) as *mut leanh::LeanObject,16981400742628996529 as *mut leanh::LeanObject] };
pub static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__0_value) as *mut leanh::LeanObject,8968079526420962855 as *mut leanh::LeanObject] };
static mut l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value) as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Elab_elabCbvSimprocPattern___lam__0(
    mut v_x_1134_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1135_: u8 = 0;
    v___x_1135_ = 0;
    return v___x_1135_;
}
pub unsafe fn l_Lean_Elab_elabCbvSimprocPattern___lam__0___boxed(
    mut v_x_1136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1137_: u8 = 0;
    let mut v_r_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1137_ = l_Lean_Elab_elabCbvSimprocPattern___lam__0(v_x_1136_);
    leanh::lean_dec(v_x_1136_);
    v_r_1138_ = leanh::lean_box((v_res_1137_) as usize);
    return v_r_1138_;
}
pub unsafe fn l_Lean_Elab_elabCbvSimprocPattern___lam__1(
    mut v_stx_1139_: *mut leanh::LeanObject,
    mut v___x_1140_: *mut leanh::LeanObject,
    mut v___x_1141_: u8,
    mut v___y_1142_: *mut leanh::LeanObject,
    mut v___y_1143_: *mut leanh::LeanObject,
    mut v___y_1144_: *mut leanh::LeanObject,
    mut v___y_1145_: *mut leanh::LeanObject,
    mut v___y_1146_: *mut leanh::LeanObject,
    mut v___y_1147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: u8 = 0;
    let mut v___x_1152_: u8 = 0;
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1156_: u8 = 0;
    let mut v___x_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1160_: u8 = 0;
    let mut v_unused_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1165_: u8 = 0;
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_1149_) == 0 {
                    v_a_1150_ = leanh::lean_ctor_get(v___x_1149_, 0);
                    leanh::lean_inc(v_a_1150_);
                    leanh::lean_dec_ref_known(v___x_1149_, 1);
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
                    if leanh::lean_obj_tag(v___x_1153_) == 0 {
                        v_isSharedCheck_1160_ =
                            (!leanh::lean_is_exclusive(v___x_1153_)) as u8;
                        if v_isSharedCheck_1160_ == 0 {
                            v_unused_1161_ = leanh::lean_ctor_get(v___x_1153_, 0);
                            leanh::lean_dec(v_unused_1161_);
                            v___x_1155_ = v___x_1153_;
                            v_isShared_1156_ = v_isSharedCheck_1160_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_1153_);
                            v___x_1155_ = leanh::lean_box(0);
                            v_isShared_1156_ = v_isSharedCheck_1160_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_1150_);
                        v_a_1162_ = leanh::lean_ctor_get(v___x_1153_, 0);
                        v_isSharedCheck_1169_ =
                            (!leanh::lean_is_exclusive(v___x_1153_)) as u8;
                        if v_isSharedCheck_1169_ == 0 {
                            v___x_1164_ = v___x_1153_;
                            v_isShared_1165_ = v_isSharedCheck_1169_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1162_);
                            leanh::lean_dec(v___x_1153_);
                            v___x_1164_ = leanh::lean_box(0);
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
                    leanh::lean_ctor_set(v___x_1155_, 0, v_a_1150_);
                    v___x_1158_ = v___x_1155_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1159_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1150_);
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
                    v_reuseFailAlloc_1168_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
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
    mut v_stx_1170_: *mut leanh::LeanObject,
    mut v___x_1171_: *mut leanh::LeanObject,
    mut v___x_1172_: *mut leanh::LeanObject,
    mut v___y_1173_: *mut leanh::LeanObject,
    mut v___y_1174_: *mut leanh::LeanObject,
    mut v___y_1175_: *mut leanh::LeanObject,
    mut v___y_1176_: *mut leanh::LeanObject,
    mut v___y_1177_: *mut leanh::LeanObject,
    mut v___y_1178_: *mut leanh::LeanObject,
    mut v___y_1179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_356__boxed_1180_: u8 = 0;
    let mut v_res_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_356__boxed_1180_ = (leanh::lean_unbox(v___x_1172_) as u8);
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
    leanh::lean_dec(v___y_1178_);
    leanh::lean_dec_ref(v___y_1177_);
    leanh::lean_dec(v___y_1176_);
    leanh::lean_dec_ref(v___y_1175_);
    leanh::lean_dec(v___y_1174_);
    leanh::lean_dec_ref(v___y_1173_);
    return v_res_1181_;
}
pub unsafe fn l_Lean_Elab_elabCbvSimprocPattern(
    mut v_stx_1196_: *mut leanh::LeanObject,
    mut v_a_1197_: *mut leanh::LeanObject,
    mut v_a_1198_: *mut leanh::LeanObject,
    mut v_a_1199_: *mut leanh::LeanObject,
    mut v_a_1200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: u8 = 0;
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_go_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1212_: u8 = 0;
    let mut v_fst_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1217_: u8 = 0;
    let mut v_a_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1221_: u8 = 0;
    let mut v___x_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1202_ = leanh::lean_box(0);
                v___x_1203_ = 1;
                v___x_1204_ = leanh::lean_box((v___x_1203_) as usize);
                v_go_1205_ = leanh::lean_alloc_closure(
                    l_Lean_Elab_elabCbvSimprocPattern___lam__1___boxed as *mut core::ffi::c_void,
                    10,
                    3,
                );
                leanh::lean_closure_set(v_go_1205_, 0, v_stx_1196_);
                leanh::lean_closure_set(v_go_1205_, 1, v___x_1202_);
                leanh::lean_closure_set(v_go_1205_, 2, v___x_1204_);
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
                if leanh::lean_obj_tag(v___x_1208_) == 0 {
                    v_a_1209_ = leanh::lean_ctor_get(v___x_1208_, 0);
                    v_isSharedCheck_1217_ = (!leanh::lean_is_exclusive(v___x_1208_)) as u8;
                    if v_isSharedCheck_1217_ == 0 {
                        v___x_1211_ = v___x_1208_;
                        v_isShared_1212_ = v_isSharedCheck_1217_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1209_);
                        leanh::lean_dec(v___x_1208_);
                        v___x_1211_ = leanh::lean_box(0);
                        v_isShared_1212_ = v_isSharedCheck_1217_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1218_ = leanh::lean_ctor_get(v___x_1208_, 0);
                    v_isSharedCheck_1225_ = (!leanh::lean_is_exclusive(v___x_1208_)) as u8;
                    if v_isSharedCheck_1225_ == 0 {
                        v___x_1220_ = v___x_1208_;
                        v_isShared_1221_ = v_isSharedCheck_1225_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1218_);
                        leanh::lean_dec(v___x_1208_);
                        v___x_1220_ = leanh::lean_box(0);
                        v_isShared_1221_ = v_isSharedCheck_1225_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1213_ = leanh::lean_ctor_get(v_a_1209_, 0);
                leanh::lean_inc(v_fst_1213_);
                leanh::lean_dec(v_a_1209_);
                if v_isShared_1212_ == 0 {
                    leanh::lean_ctor_set(v___x_1211_, 0, v_fst_1213_);
                    v___x_1215_ = v___x_1211_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1216_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_fst_1213_);
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
                    v_reuseFailAlloc_1224_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
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
    mut v_stx_1226_: *mut leanh::LeanObject,
    mut v_a_1227_: *mut leanh::LeanObject,
    mut v_a_1228_: *mut leanh::LeanObject,
    mut v_a_1229_: *mut leanh::LeanObject,
    mut v_a_1230_: *mut leanh::LeanObject,
    mut v_a_1231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1232_ =
        l_Lean_Elab_elabCbvSimprocPattern(v_stx_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
    leanh::lean_dec(v_a_1230_);
    leanh::lean_dec_ref(v_a_1229_);
    leanh::lean_dec(v_a_1228_);
    leanh::lean_dec_ref(v_a_1227_);
    return v_res_1232_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg___lam__0(
    mut v_k_1233_: *mut leanh::LeanObject,
    mut v_b_1234_: *mut leanh::LeanObject,
    mut v_c_1235_: *mut leanh::LeanObject,
    mut v___y_1236_: *mut leanh::LeanObject,
    mut v___y_1237_: *mut leanh::LeanObject,
    mut v___y_1238_: *mut leanh::LeanObject,
    mut v___y_1239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1239_);
    leanh::lean_inc_ref(v___y_1238_);
    leanh::lean_inc(v___y_1237_);
    leanh::lean_inc_ref(v___y_1236_);
    v___x_1241_ = leanh::lean_apply_7(
        v_k_1233_,
        v_b_1234_,
        v_c_1235_,
        v___y_1236_,
        v___y_1237_,
        v___y_1238_,
        v___y_1239_,
        leanh::lean_box(0),
    );
    return v___x_1241_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg___lam__0___boxed(
    mut v_k_1242_: *mut leanh::LeanObject,
    mut v_b_1243_: *mut leanh::LeanObject,
    mut v_c_1244_: *mut leanh::LeanObject,
    mut v___y_1245_: *mut leanh::LeanObject,
    mut v___y_1246_: *mut leanh::LeanObject,
    mut v___y_1247_: *mut leanh::LeanObject,
    mut v___y_1248_: *mut leanh::LeanObject,
    mut v___y_1249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1250_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg___lam__0(v_k_1242_, v_b_1243_, v_c_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
    leanh::lean_dec(v___y_1248_);
    leanh::lean_dec_ref(v___y_1247_);
    leanh::lean_dec(v___y_1246_);
    leanh::lean_dec_ref(v___y_1245_);
    return v_res_1250_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg(
    mut v_e_1251_: *mut leanh::LeanObject,
    mut v_k_1252_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1253_: u8,
    mut v___y_1254_: *mut leanh::LeanObject,
    mut v___y_1255_: *mut leanh::LeanObject,
    mut v___y_1256_: *mut leanh::LeanObject,
    mut v___y_1257_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: u8 = 0;
    let mut v___x_1261_: u8 = 0;
    let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1267_: u8 = 0;
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1271_: u8 = 0;
    let mut v_a_1272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1275_: u8 = 0;
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1279_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1259_ = leanh::lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_1259_, 0, v_k_1252_);
                v___x_1260_ = 1;
                v___x_1261_ = 0;
                v___x_1262_ = leanh::lean_box(0);
                v___x_1263_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    leanh::lean_box(0),
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
                if leanh::lean_obj_tag(v___x_1263_) == 0 {
                    v_a_1264_ = leanh::lean_ctor_get(v___x_1263_, 0);
                    v_isSharedCheck_1271_ = (!leanh::lean_is_exclusive(v___x_1263_)) as u8;
                    if v_isSharedCheck_1271_ == 0 {
                        v___x_1266_ = v___x_1263_;
                        v_isShared_1267_ = v_isSharedCheck_1271_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1264_);
                        leanh::lean_dec(v___x_1263_);
                        v___x_1266_ = leanh::lean_box(0);
                        v_isShared_1267_ = v_isSharedCheck_1271_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1272_ = leanh::lean_ctor_get(v___x_1263_, 0);
                    v_isSharedCheck_1279_ = (!leanh::lean_is_exclusive(v___x_1263_)) as u8;
                    if v_isSharedCheck_1279_ == 0 {
                        v___x_1274_ = v___x_1263_;
                        v_isShared_1275_ = v_isSharedCheck_1279_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1272_);
                        leanh::lean_dec(v___x_1263_);
                        v___x_1274_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1270_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
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
                    v_reuseFailAlloc_1278_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
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
    mut v_e_1280_: *mut leanh::LeanObject,
    mut v_k_1281_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1282_: *mut leanh::LeanObject,
    mut v___y_1283_: *mut leanh::LeanObject,
    mut v___y_1284_: *mut leanh::LeanObject,
    mut v___y_1285_: *mut leanh::LeanObject,
    mut v___y_1286_: *mut leanh::LeanObject,
    mut v___y_1287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1288_: u8 = 0;
    let mut v_res_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1288_ = (leanh::lean_unbox(v_cleanupAnnotations_1282_) as u8);
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
    leanh::lean_dec(v___y_1286_);
    leanh::lean_dec_ref(v___y_1285_);
    leanh::lean_dec(v___y_1284_);
    leanh::lean_dec_ref(v___y_1283_);
    return v_res_1289_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0(
    mut v_00_u03b1_1290_: *mut leanh::LeanObject,
    mut v_e_1291_: *mut leanh::LeanObject,
    mut v_k_1292_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1293_: u8,
    mut v___y_1294_: *mut leanh::LeanObject,
    mut v___y_1295_: *mut leanh::LeanObject,
    mut v___y_1296_: *mut leanh::LeanObject,
    mut v___y_1297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1300_: *mut leanh::LeanObject,
    mut v_e_1301_: *mut leanh::LeanObject,
    mut v_k_1302_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_1303_: *mut leanh::LeanObject,
    mut v___y_1304_: *mut leanh::LeanObject,
    mut v___y_1305_: *mut leanh::LeanObject,
    mut v___y_1306_: *mut leanh::LeanObject,
    mut v___y_1307_: *mut leanh::LeanObject,
    mut v___y_1308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_1309_: u8 = 0;
    let mut v_res_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1309_ = (leanh::lean_unbox(v_cleanupAnnotations_1303_) as u8);
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
    leanh::lean_dec(v___y_1307_);
    leanh::lean_dec_ref(v___y_1306_);
    leanh::lean_dec(v___y_1305_);
    leanh::lean_dec_ref(v___y_1304_);
    return v_res_1310_;
}
pub unsafe fn l_Lean_Elab_mkSimprocPatternFromExpr___lam__0(
    mut v___x_1311_: u8,
    mut v_args_1312_: *mut leanh::LeanObject,
    mut v_body_1313_: *mut leanh::LeanObject,
    mut v___y_1314_: *mut leanh::LeanObject,
    mut v___y_1315_: *mut leanh::LeanObject,
    mut v___y_1316_: *mut leanh::LeanObject,
    mut v___y_1317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1319_: u8 = 0;
    let mut v___x_1320_: u8 = 0;
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    mut v___x_1322_: *mut leanh::LeanObject,
    mut v_args_1323_: *mut leanh::LeanObject,
    mut v_body_1324_: *mut leanh::LeanObject,
    mut v___y_1325_: *mut leanh::LeanObject,
    mut v___y_1326_: *mut leanh::LeanObject,
    mut v___y_1327_: *mut leanh::LeanObject,
    mut v___y_1328_: *mut leanh::LeanObject,
    mut v___y_1329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_637__boxed_1330_: u8 = 0;
    let mut v_res_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_637__boxed_1330_ = (leanh::lean_unbox(v___x_1322_) as u8);
    v_res_1331_ = l_Lean_Elab_mkSimprocPatternFromExpr___lam__0(
        v___x_637__boxed_1330_,
        v_args_1323_,
        v_body_1324_,
        v___y_1325_,
        v___y_1326_,
        v___y_1327_,
        v___y_1328_,
    );
    leanh::lean_dec(v___y_1328_);
    leanh::lean_dec_ref(v___y_1327_);
    leanh::lean_dec(v___y_1326_);
    leanh::lean_dec_ref(v___y_1325_);
    leanh::lean_dec_ref(v_args_1323_);
    return v_res_1331_;
}
pub unsafe fn l_Lean_Elab_mkSimprocPatternFromExpr(
    mut v_e_1335_: *mut leanh::LeanObject,
    mut v_a_1336_: *mut leanh::LeanObject,
    mut v_a_1337_: *mut leanh::LeanObject,
    mut v_a_1338_: *mut leanh::LeanObject,
    mut v_a_1339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1341_: u8 = 0;
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramNames_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: u8 = 0;
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: u8 = 0;
    let mut v___x_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1361_: u8 = 0;
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1365_: u8 = 0;
    let mut v_a_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v___x_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1373_: u8 = 0;
    let mut v_a_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1377_: u8 = 0;
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_1342_) == 0 {
                    v_a_1343_ = leanh::lean_ctor_get(v___x_1342_, 0);
                    leanh::lean_inc(v_a_1343_);
                    leanh::lean_dec_ref_known(v___x_1342_, 1);
                    v_paramNames_1344_ = leanh::lean_ctor_get(v_a_1343_, 0);
                    leanh::lean_inc_ref(v_paramNames_1344_);
                    v_expr_1345_ = leanh::lean_ctor_get(v_a_1343_, 2);
                    leanh::lean_inc_ref(v_expr_1345_);
                    leanh::lean_dec(v_a_1343_);
                    v___f_1346_ = l_Lean_Elab_mkSimprocPatternFromExpr___closed__0;
                    v___x_1347_ = 0;
                    v___x_1348_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg(v_expr_1345_, v___f_1346_, v___x_1347_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
                    if leanh::lean_obj_tag(v___x_1348_) == 0 {
                        v_a_1349_ = leanh::lean_ctor_get(v___x_1348_, 0);
                        leanh::lean_inc(v_a_1349_);
                        leanh::lean_dec_ref_known(v___x_1348_, 1);
                        v___x_1350_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1350_, 0, v_a_1349_);
                        v___x_1351_ = 0;
                        v___x_1352_ = leanh::lean_box(0);
                        v___x_1353_ = l_Lean_Meta_mkFreshExprMVar(
                            v___x_1350_,
                            v___x_1351_,
                            v___x_1352_,
                            v_a_1336_,
                            v_a_1337_,
                            v_a_1338_,
                            v_a_1339_,
                        );
                        if leanh::lean_obj_tag(v___x_1353_) == 0 {
                            v_a_1354_ = leanh::lean_ctor_get(v___x_1353_, 0);
                            leanh::lean_inc(v_a_1354_);
                            leanh::lean_dec_ref_known(v___x_1353_, 1);
                            v___x_1355_ = lean_array_to_list(v_paramNames_1344_);
                            v___x_1356_ = leanh::lean_box(0);
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
                            leanh::lean_dec_ref(v_paramNames_1344_);
                            v_a_1358_ = leanh::lean_ctor_get(v___x_1353_, 0);
                            v_isSharedCheck_1365_ =
                                (!leanh::lean_is_exclusive(v___x_1353_)) as u8;
                            if v_isSharedCheck_1365_ == 0 {
                                v___x_1360_ = v___x_1353_;
                                v_isShared_1361_ = v_isSharedCheck_1365_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1358_);
                                leanh::lean_dec(v___x_1353_);
                                v___x_1360_ = leanh::lean_box(0);
                                v_isShared_1361_ = v_isSharedCheck_1365_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_paramNames_1344_);
                        v_a_1366_ = leanh::lean_ctor_get(v___x_1348_, 0);
                        v_isSharedCheck_1373_ =
                            (!leanh::lean_is_exclusive(v___x_1348_)) as u8;
                        if v_isSharedCheck_1373_ == 0 {
                            v___x_1368_ = v___x_1348_;
                            v_isShared_1369_ = v_isSharedCheck_1373_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1366_);
                            leanh::lean_dec(v___x_1348_);
                            v___x_1368_ = leanh::lean_box(0);
                            v_isShared_1369_ = v_isSharedCheck_1373_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_1374_ = leanh::lean_ctor_get(v___x_1342_, 0);
                    v_isSharedCheck_1381_ = (!leanh::lean_is_exclusive(v___x_1342_)) as u8;
                    if v_isSharedCheck_1381_ == 0 {
                        v___x_1376_ = v___x_1342_;
                        v_isShared_1377_ = v_isSharedCheck_1381_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1374_);
                        leanh::lean_dec(v___x_1342_);
                        v___x_1376_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1364_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
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
                    v_reuseFailAlloc_1372_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
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
                    v_reuseFailAlloc_1380_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
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
    mut v_e_1382_: *mut leanh::LeanObject,
    mut v_a_1383_: *mut leanh::LeanObject,
    mut v_a_1384_: *mut leanh::LeanObject,
    mut v_a_1385_: *mut leanh::LeanObject,
    mut v_a_1386_: *mut leanh::LeanObject,
    mut v_a_1387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1388_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1388_ =
        l_Lean_Elab_mkSimprocPatternFromExpr(v_e_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_);
    leanh::lean_dec(v_a_1386_);
    leanh::lean_dec_ref(v_a_1385_);
    leanh::lean_dec(v_a_1384_);
    leanh::lean_dec_ref(v_a_1383_);
    return v_res_1388_;
}
pub unsafe fn l_Lean_Elab_elabCbvSimprocKeys(
    mut v_stx_1389_: *mut leanh::LeanObject,
    mut v_a_1390_: *mut leanh::LeanObject,
    mut v_a_1391_: *mut leanh::LeanObject,
    mut v_a_1392_: *mut leanh::LeanObject,
    mut v_a_1393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1401_: u8 = 0;
    let mut v___x_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1406_: u8 = 0;
    let mut v_a_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1410_: u8 = 0;
    let mut v___x_1412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1414_: u8 = 0;
    let mut v_a_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1418_: u8 = 0;
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
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
                if leanh::lean_obj_tag(v___x_1395_) == 0 {
                    v_a_1396_ = leanh::lean_ctor_get(v___x_1395_, 0);
                    leanh::lean_inc(v_a_1396_);
                    leanh::lean_dec_ref_known(v___x_1395_, 1);
                    v___x_1397_ = l_Lean_Elab_mkSimprocPatternFromExpr(
                        v_a_1396_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_,
                    );
                    if leanh::lean_obj_tag(v___x_1397_) == 0 {
                        v_a_1398_ = leanh::lean_ctor_get(v___x_1397_, 0);
                        v_isSharedCheck_1406_ =
                            (!leanh::lean_is_exclusive(v___x_1397_)) as u8;
                        if v_isSharedCheck_1406_ == 0 {
                            v___x_1400_ = v___x_1397_;
                            v_isShared_1401_ = v_isSharedCheck_1406_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1398_);
                            leanh::lean_dec(v___x_1397_);
                            v___x_1400_ = leanh::lean_box(0);
                            v_isShared_1401_ = v_isSharedCheck_1406_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1407_ = leanh::lean_ctor_get(v___x_1397_, 0);
                        v_isSharedCheck_1414_ =
                            (!leanh::lean_is_exclusive(v___x_1397_)) as u8;
                        if v_isSharedCheck_1414_ == 0 {
                            v___x_1409_ = v___x_1397_;
                            v_isShared_1410_ = v_isSharedCheck_1414_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1407_);
                            leanh::lean_dec(v___x_1397_);
                            v___x_1409_ = leanh::lean_box(0);
                            v_isShared_1410_ = v_isSharedCheck_1414_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_1415_ = leanh::lean_ctor_get(v___x_1395_, 0);
                    v_isSharedCheck_1422_ = (!leanh::lean_is_exclusive(v___x_1395_)) as u8;
                    if v_isSharedCheck_1422_ == 0 {
                        v___x_1417_ = v___x_1395_;
                        v_isShared_1418_ = v_isSharedCheck_1422_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1415_);
                        leanh::lean_dec(v___x_1395_);
                        v___x_1417_ = leanh::lean_box(0);
                        v_isShared_1418_ = v_isSharedCheck_1422_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1402_ = l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(v_a_1398_);
                if v_isShared_1401_ == 0 {
                    leanh::lean_ctor_set(v___x_1400_, 0, v___x_1402_);
                    v___x_1404_ = v___x_1400_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1405_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
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
                    v_reuseFailAlloc_1413_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
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
                    v_reuseFailAlloc_1421_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
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
    mut v_stx_1423_: *mut leanh::LeanObject,
    mut v_a_1424_: *mut leanh::LeanObject,
    mut v_a_1425_: *mut leanh::LeanObject,
    mut v_a_1426_: *mut leanh::LeanObject,
    mut v_a_1427_: *mut leanh::LeanObject,
    mut v_a_1428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1429_ =
        l_Lean_Elab_elabCbvSimprocKeys(v_stx_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
    leanh::lean_dec(v_a_1427_);
    leanh::lean_dec_ref(v_a_1426_);
    leanh::lean_dec(v_a_1425_);
    leanh::lean_dec_ref(v_a_1424_);
    return v_res_1429_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1430_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1430_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1431_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0);
    v___x_1432_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1432_, 0, v___x_1431_);
    return v___x_1432_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1433_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1);
    v___x_1434_ = leanh::lean_unsigned_to_nat(0);
    v___x_1435_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_1435_, 0, v___x_1434_);
    leanh::lean_ctor_set(v___x_1435_, 1, v___x_1434_);
    leanh::lean_ctor_set(v___x_1435_, 2, v___x_1434_);
    leanh::lean_ctor_set(v___x_1435_, 3, v___x_1434_);
    leanh::lean_ctor_set(v___x_1435_, 4, v___x_1433_);
    leanh::lean_ctor_set(v___x_1435_, 5, v___x_1433_);
    leanh::lean_ctor_set(v___x_1435_, 6, v___x_1433_);
    leanh::lean_ctor_set(v___x_1435_, 7, v___x_1433_);
    leanh::lean_ctor_set(v___x_1435_, 8, v___x_1433_);
    leanh::lean_ctor_set(v___x_1435_, 9, v___x_1433_);
    return v___x_1435_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1436_ = leanh::lean_unsigned_to_nat(32);
    v___x_1437_ = lean_mk_empty_array_with_capacity(v___x_1436_);
    v___x_1438_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1438_, 0, v___x_1437_);
    return v___x_1438_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1439_: usize = 0;
    let mut v___x_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1439_ = 5usize;
    v___x_1440_ = leanh::lean_unsigned_to_nat(0);
    v___x_1441_ = leanh::lean_unsigned_to_nat(32);
    v___x_1442_ = lean_mk_empty_array_with_capacity(v___x_1441_);
    v___x_1443_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3);
    v___x_1444_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_1444_, 0, v___x_1443_);
    leanh::lean_ctor_set(v___x_1444_, 1, v___x_1442_);
    leanh::lean_ctor_set(v___x_1444_, 2, v___x_1440_);
    leanh::lean_ctor_set(v___x_1444_, 3, v___x_1440_);
    leanh::lean_ctor_set_usize(v___x_1444_, 4, v___x_1439_);
    return v___x_1444_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1445_ = leanh::lean_box(1);
    v___x_1446_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4);
    v___x_1447_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1);
    v___x_1448_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1448_, 0, v___x_1447_);
    leanh::lean_ctor_set(v___x_1448_, 1, v___x_1446_);
    leanh::lean_ctor_set(v___x_1448_, 2, v___x_1445_);
    return v___x_1448_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2(
    mut v_msgData_1449_: *mut leanh::LeanObject,
    mut v___y_1450_: *mut leanh::LeanObject,
    mut v___y_1451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1453_ = lean_st_ref_get(v___y_1451_);
    v_env_1454_ = leanh::lean_ctor_get(v___x_1453_, 0);
    leanh::lean_inc_ref(v_env_1454_);
    leanh::lean_dec(v___x_1453_);
    v_options_1455_ = leanh::lean_ctor_get(v___y_1450_, 2);
    v___x_1456_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2);
    v___x_1457_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5);
    leanh::lean_inc_ref(v_options_1455_);
    v___x_1458_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1458_, 0, v_env_1454_);
    leanh::lean_ctor_set(v___x_1458_, 1, v___x_1456_);
    leanh::lean_ctor_set(v___x_1458_, 2, v___x_1457_);
    leanh::lean_ctor_set(v___x_1458_, 3, v_options_1455_);
    v___x_1459_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1459_, 0, v___x_1458_);
    leanh::lean_ctor_set(v___x_1459_, 1, v_msgData_1449_);
    v___x_1460_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1460_, 0, v___x_1459_);
    return v___x_1460_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___boxed(
    mut v_msgData_1461_: *mut leanh::LeanObject,
    mut v___y_1462_: *mut leanh::LeanObject,
    mut v___y_1463_: *mut leanh::LeanObject,
    mut v___y_1464_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1465_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2(v_msgData_1461_, v___y_1462_, v___y_1463_);
    leanh::lean_dec(v___y_1463_);
    leanh::lean_dec_ref(v___y_1462_);
    return v_res_1465_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(
    mut v_msg_1466_: *mut leanh::LeanObject,
    mut v___y_1467_: *mut leanh::LeanObject,
    mut v___y_1468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1475_: u8 = 0;
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1470_ = leanh::lean_ctor_get(v___y_1467_, 5);
                v___x_1471_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2(v_msg_1466_, v___y_1467_, v___y_1468_);
                v_a_1472_ = leanh::lean_ctor_get(v___x_1471_, 0);
                v_isSharedCheck_1480_ = (!leanh::lean_is_exclusive(v___x_1471_)) as u8;
                if v_isSharedCheck_1480_ == 0 {
                    v___x_1474_ = v___x_1471_;
                    v_isShared_1475_ = v_isSharedCheck_1480_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1472_);
                    leanh::lean_dec(v___x_1471_);
                    v___x_1474_ = leanh::lean_box(0);
                    v_isShared_1475_ = v_isSharedCheck_1480_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1470_);
                v___x_1476_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1476_, 0, v_ref_1470_);
                leanh::lean_ctor_set(v___x_1476_, 1, v_a_1472_);
                if v_isShared_1475_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1474_, 1);
                    leanh::lean_ctor_set(v___x_1474_, 0, v___x_1476_);
                    v___x_1478_ = v___x_1474_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1479_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
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
    mut v_msg_1481_: *mut leanh::LeanObject,
    mut v___y_1482_: *mut leanh::LeanObject,
    mut v___y_1483_: *mut leanh::LeanObject,
    mut v___y_1484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1485_ = l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(
        v_msg_1481_,
        v___y_1482_,
        v___y_1483_,
    );
    leanh::lean_dec(v___y_1483_);
    leanh::lean_dec_ref(v___y_1482_);
    return v_res_1485_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1487_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0;
    v___x_1488_ = l_Lean_stringToMessageData(v___x_1487_);
    return v___x_1488_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1490_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2;
    v___x_1491_ = l_Lean_stringToMessageData(v___x_1490_);
    return v___x_1491_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1493_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4;
    v___x_1494_ = l_Lean_stringToMessageData(v___x_1493_);
    return v___x_1494_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1496_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6;
    v___x_1497_ = l_Lean_stringToMessageData(v___x_1496_);
    return v___x_1497_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1499_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8;
    v___x_1500_ = l_Lean_stringToMessageData(v___x_1499_);
    return v___x_1500_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1502_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10;
    v___x_1503_ = l_Lean_stringToMessageData(v___x_1502_);
    return v___x_1503_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1505_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12;
    v___x_1506_ = l_Lean_stringToMessageData(v___x_1505_);
    return v___x_1506_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(
    mut v_msg_1507_: *mut leanh::LeanObject,
    mut v_declHint_1508_: *mut leanh::LeanObject,
    mut v___y_1509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: u8 = 0;
    let mut v_isExporting_1514_: u8 = 0;
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: u8 = 0;
    let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1536_: u8 = 0;
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: u8 = 0;
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1568_: u8 = 0;
    let mut v___x_1569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1511_ = lean_st_ref_get(v___y_1509_);
                v_env_1512_ = leanh::lean_ctor_get(v___x_1511_, 0);
                leanh::lean_inc_ref(v_env_1512_);
                leanh::lean_dec(v___x_1511_);
                v___x_1513_ = l_Lean_Name_isAnonymous(v_declHint_1508_);
                if v___x_1513_ == 0 {
                    v_isExporting_1514_ = leanh::lean_ctor_get_uint8(
                        v_env_1512_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1514_ == 0 {
                        leanh::lean_dec_ref(v_env_1512_);
                        leanh::lean_dec(v_declHint_1508_);
                        v___x_1515_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_1515_, 0, v_msg_1507_);
                        return v___x_1515_;
                    } else {
                        leanh::lean_inc_ref(v_env_1512_);
                        v___x_1516_ = l_Lean_Environment_setExporting(v_env_1512_, v___x_1513_);
                        leanh::lean_inc(v_declHint_1508_);
                        leanh::lean_inc_ref(v___x_1516_);
                        v___x_1517_ = l_Lean_Environment_contains(
                            v___x_1516_,
                            v_declHint_1508_,
                            v_isExporting_1514_,
                        );
                        if v___x_1517_ == 0 {
                            leanh::lean_dec_ref(v___x_1516_);
                            leanh::lean_dec_ref(v_env_1512_);
                            leanh::lean_dec(v_declHint_1508_);
                            v___x_1518_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1518_, 0, v_msg_1507_);
                            return v___x_1518_;
                        } else {
                            v___x_1519_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2);
                            v___x_1520_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5);
                            v___x_1521_ = l_Lean_Options_empty;
                            v___x_1522_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_1522_, 0, v___x_1516_);
                            leanh::lean_ctor_set(v___x_1522_, 1, v___x_1519_);
                            leanh::lean_ctor_set(v___x_1522_, 2, v___x_1520_);
                            leanh::lean_ctor_set(v___x_1522_, 3, v___x_1521_);
                            leanh::lean_inc(v_declHint_1508_);
                            v___x_1523_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1508_, v___x_1513_);
                            v_c_1524_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_1524_, 0, v___x_1522_);
                            leanh::lean_ctor_set(v_c_1524_, 1, v___x_1523_);
                            v___x_1525_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1512_,
                                v_declHint_1508_,
                            );
                            if leanh::lean_obj_tag(v___x_1525_) == 0 {
                                leanh::lean_dec_ref(v_env_1512_);
                                leanh::lean_dec(v_declHint_1508_);
                                v___x_1526_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
                                v___x_1527_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1527_, 0, v___x_1526_);
                                leanh::lean_ctor_set(v___x_1527_, 1, v_c_1524_);
                                v___x_1528_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
                                v___x_1529_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1529_, 0, v___x_1527_);
                                leanh::lean_ctor_set(v___x_1529_, 1, v___x_1528_);
                                v___x_1530_ = l_Lean_MessageData_note(v___x_1529_);
                                v___x_1531_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_1531_, 0, v_msg_1507_);
                                leanh::lean_ctor_set(v___x_1531_, 1, v___x_1530_);
                                v___x_1532_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_1532_, 0, v___x_1531_);
                                return v___x_1532_;
                            } else {
                                v_val_1533_ = leanh::lean_ctor_get(v___x_1525_, 0);
                                v_isSharedCheck_1568_ =
                                    (!leanh::lean_is_exclusive(v___x_1525_)) as u8;
                                if v_isSharedCheck_1568_ == 0 {
                                    v___x_1535_ = v___x_1525_;
                                    v_isShared_1536_ = v_isSharedCheck_1568_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_1533_);
                                    leanh::lean_dec(v___x_1525_);
                                    v___x_1535_ = leanh::lean_box(0);
                                    v_isShared_1536_ = v_isSharedCheck_1568_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_1512_);
                    leanh::lean_dec(v_declHint_1508_);
                    v___x_1569_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1569_, 0, v_msg_1507_);
                    return v___x_1569_;
                }
            }
            1 => {
                v___x_1537_ = leanh::lean_box(0);
                v___x_1538_ = l_Lean_Environment_header(v_env_1512_);
                leanh::lean_dec_ref(v_env_1512_);
                v___x_1539_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1538_);
                v_mod_1540_ = lean_array_get(v___x_1537_, v___x_1539_, v_val_1533_);
                leanh::lean_dec(v_val_1533_);
                leanh::lean_dec_ref(v___x_1539_);
                v___x_1541_ = l_Lean_isPrivateName(v_declHint_1508_);
                leanh::lean_dec(v_declHint_1508_);
                if v___x_1541_ == 0 {
                    v___x_1542_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
                    v___x_1543_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1543_, 0, v___x_1542_);
                    leanh::lean_ctor_set(v___x_1543_, 1, v_c_1524_);
                    v___x_1544_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
                    v___x_1545_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1545_, 0, v___x_1543_);
                    leanh::lean_ctor_set(v___x_1545_, 1, v___x_1544_);
                    v___x_1546_ = l_Lean_MessageData_ofName(v_mod_1540_);
                    v___x_1547_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1547_, 0, v___x_1545_);
                    leanh::lean_ctor_set(v___x_1547_, 1, v___x_1546_);
                    v___x_1548_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
                    v___x_1549_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1549_, 0, v___x_1547_);
                    leanh::lean_ctor_set(v___x_1549_, 1, v___x_1548_);
                    v___x_1550_ = l_Lean_MessageData_note(v___x_1549_);
                    v___x_1551_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1551_, 0, v_msg_1507_);
                    leanh::lean_ctor_set(v___x_1551_, 1, v___x_1550_);
                    if v_isShared_1536_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1535_, 0);
                        leanh::lean_ctor_set(v___x_1535_, 0, v___x_1551_);
                        v___x_1553_ = v___x_1535_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1554_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
                        v___x_1553_ = v_reuseFailAlloc_1554_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1555_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
                    v___x_1556_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1556_, 0, v___x_1555_);
                    leanh::lean_ctor_set(v___x_1556_, 1, v_c_1524_);
                    v___x_1557_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
                    v___x_1558_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1558_, 0, v___x_1556_);
                    leanh::lean_ctor_set(v___x_1558_, 1, v___x_1557_);
                    v___x_1559_ = l_Lean_MessageData_ofName(v_mod_1540_);
                    v___x_1560_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1560_, 0, v___x_1558_);
                    leanh::lean_ctor_set(v___x_1560_, 1, v___x_1559_);
                    v___x_1561_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
                    v___x_1562_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1562_, 0, v___x_1560_);
                    leanh::lean_ctor_set(v___x_1562_, 1, v___x_1561_);
                    v___x_1563_ = l_Lean_MessageData_note(v___x_1562_);
                    v___x_1564_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1564_, 0, v_msg_1507_);
                    leanh::lean_ctor_set(v___x_1564_, 1, v___x_1563_);
                    if v_isShared_1536_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1535_, 0);
                        leanh::lean_ctor_set(v___x_1535_, 0, v___x_1564_);
                        v___x_1566_ = v___x_1535_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1567_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
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
    mut v_msg_1570_: *mut leanh::LeanObject,
    mut v_declHint_1571_: *mut leanh::LeanObject,
    mut v___y_1572_: *mut leanh::LeanObject,
    mut v___y_1573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1574_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1570_, v_declHint_1571_, v___y_1572_);
    leanh::lean_dec(v___y_1572_);
    return v_res_1574_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(
    mut v_msg_1575_: *mut leanh::LeanObject,
    mut v_declHint_1576_: *mut leanh::LeanObject,
    mut v___y_1577_: *mut leanh::LeanObject,
    mut v___y_1578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1584_: u8 = 0;
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1590_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1580_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1575_, v_declHint_1576_, v___y_1578_);
                v_a_1581_ = leanh::lean_ctor_get(v___x_1580_, 0);
                v_isSharedCheck_1590_ = (!leanh::lean_is_exclusive(v___x_1580_)) as u8;
                if v_isSharedCheck_1590_ == 0 {
                    v___x_1583_ = v___x_1580_;
                    v_isShared_1584_ = v_isSharedCheck_1590_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1581_);
                    leanh::lean_dec(v___x_1580_);
                    v___x_1583_ = leanh::lean_box(0);
                    v_isShared_1584_ = v_isSharedCheck_1590_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1585_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1586_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1586_, 0, v___x_1585_);
                leanh::lean_ctor_set(v___x_1586_, 1, v_a_1581_);
                if v_isShared_1584_ == 0 {
                    leanh::lean_ctor_set(v___x_1583_, 0, v___x_1586_);
                    v___x_1588_ = v___x_1583_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1589_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
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
    mut v_msg_1591_: *mut leanh::LeanObject,
    mut v_declHint_1592_: *mut leanh::LeanObject,
    mut v___y_1593_: *mut leanh::LeanObject,
    mut v___y_1594_: *mut leanh::LeanObject,
    mut v___y_1595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1596_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1591_, v_declHint_1592_, v___y_1593_, v___y_1594_);
    leanh::lean_dec(v___y_1594_);
    leanh::lean_dec_ref(v___y_1593_);
    return v_res_1596_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(
    mut v_ref_1597_: *mut leanh::LeanObject,
    mut v_msg_1598_: *mut leanh::LeanObject,
    mut v___y_1599_: *mut leanh::LeanObject,
    mut v___y_1600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1614_: u8 = 0;
    let mut v_cancelTk_x3f_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1616_: u8 = 0;
    let mut v_inheritedTraceOptions_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_1618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_1602_ = leanh::lean_ctor_get(v___y_1599_, 0);
    v_fileMap_1603_ = leanh::lean_ctor_get(v___y_1599_, 1);
    v_options_1604_ = leanh::lean_ctor_get(v___y_1599_, 2);
    v_currRecDepth_1605_ = leanh::lean_ctor_get(v___y_1599_, 3);
    v_maxRecDepth_1606_ = leanh::lean_ctor_get(v___y_1599_, 4);
    v_ref_1607_ = leanh::lean_ctor_get(v___y_1599_, 5);
    v_currNamespace_1608_ = leanh::lean_ctor_get(v___y_1599_, 6);
    v_openDecls_1609_ = leanh::lean_ctor_get(v___y_1599_, 7);
    v_initHeartbeats_1610_ = leanh::lean_ctor_get(v___y_1599_, 8);
    v_maxHeartbeats_1611_ = leanh::lean_ctor_get(v___y_1599_, 9);
    v_quotContext_1612_ = leanh::lean_ctor_get(v___y_1599_, 10);
    v_currMacroScope_1613_ = leanh::lean_ctor_get(v___y_1599_, 11);
    v_diag_1614_ = leanh::lean_ctor_get_uint8(
        v___y_1599_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1615_ = leanh::lean_ctor_get(v___y_1599_, 12);
    v_suppressElabErrors_1616_ = leanh::lean_ctor_get_uint8(
        v___y_1599_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1617_ = leanh::lean_ctor_get(v___y_1599_, 13);
    v_ref_1618_ = l_Lean_replaceRef(v_ref_1597_, v_ref_1607_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_1617_);
    leanh::lean_inc(v_cancelTk_x3f_1615_);
    leanh::lean_inc(v_currMacroScope_1613_);
    leanh::lean_inc(v_quotContext_1612_);
    leanh::lean_inc(v_maxHeartbeats_1611_);
    leanh::lean_inc(v_initHeartbeats_1610_);
    leanh::lean_inc(v_openDecls_1609_);
    leanh::lean_inc(v_currNamespace_1608_);
    leanh::lean_inc(v_maxRecDepth_1606_);
    leanh::lean_inc(v_currRecDepth_1605_);
    leanh::lean_inc_ref(v_options_1604_);
    leanh::lean_inc_ref(v_fileMap_1603_);
    leanh::lean_inc_ref(v_fileName_1602_);
    v___x_1619_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_1619_, 0, v_fileName_1602_);
    leanh::lean_ctor_set(v___x_1619_, 1, v_fileMap_1603_);
    leanh::lean_ctor_set(v___x_1619_, 2, v_options_1604_);
    leanh::lean_ctor_set(v___x_1619_, 3, v_currRecDepth_1605_);
    leanh::lean_ctor_set(v___x_1619_, 4, v_maxRecDepth_1606_);
    leanh::lean_ctor_set(v___x_1619_, 5, v_ref_1618_);
    leanh::lean_ctor_set(v___x_1619_, 6, v_currNamespace_1608_);
    leanh::lean_ctor_set(v___x_1619_, 7, v_openDecls_1609_);
    leanh::lean_ctor_set(v___x_1619_, 8, v_initHeartbeats_1610_);
    leanh::lean_ctor_set(v___x_1619_, 9, v_maxHeartbeats_1611_);
    leanh::lean_ctor_set(v___x_1619_, 10, v_quotContext_1612_);
    leanh::lean_ctor_set(v___x_1619_, 11, v_currMacroScope_1613_);
    leanh::lean_ctor_set(v___x_1619_, 12, v_cancelTk_x3f_1615_);
    leanh::lean_ctor_set(v___x_1619_, 13, v_inheritedTraceOptions_1617_);
    leanh::lean_ctor_set_uint8(
        v___x_1619_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_1614_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1619_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1616_,
    );
    v___x_1620_ = l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(
        v_msg_1598_,
        v___x_1619_,
        v___y_1600_,
    );
    leanh::lean_dec_ref_known(v___x_1619_, 14);
    return v___x_1620_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(
    mut v_ref_1621_: *mut leanh::LeanObject,
    mut v_msg_1622_: *mut leanh::LeanObject,
    mut v___y_1623_: *mut leanh::LeanObject,
    mut v___y_1624_: *mut leanh::LeanObject,
    mut v___y_1625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1626_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1621_, v_msg_1622_, v___y_1623_, v___y_1624_);
    leanh::lean_dec(v___y_1624_);
    leanh::lean_dec_ref(v___y_1623_);
    leanh::lean_dec(v_ref_1621_);
    return v_res_1626_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_ref_1627_: *mut leanh::LeanObject,
    mut v_msg_1628_: *mut leanh::LeanObject,
    mut v_declHint_1629_: *mut leanh::LeanObject,
    mut v___y_1630_: *mut leanh::LeanObject,
    mut v___y_1631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1633_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1628_, v_declHint_1629_, v___y_1630_, v___y_1631_);
    v_a_1634_ = leanh::lean_ctor_get(v___x_1633_, 0);
    leanh::lean_inc(v_a_1634_);
    leanh::lean_dec_ref(v___x_1633_);
    v___x_1635_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1627_, v_a_1634_, v___y_1630_, v___y_1631_);
    return v___x_1635_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_ref_1636_: *mut leanh::LeanObject,
    mut v_msg_1637_: *mut leanh::LeanObject,
    mut v_declHint_1638_: *mut leanh::LeanObject,
    mut v___y_1639_: *mut leanh::LeanObject,
    mut v___y_1640_: *mut leanh::LeanObject,
    mut v___y_1641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1642_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1636_, v_msg_1637_, v_declHint_1638_, v___y_1639_, v___y_1640_);
    leanh::lean_dec(v___y_1640_);
    leanh::lean_dec_ref(v___y_1639_);
    leanh::lean_dec(v_ref_1636_);
    return v_res_1642_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1644_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_1645_ = l_Lean_stringToMessageData(v___x_1644_);
    return v___x_1645_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1647_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_1648_ = l_Lean_stringToMessageData(v___x_1647_);
    return v___x_1648_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg(
    mut v_ref_1649_: *mut leanh::LeanObject,
    mut v_constName_1650_: *mut leanh::LeanObject,
    mut v___y_1651_: *mut leanh::LeanObject,
    mut v___y_1652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: u8 = 0;
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1654_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_1655_ = 0;
    leanh::lean_inc(v_constName_1650_);
    v___x_1656_ = l_Lean_MessageData_ofConstName(v_constName_1650_, v___x_1655_);
    v___x_1657_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1657_, 0, v___x_1654_);
    leanh::lean_ctor_set(v___x_1657_, 1, v___x_1656_);
    v___x_1658_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_1659_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1659_, 0, v___x_1657_);
    leanh::lean_ctor_set(v___x_1659_, 1, v___x_1658_);
    v___x_1660_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1649_, v___x_1659_, v_constName_1650_, v___y_1651_, v___y_1652_);
    return v___x_1660_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_1661_: *mut leanh::LeanObject,
    mut v_constName_1662_: *mut leanh::LeanObject,
    mut v___y_1663_: *mut leanh::LeanObject,
    mut v___y_1664_: *mut leanh::LeanObject,
    mut v___y_1665_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1666_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg(v_ref_1661_, v_constName_1662_, v___y_1663_, v___y_1664_);
    leanh::lean_dec(v___y_1664_);
    leanh::lean_dec_ref(v___y_1663_);
    leanh::lean_dec(v_ref_1661_);
    return v_res_1666_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg(
    mut v_constName_1667_: *mut leanh::LeanObject,
    mut v___y_1668_: *mut leanh::LeanObject,
    mut v___y_1669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_1671_ = leanh::lean_ctor_get(v___y_1668_, 5);
    v___x_1672_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg(v_ref_1671_, v_constName_1667_, v___y_1668_, v___y_1669_);
    return v___x_1672_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg___boxed(
    mut v_constName_1673_: *mut leanh::LeanObject,
    mut v___y_1674_: *mut leanh::LeanObject,
    mut v___y_1675_: *mut leanh::LeanObject,
    mut v___y_1676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1677_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg(v_constName_1673_, v___y_1674_, v___y_1675_);
    leanh::lean_dec(v___y_1675_);
    leanh::lean_dec_ref(v___y_1674_);
    return v_res_1677_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0(
    mut v_constName_1678_: *mut leanh::LeanObject,
    mut v___y_1679_: *mut leanh::LeanObject,
    mut v___y_1680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: u8 = 0;
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1690_: u8 = 0;
    let mut v___x_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1682_ = lean_st_ref_get(v___y_1680_);
                v_env_1683_ = leanh::lean_ctor_get(v___x_1682_, 0);
                leanh::lean_inc_ref(v_env_1683_);
                leanh::lean_dec(v___x_1682_);
                v___x_1684_ = 0;
                leanh::lean_inc(v_constName_1678_);
                v___x_1685_ =
                    l_Lean_Environment_find_x3f(v_env_1683_, v_constName_1678_, v___x_1684_);
                if leanh::lean_obj_tag(v___x_1685_) == 0 {
                    v___x_1686_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg(v_constName_1678_, v___y_1679_, v___y_1680_);
                    return v___x_1686_;
                } else {
                    leanh::lean_dec(v_constName_1678_);
                    v_val_1687_ = leanh::lean_ctor_get(v___x_1685_, 0);
                    v_isSharedCheck_1694_ = (!leanh::lean_is_exclusive(v___x_1685_)) as u8;
                    if v_isSharedCheck_1694_ == 0 {
                        v___x_1689_ = v___x_1685_;
                        v_isShared_1690_ = v_isSharedCheck_1694_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1687_);
                        leanh::lean_dec(v___x_1685_);
                        v___x_1689_ = leanh::lean_box(0);
                        v_isShared_1690_ = v_isSharedCheck_1694_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1690_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1689_, 0);
                    v___x_1692_ = v___x_1689_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1693_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_val_1687_);
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
    mut v_constName_1695_: *mut leanh::LeanObject,
    mut v___y_1696_: *mut leanh::LeanObject,
    mut v___y_1697_: *mut leanh::LeanObject,
    mut v___y_1698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1699_ = l_Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0(
        v_constName_1695_,
        v___y_1696_,
        v___y_1697_,
    );
    leanh::lean_dec(v___y_1697_);
    leanh::lean_dec_ref(v___y_1696_);
    return v_res_1699_;
}
pub unsafe fn _init_l_Lean_Elab_checkCbvSimprocType___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1701_ = l_Lean_Elab_checkCbvSimprocType___closed__0;
    v___x_1702_ = l_Lean_stringToMessageData(v___x_1701_);
    return v___x_1702_;
}
pub unsafe fn _init_l_Lean_Elab_checkCbvSimprocType___closed__8() -> *mut leanh::LeanObject {
    let mut v___x_1714_: u8 = 0;
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1714_ = 0;
    v___x_1715_ = l_Lean_Elab_checkCbvSimprocType___closed__7;
    v___x_1716_ = l_Lean_MessageData_ofConstName(v___x_1715_, v___x_1714_);
    return v___x_1716_;
}
pub unsafe fn _init_l_Lean_Elab_checkCbvSimprocType___closed__9() -> *mut leanh::LeanObject {
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1717_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__8_once),
        _init_l_Lean_Elab_checkCbvSimprocType___closed__8,
    );
    v___x_1718_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__1_once),
        _init_l_Lean_Elab_checkCbvSimprocType___closed__1,
    );
    v___x_1719_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1719_, 0, v___x_1718_);
    leanh::lean_ctor_set(v___x_1719_, 1, v___x_1717_);
    return v___x_1719_;
}
pub unsafe fn _init_l_Lean_Elab_checkCbvSimprocType___closed__11() -> *mut leanh::LeanObject
{
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1721_ = l_Lean_Elab_checkCbvSimprocType___closed__10;
    v___x_1722_ = l_Lean_stringToMessageData(v___x_1721_);
    return v___x_1722_;
}
pub unsafe fn _init_l_Lean_Elab_checkCbvSimprocType___closed__12() -> *mut leanh::LeanObject
{
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1723_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__11_once),
        _init_l_Lean_Elab_checkCbvSimprocType___closed__11,
    );
    v___x_1724_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__9_once),
        _init_l_Lean_Elab_checkCbvSimprocType___closed__9,
    );
    v___x_1725_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1725_, 0, v___x_1724_);
    leanh::lean_ctor_set(v___x_1725_, 1, v___x_1723_);
    return v___x_1725_;
}
pub unsafe fn _init_l_Lean_Elab_checkCbvSimprocType___closed__14() -> *mut leanh::LeanObject
{
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1727_ = l_Lean_Elab_checkCbvSimprocType___closed__13;
    v___x_1728_ = l_Lean_stringToMessageData(v___x_1727_);
    return v___x_1728_;
}
pub unsafe fn l_Lean_Elab_checkCbvSimprocType(
    mut v_declName_1729_: *mut leanh::LeanObject,
    mut v_a_1730_: *mut leanh::LeanObject,
    mut v_a_1731_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1737_: u8 = 0;
    let mut v___y_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: u8 = 0;
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: u8 = 0;
    let mut v___x_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: u8 = 0;
    let mut v___x_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: u8 = 0;
    let mut v___x_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1776_: u8 = 0;
    let mut v_a_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1780_: u8 = 0;
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1784_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_declName_1729_);
                v___x_1733_ = l_Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0(
                    v_declName_1729_,
                    v_a_1730_,
                    v_a_1731_,
                );
                if leanh::lean_obj_tag(v___x_1733_) == 0 {
                    v_a_1734_ = leanh::lean_ctor_get(v___x_1733_, 0);
                    v_isSharedCheck_1776_ = (!leanh::lean_is_exclusive(v___x_1733_)) as u8;
                    if v_isSharedCheck_1776_ == 0 {
                        v___x_1736_ = v___x_1733_;
                        v_isShared_1737_ = v_isSharedCheck_1776_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1734_);
                        leanh::lean_dec(v___x_1733_);
                        v___x_1736_ = leanh::lean_box(0);
                        v_isShared_1737_ = v_isSharedCheck_1776_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_declName_1729_);
                    v_a_1777_ = leanh::lean_ctor_get(v___x_1733_, 0);
                    v_isSharedCheck_1784_ = (!leanh::lean_is_exclusive(v___x_1733_)) as u8;
                    if v_isSharedCheck_1784_ == 0 {
                        v___x_1779_ = v___x_1733_;
                        v_isShared_1780_ = v_isSharedCheck_1784_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1777_);
                        leanh::lean_dec(v___x_1733_);
                        v___x_1779_ = leanh::lean_box(0);
                        v_isShared_1780_ = v_isSharedCheck_1784_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1750_ = l_Lean_ConstantInfo_type(v_a_1734_);
                if leanh::lean_obj_tag(v___x_1750_) == 4 {
                    v_declName_1751_ = leanh::lean_ctor_get(v___x_1750_, 0);
                    leanh::lean_inc(v_declName_1751_);
                    leanh::lean_dec_ref_known(v___x_1750_, 2);
                    if leanh::lean_obj_tag(v_declName_1751_) == 1 {
                        v_pre_1752_ = leanh::lean_ctor_get(v_declName_1751_, 0);
                        leanh::lean_inc(v_pre_1752_);
                        if leanh::lean_obj_tag(v_pre_1752_) == 1 {
                            v_pre_1753_ = leanh::lean_ctor_get(v_pre_1752_, 0);
                            leanh::lean_inc(v_pre_1753_);
                            if leanh::lean_obj_tag(v_pre_1753_) == 1 {
                                v_pre_1754_ = leanh::lean_ctor_get(v_pre_1753_, 0);
                                leanh::lean_inc(v_pre_1754_);
                                if leanh::lean_obj_tag(v_pre_1754_) == 1 {
                                    v_pre_1755_ = leanh::lean_ctor_get(v_pre_1754_, 0);
                                    leanh::lean_inc(v_pre_1755_);
                                    if leanh::lean_obj_tag(v_pre_1755_) == 1 {
                                        v_pre_1756_ = leanh::lean_ctor_get(v_pre_1755_, 0);
                                        if leanh::lean_obj_tag(v_pre_1756_) == 0 {
                                            v_str_1757_ =
                                                leanh::lean_ctor_get(v_declName_1751_, 1);
                                            leanh::lean_inc_ref(v_str_1757_);
                                            leanh::lean_dec_ref_known(v_declName_1751_, 2);
                                            v_str_1758_ =
                                                leanh::lean_ctor_get(v_pre_1752_, 1);
                                            leanh::lean_inc_ref(v_str_1758_);
                                            leanh::lean_dec_ref_known(v_pre_1752_, 2);
                                            v_str_1759_ =
                                                leanh::lean_ctor_get(v_pre_1753_, 1);
                                            leanh::lean_inc_ref(v_str_1759_);
                                            leanh::lean_dec_ref_known(v_pre_1753_, 2);
                                            v_str_1760_ =
                                                leanh::lean_ctor_get(v_pre_1754_, 1);
                                            leanh::lean_inc_ref(v_str_1760_);
                                            leanh::lean_dec_ref_known(v_pre_1754_, 2);
                                            v_str_1761_ =
                                                leanh::lean_ctor_get(v_pre_1755_, 1);
                                            leanh::lean_inc_ref(v_str_1761_);
                                            leanh::lean_dec_ref_known(v_pre_1755_, 2);
                                            v___x_1762_ =
                                                l_Lean_Elab_checkCbvSimprocType___closed__2;
                                            v___x_1763_ =
                                                lean_string_dec_eq(v_str_1761_, v___x_1762_);
                                            leanh::lean_dec_ref(v_str_1761_);
                                            if v___x_1763_ == 0 {
                                                leanh::lean_dec_ref(v_str_1760_);
                                                leanh::lean_dec_ref(v_str_1759_);
                                                leanh::lean_dec_ref(v_str_1758_);
                                                leanh::lean_dec_ref(v_str_1757_);
                                                leanh::lean_del_object(v___x_1736_);
                                                v___y_1739_ = v_a_1730_;
                                                v___y_1740_ = v_a_1731_;
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_1764_ =
                                                    l_Lean_Elab_checkCbvSimprocType___closed__3;
                                                v___x_1765_ =
                                                    lean_string_dec_eq(v_str_1760_, v___x_1764_);
                                                leanh::lean_dec_ref(v_str_1760_);
                                                if v___x_1765_ == 0 {
                                                    leanh::lean_dec_ref(v_str_1759_);
                                                    leanh::lean_dec_ref(v_str_1758_);
                                                    leanh::lean_dec_ref(v_str_1757_);
                                                    leanh::lean_del_object(v___x_1736_);
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
                                                    leanh::lean_dec_ref(v_str_1759_);
                                                    if v___x_1767_ == 0 {
                                                        leanh::lean_dec_ref(v_str_1758_);
                                                        leanh::lean_dec_ref(v_str_1757_);
                                                        leanh::lean_del_object(v___x_1736_);
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
                                                        leanh::lean_dec_ref(v_str_1758_);
                                                        if v___x_1769_ == 0 {
                                                            leanh::lean_dec_ref(v_str_1757_);
                                                            leanh::lean_del_object(
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
                                                            leanh::lean_dec_ref(v_str_1757_);
                                                            if v___x_1771_ == 0 {
                                                                leanh::lean_del_object(
                                                                    v___x_1736_,
                                                                );
                                                                v___y_1739_ = v_a_1730_;
                                                                v___y_1740_ = v_a_1731_;
                                                                state = 2;
                                                                continue;
                                                            } else {
                                                                leanh::lean_dec(v_a_1734_);
                                                                leanh::lean_dec(
                                                                    v_declName_1729_,
                                                                );
                                                                v___x_1772_ =
                                                                    leanh::lean_box(0);
                                                                if v_isShared_1737_ == 0 {
                                                                    leanh::lean_ctor_set(
                                                                        v___x_1736_,
                                                                        0,
                                                                        v___x_1772_,
                                                                    );
                                                                    v___x_1774_ = v___x_1736_;
                                                                    state = 3;
                                                                    continue;
                                                                } else {
                                                                    v_reuseFailAlloc_1775_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                    leanh::lean_ctor_set(
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
                                            leanh::lean_dec_ref_known(v_pre_1755_, 2);
                                            leanh::lean_dec_ref_known(v_pre_1754_, 2);
                                            leanh::lean_dec_ref_known(v_pre_1753_, 2);
                                            leanh::lean_dec_ref_known(v_pre_1752_, 2);
                                            leanh::lean_dec_ref_known(v_declName_1751_, 2);
                                            leanh::lean_del_object(v___x_1736_);
                                            v___y_1739_ = v_a_1730_;
                                            v___y_1740_ = v_a_1731_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec_ref_known(v_pre_1754_, 2);
                                        leanh::lean_dec(v_pre_1755_);
                                        leanh::lean_dec_ref_known(v_pre_1753_, 2);
                                        leanh::lean_dec_ref_known(v_pre_1752_, 2);
                                        leanh::lean_dec_ref_known(v_declName_1751_, 2);
                                        leanh::lean_del_object(v___x_1736_);
                                        v___y_1739_ = v_a_1730_;
                                        v___y_1740_ = v_a_1731_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_pre_1754_);
                                    leanh::lean_dec_ref_known(v_pre_1753_, 2);
                                    leanh::lean_dec_ref_known(v_pre_1752_, 2);
                                    leanh::lean_dec_ref_known(v_declName_1751_, 2);
                                    leanh::lean_del_object(v___x_1736_);
                                    v___y_1739_ = v_a_1730_;
                                    v___y_1740_ = v_a_1731_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref_known(v_pre_1752_, 2);
                                leanh::lean_dec(v_pre_1753_);
                                leanh::lean_dec_ref_known(v_declName_1751_, 2);
                                leanh::lean_del_object(v___x_1736_);
                                v___y_1739_ = v_a_1730_;
                                v___y_1740_ = v_a_1731_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref_known(v_declName_1751_, 2);
                            leanh::lean_dec(v_pre_1752_);
                            leanh::lean_del_object(v___x_1736_);
                            v___y_1739_ = v_a_1730_;
                            v___y_1740_ = v_a_1731_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_declName_1751_);
                        leanh::lean_del_object(v___x_1736_);
                        v___y_1739_ = v_a_1730_;
                        v___y_1740_ = v_a_1731_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_1750_);
                    leanh::lean_del_object(v___x_1736_);
                    v___y_1739_ = v_a_1730_;
                    v___y_1740_ = v_a_1731_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1741_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__12),
                    core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__12_once),
                    _init_l_Lean_Elab_checkCbvSimprocType___closed__12,
                );
                v___x_1742_ = l_Lean_MessageData_ofName(v_declName_1729_);
                v___x_1743_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1743_, 0, v___x_1741_);
                leanh::lean_ctor_set(v___x_1743_, 1, v___x_1742_);
                v___x_1744_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__14),
                    core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__14_once),
                    _init_l_Lean_Elab_checkCbvSimprocType___closed__14,
                );
                v___x_1745_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1745_, 0, v___x_1743_);
                leanh::lean_ctor_set(v___x_1745_, 1, v___x_1744_);
                v___x_1746_ = l_Lean_ConstantInfo_type(v_a_1734_);
                leanh::lean_dec(v_a_1734_);
                v___x_1747_ = l_Lean_indentExpr(v___x_1746_);
                v___x_1748_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1748_, 0, v___x_1745_);
                leanh::lean_ctor_set(v___x_1748_, 1, v___x_1747_);
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
                    v_reuseFailAlloc_1783_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
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
    mut v_declName_1785_: *mut leanh::LeanObject,
    mut v_a_1786_: *mut leanh::LeanObject,
    mut v_a_1787_: *mut leanh::LeanObject,
    mut v_a_1788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1789_ = l_Lean_Elab_checkCbvSimprocType(v_declName_1785_, v_a_1786_, v_a_1787_);
    leanh::lean_dec(v_a_1787_);
    leanh::lean_dec_ref(v_a_1786_);
    return v_res_1789_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1(
    mut v_00_u03b1_1790_: *mut leanh::LeanObject,
    mut v_msg_1791_: *mut leanh::LeanObject,
    mut v___y_1792_: *mut leanh::LeanObject,
    mut v___y_1793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1795_ = l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(
        v_msg_1791_,
        v___y_1792_,
        v___y_1793_,
    );
    return v___x_1795_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___boxed(
    mut v_00_u03b1_1796_: *mut leanh::LeanObject,
    mut v_msg_1797_: *mut leanh::LeanObject,
    mut v___y_1798_: *mut leanh::LeanObject,
    mut v___y_1799_: *mut leanh::LeanObject,
    mut v___y_1800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1801_ = l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1(
        v_00_u03b1_1796_,
        v_msg_1797_,
        v___y_1798_,
        v___y_1799_,
    );
    leanh::lean_dec(v___y_1799_);
    leanh::lean_dec_ref(v___y_1798_);
    return v_res_1801_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0(
    mut v_00_u03b1_1802_: *mut leanh::LeanObject,
    mut v_constName_1803_: *mut leanh::LeanObject,
    mut v___y_1804_: *mut leanh::LeanObject,
    mut v___y_1805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1807_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg(v_constName_1803_, v___y_1804_, v___y_1805_);
    return v___x_1807_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___boxed(
    mut v_00_u03b1_1808_: *mut leanh::LeanObject,
    mut v_constName_1809_: *mut leanh::LeanObject,
    mut v___y_1810_: *mut leanh::LeanObject,
    mut v___y_1811_: *mut leanh::LeanObject,
    mut v___y_1812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1813_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0(v_00_u03b1_1808_, v_constName_1809_, v___y_1810_, v___y_1811_);
    leanh::lean_dec(v___y_1811_);
    leanh::lean_dec_ref(v___y_1810_);
    return v_res_1813_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1(
    mut v_00_u03b1_1814_: *mut leanh::LeanObject,
    mut v_ref_1815_: *mut leanh::LeanObject,
    mut v_constName_1816_: *mut leanh::LeanObject,
    mut v___y_1817_: *mut leanh::LeanObject,
    mut v___y_1818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1820_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg(v_ref_1815_, v_constName_1816_, v___y_1817_, v___y_1818_);
    return v___x_1820_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_1821_: *mut leanh::LeanObject,
    mut v_ref_1822_: *mut leanh::LeanObject,
    mut v_constName_1823_: *mut leanh::LeanObject,
    mut v___y_1824_: *mut leanh::LeanObject,
    mut v___y_1825_: *mut leanh::LeanObject,
    mut v___y_1826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1827_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1(v_00_u03b1_1821_, v_ref_1822_, v_constName_1823_, v___y_1824_, v___y_1825_);
    leanh::lean_dec(v___y_1825_);
    leanh::lean_dec_ref(v___y_1824_);
    leanh::lean_dec(v_ref_1822_);
    return v_res_1827_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_1828_: *mut leanh::LeanObject,
    mut v_ref_1829_: *mut leanh::LeanObject,
    mut v_msg_1830_: *mut leanh::LeanObject,
    mut v_declHint_1831_: *mut leanh::LeanObject,
    mut v___y_1832_: *mut leanh::LeanObject,
    mut v___y_1833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1835_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1829_, v_msg_1830_, v_declHint_1831_, v___y_1832_, v___y_1833_);
    return v___x_1835_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b1_1836_: *mut leanh::LeanObject,
    mut v_ref_1837_: *mut leanh::LeanObject,
    mut v_msg_1838_: *mut leanh::LeanObject,
    mut v_declHint_1839_: *mut leanh::LeanObject,
    mut v___y_1840_: *mut leanh::LeanObject,
    mut v___y_1841_: *mut leanh::LeanObject,
    mut v___y_1842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1843_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1836_, v_ref_1837_, v_msg_1838_, v_declHint_1839_, v___y_1840_, v___y_1841_);
    leanh::lean_dec(v___y_1841_);
    leanh::lean_dec_ref(v___y_1840_);
    leanh::lean_dec(v_ref_1837_);
    return v_res_1843_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(
    mut v_msg_1844_: *mut leanh::LeanObject,
    mut v_declHint_1845_: *mut leanh::LeanObject,
    mut v___y_1846_: *mut leanh::LeanObject,
    mut v___y_1847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1849_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1844_, v_declHint_1845_, v___y_1847_);
    return v___x_1849_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(
    mut v_msg_1850_: *mut leanh::LeanObject,
    mut v_declHint_1851_: *mut leanh::LeanObject,
    mut v___y_1852_: *mut leanh::LeanObject,
    mut v___y_1853_: *mut leanh::LeanObject,
    mut v___y_1854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1855_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1850_, v_declHint_1851_, v___y_1852_, v___y_1853_);
    leanh::lean_dec(v___y_1853_);
    leanh::lean_dec_ref(v___y_1852_);
    return v_res_1855_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6(
    mut v_00_u03b1_1856_: *mut leanh::LeanObject,
    mut v_ref_1857_: *mut leanh::LeanObject,
    mut v_msg_1858_: *mut leanh::LeanObject,
    mut v___y_1859_: *mut leanh::LeanObject,
    mut v___y_1860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1862_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1857_, v_msg_1858_, v___y_1859_, v___y_1860_);
    return v___x_1862_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(
    mut v_00_u03b1_1863_: *mut leanh::LeanObject,
    mut v_ref_1864_: *mut leanh::LeanObject,
    mut v_msg_1865_: *mut leanh::LeanObject,
    mut v___y_1866_: *mut leanh::LeanObject,
    mut v___y_1867_: *mut leanh::LeanObject,
    mut v___y_1868_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1869_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_1863_, v_ref_1864_, v_msg_1865_, v___y_1866_, v___y_1867_);
    leanh::lean_dec(v___y_1867_);
    leanh::lean_dec_ref(v___y_1866_);
    leanh::lean_dec(v_ref_1864_);
    return v_res_1869_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1870_ = leanh::lean_box(0);
    v___x_1871_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1872_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1872_, 0, v___x_1871_);
    leanh::lean_ctor_set(v___x_1872_, 1, v___x_1870_);
    return v___x_1872_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg()
-> *mut leanh::LeanObject {
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1874_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0);
    v___x_1875_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1875_, 0, v___x_1874_);
    return v___x_1875_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___boxed(
    mut v___y_1876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1877_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg();
    return v_res_1877_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0(
    mut v_00_u03b1_1878_: *mut leanh::LeanObject,
    mut v___y_1879_: *mut leanh::LeanObject,
    mut v___y_1880_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1882_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg();
    return v___x_1882_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___boxed(
    mut v_00_u03b1_1883_: *mut leanh::LeanObject,
    mut v___y_1884_: *mut leanh::LeanObject,
    mut v___y_1885_: *mut leanh::LeanObject,
    mut v___y_1886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1887_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0(
            v_00_u03b1_1883_,
            v___y_1884_,
            v___y_1885_,
        );
    leanh::lean_dec(v___y_1885_);
    leanh::lean_dec_ref(v___y_1884_);
    return v_res_1887_;
}
pub unsafe fn l_Lean_Elab_Command_elabCbvSimprocPattern___lam__0(
    mut v___x_1888_: *mut leanh::LeanObject,
    mut v___x_1889_: *mut leanh::LeanObject,
    mut v___y_1890_: *mut leanh::LeanObject,
    mut v___y_1891_: *mut leanh::LeanObject,
    mut v___y_1892_: *mut leanh::LeanObject,
    mut v___y_1893_: *mut leanh::LeanObject,
    mut v___y_1894_: *mut leanh::LeanObject,
    mut v___y_1895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1906_: u8 = 0;
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1910_: u8 = 0;
    let mut v_a_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1914_: u8 = 0;
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1918_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1897_ =
                    l_Lean_realizeGlobalConstNoOverload(v___x_1888_, v___y_1894_, v___y_1895_);
                if leanh::lean_obj_tag(v___x_1897_) == 0 {
                    v_a_1898_ = leanh::lean_ctor_get(v___x_1897_, 0);
                    leanh::lean_inc_n(v_a_1898_, 2);
                    leanh::lean_dec_ref_known(v___x_1897_, 1);
                    v___x_1899_ =
                        l_Lean_Elab_checkCbvSimprocType(v_a_1898_, v___y_1894_, v___y_1895_);
                    if leanh::lean_obj_tag(v___x_1899_) == 0 {
                        leanh::lean_dec_ref_known(v___x_1899_, 1);
                        v___x_1900_ = l_Lean_Elab_elabCbvSimprocKeys(
                            v___x_1889_,
                            v___y_1892_,
                            v___y_1893_,
                            v___y_1894_,
                            v___y_1895_,
                        );
                        if leanh::lean_obj_tag(v___x_1900_) == 0 {
                            v_a_1901_ = leanh::lean_ctor_get(v___x_1900_, 0);
                            leanh::lean_inc(v_a_1901_);
                            leanh::lean_dec_ref_known(v___x_1900_, 1);
                            v___x_1902_ = l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(
                                v_a_1898_,
                                v_a_1901_,
                                v___y_1894_,
                                v___y_1895_,
                            );
                            return v___x_1902_;
                        } else {
                            leanh::lean_dec(v_a_1898_);
                            v_a_1903_ = leanh::lean_ctor_get(v___x_1900_, 0);
                            v_isSharedCheck_1910_ =
                                (!leanh::lean_is_exclusive(v___x_1900_)) as u8;
                            if v_isSharedCheck_1910_ == 0 {
                                v___x_1905_ = v___x_1900_;
                                v_isShared_1906_ = v_isSharedCheck_1910_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1903_);
                                leanh::lean_dec(v___x_1900_);
                                v___x_1905_ = leanh::lean_box(0);
                                v_isShared_1906_ = v_isSharedCheck_1910_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_1898_);
                        leanh::lean_dec(v___x_1889_);
                        return v___x_1899_;
                    }
                } else {
                    leanh::lean_dec(v___x_1889_);
                    v_a_1911_ = leanh::lean_ctor_get(v___x_1897_, 0);
                    v_isSharedCheck_1918_ = (!leanh::lean_is_exclusive(v___x_1897_)) as u8;
                    if v_isSharedCheck_1918_ == 0 {
                        v___x_1913_ = v___x_1897_;
                        v_isShared_1914_ = v_isSharedCheck_1918_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1911_);
                        leanh::lean_dec(v___x_1897_);
                        v___x_1913_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1909_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
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
                    v_reuseFailAlloc_1917_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
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
    mut v___x_1919_: *mut leanh::LeanObject,
    mut v___x_1920_: *mut leanh::LeanObject,
    mut v___y_1921_: *mut leanh::LeanObject,
    mut v___y_1922_: *mut leanh::LeanObject,
    mut v___y_1923_: *mut leanh::LeanObject,
    mut v___y_1924_: *mut leanh::LeanObject,
    mut v___y_1925_: *mut leanh::LeanObject,
    mut v___y_1926_: *mut leanh::LeanObject,
    mut v___y_1927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_1926_);
    leanh::lean_dec_ref(v___y_1925_);
    leanh::lean_dec(v___y_1924_);
    leanh::lean_dec_ref(v___y_1923_);
    leanh::lean_dec(v___y_1922_);
    leanh::lean_dec_ref(v___y_1921_);
    return v_res_1928_;
}
pub unsafe fn l_Lean_Elab_Command_elabCbvSimprocPattern(
    mut v_stx_1935_: *mut leanh::LeanObject,
    mut v_a_1936_: *mut leanh::LeanObject,
    mut v_a_1937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: u8 = 0;
    v___x_1939_ = l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2;
    leanh::lean_inc(v_stx_1935_);
    v___x_1940_ = l_Lean_Syntax_isOfKind(v_stx_1935_, v___x_1939_);
    if v___x_1940_ == 0 {
        let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stx_1935_);
        v___x_1941_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg();
        return v___x_1941_;
    } else {
        let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1944_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1942_ = leanh::lean_unsigned_to_nat(1);
        v___x_1943_ = l_Lean_Syntax_getArg(v_stx_1935_, v___x_1942_);
        v___x_1944_ = leanh::lean_unsigned_to_nat(3);
        v___x_1945_ = l_Lean_Syntax_getArg(v_stx_1935_, v___x_1944_);
        leanh::lean_dec(v_stx_1935_);
        v___f_1946_ = leanh::lean_alloc_closure(
            l_Lean_Elab_Command_elabCbvSimprocPattern___lam__0___boxed as *mut core::ffi::c_void,
            9,
            2,
        );
        leanh::lean_closure_set(v___f_1946_, 0, v___x_1945_);
        leanh::lean_closure_set(v___f_1946_, 1, v___x_1943_);
        v___x_1947_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_1946_, v_a_1936_, v_a_1937_);
        return v___x_1947_;
    }
}
pub unsafe fn l_Lean_Elab_Command_elabCbvSimprocPattern___boxed(
    mut v_stx_1948_: *mut leanh::LeanObject,
    mut v_a_1949_: *mut leanh::LeanObject,
    mut v_a_1950_: *mut leanh::LeanObject,
    mut v_a_1951_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1952_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1952_ = l_Lean_Elab_Command_elabCbvSimprocPattern(v_stx_1948_, v_a_1949_, v_a_1950_);
    leanh::lean_dec(v_a_1950_);
    leanh::lean_dec_ref(v_a_1949_);
    return v_res_1952_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1()
-> *mut leanh::LeanObject {
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1962_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_1963_ = l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2;
    v___x_1964_ = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3;
    v___x_1965_ = leanh::lean_alloc_closure(
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
    mut v_a_1967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1968_ = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1();
    return v_res_1968_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1978_ = leanh::lean_box(0);
    v___x_1979_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3;
    v___x_1980_ = l_Lean_mkConst(v___x_1979_, v___x_1978_);
    return v___x_1980_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1988_ = leanh::lean_box(0);
    v___x_1989_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6;
    v___x_1990_ = l_Lean_mkConst(v___x_1989_, v___x_1988_);
    return v___x_1990_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_1998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1998_ = leanh::lean_box(0);
    v___x_1999_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9;
    v___x_2000_ = l_Lean_mkConst(v___x_1999_, v___x_1998_);
    return v___x_2000_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_2007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2007_ = leanh::lean_box(0);
    v___x_2008_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13;
    v___x_2009_ = l_Lean_mkConst(v___x_2008_, v___x_2007_);
    return v___x_2009_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2015_ = leanh::lean_box(0);
    v___x_2016_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16;
    v___x_2017_ = l_Lean_mkConst(v___x_2016_, v___x_2015_);
    return v___x_2017_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_2025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2025_ = leanh::lean_box(0);
    v___x_2026_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19;
    v___x_2027_ = l_Lean_mkConst(v___x_2026_, v___x_2025_);
    return v___x_2027_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2034_ = leanh::lean_box(0);
    v___x_2035_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23;
    v___x_2036_ = l_Lean_mkConst(v___x_2035_, v___x_2034_);
    return v___x_2036_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_2044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2044_ = leanh::lean_box(0);
    v___x_2045_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26;
    v___x_2046_ = l_Lean_mkConst(v___x_2045_, v___x_2044_);
    return v___x_2046_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30()
-> *mut leanh::LeanObject {
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2054_ = leanh::lean_box(0);
    v___x_2055_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29;
    v___x_2056_ = l_Lean_mkConst(v___x_2055_, v___x_2054_);
    return v___x_2056_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33()
-> *mut leanh::LeanObject {
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2064_ = leanh::lean_box(0);
    v___x_2065_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32;
    v___x_2066_ = l_Lean_mkConst(v___x_2065_, v___x_2064_);
    return v___x_2066_;
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0(
    mut v_nilFn_2067_: *mut leanh::LeanObject,
    mut v_consFn_2068_: *mut leanh::LeanObject,
    mut v_x_2069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2069_) == 0 {
                    leanh::lean_dec_ref(v_consFn_2068_);
                    leanh::lean_inc_ref(v_nilFn_2067_);
                    return v_nilFn_2067_;
                } else {
                    v_head_2070_ = leanh::lean_ctor_get(v_x_2069_, 0);
                    leanh::lean_inc(v_head_2070_);
                    v_tail_2071_ = leanh::lean_ctor_get(v_x_2069_, 1);
                    leanh::lean_inc(v_tail_2071_);
                    leanh::lean_dec_ref_known(v_x_2069_, 2);
                    match leanh::lean_obj_tag(v_head_2070_) {
                        0 => {
                            v___x_2076_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4);
                            v___y_2073_ = v___x_2076_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v___x_2077_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7);
                            v___y_2073_ = v___x_2077_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            v_a_2078_ = leanh::lean_ctor_get(v_head_2070_, 0);
                            leanh::lean_inc_ref(v_a_2078_);
                            leanh::lean_dec_ref_known(v_head_2070_, 1);
                            v___x_2079_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10);
                            if leanh::lean_obj_tag(v_a_2078_) == 0 {
                                v___x_2080_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14);
                                v___x_2081_ = l_Lean_Expr_lit___override(v_a_2078_);
                                v___x_2082_ = l_Lean_Expr_app___override(v___x_2080_, v___x_2081_);
                                v___x_2083_ = l_Lean_Expr_app___override(v___x_2079_, v___x_2082_);
                                v___y_2073_ = v___x_2083_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2084_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17);
                                v___x_2085_ = l_Lean_Expr_lit___override(v_a_2078_);
                                v___x_2086_ = l_Lean_Expr_app___override(v___x_2084_, v___x_2085_);
                                v___x_2087_ = l_Lean_Expr_app___override(v___x_2079_, v___x_2086_);
                                v___y_2073_ = v___x_2087_;
                                state = 1;
                                continue;
                            }
                        }
                        3 => {
                            v_a_2088_ = leanh::lean_ctor_get(v_head_2070_, 0);
                            leanh::lean_inc(v_a_2088_);
                            v_a_2089_ = leanh::lean_ctor_get(v_head_2070_, 1);
                            leanh::lean_inc(v_a_2089_);
                            leanh::lean_dec_ref_known(v_head_2070_, 2);
                            v___x_2090_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20);
                            v___x_2091_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24);
                            v___x_2092_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_2088_);
                            v___x_2093_ = l_Lean_Expr_app___override(v___x_2091_, v___x_2092_);
                            v___x_2094_ = l_Lean_mkNatLit(v_a_2089_);
                            v___x_2095_ = l_Lean_mkAppB(v___x_2090_, v___x_2093_, v___x_2094_);
                            v___y_2073_ = v___x_2095_;
                            state = 1;
                            continue;
                        }
                        4 => {
                            v_a_2096_ = leanh::lean_ctor_get(v_head_2070_, 0);
                            leanh::lean_inc(v_a_2096_);
                            v_a_2097_ = leanh::lean_ctor_get(v_head_2070_, 1);
                            leanh::lean_inc(v_a_2097_);
                            leanh::lean_dec_ref_known(v_head_2070_, 2);
                            v___x_2098_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27);
                            v___x_2099_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_2096_);
                            v___x_2100_ = l_Lean_mkNatLit(v_a_2097_);
                            v___x_2101_ = l_Lean_mkAppB(v___x_2098_, v___x_2099_, v___x_2100_);
                            v___y_2073_ = v___x_2101_;
                            state = 1;
                            continue;
                        }
                        5 => {
                            v___x_2102_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30);
                            v___y_2073_ = v___x_2102_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_a_2103_ = leanh::lean_ctor_get(v_head_2070_, 0);
                            leanh::lean_inc(v_a_2103_);
                            v_a_2104_ = leanh::lean_ctor_get(v_head_2070_, 1);
                            leanh::lean_inc(v_a_2104_);
                            v_a_2105_ = leanh::lean_ctor_get(v_head_2070_, 2);
                            leanh::lean_inc(v_a_2105_);
                            leanh::lean_dec_ref_known(v_head_2070_, 3);
                            v___x_2106_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33);
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
                leanh::lean_inc_ref(v_consFn_2068_);
                v___x_2074_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0(v_nilFn_2067_, v_consFn_2068_, v_tail_2071_);
                v___x_2075_ = l_Lean_mkAppB(v_consFn_2068_, v___y_2073_, v___x_2074_);
                return v___x_2075_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___boxed(
    mut v_nilFn_2111_: *mut leanh::LeanObject,
    mut v_consFn_2112_: *mut leanh::LeanObject,
    mut v_x_2113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2114_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0(v_nilFn_2111_, v_consFn_2112_, v_x_2113_);
    leanh::lean_dec_ref(v_nilFn_2111_);
    return v_res_2114_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2126_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6;
    v___x_2127_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5;
    v___x_2128_ = l_Lean_mkConst(v___x_2127_, v___x_2126_);
    return v___x_2128_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2136_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6;
    v___x_2137_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11;
    v___x_2138_ = l_Lean_mkConst(v___x_2137_, v___x_2136_);
    return v___x_2138_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2143_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6;
    v___x_2144_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14;
    v___x_2145_ = l_Lean_mkConst(v___x_2144_, v___x_2143_);
    return v___x_2145_;
}
pub unsafe fn l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0(
    mut v___x_2146_: *mut leanh::LeanObject,
    mut v___x_2147_: *mut leanh::LeanObject,
    mut v___x_2148_: *mut leanh::LeanObject,
    mut v___x_2149_: *mut leanh::LeanObject,
    mut v___y_2150_: *mut leanh::LeanObject,
    mut v___y_2151_: *mut leanh::LeanObject,
    mut v___y_2152_: *mut leanh::LeanObject,
    mut v___y_2153_: *mut leanh::LeanObject,
    mut v___y_2154_: *mut leanh::LeanObject,
    mut v___y_2155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nil_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cons_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2196_: u8 = 0;
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2200_: u8 = 0;
    let mut v_a_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2204_: u8 = 0;
    let mut v___x_2206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2208_: u8 = 0;
    let mut v_a_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2212_: u8 = 0;
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2216_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2157_ =
                    l_Lean_realizeGlobalConstNoOverload(v___x_2146_, v___y_2154_, v___y_2155_);
                if leanh::lean_obj_tag(v___x_2157_) == 0 {
                    v_a_2158_ = leanh::lean_ctor_get(v___x_2157_, 0);
                    leanh::lean_inc_n(v_a_2158_, 2);
                    leanh::lean_dec_ref_known(v___x_2157_, 1);
                    v___x_2159_ =
                        l_Lean_Elab_checkCbvSimprocType(v_a_2158_, v___y_2154_, v___y_2155_);
                    if leanh::lean_obj_tag(v___x_2159_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2159_, 1);
                        v___x_2160_ = l_Lean_Elab_elabCbvSimprocKeys(
                            v___x_2147_,
                            v___y_2152_,
                            v___y_2153_,
                            v___y_2154_,
                            v___y_2155_,
                        );
                        if leanh::lean_obj_tag(v___x_2160_) == 0 {
                            v_a_2161_ = leanh::lean_ctor_get(v___x_2160_, 0);
                            leanh::lean_inc(v_a_2161_);
                            leanh::lean_dec_ref_known(v___x_2160_, 1);
                            v___x_2162_ = l_Lean_Elab_checkCbvSimprocType___closed__3;
                            v___x_2163_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__0;
                            v___x_2164_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__1;
                            v___x_2165_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__2;
                            leanh::lean_inc_ref(v___x_2148_);
                            v___x_2166_ = l_Lean_Name_mkStr5(
                                v___x_2148_,
                                v___x_2162_,
                                v___x_2163_,
                                v___x_2164_,
                                v___x_2165_,
                            );
                            v___x_2167_ = leanh::lean_box(0);
                            v___x_2168_ = l_Lean_mkConst(v___x_2166_, v___x_2167_);
                            leanh::lean_inc_n(v_a_2158_, 2);
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
                            v___x_2174_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7_once), _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7);
                            v___x_2175_ = l_Lean_mkConst(v_a_2158_, v___x_2167_);
                            v___x_2176_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__9;
                            v___x_2177_ = l_Lean_Name_append(v_a_2158_, v___x_2176_);
                            v___x_2178_ =
                                l_Lean_Core_mkFreshUserName(v___x_2177_, v___y_2154_, v___y_2155_);
                            if leanh::lean_obj_tag(v___x_2178_) == 0 {
                                v_a_2179_ = leanh::lean_ctor_get(v___x_2178_, 0);
                                leanh::lean_inc(v_a_2179_);
                                leanh::lean_dec_ref_known(v___x_2178_, 1);
                                v___x_2180_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12), core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12_once), _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12);
                                leanh::lean_inc_ref_n(v___x_2173_, 2);
                                v_nil_2181_ = l_Lean_Expr_app___override(v___x_2180_, v___x_2173_);
                                v___x_2182_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15), core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15_once), _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15);
                                v_cons_2183_ = l_Lean_Expr_app___override(v___x_2182_, v___x_2173_);
                                v___x_2184_ = lean_array_to_list(v_a_2161_);
                                v___x_2185_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0(v_nil_2181_, v_cons_2183_, v___x_2184_);
                                leanh::lean_dec_ref(v_nil_2181_);
                                v___x_2186_ = l_Lean_mkAppB(v___x_2174_, v___x_2173_, v___x_2185_);
                                v___x_2187_ = lean_mk_empty_array_with_capacity(v___x_2149_);
                                v___x_2188_ = lean_array_push(v___x_2187_, v___x_2169_);
                                v___x_2189_ = lean_array_push(v___x_2188_, v___x_2186_);
                                v___x_2190_ = lean_array_push(v___x_2189_, v___x_2175_);
                                v___x_2191_ = l_Lean_mkAppN(v___x_2168_, v___x_2190_);
                                leanh::lean_dec_ref(v___x_2190_);
                                v___x_2192_ = l_Lean_declareBuiltin(
                                    v_a_2179_,
                                    v___x_2191_,
                                    v___y_2154_,
                                    v___y_2155_,
                                );
                                return v___x_2192_;
                            } else {
                                leanh::lean_dec_ref(v___x_2175_);
                                leanh::lean_dec_ref(v___x_2173_);
                                leanh::lean_dec_ref(v___x_2169_);
                                leanh::lean_dec_ref(v___x_2168_);
                                leanh::lean_dec(v_a_2161_);
                                v_a_2193_ = leanh::lean_ctor_get(v___x_2178_, 0);
                                v_isSharedCheck_2200_ =
                                    (!leanh::lean_is_exclusive(v___x_2178_)) as u8;
                                if v_isSharedCheck_2200_ == 0 {
                                    v___x_2195_ = v___x_2178_;
                                    v_isShared_2196_ = v_isSharedCheck_2200_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_2193_);
                                    leanh::lean_dec(v___x_2178_);
                                    v___x_2195_ = leanh::lean_box(0);
                                    v_isShared_2196_ = v_isSharedCheck_2200_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_a_2158_);
                            leanh::lean_dec_ref(v___x_2148_);
                            v_a_2201_ = leanh::lean_ctor_get(v___x_2160_, 0);
                            v_isSharedCheck_2208_ =
                                (!leanh::lean_is_exclusive(v___x_2160_)) as u8;
                            if v_isSharedCheck_2208_ == 0 {
                                v___x_2203_ = v___x_2160_;
                                v_isShared_2204_ = v_isSharedCheck_2208_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2201_);
                                leanh::lean_dec(v___x_2160_);
                                v___x_2203_ = leanh::lean_box(0);
                                v_isShared_2204_ = v_isSharedCheck_2208_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_a_2158_);
                        leanh::lean_dec_ref(v___x_2148_);
                        leanh::lean_dec(v___x_2147_);
                        return v___x_2159_;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_2148_);
                    leanh::lean_dec(v___x_2147_);
                    v_a_2209_ = leanh::lean_ctor_get(v___x_2157_, 0);
                    v_isSharedCheck_2216_ = (!leanh::lean_is_exclusive(v___x_2157_)) as u8;
                    if v_isSharedCheck_2216_ == 0 {
                        v___x_2211_ = v___x_2157_;
                        v_isShared_2212_ = v_isSharedCheck_2216_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2209_);
                        leanh::lean_dec(v___x_2157_);
                        v___x_2211_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2199_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
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
                    v_reuseFailAlloc_2207_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
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
                    v_reuseFailAlloc_2215_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
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
    mut v___x_2217_: *mut leanh::LeanObject,
    mut v___x_2218_: *mut leanh::LeanObject,
    mut v___x_2219_: *mut leanh::LeanObject,
    mut v___x_2220_: *mut leanh::LeanObject,
    mut v___y_2221_: *mut leanh::LeanObject,
    mut v___y_2222_: *mut leanh::LeanObject,
    mut v___y_2223_: *mut leanh::LeanObject,
    mut v___y_2224_: *mut leanh::LeanObject,
    mut v___y_2225_: *mut leanh::LeanObject,
    mut v___y_2226_: *mut leanh::LeanObject,
    mut v___y_2227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_2226_);
    leanh::lean_dec_ref(v___y_2225_);
    leanh::lean_dec(v___y_2224_);
    leanh::lean_dec_ref(v___y_2223_);
    leanh::lean_dec(v___y_2222_);
    leanh::lean_dec_ref(v___y_2221_);
    leanh::lean_dec(v___x_2220_);
    return v_res_2228_;
}
pub unsafe fn l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin(
    mut v_stx_2234_: *mut leanh::LeanObject,
    mut v_a_2235_: *mut leanh::LeanObject,
    mut v_a_2236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: u8 = 0;
    v___x_2238_ = l_Lean_Elab_checkCbvSimprocType___closed__2;
    v___x_2239_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1;
    leanh::lean_inc(v_stx_2234_);
    v___x_2240_ = l_Lean_Syntax_isOfKind(v_stx_2234_, v___x_2239_);
    if v___x_2240_ == 0 {
        let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_stx_2234_);
        v___x_2241_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg();
        return v___x_2241_;
    } else {
        let mut v___x_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_2242_ = leanh::lean_unsigned_to_nat(1);
        v___x_2243_ = l_Lean_Syntax_getArg(v_stx_2234_, v___x_2242_);
        v___x_2244_ = leanh::lean_unsigned_to_nat(3);
        v___x_2245_ = l_Lean_Syntax_getArg(v_stx_2234_, v___x_2244_);
        leanh::lean_dec(v_stx_2234_);
        v___f_2246_ = leanh::lean_alloc_closure(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___boxed
                as *mut core::ffi::c_void,
            11,
            4,
        );
        leanh::lean_closure_set(v___f_2246_, 0, v___x_2245_);
        leanh::lean_closure_set(v___f_2246_, 1, v___x_2243_);
        leanh::lean_closure_set(v___f_2246_, 2, v___x_2238_);
        leanh::lean_closure_set(v___f_2246_, 3, v___x_2244_);
        v___x_2247_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2246_, v_a_2235_, v_a_2236_);
        return v___x_2247_;
    }
}
pub unsafe fn l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___boxed(
    mut v_stx_2248_: *mut leanh::LeanObject,
    mut v_a_2249_: *mut leanh::LeanObject,
    mut v_a_2250_: *mut leanh::LeanObject,
    mut v_a_2251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2252_ =
        l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin(v_stx_2248_, v_a_2249_, v_a_2250_);
    leanh::lean_dec(v_a_2250_);
    leanh::lean_dec_ref(v_a_2249_);
    return v_res_2252_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1()
-> *mut leanh::LeanObject {
    let mut v___x_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2260_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_2261_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1;
    v___x_2262_ = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1;
    v___x_2263_ = leanh::lean_alloc_closure(
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
    mut v_a_2265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2266_ = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1();
    return v_res_2266_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_CbvSimproc(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_CbvSimproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_CbvSimproc(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_CbvSimproc(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_CbvSimproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_CbvSimproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_CbvSimproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_CbvSimproc(builtin);
}
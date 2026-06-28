// Lean compiler output
// Module: Lean.Elab.Tactic.Simproc
// Imports: Init.Simproc Lean.Meta.Tactic.Simp.Simproc Lean.Elab.Command
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_replaceRef,
};
use crate::r#gen::Init::Simproc::{initialize_Init_Simproc, runtime_initialize_Init_Simproc};
use crate::r#gen::Lean::Compiler::InitAttr::l_Lean_declareBuiltin;
use crate::r#gen::Lean::CoreM::l_Lean_Core_mkFreshUserName;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::DeclarationRange::l_Lean_addBuiltinDeclarationRanges;
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
use crate::r#gen::Lean::Meta::Basic::l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey;
use crate::r#gen::Lean::Meta::DiscrTree::Main::l_Lean_Meta_DiscrTree_mkPath;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::l_Lean_Meta_simpGlobalConfig;
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::{
    initialize_Lean_Meta_Tactic_Simp_Simproc, l_Lean_Meta_Simp_registerSimproc,
    runtime_initialize_Lean_Meta_Tactic_Simp_Simproc,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::ReservedNameAction::l_Lean_realizeGlobalConstNoOverload;
use crate::r#gen::Lean::ToExpr::l___private_Lean_ToExpr_0__Lean_Name_toExprAux;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Elab_elabSimprocPattern___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_elabSimprocPattern___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_elabSimprocPattern___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabSimprocPattern___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_elabSimprocPattern___closed__1_value: LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Elab_elabSimprocPattern___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabSimprocPattern___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_elabSimprocPattern___closed__2_value: LeanCtorObject<10> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 8
            + 16) as u16,
        other: 8,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabSimprocPattern___closed__0_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_elabSimprocPattern___closed__1_value) as *mut LeanObject,
        16843009 as *mut LeanObject,
        65537 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_elabSimprocPattern___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabSimprocPattern___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_elabSimprocPattern___closed__3_value: LeanCtorObject<7> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 7
            + 0) as u16,
        other: 7,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_elabSimprocPattern___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabSimprocPattern___closed__3_value) as *mut LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkSimprocType___closed__0_value: LeanStringObject<48> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 48,
        m_capacity: 48,
        m_length: 47,
        m_data: [
            85, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 116, 121, 112, 101, 32, 102, 111,
            114, 32, 115, 105, 109, 112, 114, 111, 99, 32, 112, 97, 116, 116, 101, 114, 110, 58,
            32, 69, 120, 112, 101, 99, 116, 101, 100, 32, 96, 0,
        ],
    };
static mut l_Lean_Elab_checkSimprocType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_checkSimprocType___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkSimprocType___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkSimprocType___closed__2_value: LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_Elab_checkSimprocType___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_checkSimprocType___closed__3_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_checkSimprocType___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_checkSimprocType___closed__4_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_checkSimprocType___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_checkSimprocType___closed__5_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_checkSimprocType___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__5_value) as *mut LeanObject;
static l_Lean_Elab_checkSimprocType___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__2_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_checkSimprocType___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__6_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__3_value) as *mut LeanObject,
        15449383196166861506 as *mut LeanObject,
    ],
};
static l_Lean_Elab_checkSimprocType___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__6_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__4_value) as *mut LeanObject,
        492087047182689846 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_checkSimprocType___closed__6_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__6_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__5_value) as *mut LeanObject,
        18418687298610896914 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_checkSimprocType___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__6_value) as *mut LeanObject;
static mut l_Lean_Elab_checkSimprocType___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkSimprocType___closed__7: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_checkSimprocType___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkSimprocType___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkSimprocType___closed__9_value: LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [96, 32, 111, 114, 32, 96, 0],
};
static mut l_Lean_Elab_checkSimprocType___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__9_value) as *mut LeanObject;
static mut l_Lean_Elab_checkSimprocType___closed__10_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkSimprocType___closed__10: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_checkSimprocType___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkSimprocType___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkSimprocType___closed__12_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [68, 83, 105, 109, 112, 114, 111, 99, 0],
    };
static mut l_Lean_Elab_checkSimprocType___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__12_value) as *mut LeanObject;
static l_Lean_Elab_checkSimprocType___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__2_value) as *mut LeanObject,
        11948124481539785030 as *mut LeanObject,
    ],
};
static l_Lean_Elab_checkSimprocType___closed__13_value_aux_1: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__13_value_aux_0)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__3_value) as *mut LeanObject,
        15449383196166861506 as *mut LeanObject,
    ],
};
static l_Lean_Elab_checkSimprocType___closed__13_value_aux_2: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__13_value_aux_1)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__4_value) as *mut LeanObject,
        492087047182689846 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_checkSimprocType___closed__13_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__13_value_aux_2)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__12_value) as *mut LeanObject,
        11597777601497588599 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_checkSimprocType___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__13_value) as *mut LeanObject;
static mut l_Lean_Elab_checkSimprocType___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkSimprocType___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_checkSimprocType___closed__15_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkSimprocType___closed__15: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkSimprocType___closed__16_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_checkSimprocType___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__16_value) as *mut LeanObject;
static mut l_Lean_Elab_checkSimprocType___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkSimprocType___closed__17: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_checkSimprocType___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkSimprocType___closed__18: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkSimprocType___closed__19_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_checkSimprocType___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__19_value) as *mut LeanObject;
static mut l_Lean_Elab_checkSimprocType___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkSimprocType___closed__20: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabSimprocPattern___closed__0_value: LeanStringObject<7> =
    LeanStringObject {
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
static mut l_Lean_Elab_Command_elabSimprocPattern___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPattern___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabSimprocPattern___closed__1_value: LeanStringObject<15> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 15,
        m_capacity: 15,
        m_length: 14,
        m_data: [
            115, 105, 109, 112, 114, 111, 99, 80, 97, 116, 116, 101, 114, 110, 0,
        ],
    };
static mut l_Lean_Elab_Command_elabSimprocPattern___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPattern___closed__1_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_elabSimprocPattern___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__2_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabSimprocPattern___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPattern___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPattern___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabSimprocPattern___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPattern___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPattern___closed__1_value)
                as *mut LeanObject,
            18201466311632407230 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabSimprocPattern___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPattern___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__2_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 80, 97, 116, 116, 101, 114, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1_value) as *mut LeanObject,16981400742628996529 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__2_value) as *mut LeanObject,8820955551856617778 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 39 as usize) << 1) | 1) as *mut LeanObject,((( 51 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 45 as usize) << 1) | 1) as *mut LeanObject,((( 33 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__0_value) as *mut LeanObject,((( 51 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__1_value) as *mut LeanObject,((( 33 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 39 as usize) << 1) | 1) as *mut LeanObject,((( 55 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 39 as usize) << 1) | 1) as *mut LeanObject,((( 73 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__3_value) as *mut LeanObject,((( 55 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__4_value) as *mut LeanObject,((( 73 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [68, 105, 115, 99, 114, 84, 114, 101, 101, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [75, 101, 121, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 116, 97, 114, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__2_value) as *mut LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__3_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0_value) as *mut LeanObject,12558998168795833107 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1_value) as *mut LeanObject,6571394212498793888 as *mut LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__2_value) as *mut LeanObject,4525596147727532808 as *mut LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__5_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 116, 104, 101, 114, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__5_value) as *mut LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__3_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0_value) as *mut LeanObject,12558998168795833107 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1_value) as *mut LeanObject,6571394212498793888 as *mut LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__5_value) as *mut LeanObject,11989153488816012938 as *mut LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6_value) as *mut LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__8_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [108, 105, 116, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__8_value) as *mut LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__3_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0_value) as *mut LeanObject,12558998168795833107 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1_value) as *mut LeanObject,6571394212498793888 as *mut LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__8_value) as *mut LeanObject,15074539318474479562 as *mut LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9_value) as *mut LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__11_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [76, 105, 116, 101, 114, 97, 108, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__12_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [110, 97, 116, 86, 97, 108, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__12_value) as *mut LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__13_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__11_value) as *mut LeanObject,7001815944269665831 as *mut LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__13_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__12_value) as *mut LeanObject,9295767770006931264 as *mut LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__13_value) as *mut LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__15_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 116, 114, 86, 97, 108, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__15_value) as *mut LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__16_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__16_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__16_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__11_value) as *mut LeanObject,7001815944269665831 as *mut LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__16_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__15_value) as *mut LeanObject,2005404019190257220 as *mut LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__16_value) as *mut LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__18_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [102, 118, 97, 114, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__18_value) as *mut LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__3_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0_value) as *mut LeanObject,12558998168795833107 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1_value) as *mut LeanObject,6571394212498793888 as *mut LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__18_value) as *mut LeanObject,3087321959384269759 as *mut LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19_value) as *mut LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__20_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__20: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__21_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [70, 86, 97, 114, 73, 100, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__21_value) as *mut LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__22_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__22_value) as *mut LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__23_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__23_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__23_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__21_value) as *mut LeanObject,6212595679582900358 as *mut LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__23_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__22_value) as *mut LeanObject,6968149084986791158 as *mut LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__23_value) as *mut LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__24_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__24: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__25_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 111, 110, 115, 116, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__25: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__25_value) as *mut LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__3_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0_value) as *mut LeanObject,12558998168795833107 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1_value) as *mut LeanObject,6571394212498793888 as *mut LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__25_value) as *mut LeanObject,17383108283035838098 as *mut LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26_value) as *mut LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__27_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__27: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__28_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 114, 114, 111, 119, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__28: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__28_value) as *mut LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__3_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0_value) as *mut LeanObject,12558998168795833107 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1_value) as *mut LeanObject,6571394212498793888 as *mut LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__28_value) as *mut LeanObject,8457098344818307929 as *mut LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29_value) as *mut LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__30_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__30: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__31_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 114, 111, 106, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__31: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__31_value) as *mut LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__3_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0_value) as *mut LeanObject,12558998168795833107 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1_value) as *mut LeanObject,6571394212498793888 as *mut LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__31_value) as *mut LeanObject,12263618261203284320 as *mut LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32_value) as *mut LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__33_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__33: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__0_value:
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
    m_data: [76, 105, 115, 116, 0],
};
static mut l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__1_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__1_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__2_value_aux_0:
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
            l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__0_value
        ) as *mut LeanObject,
        9582258842178272501 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__2_value:
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
            l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__2_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__1_value
        ) as *mut LeanObject,
        8414467900391110369 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__3_value:
    LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        (((0 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__4: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__5_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__6_value:
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
            l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__5_value
        ) as *mut LeanObject,
        13812150225987229964 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__6_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__7_value:
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
    m_data: [110, 105, 108, 0],
};
static mut l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__7_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__8_value_aux_0:
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
            l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__0_value
        ) as *mut LeanObject,
        9582258842178272501 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__8_value:
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
            l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__8_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__7_value
        ) as *mut LeanObject,
        18135193680607614554 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__10_value:
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
    m_data: [99, 111, 110, 115, 0],
};
static mut l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__10_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__11_value_aux_0:
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
            l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__0_value
        ) as *mut LeanObject,
        9582258842178272501 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__11_value:
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
            l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__11_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__10_value
        ) as *mut LeanObject,
        8614124190858717794 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__11_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__12_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__13_value:
    LeanStringObject<23> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        114, 101, 103, 105, 115, 116, 101, 114, 66, 117, 105, 108, 116, 105, 110, 83, 105, 109,
        112, 114, 111, 99, 0,
    ],
};
static mut l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__13_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__14_value:
    LeanStringObject<24> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        114, 101, 103, 105, 115, 116, 101, 114, 66, 117, 105, 108, 116, 105, 110, 68, 83, 105, 109,
        112, 114, 111, 99, 0,
    ],
};
static mut l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__14_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__0_value: LeanStringObject<22> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            115, 105, 109, 112, 114, 111, 99, 80, 97, 116, 116, 101, 114, 110, 66, 117, 105, 108,
            116, 105, 110, 0,
        ],
    };
static mut l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__2_value) as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPattern___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(
                l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__0_value)
                as *mut LeanObject,
            10608001774515379730 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__0_value: LeanStringObject<26> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [101, 108, 97, 98, 83, 105, 109, 112, 114, 111, 99, 80, 97, 116, 116, 101, 114, 110, 66, 117, 105, 108, 116, 105, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__1_value) as *mut LeanObject,16981400742628996529 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__0_value) as *mut LeanObject,13568506880427722785 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 47 as usize) << 1) | 1) as *mut LeanObject,((( 58 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 56 as usize) << 1) | 1) as *mut LeanObject,((( 35 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__2_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__0_value) as *mut LeanObject,((( 58 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__1_value) as *mut LeanObject,((( 35 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 47 as usize) << 1) | 1) as *mut LeanObject,((( 62 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__4_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 47 as usize) << 1) | 1) as *mut LeanObject,((( 87 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__5_value: LeanCtorObject<4> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*4 + 0) as u16, other: 4, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__3_value) as *mut LeanObject,((( 62 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__4_value) as *mut LeanObject,((( 87 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__6_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__2_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__5_value) as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__6_value) as *mut LeanObject;
pub unsafe fn l_Lean_Elab_elabSimprocPattern___lam__0(mut v_x_1081_: *mut LeanObject) -> u8 {
    let mut v___x_1082_: u8 = 0;
    v___x_1082_ = 0;
    return v___x_1082_;
}
pub unsafe fn l_Lean_Elab_elabSimprocPattern___lam__0___boxed(
    mut v_x_1083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1084_: u8 = 0;
    let mut v_r_1085_: *mut LeanObject = core::ptr::null_mut();
    v_res_1084_ = l_Lean_Elab_elabSimprocPattern___lam__0(v_x_1083_);
    lean_dec(v_x_1083_);
    v_r_1085_ = lean_box((v_res_1084_) as usize);
    return v_r_1085_;
}
pub unsafe fn l_Lean_Elab_elabSimprocPattern___lam__1(
    mut v_stx_1086_: *mut LeanObject,
    mut v___x_1087_: *mut LeanObject,
    mut v___x_1088_: u8,
    mut v___y_1089_: *mut LeanObject,
    mut v___y_1090_: *mut LeanObject,
    mut v___y_1091_: *mut LeanObject,
    mut v___y_1092_: *mut LeanObject,
    mut v___y_1093_: *mut LeanObject,
    mut v___y_1094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: u8 = 0;
    let mut v___x_1099_: u8 = 0;
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1103_: u8 = 0;
    let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1107_: u8 = 0;
    let mut v_unused_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1112_: u8 = 0;
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1116_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1096_ = l_Lean_Elab_Term_elabTerm(
                    v_stx_1086_,
                    v___x_1087_,
                    v___x_1088_,
                    v___x_1088_,
                    v___y_1089_,
                    v___y_1090_,
                    v___y_1091_,
                    v___y_1092_,
                    v___y_1093_,
                    v___y_1094_,
                );
                if lean_obj_tag(v___x_1096_) == 0 {
                    v_a_1097_ = lean_ctor_get(v___x_1096_, 0);
                    lean_inc(v_a_1097_);
                    lean_dec_ref_known(v___x_1096_, 1);
                    v___x_1098_ = 0;
                    v___x_1099_ = 0;
                    v___x_1100_ = l_Lean_Elab_Term_synthesizeSyntheticMVars(
                        v___x_1098_,
                        v___x_1099_,
                        v___y_1089_,
                        v___y_1090_,
                        v___y_1091_,
                        v___y_1092_,
                        v___y_1093_,
                        v___y_1094_,
                    );
                    if lean_obj_tag(v___x_1100_) == 0 {
                        v_isSharedCheck_1107_ = (!lean_is_exclusive(v___x_1100_)) as u8;
                        if v_isSharedCheck_1107_ == 0 {
                            v_unused_1108_ = lean_ctor_get(v___x_1100_, 0);
                            lean_dec(v_unused_1108_);
                            v___x_1102_ = v___x_1100_;
                            v_isShared_1103_ = v_isSharedCheck_1107_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_1100_);
                            v___x_1102_ = lean_box(0);
                            v_isShared_1103_ = v_isSharedCheck_1107_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1097_);
                        v_a_1109_ = lean_ctor_get(v___x_1100_, 0);
                        v_isSharedCheck_1116_ = (!lean_is_exclusive(v___x_1100_)) as u8;
                        if v_isSharedCheck_1116_ == 0 {
                            v___x_1111_ = v___x_1100_;
                            v_isShared_1112_ = v_isSharedCheck_1116_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1109_);
                            lean_dec(v___x_1100_);
                            v___x_1111_ = lean_box(0);
                            v_isShared_1112_ = v_isSharedCheck_1116_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    return v___x_1096_;
                }
            }
            1 => {
                if v_isShared_1103_ == 0 {
                    lean_ctor_set(v___x_1102_, 0, v_a_1097_);
                    v___x_1105_ = v___x_1102_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1097_);
                    v___x_1105_ = v_reuseFailAlloc_1106_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1105_;
            }
            3 => {
                if v_isShared_1112_ == 0 {
                    v___x_1114_ = v___x_1111_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
                    v___x_1114_ = v_reuseFailAlloc_1115_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1114_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_elabSimprocPattern___lam__1___boxed(
    mut v_stx_1117_: *mut LeanObject,
    mut v___x_1118_: *mut LeanObject,
    mut v___x_1119_: *mut LeanObject,
    mut v___y_1120_: *mut LeanObject,
    mut v___y_1121_: *mut LeanObject,
    mut v___y_1122_: *mut LeanObject,
    mut v___y_1123_: *mut LeanObject,
    mut v___y_1124_: *mut LeanObject,
    mut v___y_1125_: *mut LeanObject,
    mut v___y_1126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_356__boxed_1127_: u8 = 0;
    let mut v_res_1128_: *mut LeanObject = core::ptr::null_mut();
    v___x_356__boxed_1127_ = (lean_unbox(v___x_1119_) as u8);
    v_res_1128_ = l_Lean_Elab_elabSimprocPattern___lam__1(
        v_stx_1117_,
        v___x_1118_,
        v___x_356__boxed_1127_,
        v___y_1120_,
        v___y_1121_,
        v___y_1122_,
        v___y_1123_,
        v___y_1124_,
        v___y_1125_,
    );
    lean_dec(v___y_1125_);
    lean_dec_ref(v___y_1124_);
    lean_dec(v___y_1123_);
    lean_dec_ref(v___y_1122_);
    lean_dec(v___y_1121_);
    lean_dec_ref(v___y_1120_);
    return v_res_1128_;
}
pub unsafe fn l_Lean_Elab_elabSimprocPattern(
    mut v_stx_1143_: *mut LeanObject,
    mut v_a_1144_: *mut LeanObject,
    mut v_a_1145_: *mut LeanObject,
    mut v_a_1146_: *mut LeanObject,
    mut v_a_1147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: u8 = 0;
    let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_go_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1159_: u8 = 0;
    let mut v_fst_1160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1164_: u8 = 0;
    let mut v_a_1165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1168_: u8 = 0;
    let mut v___x_1170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1172_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1149_ = lean_box(0);
                v___x_1150_ = 1;
                v___x_1151_ = lean_box((v___x_1150_) as usize);
                v_go_1152_ = lean_alloc_closure(
                    l_Lean_Elab_elabSimprocPattern___lam__1___boxed as *mut core::ffi::c_void,
                    10,
                    3,
                );
                lean_closure_set(v_go_1152_, 0, v_stx_1143_);
                lean_closure_set(v_go_1152_, 1, v___x_1149_);
                lean_closure_set(v_go_1152_, 2, v___x_1151_);
                v___x_1153_ = l_Lean_Elab_elabSimprocPattern___closed__2;
                v___x_1154_ = l_Lean_Elab_elabSimprocPattern___closed__3;
                v___x_1155_ = l_Lean_Elab_Term_TermElabM_run___redArg(
                    v_go_1152_,
                    v___x_1153_,
                    v___x_1154_,
                    v_a_1144_,
                    v_a_1145_,
                    v_a_1146_,
                    v_a_1147_,
                );
                if lean_obj_tag(v___x_1155_) == 0 {
                    v_a_1156_ = lean_ctor_get(v___x_1155_, 0);
                    v_isSharedCheck_1164_ = (!lean_is_exclusive(v___x_1155_)) as u8;
                    if v_isSharedCheck_1164_ == 0 {
                        v___x_1158_ = v___x_1155_;
                        v_isShared_1159_ = v_isSharedCheck_1164_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1156_);
                        lean_dec(v___x_1155_);
                        v___x_1158_ = lean_box(0);
                        v_isShared_1159_ = v_isSharedCheck_1164_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1165_ = lean_ctor_get(v___x_1155_, 0);
                    v_isSharedCheck_1172_ = (!lean_is_exclusive(v___x_1155_)) as u8;
                    if v_isSharedCheck_1172_ == 0 {
                        v___x_1167_ = v___x_1155_;
                        v_isShared_1168_ = v_isSharedCheck_1172_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1165_);
                        lean_dec(v___x_1155_);
                        v___x_1167_ = lean_box(0);
                        v_isShared_1168_ = v_isSharedCheck_1172_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1160_ = lean_ctor_get(v_a_1156_, 0);
                lean_inc(v_fst_1160_);
                lean_dec(v_a_1156_);
                if v_isShared_1159_ == 0 {
                    lean_ctor_set(v___x_1158_, 0, v_fst_1160_);
                    v___x_1162_ = v___x_1158_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1163_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_fst_1160_);
                    v___x_1162_ = v_reuseFailAlloc_1163_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1162_;
            }
            3 => {
                if v_isShared_1168_ == 0 {
                    v___x_1170_ = v___x_1167_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
                    v___x_1170_ = v_reuseFailAlloc_1171_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1170_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_elabSimprocPattern___boxed(
    mut v_stx_1173_: *mut LeanObject,
    mut v_a_1174_: *mut LeanObject,
    mut v_a_1175_: *mut LeanObject,
    mut v_a_1176_: *mut LeanObject,
    mut v_a_1177_: *mut LeanObject,
    mut v_a_1178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1179_: *mut LeanObject = core::ptr::null_mut();
    v_res_1179_ =
        l_Lean_Elab_elabSimprocPattern(v_stx_1173_, v_a_1174_, v_a_1175_, v_a_1176_, v_a_1177_);
    lean_dec(v_a_1177_);
    lean_dec_ref(v_a_1176_);
    lean_dec(v_a_1175_);
    lean_dec_ref(v_a_1174_);
    return v_res_1179_;
}
pub unsafe fn l_Lean_Elab_elabSimprocKeys(
    mut v_stx_1180_: *mut LeanObject,
    mut v_a_1181_: *mut LeanObject,
    mut v_a_1182_: *mut LeanObject,
    mut v_a_1183_: *mut LeanObject,
    mut v_a_1184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_1189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_trackZetaDelta_1190_: u8 = 0;
    let mut v_zetaDeltaSet_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_1196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_1197_: u8 = 0;
    let mut v_inTypeClassResolution_1198_: u8 = 0;
    let mut v_cacheInferType_1199_: u8 = 0;
    let mut v___x_1200_: u64 = 0;
    let mut v___x_1201_: u8 = 0;
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1208_: u8 = 0;
    let mut v___x_1210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1212_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1186_ = l_Lean_Elab_elabSimprocPattern(
                    v_stx_1180_,
                    v_a_1181_,
                    v_a_1182_,
                    v_a_1183_,
                    v_a_1184_,
                );
                if lean_obj_tag(v___x_1186_) == 0 {
                    v_a_1187_ = lean_ctor_get(v___x_1186_, 0);
                    lean_inc(v_a_1187_);
                    lean_dec_ref_known(v___x_1186_, 1);
                    v___x_1188_ = l_Lean_Meta_simpGlobalConfig;
                    v_config_1189_ = lean_ctor_get(v___x_1188_, 0);
                    v_trackZetaDelta_1190_ = lean_ctor_get_uint8(
                        v_a_1181_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    );
                    v_zetaDeltaSet_1191_ = lean_ctor_get(v_a_1181_, 1);
                    v_lctx_1192_ = lean_ctor_get(v_a_1181_, 2);
                    v_localInstances_1193_ = lean_ctor_get(v_a_1181_, 3);
                    v_defEqCtx_x3f_1194_ = lean_ctor_get(v_a_1181_, 4);
                    v_synthPendingDepth_1195_ = lean_ctor_get(v_a_1181_, 5);
                    v_canUnfold_x3f_1196_ = lean_ctor_get(v_a_1181_, 6);
                    v_univApprox_1197_ = lean_ctor_get_uint8(
                        v_a_1181_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    );
                    v_inTypeClassResolution_1198_ = lean_ctor_get_uint8(
                        v_a_1181_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    );
                    v_cacheInferType_1199_ = lean_ctor_get_uint8(
                        v_a_1181_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    );
                    v___x_1200_ =
                        l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v_config_1189_);
                    v___x_1201_ = 0;
                    lean_inc_ref(v_config_1189_);
                    v___x_1202_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v___x_1202_, 0, v_config_1189_);
                    lean_ctor_set_uint64(
                        v___x_1202_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_1200_,
                    );
                    lean_inc(v_canUnfold_x3f_1196_);
                    lean_inc(v_synthPendingDepth_1195_);
                    lean_inc(v_defEqCtx_x3f_1194_);
                    lean_inc_ref(v_localInstances_1193_);
                    lean_inc_ref(v_lctx_1192_);
                    lean_inc(v_zetaDeltaSet_1191_);
                    v___x_1203_ = lean_alloc_ctor(0, 7, (4) as u32);
                    lean_ctor_set(v___x_1203_, 0, v___x_1202_);
                    lean_ctor_set(v___x_1203_, 1, v_zetaDeltaSet_1191_);
                    lean_ctor_set(v___x_1203_, 2, v_lctx_1192_);
                    lean_ctor_set(v___x_1203_, 3, v_localInstances_1193_);
                    lean_ctor_set(v___x_1203_, 4, v_defEqCtx_x3f_1194_);
                    lean_ctor_set(v___x_1203_, 5, v_synthPendingDepth_1195_);
                    lean_ctor_set(v___x_1203_, 6, v_canUnfold_x3f_1196_);
                    lean_ctor_set_uint8(
                        v___x_1203_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v_trackZetaDelta_1190_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1203_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                        v_univApprox_1197_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1203_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                        v_inTypeClassResolution_1198_,
                    );
                    lean_ctor_set_uint8(
                        v___x_1203_,
                        (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                        v_cacheInferType_1199_,
                    );
                    v___x_1204_ = l_Lean_Meta_DiscrTree_mkPath(
                        v_a_1187_,
                        v___x_1201_,
                        v___x_1203_,
                        v_a_1182_,
                        v_a_1183_,
                        v_a_1184_,
                    );
                    lean_dec_ref_known(v___x_1203_, 7);
                    return v___x_1204_;
                } else {
                    v_a_1205_ = lean_ctor_get(v___x_1186_, 0);
                    v_isSharedCheck_1212_ = (!lean_is_exclusive(v___x_1186_)) as u8;
                    if v_isSharedCheck_1212_ == 0 {
                        v___x_1207_ = v___x_1186_;
                        v_isShared_1208_ = v_isSharedCheck_1212_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1205_);
                        lean_dec(v___x_1186_);
                        v___x_1207_ = lean_box(0);
                        v_isShared_1208_ = v_isSharedCheck_1212_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1208_ == 0 {
                    v___x_1210_ = v___x_1207_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1211_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1211_, 0, v_a_1205_);
                    v___x_1210_ = v_reuseFailAlloc_1211_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1210_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_elabSimprocKeys___boxed(
    mut v_stx_1213_: *mut LeanObject,
    mut v_a_1214_: *mut LeanObject,
    mut v_a_1215_: *mut LeanObject,
    mut v_a_1216_: *mut LeanObject,
    mut v_a_1217_: *mut LeanObject,
    mut v_a_1218_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1219_: *mut LeanObject = core::ptr::null_mut();
    v_res_1219_ =
        l_Lean_Elab_elabSimprocKeys(v_stx_1213_, v_a_1214_, v_a_1215_, v_a_1216_, v_a_1217_);
    lean_dec(v_a_1217_);
    lean_dec_ref(v_a_1216_);
    lean_dec(v_a_1215_);
    lean_dec_ref(v_a_1214_);
    return v_res_1219_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__0()
-> *mut LeanObject {
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    v___x_1220_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1220_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    v___x_1221_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__0);
    v___x_1222_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1222_, 0, v___x_1221_);
    return v___x_1222_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__2()
-> *mut LeanObject {
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    v___x_1223_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__1);
    v___x_1224_ = lean_unsigned_to_nat(0);
    v___x_1225_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1225_, 0, v___x_1224_);
    lean_ctor_set(v___x_1225_, 1, v___x_1224_);
    lean_ctor_set(v___x_1225_, 2, v___x_1224_);
    lean_ctor_set(v___x_1225_, 3, v___x_1224_);
    lean_ctor_set(v___x_1225_, 4, v___x_1223_);
    lean_ctor_set(v___x_1225_, 5, v___x_1223_);
    lean_ctor_set(v___x_1225_, 6, v___x_1223_);
    lean_ctor_set(v___x_1225_, 7, v___x_1223_);
    lean_ctor_set(v___x_1225_, 8, v___x_1223_);
    lean_ctor_set(v___x_1225_, 9, v___x_1223_);
    return v___x_1225_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__3()
-> *mut LeanObject {
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    v___x_1226_ = lean_unsigned_to_nat(32);
    v___x_1227_ = lean_mk_empty_array_with_capacity(v___x_1226_);
    v___x_1228_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1228_, 0, v___x_1227_);
    return v___x_1228_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__4()
-> *mut LeanObject {
    let mut v___x_1229_: usize = 0;
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    v___x_1229_ = 5usize;
    v___x_1230_ = lean_unsigned_to_nat(0);
    v___x_1231_ = lean_unsigned_to_nat(32);
    v___x_1232_ = lean_mk_empty_array_with_capacity(v___x_1231_);
    v___x_1233_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__3);
    v___x_1234_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1234_, 0, v___x_1233_);
    lean_ctor_set(v___x_1234_, 1, v___x_1232_);
    lean_ctor_set(v___x_1234_, 2, v___x_1230_);
    lean_ctor_set(v___x_1234_, 3, v___x_1230_);
    lean_ctor_set_usize(v___x_1234_, 4, v___x_1229_);
    return v___x_1234_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__5()
-> *mut LeanObject {
    let mut v___x_1235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    v___x_1235_ = lean_box(1);
    v___x_1236_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__4);
    v___x_1237_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__1);
    v___x_1238_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1238_, 0, v___x_1237_);
    lean_ctor_set(v___x_1238_, 1, v___x_1236_);
    lean_ctor_set(v___x_1238_, 2, v___x_1235_);
    return v___x_1238_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2(
    mut v_msgData_1239_: *mut LeanObject,
    mut v___y_1240_: *mut LeanObject,
    mut v___y_1241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut LeanObject = core::ptr::null_mut();
    v___x_1243_ = lean_st_ref_get(v___y_1241_);
    v_env_1244_ = lean_ctor_get(v___x_1243_, 0);
    lean_inc_ref(v_env_1244_);
    lean_dec(v___x_1243_);
    v_options_1245_ = lean_ctor_get(v___y_1240_, 2);
    v___x_1246_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__2);
    v___x_1247_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__5);
    lean_inc_ref(v_options_1245_);
    v___x_1248_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1248_, 0, v_env_1244_);
    lean_ctor_set(v___x_1248_, 1, v___x_1246_);
    lean_ctor_set(v___x_1248_, 2, v___x_1247_);
    lean_ctor_set(v___x_1248_, 3, v_options_1245_);
    v___x_1249_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1249_, 0, v___x_1248_);
    lean_ctor_set(v___x_1249_, 1, v_msgData_1239_);
    v___x_1250_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1250_, 0, v___x_1249_);
    return v___x_1250_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___boxed(
    mut v_msgData_1251_: *mut LeanObject,
    mut v___y_1252_: *mut LeanObject,
    mut v___y_1253_: *mut LeanObject,
    mut v___y_1254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1255_: *mut LeanObject = core::ptr::null_mut();
    v_res_1255_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2(v_msgData_1251_, v___y_1252_, v___y_1253_);
    lean_dec(v___y_1253_);
    lean_dec_ref(v___y_1252_);
    return v_res_1255_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1___redArg(
    mut v_msg_1256_: *mut LeanObject,
    mut v___y_1257_: *mut LeanObject,
    mut v___y_1258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1265_: u8 = 0;
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1270_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1260_ = lean_ctor_get(v___y_1257_, 5);
                v___x_1261_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2(v_msg_1256_, v___y_1257_, v___y_1258_);
                v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
                v_isSharedCheck_1270_ = (!lean_is_exclusive(v___x_1261_)) as u8;
                if v_isSharedCheck_1270_ == 0 {
                    v___x_1264_ = v___x_1261_;
                    v_isShared_1265_ = v_isSharedCheck_1270_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1262_);
                    lean_dec(v___x_1261_);
                    v___x_1264_ = lean_box(0);
                    v_isShared_1265_ = v_isSharedCheck_1270_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1260_);
                v___x_1266_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1266_, 0, v_ref_1260_);
                lean_ctor_set(v___x_1266_, 1, v_a_1262_);
                if v_isShared_1265_ == 0 {
                    lean_ctor_set_tag(v___x_1264_, 1);
                    lean_ctor_set(v___x_1264_, 0, v___x_1266_);
                    v___x_1268_ = v___x_1264_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1269_, 0, v___x_1266_);
                    v___x_1268_ = v_reuseFailAlloc_1269_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1268_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1___redArg___boxed(
    mut v_msg_1271_: *mut LeanObject,
    mut v___y_1272_: *mut LeanObject,
    mut v___y_1273_: *mut LeanObject,
    mut v___y_1274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1275_: *mut LeanObject = core::ptr::null_mut();
    v_res_1275_ = l_Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1___redArg(
        v_msg_1271_,
        v___y_1272_,
        v___y_1273_,
    );
    lean_dec(v___y_1273_);
    lean_dec_ref(v___y_1272_);
    return v_res_1275_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(
    mut v_ref_1276_: *mut LeanObject,
    mut v_msg_1277_: *mut LeanObject,
    mut v___y_1278_: *mut LeanObject,
    mut v___y_1279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1293_: u8 = 0;
    let mut v_cancelTk_x3f_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1295_: u8 = 0;
    let mut v_inheritedTraceOptions_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_1281_ = lean_ctor_get(v___y_1278_, 0);
    v_fileMap_1282_ = lean_ctor_get(v___y_1278_, 1);
    v_options_1283_ = lean_ctor_get(v___y_1278_, 2);
    v_currRecDepth_1284_ = lean_ctor_get(v___y_1278_, 3);
    v_maxRecDepth_1285_ = lean_ctor_get(v___y_1278_, 4);
    v_ref_1286_ = lean_ctor_get(v___y_1278_, 5);
    v_currNamespace_1287_ = lean_ctor_get(v___y_1278_, 6);
    v_openDecls_1288_ = lean_ctor_get(v___y_1278_, 7);
    v_initHeartbeats_1289_ = lean_ctor_get(v___y_1278_, 8);
    v_maxHeartbeats_1290_ = lean_ctor_get(v___y_1278_, 9);
    v_quotContext_1291_ = lean_ctor_get(v___y_1278_, 10);
    v_currMacroScope_1292_ = lean_ctor_get(v___y_1278_, 11);
    v_diag_1293_ = lean_ctor_get_uint8(
        v___y_1278_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1294_ = lean_ctor_get(v___y_1278_, 12);
    v_suppressElabErrors_1295_ = lean_ctor_get_uint8(
        v___y_1278_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1296_ = lean_ctor_get(v___y_1278_, 13);
    v_ref_1297_ = l_Lean_replaceRef(v_ref_1276_, v_ref_1286_);
    lean_inc_ref(v_inheritedTraceOptions_1296_);
    lean_inc(v_cancelTk_x3f_1294_);
    lean_inc(v_currMacroScope_1292_);
    lean_inc(v_quotContext_1291_);
    lean_inc(v_maxHeartbeats_1290_);
    lean_inc(v_initHeartbeats_1289_);
    lean_inc(v_openDecls_1288_);
    lean_inc(v_currNamespace_1287_);
    lean_inc(v_maxRecDepth_1285_);
    lean_inc(v_currRecDepth_1284_);
    lean_inc_ref(v_options_1283_);
    lean_inc_ref(v_fileMap_1282_);
    lean_inc_ref(v_fileName_1281_);
    v___x_1298_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_1298_, 0, v_fileName_1281_);
    lean_ctor_set(v___x_1298_, 1, v_fileMap_1282_);
    lean_ctor_set(v___x_1298_, 2, v_options_1283_);
    lean_ctor_set(v___x_1298_, 3, v_currRecDepth_1284_);
    lean_ctor_set(v___x_1298_, 4, v_maxRecDepth_1285_);
    lean_ctor_set(v___x_1298_, 5, v_ref_1297_);
    lean_ctor_set(v___x_1298_, 6, v_currNamespace_1287_);
    lean_ctor_set(v___x_1298_, 7, v_openDecls_1288_);
    lean_ctor_set(v___x_1298_, 8, v_initHeartbeats_1289_);
    lean_ctor_set(v___x_1298_, 9, v_maxHeartbeats_1290_);
    lean_ctor_set(v___x_1298_, 10, v_quotContext_1291_);
    lean_ctor_set(v___x_1298_, 11, v_currMacroScope_1292_);
    lean_ctor_set(v___x_1298_, 12, v_cancelTk_x3f_1294_);
    lean_ctor_set(v___x_1298_, 13, v_inheritedTraceOptions_1296_);
    lean_ctor_set_uint8(
        v___x_1298_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_1293_,
    );
    lean_ctor_set_uint8(
        v___x_1298_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1295_,
    );
    v___x_1299_ = l_Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1___redArg(
        v_msg_1277_,
        v___x_1298_,
        v___y_1279_,
    );
    lean_dec_ref_known(v___x_1298_, 14);
    return v___x_1299_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(
    mut v_ref_1300_: *mut LeanObject,
    mut v_msg_1301_: *mut LeanObject,
    mut v___y_1302_: *mut LeanObject,
    mut v___y_1303_: *mut LeanObject,
    mut v___y_1304_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1305_: *mut LeanObject = core::ptr::null_mut();
    v_res_1305_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1300_, v_msg_1301_, v___y_1302_, v___y_1303_);
    lean_dec(v___y_1303_);
    lean_dec_ref(v___y_1302_);
    lean_dec(v_ref_1300_);
    return v_res_1305_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    v___x_1307_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0;
    v___x_1308_ = l_Lean_stringToMessageData(v___x_1307_);
    return v___x_1308_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1311_: *mut LeanObject = core::ptr::null_mut();
    v___x_1310_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2;
    v___x_1311_ = l_Lean_stringToMessageData(v___x_1310_);
    return v___x_1311_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1314_: *mut LeanObject = core::ptr::null_mut();
    v___x_1313_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4;
    v___x_1314_ = l_Lean_stringToMessageData(v___x_1313_);
    return v___x_1314_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    v___x_1316_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6;
    v___x_1317_ = l_Lean_stringToMessageData(v___x_1316_);
    return v___x_1317_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    v___x_1319_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8;
    v___x_1320_ = l_Lean_stringToMessageData(v___x_1319_);
    return v___x_1320_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    v___x_1322_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10;
    v___x_1323_ = l_Lean_stringToMessageData(v___x_1322_);
    return v___x_1323_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
    v___x_1325_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12;
    v___x_1326_ = l_Lean_stringToMessageData(v___x_1325_);
    return v___x_1326_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(
    mut v_msg_1327_: *mut LeanObject,
    mut v_declHint_1328_: *mut LeanObject,
    mut v___y_1329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: u8 = 0;
    let mut v_isExporting_1334_: u8 = 0;
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: u8 = 0;
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1356_: u8 = 0;
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: u8 = 0;
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1388_: u8 = 0;
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1331_ = lean_st_ref_get(v___y_1329_);
                v_env_1332_ = lean_ctor_get(v___x_1331_, 0);
                lean_inc_ref(v_env_1332_);
                lean_dec(v___x_1331_);
                v___x_1333_ = l_Lean_Name_isAnonymous(v_declHint_1328_);
                if v___x_1333_ == 0 {
                    v_isExporting_1334_ = lean_ctor_get_uint8(
                        v_env_1332_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1334_ == 0 {
                        lean_dec_ref(v_env_1332_);
                        lean_dec(v_declHint_1328_);
                        v___x_1335_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1335_, 0, v_msg_1327_);
                        return v___x_1335_;
                    } else {
                        lean_inc_ref(v_env_1332_);
                        v___x_1336_ = l_Lean_Environment_setExporting(v_env_1332_, v___x_1333_);
                        lean_inc(v_declHint_1328_);
                        lean_inc_ref(v___x_1336_);
                        v___x_1337_ = l_Lean_Environment_contains(
                            v___x_1336_,
                            v_declHint_1328_,
                            v_isExporting_1334_,
                        );
                        if v___x_1337_ == 0 {
                            lean_dec_ref(v___x_1336_);
                            lean_dec_ref(v_env_1332_);
                            lean_dec(v_declHint_1328_);
                            v___x_1338_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1338_, 0, v_msg_1327_);
                            return v___x_1338_;
                        } else {
                            v___x_1339_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__2);
                            v___x_1340_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1_spec__2___closed__5);
                            v___x_1341_ = l_Lean_Options_empty;
                            v___x_1342_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_1342_, 0, v___x_1336_);
                            lean_ctor_set(v___x_1342_, 1, v___x_1339_);
                            lean_ctor_set(v___x_1342_, 2, v___x_1340_);
                            lean_ctor_set(v___x_1342_, 3, v___x_1341_);
                            lean_inc(v_declHint_1328_);
                            v___x_1343_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1328_, v___x_1333_);
                            v_c_1344_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_1344_, 0, v___x_1342_);
                            lean_ctor_set(v_c_1344_, 1, v___x_1343_);
                            v___x_1345_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1332_,
                                v_declHint_1328_,
                            );
                            if lean_obj_tag(v___x_1345_) == 0 {
                                lean_dec_ref(v_env_1332_);
                                lean_dec(v_declHint_1328_);
                                v___x_1346_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
                                v___x_1347_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1347_, 0, v___x_1346_);
                                lean_ctor_set(v___x_1347_, 1, v_c_1344_);
                                v___x_1348_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
                                v___x_1349_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1349_, 0, v___x_1347_);
                                lean_ctor_set(v___x_1349_, 1, v___x_1348_);
                                v___x_1350_ = l_Lean_MessageData_note(v___x_1349_);
                                v___x_1351_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1351_, 0, v_msg_1327_);
                                lean_ctor_set(v___x_1351_, 1, v___x_1350_);
                                v___x_1352_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_1352_, 0, v___x_1351_);
                                return v___x_1352_;
                            } else {
                                v_val_1353_ = lean_ctor_get(v___x_1345_, 0);
                                v_isSharedCheck_1388_ = (!lean_is_exclusive(v___x_1345_)) as u8;
                                if v_isSharedCheck_1388_ == 0 {
                                    v___x_1355_ = v___x_1345_;
                                    v_isShared_1356_ = v_isSharedCheck_1388_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_1353_);
                                    lean_dec(v___x_1345_);
                                    v___x_1355_ = lean_box(0);
                                    v_isShared_1356_ = v_isSharedCheck_1388_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_1332_);
                    lean_dec(v_declHint_1328_);
                    v___x_1389_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1389_, 0, v_msg_1327_);
                    return v___x_1389_;
                }
            }
            1 => {
                v___x_1357_ = lean_box(0);
                v___x_1358_ = l_Lean_Environment_header(v_env_1332_);
                lean_dec_ref(v_env_1332_);
                v___x_1359_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1358_);
                v_mod_1360_ = lean_array_get(v___x_1357_, v___x_1359_, v_val_1353_);
                lean_dec(v_val_1353_);
                lean_dec_ref(v___x_1359_);
                v___x_1361_ = l_Lean_isPrivateName(v_declHint_1328_);
                lean_dec(v_declHint_1328_);
                if v___x_1361_ == 0 {
                    v___x_1362_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
                    v___x_1363_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1363_, 0, v___x_1362_);
                    lean_ctor_set(v___x_1363_, 1, v_c_1344_);
                    v___x_1364_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
                    v___x_1365_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1365_, 0, v___x_1363_);
                    lean_ctor_set(v___x_1365_, 1, v___x_1364_);
                    v___x_1366_ = l_Lean_MessageData_ofName(v_mod_1360_);
                    v___x_1367_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1367_, 0, v___x_1365_);
                    lean_ctor_set(v___x_1367_, 1, v___x_1366_);
                    v___x_1368_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
                    v___x_1369_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1369_, 0, v___x_1367_);
                    lean_ctor_set(v___x_1369_, 1, v___x_1368_);
                    v___x_1370_ = l_Lean_MessageData_note(v___x_1369_);
                    v___x_1371_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1371_, 0, v_msg_1327_);
                    lean_ctor_set(v___x_1371_, 1, v___x_1370_);
                    if v_isShared_1356_ == 0 {
                        lean_ctor_set_tag(v___x_1355_, 0);
                        lean_ctor_set(v___x_1355_, 0, v___x_1371_);
                        v___x_1373_ = v___x_1355_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1374_, 0, v___x_1371_);
                        v___x_1373_ = v_reuseFailAlloc_1374_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1375_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
                    v___x_1376_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1376_, 0, v___x_1375_);
                    lean_ctor_set(v___x_1376_, 1, v_c_1344_);
                    v___x_1377_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
                    v___x_1378_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1378_, 0, v___x_1376_);
                    lean_ctor_set(v___x_1378_, 1, v___x_1377_);
                    v___x_1379_ = l_Lean_MessageData_ofName(v_mod_1360_);
                    v___x_1380_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1380_, 0, v___x_1378_);
                    lean_ctor_set(v___x_1380_, 1, v___x_1379_);
                    v___x_1381_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
                    v___x_1382_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1382_, 0, v___x_1380_);
                    lean_ctor_set(v___x_1382_, 1, v___x_1381_);
                    v___x_1383_ = l_Lean_MessageData_note(v___x_1382_);
                    v___x_1384_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1384_, 0, v_msg_1327_);
                    lean_ctor_set(v___x_1384_, 1, v___x_1383_);
                    if v_isShared_1356_ == 0 {
                        lean_ctor_set_tag(v___x_1355_, 0);
                        lean_ctor_set(v___x_1355_, 0, v___x_1384_);
                        v___x_1386_ = v___x_1355_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1387_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1384_);
                        v___x_1386_ = v_reuseFailAlloc_1387_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1373_;
            }
            3 => {
                return v___x_1386_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___boxed(
    mut v_msg_1390_: *mut LeanObject,
    mut v_declHint_1391_: *mut LeanObject,
    mut v___y_1392_: *mut LeanObject,
    mut v___y_1393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1394_: *mut LeanObject = core::ptr::null_mut();
    v_res_1394_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1390_, v_declHint_1391_, v___y_1392_);
    lean_dec(v___y_1392_);
    return v_res_1394_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(
    mut v_msg_1395_: *mut LeanObject,
    mut v_declHint_1396_: *mut LeanObject,
    mut v___y_1397_: *mut LeanObject,
    mut v___y_1398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1404_: u8 = 0;
    let mut v___x_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1410_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1400_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1395_, v_declHint_1396_, v___y_1398_);
                v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
                v_isSharedCheck_1410_ = (!lean_is_exclusive(v___x_1400_)) as u8;
                if v_isSharedCheck_1410_ == 0 {
                    v___x_1403_ = v___x_1400_;
                    v_isShared_1404_ = v_isSharedCheck_1410_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1401_);
                    lean_dec(v___x_1400_);
                    v___x_1403_ = lean_box(0);
                    v_isShared_1404_ = v_isSharedCheck_1410_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1405_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1406_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_1406_, 0, v___x_1405_);
                lean_ctor_set(v___x_1406_, 1, v_a_1401_);
                if v_isShared_1404_ == 0 {
                    lean_ctor_set(v___x_1403_, 0, v___x_1406_);
                    v___x_1408_ = v___x_1403_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1409_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1409_, 0, v___x_1406_);
                    v___x_1408_ = v_reuseFailAlloc_1409_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1408_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5___boxed(
    mut v_msg_1411_: *mut LeanObject,
    mut v_declHint_1412_: *mut LeanObject,
    mut v___y_1413_: *mut LeanObject,
    mut v___y_1414_: *mut LeanObject,
    mut v___y_1415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1416_: *mut LeanObject = core::ptr::null_mut();
    v_res_1416_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1411_, v_declHint_1412_, v___y_1413_, v___y_1414_);
    lean_dec(v___y_1414_);
    lean_dec_ref(v___y_1413_);
    return v_res_1416_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_ref_1417_: *mut LeanObject,
    mut v_msg_1418_: *mut LeanObject,
    mut v_declHint_1419_: *mut LeanObject,
    mut v___y_1420_: *mut LeanObject,
    mut v___y_1421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    v___x_1423_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1418_, v_declHint_1419_, v___y_1420_, v___y_1421_);
    v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
    lean_inc(v_a_1424_);
    lean_dec_ref(v___x_1423_);
    v___x_1425_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1417_, v_a_1424_, v___y_1420_, v___y_1421_);
    return v___x_1425_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_ref_1426_: *mut LeanObject,
    mut v_msg_1427_: *mut LeanObject,
    mut v_declHint_1428_: *mut LeanObject,
    mut v___y_1429_: *mut LeanObject,
    mut v___y_1430_: *mut LeanObject,
    mut v___y_1431_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1432_: *mut LeanObject = core::ptr::null_mut();
    v_res_1432_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1426_, v_msg_1427_, v_declHint_1428_, v___y_1429_, v___y_1430_);
    lean_dec(v___y_1430_);
    lean_dec_ref(v___y_1429_);
    lean_dec(v_ref_1426_);
    return v_res_1432_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    v___x_1434_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_1435_ = l_Lean_stringToMessageData(v___x_1434_);
    return v___x_1435_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    v___x_1437_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_1438_ = l_Lean_stringToMessageData(v___x_1437_);
    return v___x_1438_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg(
    mut v_ref_1439_: *mut LeanObject,
    mut v_constName_1440_: *mut LeanObject,
    mut v___y_1441_: *mut LeanObject,
    mut v___y_1442_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1445_: u8 = 0;
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    v___x_1444_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_1445_ = 0;
    lean_inc(v_constName_1440_);
    v___x_1446_ = l_Lean_MessageData_ofConstName(v_constName_1440_, v___x_1445_);
    v___x_1447_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1447_, 0, v___x_1444_);
    lean_ctor_set(v___x_1447_, 1, v___x_1446_);
    v___x_1448_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_1449_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1449_, 0, v___x_1447_);
    lean_ctor_set(v___x_1449_, 1, v___x_1448_);
    v___x_1450_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1439_, v___x_1449_, v_constName_1440_, v___y_1441_, v___y_1442_);
    return v___x_1450_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_1451_: *mut LeanObject,
    mut v_constName_1452_: *mut LeanObject,
    mut v___y_1453_: *mut LeanObject,
    mut v___y_1454_: *mut LeanObject,
    mut v___y_1455_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1456_: *mut LeanObject = core::ptr::null_mut();
    v_res_1456_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg(v_ref_1451_, v_constName_1452_, v___y_1453_, v___y_1454_);
    lean_dec(v___y_1454_);
    lean_dec_ref(v___y_1453_);
    lean_dec(v_ref_1451_);
    return v_res_1456_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0___redArg(
    mut v_constName_1457_: *mut LeanObject,
    mut v___y_1458_: *mut LeanObject,
    mut v___y_1459_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
    v_ref_1461_ = lean_ctor_get(v___y_1458_, 5);
    v___x_1462_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg(v_ref_1461_, v_constName_1457_, v___y_1458_, v___y_1459_);
    return v___x_1462_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0___redArg___boxed(
    mut v_constName_1463_: *mut LeanObject,
    mut v___y_1464_: *mut LeanObject,
    mut v___y_1465_: *mut LeanObject,
    mut v___y_1466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1467_: *mut LeanObject = core::ptr::null_mut();
    v_res_1467_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0___redArg(v_constName_1463_, v___y_1464_, v___y_1465_);
    lean_dec(v___y_1465_);
    lean_dec_ref(v___y_1464_);
    return v_res_1467_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0(
    mut v_constName_1468_: *mut LeanObject,
    mut v___y_1469_: *mut LeanObject,
    mut v___y_1470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: u8 = 0;
    let mut v___x_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1480_: u8 = 0;
    let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1484_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1472_ = lean_st_ref_get(v___y_1470_);
                v_env_1473_ = lean_ctor_get(v___x_1472_, 0);
                lean_inc_ref(v_env_1473_);
                lean_dec(v___x_1472_);
                v___x_1474_ = 0;
                lean_inc(v_constName_1468_);
                v___x_1475_ =
                    l_Lean_Environment_find_x3f(v_env_1473_, v_constName_1468_, v___x_1474_);
                if lean_obj_tag(v___x_1475_) == 0 {
                    v___x_1476_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0___redArg(v_constName_1468_, v___y_1469_, v___y_1470_);
                    return v___x_1476_;
                } else {
                    lean_dec(v_constName_1468_);
                    v_val_1477_ = lean_ctor_get(v___x_1475_, 0);
                    v_isSharedCheck_1484_ = (!lean_is_exclusive(v___x_1475_)) as u8;
                    if v_isSharedCheck_1484_ == 0 {
                        v___x_1479_ = v___x_1475_;
                        v_isShared_1480_ = v_isSharedCheck_1484_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1477_);
                        lean_dec(v___x_1475_);
                        v___x_1479_ = lean_box(0);
                        v_isShared_1480_ = v_isSharedCheck_1484_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1480_ == 0 {
                    lean_ctor_set_tag(v___x_1479_, 0);
                    v___x_1482_ = v___x_1479_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1483_, 0, v_val_1477_);
                    v___x_1482_ = v_reuseFailAlloc_1483_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1482_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0___boxed(
    mut v_constName_1485_: *mut LeanObject,
    mut v___y_1486_: *mut LeanObject,
    mut v___y_1487_: *mut LeanObject,
    mut v___y_1488_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1489_: *mut LeanObject = core::ptr::null_mut();
    v_res_1489_ = l_Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0(
        v_constName_1485_,
        v___y_1486_,
        v___y_1487_,
    );
    lean_dec(v___y_1487_);
    lean_dec_ref(v___y_1486_);
    return v_res_1489_;
}
pub unsafe fn _init_l_Lean_Elab_checkSimprocType___closed__1() -> *mut LeanObject {
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut LeanObject = core::ptr::null_mut();
    v___x_1491_ = l_Lean_Elab_checkSimprocType___closed__0;
    v___x_1492_ = l_Lean_stringToMessageData(v___x_1491_);
    return v___x_1492_;
}
pub unsafe fn _init_l_Lean_Elab_checkSimprocType___closed__7() -> *mut LeanObject {
    let mut v___x_1502_: u8 = 0;
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
    v___x_1502_ = 0;
    v___x_1503_ = l_Lean_Elab_checkSimprocType___closed__6;
    v___x_1504_ = l_Lean_MessageData_ofConstName(v___x_1503_, v___x_1502_);
    return v___x_1504_;
}
pub unsafe fn _init_l_Lean_Elab_checkSimprocType___closed__8() -> *mut LeanObject {
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    v___x_1505_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkSimprocType___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Elab_checkSimprocType___closed__7_once),
        _init_l_Lean_Elab_checkSimprocType___closed__7,
    );
    v___x_1506_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkSimprocType___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_checkSimprocType___closed__1_once),
        _init_l_Lean_Elab_checkSimprocType___closed__1,
    );
    v___x_1507_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1507_, 0, v___x_1506_);
    lean_ctor_set(v___x_1507_, 1, v___x_1505_);
    return v___x_1507_;
}
pub unsafe fn _init_l_Lean_Elab_checkSimprocType___closed__10() -> *mut LeanObject {
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
    v___x_1509_ = l_Lean_Elab_checkSimprocType___closed__9;
    v___x_1510_ = l_Lean_stringToMessageData(v___x_1509_);
    return v___x_1510_;
}
pub unsafe fn _init_l_Lean_Elab_checkSimprocType___closed__11() -> *mut LeanObject {
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut LeanObject = core::ptr::null_mut();
    v___x_1511_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkSimprocType___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Elab_checkSimprocType___closed__10_once),
        _init_l_Lean_Elab_checkSimprocType___closed__10,
    );
    v___x_1512_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkSimprocType___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Elab_checkSimprocType___closed__8_once),
        _init_l_Lean_Elab_checkSimprocType___closed__8,
    );
    v___x_1513_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1513_, 0, v___x_1512_);
    lean_ctor_set(v___x_1513_, 1, v___x_1511_);
    return v___x_1513_;
}
pub unsafe fn _init_l_Lean_Elab_checkSimprocType___closed__14() -> *mut LeanObject {
    let mut v___x_1520_: u8 = 0;
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    v___x_1520_ = 0;
    v___x_1521_ = l_Lean_Elab_checkSimprocType___closed__13;
    v___x_1522_ = l_Lean_MessageData_ofConstName(v___x_1521_, v___x_1520_);
    return v___x_1522_;
}
pub unsafe fn _init_l_Lean_Elab_checkSimprocType___closed__15() -> *mut LeanObject {
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    v___x_1523_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkSimprocType___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Elab_checkSimprocType___closed__14_once),
        _init_l_Lean_Elab_checkSimprocType___closed__14,
    );
    v___x_1524_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkSimprocType___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Elab_checkSimprocType___closed__11_once),
        _init_l_Lean_Elab_checkSimprocType___closed__11,
    );
    v___x_1525_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1525_, 0, v___x_1524_);
    lean_ctor_set(v___x_1525_, 1, v___x_1523_);
    return v___x_1525_;
}
pub unsafe fn _init_l_Lean_Elab_checkSimprocType___closed__17() -> *mut LeanObject {
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    v___x_1527_ = l_Lean_Elab_checkSimprocType___closed__16;
    v___x_1528_ = l_Lean_stringToMessageData(v___x_1527_);
    return v___x_1528_;
}
pub unsafe fn _init_l_Lean_Elab_checkSimprocType___closed__18() -> *mut LeanObject {
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    v___x_1529_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkSimprocType___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Elab_checkSimprocType___closed__17_once),
        _init_l_Lean_Elab_checkSimprocType___closed__17,
    );
    v___x_1530_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkSimprocType___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Elab_checkSimprocType___closed__15_once),
        _init_l_Lean_Elab_checkSimprocType___closed__15,
    );
    v___x_1531_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1531_, 0, v___x_1530_);
    lean_ctor_set(v___x_1531_, 1, v___x_1529_);
    return v___x_1531_;
}
pub unsafe fn _init_l_Lean_Elab_checkSimprocType___closed__20() -> *mut LeanObject {
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
    v___x_1533_ = l_Lean_Elab_checkSimprocType___closed__19;
    v___x_1534_ = l_Lean_stringToMessageData(v___x_1533_);
    return v___x_1534_;
}
pub unsafe fn l_Lean_Elab_checkSimprocType(
    mut v_declName_1535_: *mut LeanObject,
    mut v_a_1536_: *mut LeanObject,
    mut v_a_1537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1543_: u8 = 0;
    let mut v___y_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: u8 = 0;
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: u8 = 0;
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: u8 = 0;
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: u8 = 0;
    let mut v___x_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: u8 = 0;
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: u8 = 0;
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1585_: u8 = 0;
    let mut v_a_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1589_: u8 = 0;
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1593_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_declName_1535_);
                v___x_1539_ = l_Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0(
                    v_declName_1535_,
                    v_a_1536_,
                    v_a_1537_,
                );
                if lean_obj_tag(v___x_1539_) == 0 {
                    v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
                    v_isSharedCheck_1585_ = (!lean_is_exclusive(v___x_1539_)) as u8;
                    if v_isSharedCheck_1585_ == 0 {
                        v___x_1542_ = v___x_1539_;
                        v_isShared_1543_ = v_isSharedCheck_1585_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1540_);
                        lean_dec(v___x_1539_);
                        v___x_1542_ = lean_box(0);
                        v_isShared_1543_ = v_isSharedCheck_1585_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_declName_1535_);
                    v_a_1586_ = lean_ctor_get(v___x_1539_, 0);
                    v_isSharedCheck_1593_ = (!lean_is_exclusive(v___x_1539_)) as u8;
                    if v_isSharedCheck_1593_ == 0 {
                        v___x_1588_ = v___x_1539_;
                        v_isShared_1589_ = v_isSharedCheck_1593_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1586_);
                        lean_dec(v___x_1539_);
                        v___x_1588_ = lean_box(0);
                        v_isShared_1589_ = v_isSharedCheck_1593_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1556_ = l_Lean_ConstantInfo_type(v_a_1540_);
                if lean_obj_tag(v___x_1556_) == 4 {
                    v_declName_1557_ = lean_ctor_get(v___x_1556_, 0);
                    lean_inc(v_declName_1557_);
                    lean_dec_ref_known(v___x_1556_, 2);
                    if lean_obj_tag(v_declName_1557_) == 1 {
                        v_pre_1558_ = lean_ctor_get(v_declName_1557_, 0);
                        lean_inc(v_pre_1558_);
                        if lean_obj_tag(v_pre_1558_) == 1 {
                            v_pre_1559_ = lean_ctor_get(v_pre_1558_, 0);
                            lean_inc(v_pre_1559_);
                            if lean_obj_tag(v_pre_1559_) == 1 {
                                v_pre_1560_ = lean_ctor_get(v_pre_1559_, 0);
                                lean_inc(v_pre_1560_);
                                if lean_obj_tag(v_pre_1560_) == 1 {
                                    v_pre_1561_ = lean_ctor_get(v_pre_1560_, 0);
                                    if lean_obj_tag(v_pre_1561_) == 0 {
                                        v_str_1562_ = lean_ctor_get(v_declName_1557_, 1);
                                        lean_inc_ref(v_str_1562_);
                                        lean_dec_ref_known(v_declName_1557_, 2);
                                        v_str_1563_ = lean_ctor_get(v_pre_1558_, 1);
                                        lean_inc_ref(v_str_1563_);
                                        lean_dec_ref_known(v_pre_1558_, 2);
                                        v_str_1564_ = lean_ctor_get(v_pre_1559_, 1);
                                        lean_inc_ref(v_str_1564_);
                                        lean_dec_ref_known(v_pre_1559_, 2);
                                        v_str_1565_ = lean_ctor_get(v_pre_1560_, 1);
                                        lean_inc_ref(v_str_1565_);
                                        lean_dec_ref_known(v_pre_1560_, 2);
                                        v___x_1566_ = l_Lean_Elab_checkSimprocType___closed__2;
                                        v___x_1567_ = lean_string_dec_eq(v_str_1565_, v___x_1566_);
                                        lean_dec_ref(v_str_1565_);
                                        if v___x_1567_ == 0 {
                                            lean_dec_ref(v_str_1564_);
                                            lean_dec_ref(v_str_1563_);
                                            lean_dec_ref(v_str_1562_);
                                            lean_del_object(v___x_1542_);
                                            v___y_1545_ = v_a_1536_;
                                            v___y_1546_ = v_a_1537_;
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_1568_ = l_Lean_Elab_checkSimprocType___closed__3;
                                            v___x_1569_ =
                                                lean_string_dec_eq(v_str_1564_, v___x_1568_);
                                            lean_dec_ref(v_str_1564_);
                                            if v___x_1569_ == 0 {
                                                lean_dec_ref(v_str_1563_);
                                                lean_dec_ref(v_str_1562_);
                                                lean_del_object(v___x_1542_);
                                                v___y_1545_ = v_a_1536_;
                                                v___y_1546_ = v_a_1537_;
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_1570_ =
                                                    l_Lean_Elab_checkSimprocType___closed__4;
                                                v___x_1571_ =
                                                    lean_string_dec_eq(v_str_1563_, v___x_1570_);
                                                lean_dec_ref(v_str_1563_);
                                                if v___x_1571_ == 0 {
                                                    lean_dec_ref(v_str_1562_);
                                                    lean_del_object(v___x_1542_);
                                                    v___y_1545_ = v_a_1536_;
                                                    v___y_1546_ = v_a_1537_;
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    v___x_1572_ =
                                                        l_Lean_Elab_checkSimprocType___closed__5;
                                                    v___x_1573_ = lean_string_dec_eq(
                                                        v_str_1562_,
                                                        v___x_1572_,
                                                    );
                                                    if v___x_1573_ == 0 {
                                                        v___x_1574_ = l_Lean_Elab_checkSimprocType___closed__12;
                                                        v___x_1575_ = lean_string_dec_eq(
                                                            v_str_1562_,
                                                            v___x_1574_,
                                                        );
                                                        lean_dec_ref(v_str_1562_);
                                                        if v___x_1575_ == 0 {
                                                            lean_del_object(v___x_1542_);
                                                            v___y_1545_ = v_a_1536_;
                                                            v___y_1546_ = v_a_1537_;
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            lean_dec(v_a_1540_);
                                                            lean_dec(v_declName_1535_);
                                                            v___x_1576_ =
                                                                lean_box((v___x_1575_) as usize);
                                                            if v_isShared_1543_ == 0 {
                                                                lean_ctor_set(
                                                                    v___x_1542_,
                                                                    0,
                                                                    v___x_1576_,
                                                                );
                                                                v___x_1578_ = v___x_1542_;
                                                                state = 3;
                                                                continue;
                                                            } else {
                                                                v_reuseFailAlloc_1579_ =
                                                                    lean_alloc_ctor(
                                                                        0,
                                                                        1,
                                                                        (0) as u32,
                                                                    );
                                                                lean_ctor_set(
                                                                    v_reuseFailAlloc_1579_,
                                                                    0,
                                                                    v___x_1576_,
                                                                );
                                                                v___x_1578_ =
                                                                    v_reuseFailAlloc_1579_;
                                                                state = 3;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_str_1562_);
                                                        lean_dec(v_a_1540_);
                                                        lean_dec(v_declName_1535_);
                                                        v___x_1580_ = 0;
                                                        v___x_1581_ =
                                                            lean_box((v___x_1580_) as usize);
                                                        if v_isShared_1543_ == 0 {
                                                            lean_ctor_set(
                                                                v___x_1542_,
                                                                0,
                                                                v___x_1581_,
                                                            );
                                                            v___x_1583_ = v___x_1542_;
                                                            state = 4;
                                                            continue;
                                                        } else {
                                                            v_reuseFailAlloc_1584_ =
                                                                lean_alloc_ctor(0, 1, (0) as u32);
                                                            lean_ctor_set(
                                                                v_reuseFailAlloc_1584_,
                                                                0,
                                                                v___x_1581_,
                                                            );
                                                            v___x_1583_ = v_reuseFailAlloc_1584_;
                                                            state = 4;
                                                            continue;
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec_ref_known(v_pre_1560_, 2);
                                        lean_dec_ref_known(v_pre_1559_, 2);
                                        lean_dec_ref_known(v_pre_1558_, 2);
                                        lean_dec_ref_known(v_declName_1557_, 2);
                                        lean_del_object(v___x_1542_);
                                        v___y_1545_ = v_a_1536_;
                                        v___y_1546_ = v_a_1537_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_pre_1560_);
                                    lean_dec_ref_known(v_pre_1559_, 2);
                                    lean_dec_ref_known(v_pre_1558_, 2);
                                    lean_dec_ref_known(v_declName_1557_, 2);
                                    lean_del_object(v___x_1542_);
                                    v___y_1545_ = v_a_1536_;
                                    v___y_1546_ = v_a_1537_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v_pre_1558_, 2);
                                lean_dec(v_pre_1559_);
                                lean_dec_ref_known(v_declName_1557_, 2);
                                lean_del_object(v___x_1542_);
                                v___y_1545_ = v_a_1536_;
                                v___y_1546_ = v_a_1537_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_pre_1558_);
                            lean_dec_ref_known(v_declName_1557_, 2);
                            lean_del_object(v___x_1542_);
                            v___y_1545_ = v_a_1536_;
                            v___y_1546_ = v_a_1537_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_declName_1557_);
                        lean_del_object(v___x_1542_);
                        v___y_1545_ = v_a_1536_;
                        v___y_1546_ = v_a_1537_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_1556_);
                    lean_del_object(v___x_1542_);
                    v___y_1545_ = v_a_1536_;
                    v___y_1546_ = v_a_1537_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1547_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_checkSimprocType___closed__18),
                    core::ptr::addr_of_mut!(l_Lean_Elab_checkSimprocType___closed__18_once),
                    _init_l_Lean_Elab_checkSimprocType___closed__18,
                );
                v___x_1548_ = l_Lean_MessageData_ofName(v_declName_1535_);
                v___x_1549_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1549_, 0, v___x_1547_);
                lean_ctor_set(v___x_1549_, 1, v___x_1548_);
                v___x_1550_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_checkSimprocType___closed__20),
                    core::ptr::addr_of_mut!(l_Lean_Elab_checkSimprocType___closed__20_once),
                    _init_l_Lean_Elab_checkSimprocType___closed__20,
                );
                v___x_1551_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1551_, 0, v___x_1549_);
                lean_ctor_set(v___x_1551_, 1, v___x_1550_);
                v___x_1552_ = l_Lean_ConstantInfo_type(v_a_1540_);
                lean_dec(v_a_1540_);
                v___x_1553_ = l_Lean_indentExpr(v___x_1552_);
                v___x_1554_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1554_, 0, v___x_1551_);
                lean_ctor_set(v___x_1554_, 1, v___x_1553_);
                v___x_1555_ =
                    l_Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1___redArg(
                        v___x_1554_,
                        v___y_1545_,
                        v___y_1546_,
                    );
                return v___x_1555_;
            }
            3 => {
                return v___x_1578_;
            }
            4 => {
                return v___x_1583_;
            }
            5 => {
                if v_isShared_1589_ == 0 {
                    v___x_1591_ = v___x_1588_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
                    v___x_1591_ = v_reuseFailAlloc_1592_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1591_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_checkSimprocType___boxed(
    mut v_declName_1594_: *mut LeanObject,
    mut v_a_1595_: *mut LeanObject,
    mut v_a_1596_: *mut LeanObject,
    mut v_a_1597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1598_: *mut LeanObject = core::ptr::null_mut();
    v_res_1598_ = l_Lean_Elab_checkSimprocType(v_declName_1594_, v_a_1595_, v_a_1596_);
    lean_dec(v_a_1596_);
    lean_dec_ref(v_a_1595_);
    return v_res_1598_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1(
    mut v_00_u03b1_1599_: *mut LeanObject,
    mut v_msg_1600_: *mut LeanObject,
    mut v___y_1601_: *mut LeanObject,
    mut v___y_1602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    v___x_1604_ = l_Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1___redArg(
        v_msg_1600_,
        v___y_1601_,
        v___y_1602_,
    );
    return v___x_1604_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1___boxed(
    mut v_00_u03b1_1605_: *mut LeanObject,
    mut v_msg_1606_: *mut LeanObject,
    mut v___y_1607_: *mut LeanObject,
    mut v___y_1608_: *mut LeanObject,
    mut v___y_1609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1610_: *mut LeanObject = core::ptr::null_mut();
    v_res_1610_ = l_Lean_throwError___at___00Lean_Elab_checkSimprocType_spec__1(
        v_00_u03b1_1605_,
        v_msg_1606_,
        v___y_1607_,
        v___y_1608_,
    );
    lean_dec(v___y_1608_);
    lean_dec_ref(v___y_1607_);
    return v_res_1610_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0(
    mut v_00_u03b1_1611_: *mut LeanObject,
    mut v_constName_1612_: *mut LeanObject,
    mut v___y_1613_: *mut LeanObject,
    mut v___y_1614_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    v___x_1616_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0___redArg(v_constName_1612_, v___y_1613_, v___y_1614_);
    return v___x_1616_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0___boxed(
    mut v_00_u03b1_1617_: *mut LeanObject,
    mut v_constName_1618_: *mut LeanObject,
    mut v___y_1619_: *mut LeanObject,
    mut v___y_1620_: *mut LeanObject,
    mut v___y_1621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1622_: *mut LeanObject = core::ptr::null_mut();
    v_res_1622_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0(v_00_u03b1_1617_, v_constName_1618_, v___y_1619_, v___y_1620_);
    lean_dec(v___y_1620_);
    lean_dec_ref(v___y_1619_);
    return v_res_1622_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1(
    mut v_00_u03b1_1623_: *mut LeanObject,
    mut v_ref_1624_: *mut LeanObject,
    mut v_constName_1625_: *mut LeanObject,
    mut v___y_1626_: *mut LeanObject,
    mut v___y_1627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    v___x_1629_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___redArg(v_ref_1624_, v_constName_1625_, v___y_1626_, v___y_1627_);
    return v___x_1629_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_1630_: *mut LeanObject,
    mut v_ref_1631_: *mut LeanObject,
    mut v_constName_1632_: *mut LeanObject,
    mut v___y_1633_: *mut LeanObject,
    mut v___y_1634_: *mut LeanObject,
    mut v___y_1635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1636_: *mut LeanObject = core::ptr::null_mut();
    v_res_1636_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1(v_00_u03b1_1630_, v_ref_1631_, v_constName_1632_, v___y_1633_, v___y_1634_);
    lean_dec(v___y_1634_);
    lean_dec_ref(v___y_1633_);
    lean_dec(v_ref_1631_);
    return v_res_1636_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_1637_: *mut LeanObject,
    mut v_ref_1638_: *mut LeanObject,
    mut v_msg_1639_: *mut LeanObject,
    mut v_declHint_1640_: *mut LeanObject,
    mut v___y_1641_: *mut LeanObject,
    mut v___y_1642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    v___x_1644_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1638_, v_msg_1639_, v_declHint_1640_, v___y_1641_, v___y_1642_);
    return v___x_1644_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b1_1645_: *mut LeanObject,
    mut v_ref_1646_: *mut LeanObject,
    mut v_msg_1647_: *mut LeanObject,
    mut v_declHint_1648_: *mut LeanObject,
    mut v___y_1649_: *mut LeanObject,
    mut v___y_1650_: *mut LeanObject,
    mut v___y_1651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1652_: *mut LeanObject = core::ptr::null_mut();
    v_res_1652_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1645_, v_ref_1646_, v_msg_1647_, v_declHint_1648_, v___y_1649_, v___y_1650_);
    lean_dec(v___y_1650_);
    lean_dec_ref(v___y_1649_);
    lean_dec(v_ref_1646_);
    return v_res_1652_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(
    mut v_msg_1653_: *mut LeanObject,
    mut v_declHint_1654_: *mut LeanObject,
    mut v___y_1655_: *mut LeanObject,
    mut v___y_1656_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    v___x_1658_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1653_, v_declHint_1654_, v___y_1656_);
    return v___x_1658_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(
    mut v_msg_1659_: *mut LeanObject,
    mut v_declHint_1660_: *mut LeanObject,
    mut v___y_1661_: *mut LeanObject,
    mut v___y_1662_: *mut LeanObject,
    mut v___y_1663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1664_: *mut LeanObject = core::ptr::null_mut();
    v_res_1664_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1659_, v_declHint_1660_, v___y_1661_, v___y_1662_);
    lean_dec(v___y_1662_);
    lean_dec_ref(v___y_1661_);
    return v_res_1664_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6(
    mut v_00_u03b1_1665_: *mut LeanObject,
    mut v_ref_1666_: *mut LeanObject,
    mut v_msg_1667_: *mut LeanObject,
    mut v___y_1668_: *mut LeanObject,
    mut v___y_1669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    v___x_1671_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1666_, v_msg_1667_, v___y_1668_, v___y_1669_);
    return v___x_1671_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(
    mut v_00_u03b1_1672_: *mut LeanObject,
    mut v_ref_1673_: *mut LeanObject,
    mut v_msg_1674_: *mut LeanObject,
    mut v___y_1675_: *mut LeanObject,
    mut v___y_1676_: *mut LeanObject,
    mut v___y_1677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1678_: *mut LeanObject = core::ptr::null_mut();
    v_res_1678_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_1672_, v_ref_1673_, v_msg_1674_, v___y_1675_, v___y_1676_);
    lean_dec(v___y_1676_);
    lean_dec_ref(v___y_1675_);
    lean_dec(v_ref_1673_);
    return v_res_1678_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    v___x_1679_ = lean_box(0);
    v___x_1680_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1681_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1681_, 0, v___x_1680_);
    lean_ctor_set(v___x_1681_, 1, v___x_1679_);
    return v___x_1681_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut LeanObject = core::ptr::null_mut();
    v___x_1683_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg___closed__0);
    v___x_1684_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1684_, 0, v___x_1683_);
    return v___x_1684_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg___boxed(
    mut v___y_1685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1686_: *mut LeanObject = core::ptr::null_mut();
    v_res_1686_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg();
    return v_res_1686_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0(
    mut v_00_u03b1_1687_: *mut LeanObject,
    mut v___y_1688_: *mut LeanObject,
    mut v___y_1689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    v___x_1691_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg();
    return v___x_1691_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___boxed(
    mut v_00_u03b1_1692_: *mut LeanObject,
    mut v___y_1693_: *mut LeanObject,
    mut v___y_1694_: *mut LeanObject,
    mut v___y_1695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1696_: *mut LeanObject = core::ptr::null_mut();
    v_res_1696_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0(
            v_00_u03b1_1692_,
            v___y_1693_,
            v___y_1694_,
        );
    lean_dec(v___y_1694_);
    lean_dec_ref(v___y_1693_);
    return v_res_1696_;
}
pub unsafe fn l_Lean_Elab_Command_elabSimprocPattern___lam__0(
    mut v___x_1697_: *mut LeanObject,
    mut v___x_1698_: *mut LeanObject,
    mut v___y_1699_: *mut LeanObject,
    mut v___y_1700_: *mut LeanObject,
    mut v___y_1701_: *mut LeanObject,
    mut v___y_1702_: *mut LeanObject,
    mut v___y_1703_: *mut LeanObject,
    mut v___y_1704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1715_: u8 = 0;
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1719_: u8 = 0;
    let mut v_a_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1723_: u8 = 0;
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1727_: u8 = 0;
    let mut v_a_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1731_: u8 = 0;
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1735_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1706_ =
                    l_Lean_realizeGlobalConstNoOverload(v___x_1697_, v___y_1703_, v___y_1704_);
                if lean_obj_tag(v___x_1706_) == 0 {
                    v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
                    lean_inc_n(v_a_1707_, 2);
                    lean_dec_ref_known(v___x_1706_, 1);
                    v___x_1708_ = l_Lean_Elab_checkSimprocType(v_a_1707_, v___y_1703_, v___y_1704_);
                    if lean_obj_tag(v___x_1708_) == 0 {
                        lean_dec_ref_known(v___x_1708_, 1);
                        v___x_1709_ = l_Lean_Elab_elabSimprocKeys(
                            v___x_1698_,
                            v___y_1701_,
                            v___y_1702_,
                            v___y_1703_,
                            v___y_1704_,
                        );
                        if lean_obj_tag(v___x_1709_) == 0 {
                            v_a_1710_ = lean_ctor_get(v___x_1709_, 0);
                            lean_inc(v_a_1710_);
                            lean_dec_ref_known(v___x_1709_, 1);
                            v___x_1711_ = l_Lean_Meta_Simp_registerSimproc(
                                v_a_1707_,
                                v_a_1710_,
                                v___y_1703_,
                                v___y_1704_,
                            );
                            return v___x_1711_;
                        } else {
                            lean_dec(v_a_1707_);
                            v_a_1712_ = lean_ctor_get(v___x_1709_, 0);
                            v_isSharedCheck_1719_ = (!lean_is_exclusive(v___x_1709_)) as u8;
                            if v_isSharedCheck_1719_ == 0 {
                                v___x_1714_ = v___x_1709_;
                                v_isShared_1715_ = v_isSharedCheck_1719_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1712_);
                                lean_dec(v___x_1709_);
                                v___x_1714_ = lean_box(0);
                                v_isShared_1715_ = v_isSharedCheck_1719_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_1707_);
                        lean_dec(v___x_1698_);
                        v_a_1720_ = lean_ctor_get(v___x_1708_, 0);
                        v_isSharedCheck_1727_ = (!lean_is_exclusive(v___x_1708_)) as u8;
                        if v_isSharedCheck_1727_ == 0 {
                            v___x_1722_ = v___x_1708_;
                            v_isShared_1723_ = v_isSharedCheck_1727_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1720_);
                            lean_dec(v___x_1708_);
                            v___x_1722_ = lean_box(0);
                            v_isShared_1723_ = v_isSharedCheck_1727_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_1698_);
                    v_a_1728_ = lean_ctor_get(v___x_1706_, 0);
                    v_isSharedCheck_1735_ = (!lean_is_exclusive(v___x_1706_)) as u8;
                    if v_isSharedCheck_1735_ == 0 {
                        v___x_1730_ = v___x_1706_;
                        v_isShared_1731_ = v_isSharedCheck_1735_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1728_);
                        lean_dec(v___x_1706_);
                        v___x_1730_ = lean_box(0);
                        v_isShared_1731_ = v_isSharedCheck_1735_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1715_ == 0 {
                    v___x_1717_ = v___x_1714_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1718_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1718_, 0, v_a_1712_);
                    v___x_1717_ = v_reuseFailAlloc_1718_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1717_;
            }
            3 => {
                if v_isShared_1723_ == 0 {
                    v___x_1725_ = v___x_1722_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1726_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1726_, 0, v_a_1720_);
                    v___x_1725_ = v_reuseFailAlloc_1726_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1725_;
            }
            5 => {
                if v_isShared_1731_ == 0 {
                    v___x_1733_ = v___x_1730_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1734_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1734_, 0, v_a_1728_);
                    v___x_1733_ = v_reuseFailAlloc_1734_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1733_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabSimprocPattern___lam__0___boxed(
    mut v___x_1736_: *mut LeanObject,
    mut v___x_1737_: *mut LeanObject,
    mut v___y_1738_: *mut LeanObject,
    mut v___y_1739_: *mut LeanObject,
    mut v___y_1740_: *mut LeanObject,
    mut v___y_1741_: *mut LeanObject,
    mut v___y_1742_: *mut LeanObject,
    mut v___y_1743_: *mut LeanObject,
    mut v___y_1744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1745_: *mut LeanObject = core::ptr::null_mut();
    v_res_1745_ = l_Lean_Elab_Command_elabSimprocPattern___lam__0(
        v___x_1736_,
        v___x_1737_,
        v___y_1738_,
        v___y_1739_,
        v___y_1740_,
        v___y_1741_,
        v___y_1742_,
        v___y_1743_,
    );
    lean_dec(v___y_1743_);
    lean_dec_ref(v___y_1742_);
    lean_dec(v___y_1741_);
    lean_dec_ref(v___y_1740_);
    lean_dec(v___y_1739_);
    lean_dec_ref(v___y_1738_);
    return v_res_1745_;
}
pub unsafe fn l_Lean_Elab_Command_elabSimprocPattern(
    mut v_stx_1752_: *mut LeanObject,
    mut v_a_1753_: *mut LeanObject,
    mut v_a_1754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: u8 = 0;
    v___x_1756_ = l_Lean_Elab_Command_elabSimprocPattern___closed__2;
    lean_inc(v_stx_1752_);
    v___x_1757_ = l_Lean_Syntax_isOfKind(v_stx_1752_, v___x_1756_);
    if v___x_1757_ == 0 {
        let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_stx_1752_);
        v___x_1758_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg();
        return v___x_1758_;
    } else {
        let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1761_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1763_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
        v___x_1759_ = lean_unsigned_to_nat(1);
        v___x_1760_ = l_Lean_Syntax_getArg(v_stx_1752_, v___x_1759_);
        v___x_1761_ = lean_unsigned_to_nat(3);
        v___x_1762_ = l_Lean_Syntax_getArg(v_stx_1752_, v___x_1761_);
        lean_dec(v_stx_1752_);
        v___f_1763_ = lean_alloc_closure(
            l_Lean_Elab_Command_elabSimprocPattern___lam__0___boxed as *mut core::ffi::c_void,
            9,
            2,
        );
        lean_closure_set(v___f_1763_, 0, v___x_1762_);
        lean_closure_set(v___f_1763_, 1, v___x_1760_);
        v___x_1764_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_1763_, v_a_1753_, v_a_1754_);
        return v___x_1764_;
    }
}
pub unsafe fn l_Lean_Elab_Command_elabSimprocPattern___boxed(
    mut v_stx_1765_: *mut LeanObject,
    mut v_a_1766_: *mut LeanObject,
    mut v_a_1767_: *mut LeanObject,
    mut v_a_1768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1769_: *mut LeanObject = core::ptr::null_mut();
    v_res_1769_ = l_Lean_Elab_Command_elabSimprocPattern(v_stx_1765_, v_a_1766_, v_a_1767_);
    lean_dec(v_a_1767_);
    lean_dec_ref(v_a_1766_);
    return v_res_1769_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1()
-> *mut LeanObject {
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    v___x_1779_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_1780_ = l_Lean_Elab_Command_elabSimprocPattern___closed__2;
    v___x_1781_ = l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3;
    v___x_1782_ = lean_alloc_closure(
        l_Lean_Elab_Command_elabSimprocPattern___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_1783_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_1779_,
        v___x_1780_,
        v___x_1781_,
        v___x_1782_,
    );
    return v___x_1783_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___boxed(
    mut v_a_1784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1785_: *mut LeanObject = core::ptr::null_mut();
    v_res_1785_ = l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1();
    return v_res_1785_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3()
-> *mut LeanObject {
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    v___x_1812_ = l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1___closed__3;
    v___x_1813_ = l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___closed__6;
    v___x_1814_ = l_Lean_addBuiltinDeclarationRanges(v___x_1812_, v___x_1813_);
    return v___x_1814_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3___boxed(
    mut v_a_1815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1816_: *mut LeanObject = core::ptr::null_mut();
    v_res_1816_ = l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3();
    return v_res_1816_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    v___x_1826_ = lean_box(0);
    v___x_1827_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__3;
    v___x_1828_ = l_Lean_mkConst(v___x_1827_, v___x_1826_);
    return v___x_1828_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__7()
-> *mut LeanObject {
    let mut v___x_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    v___x_1836_ = lean_box(0);
    v___x_1837_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__6;
    v___x_1838_ = l_Lean_mkConst(v___x_1837_, v___x_1836_);
    return v___x_1838_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__10()
-> *mut LeanObject {
    let mut v___x_1846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    v___x_1846_ = lean_box(0);
    v___x_1847_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__9;
    v___x_1848_ = l_Lean_mkConst(v___x_1847_, v___x_1846_);
    return v___x_1848_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__14()
-> *mut LeanObject {
    let mut v___x_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    v___x_1855_ = lean_box(0);
    v___x_1856_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__13;
    v___x_1857_ = l_Lean_mkConst(v___x_1856_, v___x_1855_);
    return v___x_1857_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__17()
-> *mut LeanObject {
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    v___x_1863_ = lean_box(0);
    v___x_1864_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__16;
    v___x_1865_ = l_Lean_mkConst(v___x_1864_, v___x_1863_);
    return v___x_1865_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__20()
-> *mut LeanObject {
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    v___x_1873_ = lean_box(0);
    v___x_1874_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__19;
    v___x_1875_ = l_Lean_mkConst(v___x_1874_, v___x_1873_);
    return v___x_1875_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__24()
-> *mut LeanObject {
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    v___x_1882_ = lean_box(0);
    v___x_1883_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__23;
    v___x_1884_ = l_Lean_mkConst(v___x_1883_, v___x_1882_);
    return v___x_1884_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__27()
-> *mut LeanObject {
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    v___x_1892_ = lean_box(0);
    v___x_1893_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__26;
    v___x_1894_ = l_Lean_mkConst(v___x_1893_, v___x_1892_);
    return v___x_1894_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__30()
-> *mut LeanObject {
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    v___x_1902_ = lean_box(0);
    v___x_1903_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__29;
    v___x_1904_ = l_Lean_mkConst(v___x_1903_, v___x_1902_);
    return v___x_1904_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__33()
-> *mut LeanObject {
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    v___x_1912_ = lean_box(0);
    v___x_1913_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__32;
    v___x_1914_ = l_Lean_mkConst(v___x_1913_, v___x_1912_);
    return v___x_1914_;
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0(
    mut v_nilFn_1915_: *mut LeanObject,
    mut v_consFn_1916_: *mut LeanObject,
    mut v_x_1917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1917_) == 0 {
                    lean_dec_ref(v_consFn_1916_);
                    lean_inc_ref(v_nilFn_1915_);
                    return v_nilFn_1915_;
                } else {
                    v_head_1918_ = lean_ctor_get(v_x_1917_, 0);
                    lean_inc(v_head_1918_);
                    v_tail_1919_ = lean_ctor_get(v_x_1917_, 1);
                    lean_inc(v_tail_1919_);
                    lean_dec_ref_known(v_x_1917_, 2);
                    match lean_obj_tag(v_head_1918_) {
                        0 => {
                            v___x_1924_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__4_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__4);
                            v___y_1921_ = v___x_1924_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v___x_1925_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__7), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__7_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__7);
                            v___y_1921_ = v___x_1925_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            v_a_1926_ = lean_ctor_get(v_head_1918_, 0);
                            lean_inc_ref(v_a_1926_);
                            lean_dec_ref_known(v_head_1918_, 1);
                            v___x_1927_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__10), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__10_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__10);
                            if lean_obj_tag(v_a_1926_) == 0 {
                                v___x_1928_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__14_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__14);
                                v___x_1929_ = l_Lean_Expr_lit___override(v_a_1926_);
                                v___x_1930_ = l_Lean_Expr_app___override(v___x_1928_, v___x_1929_);
                                v___x_1931_ = l_Lean_Expr_app___override(v___x_1927_, v___x_1930_);
                                v___y_1921_ = v___x_1931_;
                                state = 1;
                                continue;
                            } else {
                                v___x_1932_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__17), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__17_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__17);
                                v___x_1933_ = l_Lean_Expr_lit___override(v_a_1926_);
                                v___x_1934_ = l_Lean_Expr_app___override(v___x_1932_, v___x_1933_);
                                v___x_1935_ = l_Lean_Expr_app___override(v___x_1927_, v___x_1934_);
                                v___y_1921_ = v___x_1935_;
                                state = 1;
                                continue;
                            }
                        }
                        3 => {
                            v_a_1936_ = lean_ctor_get(v_head_1918_, 0);
                            lean_inc(v_a_1936_);
                            v_a_1937_ = lean_ctor_get(v_head_1918_, 1);
                            lean_inc(v_a_1937_);
                            lean_dec_ref_known(v_head_1918_, 2);
                            v___x_1938_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__20), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__20_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__20);
                            v___x_1939_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__24), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__24_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__24);
                            v___x_1940_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_1936_);
                            v___x_1941_ = l_Lean_Expr_app___override(v___x_1939_, v___x_1940_);
                            v___x_1942_ = l_Lean_mkNatLit(v_a_1937_);
                            v___x_1943_ = l_Lean_mkAppB(v___x_1938_, v___x_1941_, v___x_1942_);
                            v___y_1921_ = v___x_1943_;
                            state = 1;
                            continue;
                        }
                        4 => {
                            v_a_1944_ = lean_ctor_get(v_head_1918_, 0);
                            lean_inc(v_a_1944_);
                            v_a_1945_ = lean_ctor_get(v_head_1918_, 1);
                            lean_inc(v_a_1945_);
                            lean_dec_ref_known(v_head_1918_, 2);
                            v___x_1946_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__27), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__27_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__27);
                            v___x_1947_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_1944_);
                            v___x_1948_ = l_Lean_mkNatLit(v_a_1945_);
                            v___x_1949_ = l_Lean_mkAppB(v___x_1946_, v___x_1947_, v___x_1948_);
                            v___y_1921_ = v___x_1949_;
                            state = 1;
                            continue;
                        }
                        5 => {
                            v___x_1950_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__30), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__30_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__30);
                            v___y_1921_ = v___x_1950_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_a_1951_ = lean_ctor_get(v_head_1918_, 0);
                            lean_inc(v_a_1951_);
                            v_a_1952_ = lean_ctor_get(v_head_1918_, 1);
                            lean_inc(v_a_1952_);
                            v_a_1953_ = lean_ctor_get(v_head_1918_, 2);
                            lean_inc(v_a_1953_);
                            lean_dec_ref_known(v_head_1918_, 3);
                            v___x_1954_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__33), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__33_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__33);
                            v___x_1955_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_1951_);
                            v___x_1956_ = l_Lean_mkNatLit(v_a_1952_);
                            v___x_1957_ = l_Lean_mkNatLit(v_a_1953_);
                            v___x_1958_ =
                                l_Lean_mkApp3(v___x_1954_, v___x_1955_, v___x_1956_, v___x_1957_);
                            v___y_1921_ = v___x_1958_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                lean_inc_ref(v_consFn_1916_);
                v___x_1922_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0(v_nilFn_1915_, v_consFn_1916_, v_tail_1919_);
                v___x_1923_ = l_Lean_mkAppB(v_consFn_1916_, v___y_1921_, v___x_1922_);
                return v___x_1923_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___boxed(
    mut v_nilFn_1959_: *mut LeanObject,
    mut v_consFn_1960_: *mut LeanObject,
    mut v_x_1961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1962_: *mut LeanObject = core::ptr::null_mut();
    v_res_1962_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0(v_nilFn_1959_, v_consFn_1960_, v_x_1961_);
    lean_dec_ref(v_nilFn_1959_);
    return v_res_1962_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__4()
-> *mut LeanObject {
    let mut v___x_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    v___x_1971_ = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__3;
    v___x_1972_ = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__2;
    v___x_1973_ = l_Lean_mkConst(v___x_1972_, v___x_1971_);
    return v___x_1973_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__9()
-> *mut LeanObject {
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    v___x_1981_ = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__3;
    v___x_1982_ = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__8;
    v___x_1983_ = l_Lean_mkConst(v___x_1982_, v___x_1981_);
    return v___x_1983_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__12()
-> *mut LeanObject {
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    v___x_1988_ = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__3;
    v___x_1989_ = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__11;
    v___x_1990_ = l_Lean_mkConst(v___x_1989_, v___x_1988_);
    return v___x_1990_;
}
pub unsafe fn l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0(
    mut v___x_1993_: *mut LeanObject,
    mut v___x_1994_: *mut LeanObject,
    mut v___x_1995_: *mut LeanObject,
    mut v___x_1996_: *mut LeanObject,
    mut v___y_1997_: *mut LeanObject,
    mut v___y_1998_: *mut LeanObject,
    mut v___y_1999_: *mut LeanObject,
    mut v___y_2000_: *mut LeanObject,
    mut v___y_2001_: *mut LeanObject,
    mut v___y_2002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nil_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cons_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2042_: u8 = 0;
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2046_: u8 = 0;
    let mut v___x_2047_: u8 = 0;
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2059_: u8 = 0;
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2063_: u8 = 0;
    let mut v_a_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2067_: u8 = 0;
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2071_: u8 = 0;
    let mut v_a_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2075_: u8 = 0;
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2079_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2004_ =
                    l_Lean_realizeGlobalConstNoOverload(v___x_1993_, v___y_2001_, v___y_2002_);
                if lean_obj_tag(v___x_2004_) == 0 {
                    v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
                    lean_inc_n(v_a_2005_, 2);
                    lean_dec_ref_known(v___x_2004_, 1);
                    v___x_2006_ = l_Lean_Elab_checkSimprocType(v_a_2005_, v___y_2001_, v___y_2002_);
                    if lean_obj_tag(v___x_2006_) == 0 {
                        v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
                        lean_inc(v_a_2007_);
                        lean_dec_ref_known(v___x_2006_, 1);
                        v___x_2008_ = l_Lean_Elab_elabSimprocKeys(
                            v___x_1994_,
                            v___y_1999_,
                            v___y_2000_,
                            v___y_2001_,
                            v___y_2002_,
                        );
                        if lean_obj_tag(v___x_2008_) == 0 {
                            v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
                            lean_inc(v_a_2009_);
                            lean_dec_ref_known(v___x_2008_, 1);
                            v___x_2047_ = (lean_unbox(v_a_2007_) as u8);
                            lean_dec(v_a_2007_);
                            if v___x_2047_ == 0 {
                                v___x_2048_ = l_Lean_Elab_checkSimprocType___closed__3;
                                v___x_2049_ = l_Lean_Elab_checkSimprocType___closed__4;
                                v___x_2050_ = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__13;
                                lean_inc_ref(v___x_1995_);
                                v___x_2051_ = l_Lean_Name_mkStr4(
                                    v___x_1995_,
                                    v___x_2048_,
                                    v___x_2049_,
                                    v___x_2050_,
                                );
                                v___y_2011_ = v___x_2051_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2052_ = l_Lean_Elab_checkSimprocType___closed__3;
                                v___x_2053_ = l_Lean_Elab_checkSimprocType___closed__4;
                                v___x_2054_ = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__14;
                                lean_inc_ref(v___x_1995_);
                                v___x_2055_ = l_Lean_Name_mkStr4(
                                    v___x_1995_,
                                    v___x_2052_,
                                    v___x_2053_,
                                    v___x_2054_,
                                );
                                v___y_2011_ = v___x_2055_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_2007_);
                            lean_dec(v_a_2005_);
                            lean_dec_ref(v___x_1995_);
                            v_a_2056_ = lean_ctor_get(v___x_2008_, 0);
                            v_isSharedCheck_2063_ = (!lean_is_exclusive(v___x_2008_)) as u8;
                            if v_isSharedCheck_2063_ == 0 {
                                v___x_2058_ = v___x_2008_;
                                v_isShared_2059_ = v_isSharedCheck_2063_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_2056_);
                                lean_dec(v___x_2008_);
                                v___x_2058_ = lean_box(0);
                                v_isShared_2059_ = v_isSharedCheck_2063_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_2005_);
                        lean_dec_ref(v___x_1995_);
                        lean_dec(v___x_1994_);
                        v_a_2064_ = lean_ctor_get(v___x_2006_, 0);
                        v_isSharedCheck_2071_ = (!lean_is_exclusive(v___x_2006_)) as u8;
                        if v_isSharedCheck_2071_ == 0 {
                            v___x_2066_ = v___x_2006_;
                            v_isShared_2067_ = v_isSharedCheck_2071_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2064_);
                            lean_dec(v___x_2006_);
                            v___x_2066_ = lean_box(0);
                            v_isShared_2067_ = v_isSharedCheck_2071_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_1995_);
                    lean_dec(v___x_1994_);
                    v_a_2072_ = lean_ctor_get(v___x_2004_, 0);
                    v_isSharedCheck_2079_ = (!lean_is_exclusive(v___x_2004_)) as u8;
                    if v_isSharedCheck_2079_ == 0 {
                        v___x_2074_ = v___x_2004_;
                        v_isShared_2075_ = v_isSharedCheck_2079_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2072_);
                        lean_dec(v___x_2004_);
                        v___x_2074_ = lean_box(0);
                        v_isShared_2075_ = v_isSharedCheck_2079_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2012_ = lean_box(0);
                v___x_2013_ = l_Lean_mkConst(v___y_2011_, v___x_2012_);
                lean_inc_n(v_a_2005_, 2);
                v___x_2014_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_2005_);
                v___x_2015_ = l_Lean_Elab_checkSimprocType___closed__3;
                v___x_2016_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__0;
                v___x_2017_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0___closed__1;
                v___x_2018_ =
                    l_Lean_Name_mkStr4(v___x_1995_, v___x_2015_, v___x_2016_, v___x_2017_);
                v___x_2019_ = l_Lean_mkConst(v___x_2018_, v___x_2012_);
                v___x_2020_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__4
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__4_once
                    ),
                    _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__4,
                );
                v___x_2021_ = l_Lean_mkConst(v_a_2005_, v___x_2012_);
                v___x_2022_ = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__6;
                v___x_2023_ = l_Lean_Name_append(v_a_2005_, v___x_2022_);
                v___x_2024_ = l_Lean_Core_mkFreshUserName(v___x_2023_, v___y_2001_, v___y_2002_);
                if lean_obj_tag(v___x_2024_) == 0 {
                    v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
                    lean_inc(v_a_2025_);
                    lean_dec_ref_known(v___x_2024_, 1);
                    v___x_2026_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__9
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__9_once
                        ),
                        _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__9,
                    );
                    lean_inc_ref_n(v___x_2019_, 2);
                    v_nil_2027_ = l_Lean_Expr_app___override(v___x_2026_, v___x_2019_);
                    v___x_2028_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__12), core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__12_once), _init_l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___closed__12);
                    v_cons_2029_ = l_Lean_Expr_app___override(v___x_2028_, v___x_2019_);
                    v___x_2030_ = lean_array_to_list(v_a_2009_);
                    v___x_2031_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabSimprocPatternBuiltin_spec__0(v_nil_2027_, v_cons_2029_, v___x_2030_);
                    lean_dec_ref(v_nil_2027_);
                    v___x_2032_ = l_Lean_mkAppB(v___x_2020_, v___x_2019_, v___x_2031_);
                    v___x_2033_ = lean_mk_empty_array_with_capacity(v___x_1996_);
                    v___x_2034_ = lean_array_push(v___x_2033_, v___x_2014_);
                    v___x_2035_ = lean_array_push(v___x_2034_, v___x_2032_);
                    v___x_2036_ = lean_array_push(v___x_2035_, v___x_2021_);
                    v___x_2037_ = l_Lean_mkAppN(v___x_2013_, v___x_2036_);
                    lean_dec_ref(v___x_2036_);
                    v___x_2038_ =
                        l_Lean_declareBuiltin(v_a_2025_, v___x_2037_, v___y_2001_, v___y_2002_);
                    return v___x_2038_;
                } else {
                    lean_dec_ref(v___x_2021_);
                    lean_dec_ref(v___x_2019_);
                    lean_dec_ref(v___x_2014_);
                    lean_dec_ref(v___x_2013_);
                    lean_dec(v_a_2009_);
                    v_a_2039_ = lean_ctor_get(v___x_2024_, 0);
                    v_isSharedCheck_2046_ = (!lean_is_exclusive(v___x_2024_)) as u8;
                    if v_isSharedCheck_2046_ == 0 {
                        v___x_2041_ = v___x_2024_;
                        v_isShared_2042_ = v_isSharedCheck_2046_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2039_);
                        lean_dec(v___x_2024_);
                        v___x_2041_ = lean_box(0);
                        v_isShared_2042_ = v_isSharedCheck_2046_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2042_ == 0 {
                    v___x_2044_ = v___x_2041_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
                    v___x_2044_ = v_reuseFailAlloc_2045_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2044_;
            }
            4 => {
                if v_isShared_2059_ == 0 {
                    v___x_2061_ = v___x_2058_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2062_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2062_, 0, v_a_2056_);
                    v___x_2061_ = v_reuseFailAlloc_2062_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2061_;
            }
            6 => {
                if v_isShared_2067_ == 0 {
                    v___x_2069_ = v___x_2066_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2070_, 0, v_a_2064_);
                    v___x_2069_ = v_reuseFailAlloc_2070_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2069_;
            }
            8 => {
                if v_isShared_2075_ == 0 {
                    v___x_2077_ = v___x_2074_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
                    v___x_2077_ = v_reuseFailAlloc_2078_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2077_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___boxed(
    mut v___x_2080_: *mut LeanObject,
    mut v___x_2081_: *mut LeanObject,
    mut v___x_2082_: *mut LeanObject,
    mut v___x_2083_: *mut LeanObject,
    mut v___y_2084_: *mut LeanObject,
    mut v___y_2085_: *mut LeanObject,
    mut v___y_2086_: *mut LeanObject,
    mut v___y_2087_: *mut LeanObject,
    mut v___y_2088_: *mut LeanObject,
    mut v___y_2089_: *mut LeanObject,
    mut v___y_2090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2091_: *mut LeanObject = core::ptr::null_mut();
    v_res_2091_ = l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0(
        v___x_2080_,
        v___x_2081_,
        v___x_2082_,
        v___x_2083_,
        v___y_2084_,
        v___y_2085_,
        v___y_2086_,
        v___y_2087_,
        v___y_2088_,
        v___y_2089_,
    );
    lean_dec(v___y_2089_);
    lean_dec_ref(v___y_2088_);
    lean_dec(v___y_2087_);
    lean_dec_ref(v___y_2086_);
    lean_dec(v___y_2085_);
    lean_dec_ref(v___y_2084_);
    lean_dec(v___x_2083_);
    return v_res_2091_;
}
pub unsafe fn l_Lean_Elab_Command_elabSimprocPatternBuiltin(
    mut v_stx_2097_: *mut LeanObject,
    mut v_a_2098_: *mut LeanObject,
    mut v_a_2099_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: u8 = 0;
    v___x_2101_ = l_Lean_Elab_checkSimprocType___closed__2;
    v___x_2102_ = l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1;
    lean_inc(v_stx_2097_);
    v___x_2103_ = l_Lean_Syntax_isOfKind(v_stx_2097_, v___x_2102_);
    if v___x_2103_ == 0 {
        let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_stx_2097_);
        v___x_2104_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabSimprocPattern_spec__0___redArg();
        return v___x_2104_;
    } else {
        let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2109_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
        v___x_2105_ = lean_unsigned_to_nat(1);
        v___x_2106_ = l_Lean_Syntax_getArg(v_stx_2097_, v___x_2105_);
        v___x_2107_ = lean_unsigned_to_nat(3);
        v___x_2108_ = l_Lean_Syntax_getArg(v_stx_2097_, v___x_2107_);
        lean_dec(v_stx_2097_);
        v___f_2109_ = lean_alloc_closure(
            l_Lean_Elab_Command_elabSimprocPatternBuiltin___lam__0___boxed
                as *mut core::ffi::c_void,
            11,
            4,
        );
        lean_closure_set(v___f_2109_, 0, v___x_2108_);
        lean_closure_set(v___f_2109_, 1, v___x_2106_);
        lean_closure_set(v___f_2109_, 2, v___x_2101_);
        lean_closure_set(v___f_2109_, 3, v___x_2107_);
        v___x_2110_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2109_, v_a_2098_, v_a_2099_);
        return v___x_2110_;
    }
}
pub unsafe fn l_Lean_Elab_Command_elabSimprocPatternBuiltin___boxed(
    mut v_stx_2111_: *mut LeanObject,
    mut v_a_2112_: *mut LeanObject,
    mut v_a_2113_: *mut LeanObject,
    mut v_a_2114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2115_: *mut LeanObject = core::ptr::null_mut();
    v_res_2115_ = l_Lean_Elab_Command_elabSimprocPatternBuiltin(v_stx_2111_, v_a_2112_, v_a_2113_);
    lean_dec(v_a_2113_);
    lean_dec_ref(v_a_2112_);
    return v_res_2115_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1()
-> *mut LeanObject {
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    v___x_2123_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_2124_ = l_Lean_Elab_Command_elabSimprocPatternBuiltin___closed__1;
    v___x_2125_ = l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1;
    v___x_2126_ = lean_alloc_closure(
        l_Lean_Elab_Command_elabSimprocPatternBuiltin___boxed as *mut core::ffi::c_void,
        4,
        0,
    );
    v___x_2127_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_2123_,
        v___x_2124_,
        v___x_2125_,
        v___x_2126_,
    );
    return v___x_2127_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___boxed(
    mut v_a_2128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2129_: *mut LeanObject = core::ptr::null_mut();
    v_res_2129_ = l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1();
    return v_res_2129_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3()
-> *mut LeanObject {
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    v___x_2156_ = l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1___closed__1;
    v___x_2157_ = l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___closed__6;
    v___x_2158_ = l_Lean_addBuiltinDeclarationRanges(v___x_2156_, v___x_2157_);
    return v___x_2158_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3___boxed(
    mut v_a_2159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2160_: *mut LeanObject = core::ptr::null_mut();
    v_res_2160_ = l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3();
    return v_res_2160_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Simproc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPattern___regBuiltin_Lean_Elab_Command_elabSimprocPattern_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Simproc_0__Lean_Elab_Command_elabSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabSimprocPatternBuiltin_declRange__3();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Simproc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Simproc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Simproc(builtin);
}

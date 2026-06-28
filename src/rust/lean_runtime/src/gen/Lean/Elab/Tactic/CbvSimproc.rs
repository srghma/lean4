// Lean compiler output
// Module: Lean.Elab.Tactic.CbvSimproc
// Imports: Init.CbvSimproc Lean.Meta.Tactic.Cbv.CbvSimproc Lean.Elab.Command
use crate::r#gen::Init::CbvSimproc::{
    initialize_Init_CbvSimproc, runtime_initialize_Init_CbvSimproc,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_Name_mkStr5, l_Lean_Syntax_getArg, l_Lean_Syntax_isOfKind,
    l_Lean_replaceRef,
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
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get, lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity,
    lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox,
    lean_unsigned_to_nat,
};
pub static l_Lean_Elab_elabCbvSimprocPattern___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Elab_elabCbvSimprocPattern___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Elab_elabCbvSimprocPattern___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabCbvSimprocPattern___closed__0_value) as *mut LeanObject;
pub static l_Lean_Elab_elabCbvSimprocPattern___closed__1_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Elab_elabCbvSimprocPattern___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabCbvSimprocPattern___closed__1_value) as *mut LeanObject;
pub static l_Lean_Elab_elabCbvSimprocPattern___closed__2_value: LeanCtorObject<10> =
    LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Elab_elabCbvSimprocPattern___closed__0_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_elabCbvSimprocPattern___closed__1_value)
                as *mut LeanObject,
            16843009 as *mut LeanObject,
            65537 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_elabCbvSimprocPattern___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabCbvSimprocPattern___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_elabCbvSimprocPattern___closed__3_value: LeanCtorObject<7> =
    LeanCtorObject {
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
static mut l_Lean_Elab_elabCbvSimprocPattern___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_elabCbvSimprocPattern___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_mkSimprocPatternFromExpr___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Elab_mkSimprocPatternFromExpr___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 1,
        m_objs: [(((1 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Elab_mkSimprocPatternFromExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_mkSimprocPatternFromExpr___closed__0_value) as *mut LeanObject;
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value: LeanStringObject<24> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value: LeanStringObject<79> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value: LeanStringObject<68> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12: *mut LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12_value) as *mut LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__0_value: LeanStringObject<19> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__2_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkCbvSimprocType___closed__0_value: LeanStringObject<52> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_checkCbvSimprocType___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_checkCbvSimprocType___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkCbvSimprocType___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkCbvSimprocType___closed__2_value: LeanStringObject<5> =
    LeanStringObject {
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
static mut l_Lean_Elab_checkCbvSimprocType___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut LeanObject;
pub static l_Lean_Elab_checkCbvSimprocType___closed__3_value: LeanStringObject<5> =
    LeanStringObject {
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
static mut l_Lean_Elab_checkCbvSimprocType___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value) as *mut LeanObject;
pub static l_Lean_Elab_checkCbvSimprocType___closed__4_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_checkCbvSimprocType___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__4_value) as *mut LeanObject;
pub static l_Lean_Elab_checkCbvSimprocType___closed__5_value: LeanStringObject<5> =
    LeanStringObject {
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
static mut l_Lean_Elab_checkCbvSimprocType___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__5_value) as *mut LeanObject;
pub static l_Lean_Elab_checkCbvSimprocType___closed__6_value: LeanStringObject<8> =
    LeanStringObject {
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
static mut l_Lean_Elab_checkCbvSimprocType___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__6_value) as *mut LeanObject;
static l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value)
                as *mut LeanObject,
            15449383196166861506 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_2: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__4_value)
                as *mut LeanObject,
            4034176598647545331 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_3: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_2)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__5_value)
                as *mut LeanObject,
            13806531830123099675 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_checkCbvSimprocType___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__7_value_aux_3)
            as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__6_value) as *mut LeanObject,
        4585357269266081267 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_checkCbvSimprocType___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__7_value) as *mut LeanObject;
static mut l_Lean_Elab_checkCbvSimprocType___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkCbvSimprocType___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_checkCbvSimprocType___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkCbvSimprocType___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkCbvSimprocType___closed__10_value: LeanStringObject<9> =
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
static mut l_Lean_Elab_checkCbvSimprocType___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__10_value) as *mut LeanObject;
static mut l_Lean_Elab_checkCbvSimprocType___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkCbvSimprocType___closed__11: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_checkCbvSimprocType___closed__12_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkCbvSimprocType___closed__12: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_checkCbvSimprocType___closed__13_value: LeanStringObject<11> =
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
static mut l_Lean_Elab_checkCbvSimprocType___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__13_value) as *mut LeanObject;
static mut l_Lean_Elab_checkCbvSimprocType___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_checkCbvSimprocType___closed__14: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabCbvSimprocPattern___closed__0_value: LeanStringObject<7> =
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
static mut l_Lean_Elab_Command_elabCbvSimprocPattern___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPattern___closed__1_value: LeanStringObject<18> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabCbvSimprocPattern___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__1_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__1_value)
                as *mut LeanObject,
            5000477209128750040 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__1_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [67, 111, 109, 109, 97, 110, 100, 0]};
static mut l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__2_value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [101, 108, 97, 98, 67, 98, 118, 83, 105, 109, 112, 114, 111, 99, 80, 97, 116, 116, 101, 114, 110, 0]};
static mut l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__1_value) as *mut LeanObject,16981400742628996529 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__2_value) as *mut LeanObject,14237717666078075311 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [68, 105, 115, 99, 114, 84, 114, 101, 101, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [75, 101, 121, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__2_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [115, 116, 97, 114, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__2_value) as *mut LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut LeanObject,12558998168795833107 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut LeanObject,6571394212498793888 as *mut LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__2_value) as *mut LeanObject,4525596147727532808 as *mut LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__5_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 116, 104, 101, 114, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__5_value) as *mut LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut LeanObject,12558998168795833107 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut LeanObject,6571394212498793888 as *mut LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__5_value) as *mut LeanObject,11989153488816012938 as *mut LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6_value) as *mut LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__8_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [108, 105, 116, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__8_value) as *mut LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut LeanObject,12558998168795833107 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut LeanObject,6571394212498793888 as *mut LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__8_value) as *mut LeanObject,15074539318474479562 as *mut LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9_value) as *mut LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__11_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [76, 105, 116, 101, 114, 97, 108, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__12_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [110, 97, 116, 86, 97, 108, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__12_value) as *mut LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__11_value) as *mut LeanObject,7001815944269665831 as *mut LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__12_value) as *mut LeanObject,9295767770006931264 as *mut LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13_value) as *mut LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__15_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 116, 114, 86, 97, 108, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__15_value) as *mut LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__11_value) as *mut LeanObject,7001815944269665831 as *mut LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__15_value) as *mut LeanObject,2005404019190257220 as *mut LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16_value) as *mut LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__18_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [102, 118, 97, 114, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__18_value) as *mut LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut LeanObject,12558998168795833107 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut LeanObject,6571394212498793888 as *mut LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__18_value) as *mut LeanObject,3087321959384269759 as *mut LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19_value) as *mut LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__21_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [70, 86, 97, 114, 73, 100, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__21_value) as *mut LeanObject;
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__22_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__22: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__22_value) as *mut LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__21_value) as *mut LeanObject,6212595679582900358 as *mut LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__22_value) as *mut LeanObject,6968149084986791158 as *mut LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23_value) as *mut LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__25_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [99, 111, 110, 115, 116, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__25: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__25_value) as *mut LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut LeanObject,12558998168795833107 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut LeanObject,6571394212498793888 as *mut LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__25_value) as *mut LeanObject,17383108283035838098 as *mut LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26_value) as *mut LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__28_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [97, 114, 114, 111, 119, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__28: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__28_value) as *mut LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut LeanObject,12558998168795833107 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut LeanObject,6571394212498793888 as *mut LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__28_value) as *mut LeanObject,8457098344818307929 as *mut LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29_value) as *mut LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__31_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 114, 111, 106, 0]};
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__31: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__31_value) as *mut LeanObject;
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__3_value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__0_value) as *mut LeanObject,12558998168795833107 as *mut LeanObject] };
static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__1_value) as *mut LeanObject,6571394212498793888 as *mut LeanObject] };
pub static l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__31_value) as *mut LeanObject,12263618261203284320 as *mut LeanObject] };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32_value) as *mut LeanObject;
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__0_value:
    LeanStringObject<7> = LeanStringObject {
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
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__1_value:
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
    m_data: [67, 98, 118, 0],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__2_value:
    LeanStringObject<26> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3_value:
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
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__4_value:
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
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__4_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5_value_aux_0:
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
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3_value
        ) as *mut LeanObject,
        9582258842178272501 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5_value:
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
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__4_value
        ) as *mut LeanObject,
        8414467900391110369 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6_value:
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
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6_value)
        as *mut LeanObject;
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__8_value:
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
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__8_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__9_value:
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
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__8_value
        ) as *mut LeanObject,
        13812150225987229964 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__9_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__10_value:
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
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__10: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__10_value
)
    as *mut LeanObject;
static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11_value_aux_0:
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
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3_value
        ) as *mut LeanObject,
        9582258842178272501 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11_value:
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
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__10_value
        ) as *mut LeanObject,
        18135193680607614554 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11_value
)
    as *mut LeanObject;
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__13_value:
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
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__13: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__13_value
)
    as *mut LeanObject;
static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14_value_aux_0:
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
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__3_value
        ) as *mut LeanObject,
        9582258842178272501 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14_value:
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
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__13_value
        ) as *mut LeanObject,
        8614124190858717794 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14_value
)
    as *mut LeanObject;
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__0_value: LeanStringObject<
    25,
> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__0_value)
        as *mut LeanObject;
static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value_aux_1: LeanCtorObject<3> =
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
                l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value_aux_0
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPattern___closed__0_value)
                as *mut LeanObject,
            8018486133748762727 as *mut LeanObject,
        ],
    };
pub static l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value: LeanCtorObject<3> =
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
                l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value_aux_1
            ) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__0_value)
                as *mut LeanObject,
            2235975067317863979 as *mut LeanObject,
        ],
    };
static mut l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__0_value: LeanStringObject<29> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [101, 108, 97, 98, 67, 98, 118, 83, 105, 109, 112, 114, 111, 99, 80, 97, 116, 116, 101, 114, 110, 66, 117, 105, 108, 116, 105, 110, 0]};
static mut l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__0_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_checkCbvSimprocType___closed__2_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__0_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__1_value) as *mut LeanObject,16981400742628996529 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__0_value) as *mut LeanObject,8968079526420962855 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_Elab_elabCbvSimprocPattern___lam__0(mut v_x_1134_: *mut LeanObject) -> u8 {
    let mut v___x_1135_: u8 = 0;
    v___x_1135_ = 0;
    return v___x_1135_;
}
pub unsafe fn l_Lean_Elab_elabCbvSimprocPattern___lam__0___boxed(
    mut v_x_1136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1137_: u8 = 0;
    let mut v_r_1138_: *mut LeanObject = core::ptr::null_mut();
    v_res_1137_ = l_Lean_Elab_elabCbvSimprocPattern___lam__0(v_x_1136_);
    lean_dec(v_x_1136_);
    v_r_1138_ = lean_box((v_res_1137_) as usize);
    return v_r_1138_;
}
pub unsafe fn l_Lean_Elab_elabCbvSimprocPattern___lam__1(
    mut v_stx_1139_: *mut LeanObject,
    mut v___x_1140_: *mut LeanObject,
    mut v___x_1141_: u8,
    mut v___y_1142_: *mut LeanObject,
    mut v___y_1143_: *mut LeanObject,
    mut v___y_1144_: *mut LeanObject,
    mut v___y_1145_: *mut LeanObject,
    mut v___y_1146_: *mut LeanObject,
    mut v___y_1147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: u8 = 0;
    let mut v___x_1152_: u8 = 0;
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1156_: u8 = 0;
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1160_: u8 = 0;
    let mut v_unused_1161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1165_: u8 = 0;
    let mut v___x_1167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1168_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_1149_) == 0 {
                    v_a_1150_ = lean_ctor_get(v___x_1149_, 0);
                    lean_inc(v_a_1150_);
                    lean_dec_ref_known(v___x_1149_, 1);
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
                    if lean_obj_tag(v___x_1153_) == 0 {
                        v_isSharedCheck_1160_ = (!lean_is_exclusive(v___x_1153_)) as u8;
                        if v_isSharedCheck_1160_ == 0 {
                            v_unused_1161_ = lean_ctor_get(v___x_1153_, 0);
                            lean_dec(v_unused_1161_);
                            v___x_1155_ = v___x_1153_;
                            v_isShared_1156_ = v_isSharedCheck_1160_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_1153_);
                            v___x_1155_ = lean_box(0);
                            v_isShared_1156_ = v_isSharedCheck_1160_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1150_);
                        v_a_1162_ = lean_ctor_get(v___x_1153_, 0);
                        v_isSharedCheck_1169_ = (!lean_is_exclusive(v___x_1153_)) as u8;
                        if v_isSharedCheck_1169_ == 0 {
                            v___x_1164_ = v___x_1153_;
                            v_isShared_1165_ = v_isSharedCheck_1169_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1162_);
                            lean_dec(v___x_1153_);
                            v___x_1164_ = lean_box(0);
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
                    lean_ctor_set(v___x_1155_, 0, v_a_1150_);
                    v___x_1158_ = v___x_1155_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1150_);
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
                    v_reuseFailAlloc_1168_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_a_1162_);
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
    mut v_stx_1170_: *mut LeanObject,
    mut v___x_1171_: *mut LeanObject,
    mut v___x_1172_: *mut LeanObject,
    mut v___y_1173_: *mut LeanObject,
    mut v___y_1174_: *mut LeanObject,
    mut v___y_1175_: *mut LeanObject,
    mut v___y_1176_: *mut LeanObject,
    mut v___y_1177_: *mut LeanObject,
    mut v___y_1178_: *mut LeanObject,
    mut v___y_1179_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_356__boxed_1180_: u8 = 0;
    let mut v_res_1181_: *mut LeanObject = core::ptr::null_mut();
    v___x_356__boxed_1180_ = (lean_unbox(v___x_1172_) as u8);
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
    lean_dec(v___y_1178_);
    lean_dec_ref(v___y_1177_);
    lean_dec(v___y_1176_);
    lean_dec_ref(v___y_1175_);
    lean_dec(v___y_1174_);
    lean_dec_ref(v___y_1173_);
    return v_res_1181_;
}
pub unsafe fn l_Lean_Elab_elabCbvSimprocPattern(
    mut v_stx_1196_: *mut LeanObject,
    mut v_a_1197_: *mut LeanObject,
    mut v_a_1198_: *mut LeanObject,
    mut v_a_1199_: *mut LeanObject,
    mut v_a_1200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: u8 = 0;
    let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_go_1205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1212_: u8 = 0;
    let mut v_fst_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1217_: u8 = 0;
    let mut v_a_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1221_: u8 = 0;
    let mut v___x_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1202_ = lean_box(0);
                v___x_1203_ = 1;
                v___x_1204_ = lean_box((v___x_1203_) as usize);
                v_go_1205_ = lean_alloc_closure(
                    l_Lean_Elab_elabCbvSimprocPattern___lam__1___boxed as *mut core::ffi::c_void,
                    10,
                    3,
                );
                lean_closure_set(v_go_1205_, 0, v_stx_1196_);
                lean_closure_set(v_go_1205_, 1, v___x_1202_);
                lean_closure_set(v_go_1205_, 2, v___x_1204_);
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
                if lean_obj_tag(v___x_1208_) == 0 {
                    v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
                    v_isSharedCheck_1217_ = (!lean_is_exclusive(v___x_1208_)) as u8;
                    if v_isSharedCheck_1217_ == 0 {
                        v___x_1211_ = v___x_1208_;
                        v_isShared_1212_ = v_isSharedCheck_1217_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1209_);
                        lean_dec(v___x_1208_);
                        v___x_1211_ = lean_box(0);
                        v_isShared_1212_ = v_isSharedCheck_1217_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1218_ = lean_ctor_get(v___x_1208_, 0);
                    v_isSharedCheck_1225_ = (!lean_is_exclusive(v___x_1208_)) as u8;
                    if v_isSharedCheck_1225_ == 0 {
                        v___x_1220_ = v___x_1208_;
                        v_isShared_1221_ = v_isSharedCheck_1225_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1218_);
                        lean_dec(v___x_1208_);
                        v___x_1220_ = lean_box(0);
                        v_isShared_1221_ = v_isSharedCheck_1225_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1213_ = lean_ctor_get(v_a_1209_, 0);
                lean_inc(v_fst_1213_);
                lean_dec(v_a_1209_);
                if v_isShared_1212_ == 0 {
                    lean_ctor_set(v___x_1211_, 0, v_fst_1213_);
                    v___x_1215_ = v___x_1211_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_fst_1213_);
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
                    v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
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
    mut v_stx_1226_: *mut LeanObject,
    mut v_a_1227_: *mut LeanObject,
    mut v_a_1228_: *mut LeanObject,
    mut v_a_1229_: *mut LeanObject,
    mut v_a_1230_: *mut LeanObject,
    mut v_a_1231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1232_: *mut LeanObject = core::ptr::null_mut();
    v_res_1232_ =
        l_Lean_Elab_elabCbvSimprocPattern(v_stx_1226_, v_a_1227_, v_a_1228_, v_a_1229_, v_a_1230_);
    lean_dec(v_a_1230_);
    lean_dec_ref(v_a_1229_);
    lean_dec(v_a_1228_);
    lean_dec_ref(v_a_1227_);
    return v_res_1232_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg___lam__0(
    mut v_k_1233_: *mut LeanObject,
    mut v_b_1234_: *mut LeanObject,
    mut v_c_1235_: *mut LeanObject,
    mut v___y_1236_: *mut LeanObject,
    mut v___y_1237_: *mut LeanObject,
    mut v___y_1238_: *mut LeanObject,
    mut v___y_1239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1241_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1239_);
    lean_inc_ref(v___y_1238_);
    lean_inc(v___y_1237_);
    lean_inc_ref(v___y_1236_);
    v___x_1241_ = lean_apply_7(
        v_k_1233_,
        v_b_1234_,
        v_c_1235_,
        v___y_1236_,
        v___y_1237_,
        v___y_1238_,
        v___y_1239_,
        lean_box(0),
    );
    return v___x_1241_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg___lam__0___boxed(
    mut v_k_1242_: *mut LeanObject,
    mut v_b_1243_: *mut LeanObject,
    mut v_c_1244_: *mut LeanObject,
    mut v___y_1245_: *mut LeanObject,
    mut v___y_1246_: *mut LeanObject,
    mut v___y_1247_: *mut LeanObject,
    mut v___y_1248_: *mut LeanObject,
    mut v___y_1249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1250_: *mut LeanObject = core::ptr::null_mut();
    v_res_1250_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg___lam__0(v_k_1242_, v_b_1243_, v_c_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
    lean_dec(v___y_1248_);
    lean_dec_ref(v___y_1247_);
    lean_dec(v___y_1246_);
    lean_dec_ref(v___y_1245_);
    return v_res_1250_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg(
    mut v_e_1251_: *mut LeanObject,
    mut v_k_1252_: *mut LeanObject,
    mut v_cleanupAnnotations_1253_: u8,
    mut v___y_1254_: *mut LeanObject,
    mut v___y_1255_: *mut LeanObject,
    mut v___y_1256_: *mut LeanObject,
    mut v___y_1257_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1260_: u8 = 0;
    let mut v___x_1261_: u8 = 0;
    let mut v___x_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1267_: u8 = 0;
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1271_: u8 = 0;
    let mut v_a_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1275_: u8 = 0;
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1279_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1259_ = lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                lean_closure_set(v___f_1259_, 0, v_k_1252_);
                v___x_1260_ = 1;
                v___x_1261_ = 0;
                v___x_1262_ = lean_box(0);
                v___x_1263_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    lean_box(0),
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
                if lean_obj_tag(v___x_1263_) == 0 {
                    v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
                    v_isSharedCheck_1271_ = (!lean_is_exclusive(v___x_1263_)) as u8;
                    if v_isSharedCheck_1271_ == 0 {
                        v___x_1266_ = v___x_1263_;
                        v_isShared_1267_ = v_isSharedCheck_1271_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1264_);
                        lean_dec(v___x_1263_);
                        v___x_1266_ = lean_box(0);
                        v_isShared_1267_ = v_isSharedCheck_1271_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1272_ = lean_ctor_get(v___x_1263_, 0);
                    v_isSharedCheck_1279_ = (!lean_is_exclusive(v___x_1263_)) as u8;
                    if v_isSharedCheck_1279_ == 0 {
                        v___x_1274_ = v___x_1263_;
                        v_isShared_1275_ = v_isSharedCheck_1279_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1272_);
                        lean_dec(v___x_1263_);
                        v___x_1274_ = lean_box(0);
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
                    v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
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
                    v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1278_, 0, v_a_1272_);
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
    mut v_e_1280_: *mut LeanObject,
    mut v_k_1281_: *mut LeanObject,
    mut v_cleanupAnnotations_1282_: *mut LeanObject,
    mut v___y_1283_: *mut LeanObject,
    mut v___y_1284_: *mut LeanObject,
    mut v___y_1285_: *mut LeanObject,
    mut v___y_1286_: *mut LeanObject,
    mut v___y_1287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1288_: u8 = 0;
    let mut v_res_1289_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1288_ = (lean_unbox(v_cleanupAnnotations_1282_) as u8);
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
    lean_dec(v___y_1286_);
    lean_dec_ref(v___y_1285_);
    lean_dec(v___y_1284_);
    lean_dec_ref(v___y_1283_);
    return v_res_1289_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0(
    mut v_00_u03b1_1290_: *mut LeanObject,
    mut v_e_1291_: *mut LeanObject,
    mut v_k_1292_: *mut LeanObject,
    mut v_cleanupAnnotations_1293_: u8,
    mut v___y_1294_: *mut LeanObject,
    mut v___y_1295_: *mut LeanObject,
    mut v___y_1296_: *mut LeanObject,
    mut v___y_1297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_1300_: *mut LeanObject,
    mut v_e_1301_: *mut LeanObject,
    mut v_k_1302_: *mut LeanObject,
    mut v_cleanupAnnotations_1303_: *mut LeanObject,
    mut v___y_1304_: *mut LeanObject,
    mut v___y_1305_: *mut LeanObject,
    mut v___y_1306_: *mut LeanObject,
    mut v___y_1307_: *mut LeanObject,
    mut v___y_1308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cleanupAnnotations_boxed_1309_: u8 = 0;
    let mut v_res_1310_: *mut LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_1309_ = (lean_unbox(v_cleanupAnnotations_1303_) as u8);
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
    lean_dec(v___y_1307_);
    lean_dec_ref(v___y_1306_);
    lean_dec(v___y_1305_);
    lean_dec_ref(v___y_1304_);
    return v_res_1310_;
}
pub unsafe fn l_Lean_Elab_mkSimprocPatternFromExpr___lam__0(
    mut v___x_1311_: u8,
    mut v_args_1312_: *mut LeanObject,
    mut v_body_1313_: *mut LeanObject,
    mut v___y_1314_: *mut LeanObject,
    mut v___y_1315_: *mut LeanObject,
    mut v___y_1316_: *mut LeanObject,
    mut v___y_1317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1319_: u8 = 0;
    let mut v___x_1320_: u8 = 0;
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___x_1322_: *mut LeanObject,
    mut v_args_1323_: *mut LeanObject,
    mut v_body_1324_: *mut LeanObject,
    mut v___y_1325_: *mut LeanObject,
    mut v___y_1326_: *mut LeanObject,
    mut v___y_1327_: *mut LeanObject,
    mut v___y_1328_: *mut LeanObject,
    mut v___y_1329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_637__boxed_1330_: u8 = 0;
    let mut v_res_1331_: *mut LeanObject = core::ptr::null_mut();
    v___x_637__boxed_1330_ = (lean_unbox(v___x_1322_) as u8);
    v_res_1331_ = l_Lean_Elab_mkSimprocPatternFromExpr___lam__0(
        v___x_637__boxed_1330_,
        v_args_1323_,
        v_body_1324_,
        v___y_1325_,
        v___y_1326_,
        v___y_1327_,
        v___y_1328_,
    );
    lean_dec(v___y_1328_);
    lean_dec_ref(v___y_1327_);
    lean_dec(v___y_1326_);
    lean_dec_ref(v___y_1325_);
    lean_dec_ref(v_args_1323_);
    return v_res_1331_;
}
pub unsafe fn l_Lean_Elab_mkSimprocPatternFromExpr(
    mut v_e_1335_: *mut LeanObject,
    mut v_a_1336_: *mut LeanObject,
    mut v_a_1337_: *mut LeanObject,
    mut v_a_1338_: *mut LeanObject,
    mut v_a_1339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1341_: u8 = 0;
    let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_paramNames_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: u8 = 0;
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1351_: u8 = 0;
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1361_: u8 = 0;
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1365_: u8 = 0;
    let mut v_a_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1369_: u8 = 0;
    let mut v___x_1371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1373_: u8 = 0;
    let mut v_a_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1377_: u8 = 0;
    let mut v___x_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1380_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_1342_) == 0 {
                    v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
                    lean_inc(v_a_1343_);
                    lean_dec_ref_known(v___x_1342_, 1);
                    v_paramNames_1344_ = lean_ctor_get(v_a_1343_, 0);
                    lean_inc_ref(v_paramNames_1344_);
                    v_expr_1345_ = lean_ctor_get(v_a_1343_, 2);
                    lean_inc_ref(v_expr_1345_);
                    lean_dec(v_a_1343_);
                    v___f_1346_ = l_Lean_Elab_mkSimprocPatternFromExpr___closed__0;
                    v___x_1347_ = 0;
                    v___x_1348_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_mkSimprocPatternFromExpr_spec__0___redArg(v_expr_1345_, v___f_1346_, v___x_1347_, v_a_1336_, v_a_1337_, v_a_1338_, v_a_1339_);
                    if lean_obj_tag(v___x_1348_) == 0 {
                        v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
                        lean_inc(v_a_1349_);
                        lean_dec_ref_known(v___x_1348_, 1);
                        v___x_1350_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1350_, 0, v_a_1349_);
                        v___x_1351_ = 0;
                        v___x_1352_ = lean_box(0);
                        v___x_1353_ = l_Lean_Meta_mkFreshExprMVar(
                            v___x_1350_,
                            v___x_1351_,
                            v___x_1352_,
                            v_a_1336_,
                            v_a_1337_,
                            v_a_1338_,
                            v_a_1339_,
                        );
                        if lean_obj_tag(v___x_1353_) == 0 {
                            v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
                            lean_inc(v_a_1354_);
                            lean_dec_ref_known(v___x_1353_, 1);
                            v___x_1355_ = lean_array_to_list(v_paramNames_1344_);
                            v___x_1356_ = lean_box(0);
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
                            lean_dec_ref(v_paramNames_1344_);
                            v_a_1358_ = lean_ctor_get(v___x_1353_, 0);
                            v_isSharedCheck_1365_ = (!lean_is_exclusive(v___x_1353_)) as u8;
                            if v_isSharedCheck_1365_ == 0 {
                                v___x_1360_ = v___x_1353_;
                                v_isShared_1361_ = v_isSharedCheck_1365_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1358_);
                                lean_dec(v___x_1353_);
                                v___x_1360_ = lean_box(0);
                                v_isShared_1361_ = v_isSharedCheck_1365_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_paramNames_1344_);
                        v_a_1366_ = lean_ctor_get(v___x_1348_, 0);
                        v_isSharedCheck_1373_ = (!lean_is_exclusive(v___x_1348_)) as u8;
                        if v_isSharedCheck_1373_ == 0 {
                            v___x_1368_ = v___x_1348_;
                            v_isShared_1369_ = v_isSharedCheck_1373_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1366_);
                            lean_dec(v___x_1348_);
                            v___x_1368_ = lean_box(0);
                            v_isShared_1369_ = v_isSharedCheck_1373_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_1374_ = lean_ctor_get(v___x_1342_, 0);
                    v_isSharedCheck_1381_ = (!lean_is_exclusive(v___x_1342_)) as u8;
                    if v_isSharedCheck_1381_ == 0 {
                        v___x_1376_ = v___x_1342_;
                        v_isShared_1377_ = v_isSharedCheck_1381_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1374_);
                        lean_dec(v___x_1342_);
                        v___x_1376_ = lean_box(0);
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
                    v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
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
                    v_reuseFailAlloc_1372_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1372_, 0, v_a_1366_);
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
                    v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_a_1374_);
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
    mut v_e_1382_: *mut LeanObject,
    mut v_a_1383_: *mut LeanObject,
    mut v_a_1384_: *mut LeanObject,
    mut v_a_1385_: *mut LeanObject,
    mut v_a_1386_: *mut LeanObject,
    mut v_a_1387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1388_: *mut LeanObject = core::ptr::null_mut();
    v_res_1388_ =
        l_Lean_Elab_mkSimprocPatternFromExpr(v_e_1382_, v_a_1383_, v_a_1384_, v_a_1385_, v_a_1386_);
    lean_dec(v_a_1386_);
    lean_dec_ref(v_a_1385_);
    lean_dec(v_a_1384_);
    lean_dec_ref(v_a_1383_);
    return v_res_1388_;
}
pub unsafe fn l_Lean_Elab_elabCbvSimprocKeys(
    mut v_stx_1389_: *mut LeanObject,
    mut v_a_1390_: *mut LeanObject,
    mut v_a_1391_: *mut LeanObject,
    mut v_a_1392_: *mut LeanObject,
    mut v_a_1393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1401_: u8 = 0;
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1406_: u8 = 0;
    let mut v_a_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1410_: u8 = 0;
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1414_: u8 = 0;
    let mut v_a_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1418_: u8 = 0;
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1421_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_1395_) == 0 {
                    v_a_1396_ = lean_ctor_get(v___x_1395_, 0);
                    lean_inc(v_a_1396_);
                    lean_dec_ref_known(v___x_1395_, 1);
                    v___x_1397_ = l_Lean_Elab_mkSimprocPatternFromExpr(
                        v_a_1396_, v_a_1390_, v_a_1391_, v_a_1392_, v_a_1393_,
                    );
                    if lean_obj_tag(v___x_1397_) == 0 {
                        v_a_1398_ = lean_ctor_get(v___x_1397_, 0);
                        v_isSharedCheck_1406_ = (!lean_is_exclusive(v___x_1397_)) as u8;
                        if v_isSharedCheck_1406_ == 0 {
                            v___x_1400_ = v___x_1397_;
                            v_isShared_1401_ = v_isSharedCheck_1406_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1398_);
                            lean_dec(v___x_1397_);
                            v___x_1400_ = lean_box(0);
                            v_isShared_1401_ = v_isSharedCheck_1406_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1407_ = lean_ctor_get(v___x_1397_, 0);
                        v_isSharedCheck_1414_ = (!lean_is_exclusive(v___x_1397_)) as u8;
                        if v_isSharedCheck_1414_ == 0 {
                            v___x_1409_ = v___x_1397_;
                            v_isShared_1410_ = v_isSharedCheck_1414_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1407_);
                            lean_dec(v___x_1397_);
                            v___x_1409_ = lean_box(0);
                            v_isShared_1410_ = v_isSharedCheck_1414_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_1415_ = lean_ctor_get(v___x_1395_, 0);
                    v_isSharedCheck_1422_ = (!lean_is_exclusive(v___x_1395_)) as u8;
                    if v_isSharedCheck_1422_ == 0 {
                        v___x_1417_ = v___x_1395_;
                        v_isShared_1418_ = v_isSharedCheck_1422_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_1415_);
                        lean_dec(v___x_1395_);
                        v___x_1417_ = lean_box(0);
                        v_isShared_1418_ = v_isSharedCheck_1422_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1402_ = l_Lean_Meta_Sym_Pattern_mkDiscrTreeKeys(v_a_1398_);
                if v_isShared_1401_ == 0 {
                    lean_ctor_set(v___x_1400_, 0, v___x_1402_);
                    v___x_1404_ = v___x_1400_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
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
                    v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1413_, 0, v_a_1407_);
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
                    v_reuseFailAlloc_1421_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1421_, 0, v_a_1415_);
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
    mut v_stx_1423_: *mut LeanObject,
    mut v_a_1424_: *mut LeanObject,
    mut v_a_1425_: *mut LeanObject,
    mut v_a_1426_: *mut LeanObject,
    mut v_a_1427_: *mut LeanObject,
    mut v_a_1428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1429_: *mut LeanObject = core::ptr::null_mut();
    v_res_1429_ =
        l_Lean_Elab_elabCbvSimprocKeys(v_stx_1423_, v_a_1424_, v_a_1425_, v_a_1426_, v_a_1427_);
    lean_dec(v_a_1427_);
    lean_dec_ref(v_a_1426_);
    lean_dec(v_a_1425_);
    lean_dec_ref(v_a_1424_);
    return v_res_1429_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0()
-> *mut LeanObject {
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    v___x_1430_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1430_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1432_: *mut LeanObject = core::ptr::null_mut();
    v___x_1431_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__0);
    v___x_1432_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1432_, 0, v___x_1431_);
    return v___x_1432_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2()
-> *mut LeanObject {
    let mut v___x_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    v___x_1433_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1);
    v___x_1434_ = lean_unsigned_to_nat(0);
    v___x_1435_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_1435_, 0, v___x_1434_);
    lean_ctor_set(v___x_1435_, 1, v___x_1434_);
    lean_ctor_set(v___x_1435_, 2, v___x_1434_);
    lean_ctor_set(v___x_1435_, 3, v___x_1434_);
    lean_ctor_set(v___x_1435_, 4, v___x_1433_);
    lean_ctor_set(v___x_1435_, 5, v___x_1433_);
    lean_ctor_set(v___x_1435_, 6, v___x_1433_);
    lean_ctor_set(v___x_1435_, 7, v___x_1433_);
    lean_ctor_set(v___x_1435_, 8, v___x_1433_);
    lean_ctor_set(v___x_1435_, 9, v___x_1433_);
    return v___x_1435_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3()
-> *mut LeanObject {
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    v___x_1436_ = lean_unsigned_to_nat(32);
    v___x_1437_ = lean_mk_empty_array_with_capacity(v___x_1436_);
    v___x_1438_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1438_, 0, v___x_1437_);
    return v___x_1438_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4()
-> *mut LeanObject {
    let mut v___x_1439_: usize = 0;
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    v___x_1439_ = 5usize;
    v___x_1440_ = lean_unsigned_to_nat(0);
    v___x_1441_ = lean_unsigned_to_nat(32);
    v___x_1442_ = lean_mk_empty_array_with_capacity(v___x_1441_);
    v___x_1443_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__3);
    v___x_1444_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1444_, 0, v___x_1443_);
    lean_ctor_set(v___x_1444_, 1, v___x_1442_);
    lean_ctor_set(v___x_1444_, 2, v___x_1440_);
    lean_ctor_set(v___x_1444_, 3, v___x_1440_);
    lean_ctor_set_usize(v___x_1444_, 4, v___x_1439_);
    return v___x_1444_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5()
-> *mut LeanObject {
    let mut v___x_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    v___x_1445_ = lean_box(1);
    v___x_1446_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__4);
    v___x_1447_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__1);
    v___x_1448_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1448_, 0, v___x_1447_);
    lean_ctor_set(v___x_1448_, 1, v___x_1446_);
    lean_ctor_set(v___x_1448_, 2, v___x_1445_);
    return v___x_1448_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2(
    mut v_msgData_1449_: *mut LeanObject,
    mut v___y_1450_: *mut LeanObject,
    mut v___y_1451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
    v___x_1453_ = lean_st_ref_get(v___y_1451_);
    v_env_1454_ = lean_ctor_get(v___x_1453_, 0);
    lean_inc_ref(v_env_1454_);
    lean_dec(v___x_1453_);
    v_options_1455_ = lean_ctor_get(v___y_1450_, 2);
    v___x_1456_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2);
    v___x_1457_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5);
    lean_inc_ref(v_options_1455_);
    v___x_1458_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_1458_, 0, v_env_1454_);
    lean_ctor_set(v___x_1458_, 1, v___x_1456_);
    lean_ctor_set(v___x_1458_, 2, v___x_1457_);
    lean_ctor_set(v___x_1458_, 3, v_options_1455_);
    v___x_1459_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_1459_, 0, v___x_1458_);
    lean_ctor_set(v___x_1459_, 1, v_msgData_1449_);
    v___x_1460_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1460_, 0, v___x_1459_);
    return v___x_1460_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___boxed(
    mut v_msgData_1461_: *mut LeanObject,
    mut v___y_1462_: *mut LeanObject,
    mut v___y_1463_: *mut LeanObject,
    mut v___y_1464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1465_: *mut LeanObject = core::ptr::null_mut();
    v_res_1465_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2(v_msgData_1461_, v___y_1462_, v___y_1463_);
    lean_dec(v___y_1463_);
    lean_dec_ref(v___y_1462_);
    return v_res_1465_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(
    mut v_msg_1466_: *mut LeanObject,
    mut v___y_1467_: *mut LeanObject,
    mut v___y_1468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1475_: u8 = 0;
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1470_ = lean_ctor_get(v___y_1467_, 5);
                v___x_1471_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2(v_msg_1466_, v___y_1467_, v___y_1468_);
                v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
                v_isSharedCheck_1480_ = (!lean_is_exclusive(v___x_1471_)) as u8;
                if v_isSharedCheck_1480_ == 0 {
                    v___x_1474_ = v___x_1471_;
                    v_isShared_1475_ = v_isSharedCheck_1480_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1472_);
                    lean_dec(v___x_1471_);
                    v___x_1474_ = lean_box(0);
                    v_isShared_1475_ = v_isSharedCheck_1480_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_1470_);
                v___x_1476_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1476_, 0, v_ref_1470_);
                lean_ctor_set(v___x_1476_, 1, v_a_1472_);
                if v_isShared_1475_ == 0 {
                    lean_ctor_set_tag(v___x_1474_, 1);
                    lean_ctor_set(v___x_1474_, 0, v___x_1476_);
                    v___x_1478_ = v___x_1474_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1479_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1479_, 0, v___x_1476_);
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
    mut v_msg_1481_: *mut LeanObject,
    mut v___y_1482_: *mut LeanObject,
    mut v___y_1483_: *mut LeanObject,
    mut v___y_1484_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1485_: *mut LeanObject = core::ptr::null_mut();
    v_res_1485_ = l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(
        v_msg_1481_,
        v___y_1482_,
        v___y_1483_,
    );
    lean_dec(v___y_1483_);
    lean_dec_ref(v___y_1482_);
    return v_res_1485_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    v___x_1487_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__0;
    v___x_1488_ = l_Lean_stringToMessageData(v___x_1487_);
    return v___x_1488_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1491_: *mut LeanObject = core::ptr::null_mut();
    v___x_1490_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__2;
    v___x_1491_ = l_Lean_stringToMessageData(v___x_1490_);
    return v___x_1491_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut LeanObject = core::ptr::null_mut();
    v___x_1493_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__4;
    v___x_1494_ = l_Lean_stringToMessageData(v___x_1493_);
    return v___x_1494_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7()
-> *mut LeanObject {
    let mut v___x_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    v___x_1496_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__6;
    v___x_1497_ = l_Lean_stringToMessageData(v___x_1496_);
    return v___x_1497_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9()
-> *mut LeanObject {
    let mut v___x_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut LeanObject = core::ptr::null_mut();
    v___x_1499_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__8;
    v___x_1500_ = l_Lean_stringToMessageData(v___x_1499_);
    return v___x_1500_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11()
-> *mut LeanObject {
    let mut v___x_1502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    v___x_1502_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__10;
    v___x_1503_ = l_Lean_stringToMessageData(v___x_1502_);
    return v___x_1503_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13()
-> *mut LeanObject {
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut LeanObject = core::ptr::null_mut();
    v___x_1505_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__12;
    v___x_1506_ = l_Lean_stringToMessageData(v___x_1505_);
    return v___x_1506_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(
    mut v_msg_1507_: *mut LeanObject,
    mut v_declHint_1508_: *mut LeanObject,
    mut v___y_1509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: u8 = 0;
    let mut v_isExporting_1514_: u8 = 0;
    let mut v___x_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: u8 = 0;
    let mut v___x_1518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_c_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1536_: u8 = 0;
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mod_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: u8 = 0;
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1568_: u8 = 0;
    let mut v___x_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1511_ = lean_st_ref_get(v___y_1509_);
                v_env_1512_ = lean_ctor_get(v___x_1511_, 0);
                lean_inc_ref(v_env_1512_);
                lean_dec(v___x_1511_);
                v___x_1513_ = l_Lean_Name_isAnonymous(v_declHint_1508_);
                if v___x_1513_ == 0 {
                    v_isExporting_1514_ = lean_ctor_get_uint8(
                        v_env_1512_,
                        (core::mem::size_of::<*mut LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_1514_ == 0 {
                        lean_dec_ref(v_env_1512_);
                        lean_dec(v_declHint_1508_);
                        v___x_1515_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_1515_, 0, v_msg_1507_);
                        return v___x_1515_;
                    } else {
                        lean_inc_ref(v_env_1512_);
                        v___x_1516_ = l_Lean_Environment_setExporting(v_env_1512_, v___x_1513_);
                        lean_inc(v_declHint_1508_);
                        lean_inc_ref(v___x_1516_);
                        v___x_1517_ = l_Lean_Environment_contains(
                            v___x_1516_,
                            v_declHint_1508_,
                            v_isExporting_1514_,
                        );
                        if v___x_1517_ == 0 {
                            lean_dec_ref(v___x_1516_);
                            lean_dec_ref(v_env_1512_);
                            lean_dec(v_declHint_1508_);
                            v___x_1518_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_1518_, 0, v_msg_1507_);
                            return v___x_1518_;
                        } else {
                            v___x_1519_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__2);
                            v___x_1520_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1_spec__2___closed__5);
                            v___x_1521_ = l_Lean_Options_empty;
                            v___x_1522_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v___x_1522_, 0, v___x_1516_);
                            lean_ctor_set(v___x_1522_, 1, v___x_1519_);
                            lean_ctor_set(v___x_1522_, 2, v___x_1520_);
                            lean_ctor_set(v___x_1522_, 3, v___x_1521_);
                            lean_inc(v_declHint_1508_);
                            v___x_1523_ =
                                l_Lean_MessageData_ofConstName(v_declHint_1508_, v___x_1513_);
                            v_c_1524_ = lean_alloc_ctor(3, 2, (0) as u32);
                            lean_ctor_set(v_c_1524_, 0, v___x_1522_);
                            lean_ctor_set(v_c_1524_, 1, v___x_1523_);
                            v___x_1525_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_1512_,
                                v_declHint_1508_,
                            );
                            if lean_obj_tag(v___x_1525_) == 0 {
                                lean_dec_ref(v_env_1512_);
                                lean_dec(v_declHint_1508_);
                                v___x_1526_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
                                v___x_1527_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1527_, 0, v___x_1526_);
                                lean_ctor_set(v___x_1527_, 1, v_c_1524_);
                                v___x_1528_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__3);
                                v___x_1529_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1529_, 0, v___x_1527_);
                                lean_ctor_set(v___x_1529_, 1, v___x_1528_);
                                v___x_1530_ = l_Lean_MessageData_note(v___x_1529_);
                                v___x_1531_ = lean_alloc_ctor(7, 2, (0) as u32);
                                lean_ctor_set(v___x_1531_, 0, v_msg_1507_);
                                lean_ctor_set(v___x_1531_, 1, v___x_1530_);
                                v___x_1532_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_1532_, 0, v___x_1531_);
                                return v___x_1532_;
                            } else {
                                v_val_1533_ = lean_ctor_get(v___x_1525_, 0);
                                v_isSharedCheck_1568_ = (!lean_is_exclusive(v___x_1525_)) as u8;
                                if v_isSharedCheck_1568_ == 0 {
                                    v___x_1535_ = v___x_1525_;
                                    v_isShared_1536_ = v_isSharedCheck_1568_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_val_1533_);
                                    lean_dec(v___x_1525_);
                                    v___x_1535_ = lean_box(0);
                                    v_isShared_1536_ = v_isSharedCheck_1568_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_env_1512_);
                    lean_dec(v_declHint_1508_);
                    v___x_1569_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1569_, 0, v_msg_1507_);
                    return v___x_1569_;
                }
            }
            1 => {
                v___x_1537_ = lean_box(0);
                v___x_1538_ = l_Lean_Environment_header(v_env_1512_);
                lean_dec_ref(v_env_1512_);
                v___x_1539_ = l_Lean_EnvironmentHeader_moduleNames(v___x_1538_);
                v_mod_1540_ = lean_array_get(v___x_1537_, v___x_1539_, v_val_1533_);
                lean_dec(v_val_1533_);
                lean_dec_ref(v___x_1539_);
                v___x_1541_ = l_Lean_isPrivateName(v_declHint_1508_);
                lean_dec(v_declHint_1508_);
                if v___x_1541_ == 0 {
                    v___x_1542_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__5);
                    v___x_1543_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1543_, 0, v___x_1542_);
                    lean_ctor_set(v___x_1543_, 1, v_c_1524_);
                    v___x_1544_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__7);
                    v___x_1545_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1545_, 0, v___x_1543_);
                    lean_ctor_set(v___x_1545_, 1, v___x_1544_);
                    v___x_1546_ = l_Lean_MessageData_ofName(v_mod_1540_);
                    v___x_1547_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1547_, 0, v___x_1545_);
                    lean_ctor_set(v___x_1547_, 1, v___x_1546_);
                    v___x_1548_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__9);
                    v___x_1549_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1549_, 0, v___x_1547_);
                    lean_ctor_set(v___x_1549_, 1, v___x_1548_);
                    v___x_1550_ = l_Lean_MessageData_note(v___x_1549_);
                    v___x_1551_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1551_, 0, v_msg_1507_);
                    lean_ctor_set(v___x_1551_, 1, v___x_1550_);
                    if v_isShared_1536_ == 0 {
                        lean_ctor_set_tag(v___x_1535_, 0);
                        lean_ctor_set(v___x_1535_, 0, v___x_1551_);
                        v___x_1553_ = v___x_1535_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1551_);
                        v___x_1553_ = v_reuseFailAlloc_1554_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1555_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__1);
                    v___x_1556_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1556_, 0, v___x_1555_);
                    lean_ctor_set(v___x_1556_, 1, v_c_1524_);
                    v___x_1557_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__11);
                    v___x_1558_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1558_, 0, v___x_1556_);
                    lean_ctor_set(v___x_1558_, 1, v___x_1557_);
                    v___x_1559_ = l_Lean_MessageData_ofName(v_mod_1540_);
                    v___x_1560_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1560_, 0, v___x_1558_);
                    lean_ctor_set(v___x_1560_, 1, v___x_1559_);
                    v___x_1561_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg___closed__13);
                    v___x_1562_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1562_, 0, v___x_1560_);
                    lean_ctor_set(v___x_1562_, 1, v___x_1561_);
                    v___x_1563_ = l_Lean_MessageData_note(v___x_1562_);
                    v___x_1564_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_1564_, 0, v_msg_1507_);
                    lean_ctor_set(v___x_1564_, 1, v___x_1563_);
                    if v_isShared_1536_ == 0 {
                        lean_ctor_set_tag(v___x_1535_, 0);
                        lean_ctor_set(v___x_1535_, 0, v___x_1564_);
                        v___x_1566_ = v___x_1535_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1567_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1567_, 0, v___x_1564_);
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
    mut v_msg_1570_: *mut LeanObject,
    mut v_declHint_1571_: *mut LeanObject,
    mut v___y_1572_: *mut LeanObject,
    mut v___y_1573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1574_: *mut LeanObject = core::ptr::null_mut();
    v_res_1574_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1570_, v_declHint_1571_, v___y_1572_);
    lean_dec(v___y_1572_);
    return v_res_1574_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(
    mut v_msg_1575_: *mut LeanObject,
    mut v_declHint_1576_: *mut LeanObject,
    mut v___y_1577_: *mut LeanObject,
    mut v___y_1578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1584_: u8 = 0;
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1590_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1580_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1575_, v_declHint_1576_, v___y_1578_);
                v_a_1581_ = lean_ctor_get(v___x_1580_, 0);
                v_isSharedCheck_1590_ = (!lean_is_exclusive(v___x_1580_)) as u8;
                if v_isSharedCheck_1590_ == 0 {
                    v___x_1583_ = v___x_1580_;
                    v_isShared_1584_ = v_isSharedCheck_1590_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_1581_);
                    lean_dec(v___x_1580_);
                    v___x_1583_ = lean_box(0);
                    v_isShared_1584_ = v_isSharedCheck_1590_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1585_ = l_Lean_unknownIdentifierMessageTag;
                v___x_1586_ = lean_alloc_ctor(8, 2, (0) as u32);
                lean_ctor_set(v___x_1586_, 0, v___x_1585_);
                lean_ctor_set(v___x_1586_, 1, v_a_1581_);
                if v_isShared_1584_ == 0 {
                    lean_ctor_set(v___x_1583_, 0, v___x_1586_);
                    v___x_1588_ = v___x_1583_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1589_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1586_);
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
    mut v_msg_1591_: *mut LeanObject,
    mut v_declHint_1592_: *mut LeanObject,
    mut v___y_1593_: *mut LeanObject,
    mut v___y_1594_: *mut LeanObject,
    mut v___y_1595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1596_: *mut LeanObject = core::ptr::null_mut();
    v_res_1596_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1591_, v_declHint_1592_, v___y_1593_, v___y_1594_);
    lean_dec(v___y_1594_);
    lean_dec_ref(v___y_1593_);
    return v_res_1596_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(
    mut v_ref_1597_: *mut LeanObject,
    mut v_msg_1598_: *mut LeanObject,
    mut v___y_1599_: *mut LeanObject,
    mut v___y_1600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_1608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_1609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_1610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_1612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1614_: u8 = 0;
    let mut v_cancelTk_x3f_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_1616_: u8 = 0;
    let mut v_inheritedTraceOptions_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    v_fileName_1602_ = lean_ctor_get(v___y_1599_, 0);
    v_fileMap_1603_ = lean_ctor_get(v___y_1599_, 1);
    v_options_1604_ = lean_ctor_get(v___y_1599_, 2);
    v_currRecDepth_1605_ = lean_ctor_get(v___y_1599_, 3);
    v_maxRecDepth_1606_ = lean_ctor_get(v___y_1599_, 4);
    v_ref_1607_ = lean_ctor_get(v___y_1599_, 5);
    v_currNamespace_1608_ = lean_ctor_get(v___y_1599_, 6);
    v_openDecls_1609_ = lean_ctor_get(v___y_1599_, 7);
    v_initHeartbeats_1610_ = lean_ctor_get(v___y_1599_, 8);
    v_maxHeartbeats_1611_ = lean_ctor_get(v___y_1599_, 9);
    v_quotContext_1612_ = lean_ctor_get(v___y_1599_, 10);
    v_currMacroScope_1613_ = lean_ctor_get(v___y_1599_, 11);
    v_diag_1614_ = lean_ctor_get_uint8(
        v___y_1599_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_1615_ = lean_ctor_get(v___y_1599_, 12);
    v_suppressElabErrors_1616_ = lean_ctor_get_uint8(
        v___y_1599_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_1617_ = lean_ctor_get(v___y_1599_, 13);
    v_ref_1618_ = l_Lean_replaceRef(v_ref_1597_, v_ref_1607_);
    lean_inc_ref(v_inheritedTraceOptions_1617_);
    lean_inc(v_cancelTk_x3f_1615_);
    lean_inc(v_currMacroScope_1613_);
    lean_inc(v_quotContext_1612_);
    lean_inc(v_maxHeartbeats_1611_);
    lean_inc(v_initHeartbeats_1610_);
    lean_inc(v_openDecls_1609_);
    lean_inc(v_currNamespace_1608_);
    lean_inc(v_maxRecDepth_1606_);
    lean_inc(v_currRecDepth_1605_);
    lean_inc_ref(v_options_1604_);
    lean_inc_ref(v_fileMap_1603_);
    lean_inc_ref(v_fileName_1602_);
    v___x_1619_ = lean_alloc_ctor(0, 14, (2) as u32);
    lean_ctor_set(v___x_1619_, 0, v_fileName_1602_);
    lean_ctor_set(v___x_1619_, 1, v_fileMap_1603_);
    lean_ctor_set(v___x_1619_, 2, v_options_1604_);
    lean_ctor_set(v___x_1619_, 3, v_currRecDepth_1605_);
    lean_ctor_set(v___x_1619_, 4, v_maxRecDepth_1606_);
    lean_ctor_set(v___x_1619_, 5, v_ref_1618_);
    lean_ctor_set(v___x_1619_, 6, v_currNamespace_1608_);
    lean_ctor_set(v___x_1619_, 7, v_openDecls_1609_);
    lean_ctor_set(v___x_1619_, 8, v_initHeartbeats_1610_);
    lean_ctor_set(v___x_1619_, 9, v_maxHeartbeats_1611_);
    lean_ctor_set(v___x_1619_, 10, v_quotContext_1612_);
    lean_ctor_set(v___x_1619_, 11, v_currMacroScope_1613_);
    lean_ctor_set(v___x_1619_, 12, v_cancelTk_x3f_1615_);
    lean_ctor_set(v___x_1619_, 13, v_inheritedTraceOptions_1617_);
    lean_ctor_set_uint8(
        v___x_1619_,
        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
        v_diag_1614_,
    );
    lean_ctor_set_uint8(
        v___x_1619_,
        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_1616_,
    );
    v___x_1620_ = l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(
        v_msg_1598_,
        v___x_1619_,
        v___y_1600_,
    );
    lean_dec_ref_known(v___x_1619_, 14);
    return v___x_1620_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg___boxed(
    mut v_ref_1621_: *mut LeanObject,
    mut v_msg_1622_: *mut LeanObject,
    mut v___y_1623_: *mut LeanObject,
    mut v___y_1624_: *mut LeanObject,
    mut v___y_1625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1626_: *mut LeanObject = core::ptr::null_mut();
    v_res_1626_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1621_, v_msg_1622_, v___y_1623_, v___y_1624_);
    lean_dec(v___y_1624_);
    lean_dec_ref(v___y_1623_);
    lean_dec(v_ref_1621_);
    return v_res_1626_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_ref_1627_: *mut LeanObject,
    mut v_msg_1628_: *mut LeanObject,
    mut v_declHint_1629_: *mut LeanObject,
    mut v___y_1630_: *mut LeanObject,
    mut v___y_1631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    v___x_1633_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5(v_msg_1628_, v_declHint_1629_, v___y_1630_, v___y_1631_);
    v_a_1634_ = lean_ctor_get(v___x_1633_, 0);
    lean_inc(v_a_1634_);
    lean_dec_ref(v___x_1633_);
    v___x_1635_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1627_, v_a_1634_, v___y_1630_, v___y_1631_);
    return v___x_1635_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_ref_1636_: *mut LeanObject,
    mut v_msg_1637_: *mut LeanObject,
    mut v_declHint_1638_: *mut LeanObject,
    mut v___y_1639_: *mut LeanObject,
    mut v___y_1640_: *mut LeanObject,
    mut v___y_1641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1642_: *mut LeanObject = core::ptr::null_mut();
    v_res_1642_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1636_, v_msg_1637_, v_declHint_1638_, v___y_1639_, v___y_1640_);
    lean_dec(v___y_1640_);
    lean_dec_ref(v___y_1639_);
    lean_dec(v_ref_1636_);
    return v_res_1642_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    v___x_1644_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_1645_ = l_Lean_stringToMessageData(v___x_1644_);
    return v___x_1645_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1648_: *mut LeanObject = core::ptr::null_mut();
    v___x_1647_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_1648_ = l_Lean_stringToMessageData(v___x_1647_);
    return v___x_1648_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg(
    mut v_ref_1649_: *mut LeanObject,
    mut v_constName_1650_: *mut LeanObject,
    mut v___y_1651_: *mut LeanObject,
    mut v___y_1652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: u8 = 0;
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    v___x_1654_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_1655_ = 0;
    lean_inc(v_constName_1650_);
    v___x_1656_ = l_Lean_MessageData_ofConstName(v_constName_1650_, v___x_1655_);
    v___x_1657_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1657_, 0, v___x_1654_);
    lean_ctor_set(v___x_1657_, 1, v___x_1656_);
    v___x_1658_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_1659_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1659_, 0, v___x_1657_);
    lean_ctor_set(v___x_1659_, 1, v___x_1658_);
    v___x_1660_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1649_, v___x_1659_, v_constName_1650_, v___y_1651_, v___y_1652_);
    return v___x_1660_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_1661_: *mut LeanObject,
    mut v_constName_1662_: *mut LeanObject,
    mut v___y_1663_: *mut LeanObject,
    mut v___y_1664_: *mut LeanObject,
    mut v___y_1665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1666_: *mut LeanObject = core::ptr::null_mut();
    v_res_1666_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg(v_ref_1661_, v_constName_1662_, v___y_1663_, v___y_1664_);
    lean_dec(v___y_1664_);
    lean_dec_ref(v___y_1663_);
    lean_dec(v_ref_1661_);
    return v_res_1666_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg(
    mut v_constName_1667_: *mut LeanObject,
    mut v___y_1668_: *mut LeanObject,
    mut v___y_1669_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
    v_ref_1671_ = lean_ctor_get(v___y_1668_, 5);
    v___x_1672_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg(v_ref_1671_, v_constName_1667_, v___y_1668_, v___y_1669_);
    return v___x_1672_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg___boxed(
    mut v_constName_1673_: *mut LeanObject,
    mut v___y_1674_: *mut LeanObject,
    mut v___y_1675_: *mut LeanObject,
    mut v___y_1676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1677_: *mut LeanObject = core::ptr::null_mut();
    v_res_1677_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg(v_constName_1673_, v___y_1674_, v___y_1675_);
    lean_dec(v___y_1675_);
    lean_dec_ref(v___y_1674_);
    return v_res_1677_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0(
    mut v_constName_1678_: *mut LeanObject,
    mut v___y_1679_: *mut LeanObject,
    mut v___y_1680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: u8 = 0;
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1690_: u8 = 0;
    let mut v___x_1692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1694_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1682_ = lean_st_ref_get(v___y_1680_);
                v_env_1683_ = lean_ctor_get(v___x_1682_, 0);
                lean_inc_ref(v_env_1683_);
                lean_dec(v___x_1682_);
                v___x_1684_ = 0;
                lean_inc(v_constName_1678_);
                v___x_1685_ =
                    l_Lean_Environment_find_x3f(v_env_1683_, v_constName_1678_, v___x_1684_);
                if lean_obj_tag(v___x_1685_) == 0 {
                    v___x_1686_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg(v_constName_1678_, v___y_1679_, v___y_1680_);
                    return v___x_1686_;
                } else {
                    lean_dec(v_constName_1678_);
                    v_val_1687_ = lean_ctor_get(v___x_1685_, 0);
                    v_isSharedCheck_1694_ = (!lean_is_exclusive(v___x_1685_)) as u8;
                    if v_isSharedCheck_1694_ == 0 {
                        v___x_1689_ = v___x_1685_;
                        v_isShared_1690_ = v_isSharedCheck_1694_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1687_);
                        lean_dec(v___x_1685_);
                        v___x_1689_ = lean_box(0);
                        v_isShared_1690_ = v_isSharedCheck_1694_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1690_ == 0 {
                    lean_ctor_set_tag(v___x_1689_, 0);
                    v___x_1692_ = v___x_1689_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1693_, 0, v_val_1687_);
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
    mut v_constName_1695_: *mut LeanObject,
    mut v___y_1696_: *mut LeanObject,
    mut v___y_1697_: *mut LeanObject,
    mut v___y_1698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1699_: *mut LeanObject = core::ptr::null_mut();
    v_res_1699_ = l_Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0(
        v_constName_1695_,
        v___y_1696_,
        v___y_1697_,
    );
    lean_dec(v___y_1697_);
    lean_dec_ref(v___y_1696_);
    return v_res_1699_;
}
pub unsafe fn _init_l_Lean_Elab_checkCbvSimprocType___closed__1() -> *mut LeanObject {
    let mut v___x_1701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    v___x_1701_ = l_Lean_Elab_checkCbvSimprocType___closed__0;
    v___x_1702_ = l_Lean_stringToMessageData(v___x_1701_);
    return v___x_1702_;
}
pub unsafe fn _init_l_Lean_Elab_checkCbvSimprocType___closed__8() -> *mut LeanObject {
    let mut v___x_1714_: u8 = 0;
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    v___x_1714_ = 0;
    v___x_1715_ = l_Lean_Elab_checkCbvSimprocType___closed__7;
    v___x_1716_ = l_Lean_MessageData_ofConstName(v___x_1715_, v___x_1714_);
    return v___x_1716_;
}
pub unsafe fn _init_l_Lean_Elab_checkCbvSimprocType___closed__9() -> *mut LeanObject {
    let mut v___x_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    v___x_1717_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__8_once),
        _init_l_Lean_Elab_checkCbvSimprocType___closed__8,
    );
    v___x_1718_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__1_once),
        _init_l_Lean_Elab_checkCbvSimprocType___closed__1,
    );
    v___x_1719_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1719_, 0, v___x_1718_);
    lean_ctor_set(v___x_1719_, 1, v___x_1717_);
    return v___x_1719_;
}
pub unsafe fn _init_l_Lean_Elab_checkCbvSimprocType___closed__11() -> *mut LeanObject {
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    v___x_1721_ = l_Lean_Elab_checkCbvSimprocType___closed__10;
    v___x_1722_ = l_Lean_stringToMessageData(v___x_1721_);
    return v___x_1722_;
}
pub unsafe fn _init_l_Lean_Elab_checkCbvSimprocType___closed__12() -> *mut LeanObject {
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    v___x_1723_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__11_once),
        _init_l_Lean_Elab_checkCbvSimprocType___closed__11,
    );
    v___x_1724_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__9_once),
        _init_l_Lean_Elab_checkCbvSimprocType___closed__9,
    );
    v___x_1725_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_1725_, 0, v___x_1724_);
    lean_ctor_set(v___x_1725_, 1, v___x_1723_);
    return v___x_1725_;
}
pub unsafe fn _init_l_Lean_Elab_checkCbvSimprocType___closed__14() -> *mut LeanObject {
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    v___x_1727_ = l_Lean_Elab_checkCbvSimprocType___closed__13;
    v___x_1728_ = l_Lean_stringToMessageData(v___x_1727_);
    return v___x_1728_;
}
pub unsafe fn l_Lean_Elab_checkCbvSimprocType(
    mut v_declName_1729_: *mut LeanObject,
    mut v_a_1730_: *mut LeanObject,
    mut v_a_1731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1737_: u8 = 0;
    let mut v___y_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_1761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1763_: u8 = 0;
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1765_: u8 = 0;
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: u8 = 0;
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: u8 = 0;
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: u8 = 0;
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1776_: u8 = 0;
    let mut v_a_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1780_: u8 = 0;
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1784_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_declName_1729_);
                v___x_1733_ = l_Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0(
                    v_declName_1729_,
                    v_a_1730_,
                    v_a_1731_,
                );
                if lean_obj_tag(v___x_1733_) == 0 {
                    v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
                    v_isSharedCheck_1776_ = (!lean_is_exclusive(v___x_1733_)) as u8;
                    if v_isSharedCheck_1776_ == 0 {
                        v___x_1736_ = v___x_1733_;
                        v_isShared_1737_ = v_isSharedCheck_1776_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1734_);
                        lean_dec(v___x_1733_);
                        v___x_1736_ = lean_box(0);
                        v_isShared_1737_ = v_isSharedCheck_1776_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_declName_1729_);
                    v_a_1777_ = lean_ctor_get(v___x_1733_, 0);
                    v_isSharedCheck_1784_ = (!lean_is_exclusive(v___x_1733_)) as u8;
                    if v_isSharedCheck_1784_ == 0 {
                        v___x_1779_ = v___x_1733_;
                        v_isShared_1780_ = v_isSharedCheck_1784_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1777_);
                        lean_dec(v___x_1733_);
                        v___x_1779_ = lean_box(0);
                        v_isShared_1780_ = v_isSharedCheck_1784_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1750_ = l_Lean_ConstantInfo_type(v_a_1734_);
                if lean_obj_tag(v___x_1750_) == 4 {
                    v_declName_1751_ = lean_ctor_get(v___x_1750_, 0);
                    lean_inc(v_declName_1751_);
                    lean_dec_ref_known(v___x_1750_, 2);
                    if lean_obj_tag(v_declName_1751_) == 1 {
                        v_pre_1752_ = lean_ctor_get(v_declName_1751_, 0);
                        lean_inc(v_pre_1752_);
                        if lean_obj_tag(v_pre_1752_) == 1 {
                            v_pre_1753_ = lean_ctor_get(v_pre_1752_, 0);
                            lean_inc(v_pre_1753_);
                            if lean_obj_tag(v_pre_1753_) == 1 {
                                v_pre_1754_ = lean_ctor_get(v_pre_1753_, 0);
                                lean_inc(v_pre_1754_);
                                if lean_obj_tag(v_pre_1754_) == 1 {
                                    v_pre_1755_ = lean_ctor_get(v_pre_1754_, 0);
                                    lean_inc(v_pre_1755_);
                                    if lean_obj_tag(v_pre_1755_) == 1 {
                                        v_pre_1756_ = lean_ctor_get(v_pre_1755_, 0);
                                        if lean_obj_tag(v_pre_1756_) == 0 {
                                            v_str_1757_ = lean_ctor_get(v_declName_1751_, 1);
                                            lean_inc_ref(v_str_1757_);
                                            lean_dec_ref_known(v_declName_1751_, 2);
                                            v_str_1758_ = lean_ctor_get(v_pre_1752_, 1);
                                            lean_inc_ref(v_str_1758_);
                                            lean_dec_ref_known(v_pre_1752_, 2);
                                            v_str_1759_ = lean_ctor_get(v_pre_1753_, 1);
                                            lean_inc_ref(v_str_1759_);
                                            lean_dec_ref_known(v_pre_1753_, 2);
                                            v_str_1760_ = lean_ctor_get(v_pre_1754_, 1);
                                            lean_inc_ref(v_str_1760_);
                                            lean_dec_ref_known(v_pre_1754_, 2);
                                            v_str_1761_ = lean_ctor_get(v_pre_1755_, 1);
                                            lean_inc_ref(v_str_1761_);
                                            lean_dec_ref_known(v_pre_1755_, 2);
                                            v___x_1762_ =
                                                l_Lean_Elab_checkCbvSimprocType___closed__2;
                                            v___x_1763_ =
                                                lean_string_dec_eq(v_str_1761_, v___x_1762_);
                                            lean_dec_ref(v_str_1761_);
                                            if v___x_1763_ == 0 {
                                                lean_dec_ref(v_str_1760_);
                                                lean_dec_ref(v_str_1759_);
                                                lean_dec_ref(v_str_1758_);
                                                lean_dec_ref(v_str_1757_);
                                                lean_del_object(v___x_1736_);
                                                v___y_1739_ = v_a_1730_;
                                                v___y_1740_ = v_a_1731_;
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_1764_ =
                                                    l_Lean_Elab_checkCbvSimprocType___closed__3;
                                                v___x_1765_ =
                                                    lean_string_dec_eq(v_str_1760_, v___x_1764_);
                                                lean_dec_ref(v_str_1760_);
                                                if v___x_1765_ == 0 {
                                                    lean_dec_ref(v_str_1759_);
                                                    lean_dec_ref(v_str_1758_);
                                                    lean_dec_ref(v_str_1757_);
                                                    lean_del_object(v___x_1736_);
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
                                                    lean_dec_ref(v_str_1759_);
                                                    if v___x_1767_ == 0 {
                                                        lean_dec_ref(v_str_1758_);
                                                        lean_dec_ref(v_str_1757_);
                                                        lean_del_object(v___x_1736_);
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
                                                        lean_dec_ref(v_str_1758_);
                                                        if v___x_1769_ == 0 {
                                                            lean_dec_ref(v_str_1757_);
                                                            lean_del_object(v___x_1736_);
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
                                                            lean_dec_ref(v_str_1757_);
                                                            if v___x_1771_ == 0 {
                                                                lean_del_object(v___x_1736_);
                                                                v___y_1739_ = v_a_1730_;
                                                                v___y_1740_ = v_a_1731_;
                                                                state = 2;
                                                                continue;
                                                            } else {
                                                                lean_dec(v_a_1734_);
                                                                lean_dec(v_declName_1729_);
                                                                v___x_1772_ = lean_box(0);
                                                                if v_isShared_1737_ == 0 {
                                                                    lean_ctor_set(
                                                                        v___x_1736_,
                                                                        0,
                                                                        v___x_1772_,
                                                                    );
                                                                    v___x_1774_ = v___x_1736_;
                                                                    state = 3;
                                                                    continue;
                                                                } else {
                                                                    v_reuseFailAlloc_1775_ =
                                                                        lean_alloc_ctor(
                                                                            0,
                                                                            1,
                                                                            (0) as u32,
                                                                        );
                                                                    lean_ctor_set(
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
                                            lean_dec_ref_known(v_pre_1755_, 2);
                                            lean_dec_ref_known(v_pre_1754_, 2);
                                            lean_dec_ref_known(v_pre_1753_, 2);
                                            lean_dec_ref_known(v_pre_1752_, 2);
                                            lean_dec_ref_known(v_declName_1751_, 2);
                                            lean_del_object(v___x_1736_);
                                            v___y_1739_ = v_a_1730_;
                                            v___y_1740_ = v_a_1731_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref_known(v_pre_1754_, 2);
                                        lean_dec(v_pre_1755_);
                                        lean_dec_ref_known(v_pre_1753_, 2);
                                        lean_dec_ref_known(v_pre_1752_, 2);
                                        lean_dec_ref_known(v_declName_1751_, 2);
                                        lean_del_object(v___x_1736_);
                                        v___y_1739_ = v_a_1730_;
                                        v___y_1740_ = v_a_1731_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_pre_1754_);
                                    lean_dec_ref_known(v_pre_1753_, 2);
                                    lean_dec_ref_known(v_pre_1752_, 2);
                                    lean_dec_ref_known(v_declName_1751_, 2);
                                    lean_del_object(v___x_1736_);
                                    v___y_1739_ = v_a_1730_;
                                    v___y_1740_ = v_a_1731_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v_pre_1752_, 2);
                                lean_dec(v_pre_1753_);
                                lean_dec_ref_known(v_declName_1751_, 2);
                                lean_del_object(v___x_1736_);
                                v___y_1739_ = v_a_1730_;
                                v___y_1740_ = v_a_1731_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref_known(v_declName_1751_, 2);
                            lean_dec(v_pre_1752_);
                            lean_del_object(v___x_1736_);
                            v___y_1739_ = v_a_1730_;
                            v___y_1740_ = v_a_1731_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_declName_1751_);
                        lean_del_object(v___x_1736_);
                        v___y_1739_ = v_a_1730_;
                        v___y_1740_ = v_a_1731_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_1750_);
                    lean_del_object(v___x_1736_);
                    v___y_1739_ = v_a_1730_;
                    v___y_1740_ = v_a_1731_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1741_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__12),
                    core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__12_once),
                    _init_l_Lean_Elab_checkCbvSimprocType___closed__12,
                );
                v___x_1742_ = l_Lean_MessageData_ofName(v_declName_1729_);
                v___x_1743_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1743_, 0, v___x_1741_);
                lean_ctor_set(v___x_1743_, 1, v___x_1742_);
                v___x_1744_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__14),
                    core::ptr::addr_of_mut!(l_Lean_Elab_checkCbvSimprocType___closed__14_once),
                    _init_l_Lean_Elab_checkCbvSimprocType___closed__14,
                );
                v___x_1745_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1745_, 0, v___x_1743_);
                lean_ctor_set(v___x_1745_, 1, v___x_1744_);
                v___x_1746_ = l_Lean_ConstantInfo_type(v_a_1734_);
                lean_dec(v_a_1734_);
                v___x_1747_ = l_Lean_indentExpr(v___x_1746_);
                v___x_1748_ = lean_alloc_ctor(7, 2, (0) as u32);
                lean_ctor_set(v___x_1748_, 0, v___x_1745_);
                lean_ctor_set(v___x_1748_, 1, v___x_1747_);
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
                    v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
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
    mut v_declName_1785_: *mut LeanObject,
    mut v_a_1786_: *mut LeanObject,
    mut v_a_1787_: *mut LeanObject,
    mut v_a_1788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1789_: *mut LeanObject = core::ptr::null_mut();
    v_res_1789_ = l_Lean_Elab_checkCbvSimprocType(v_declName_1785_, v_a_1786_, v_a_1787_);
    lean_dec(v_a_1787_);
    lean_dec_ref(v_a_1786_);
    return v_res_1789_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1(
    mut v_00_u03b1_1790_: *mut LeanObject,
    mut v_msg_1791_: *mut LeanObject,
    mut v___y_1792_: *mut LeanObject,
    mut v___y_1793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    v___x_1795_ = l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___redArg(
        v_msg_1791_,
        v___y_1792_,
        v___y_1793_,
    );
    return v___x_1795_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1___boxed(
    mut v_00_u03b1_1796_: *mut LeanObject,
    mut v_msg_1797_: *mut LeanObject,
    mut v___y_1798_: *mut LeanObject,
    mut v___y_1799_: *mut LeanObject,
    mut v___y_1800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1801_: *mut LeanObject = core::ptr::null_mut();
    v_res_1801_ = l_Lean_throwError___at___00Lean_Elab_checkCbvSimprocType_spec__1(
        v_00_u03b1_1796_,
        v_msg_1797_,
        v___y_1798_,
        v___y_1799_,
    );
    lean_dec(v___y_1799_);
    lean_dec_ref(v___y_1798_);
    return v_res_1801_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0(
    mut v_00_u03b1_1802_: *mut LeanObject,
    mut v_constName_1803_: *mut LeanObject,
    mut v___y_1804_: *mut LeanObject,
    mut v___y_1805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    v___x_1807_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___redArg(v_constName_1803_, v___y_1804_, v___y_1805_);
    return v___x_1807_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0___boxed(
    mut v_00_u03b1_1808_: *mut LeanObject,
    mut v_constName_1809_: *mut LeanObject,
    mut v___y_1810_: *mut LeanObject,
    mut v___y_1811_: *mut LeanObject,
    mut v___y_1812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1813_: *mut LeanObject = core::ptr::null_mut();
    v_res_1813_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0(v_00_u03b1_1808_, v_constName_1809_, v___y_1810_, v___y_1811_);
    lean_dec(v___y_1811_);
    lean_dec_ref(v___y_1810_);
    return v_res_1813_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1(
    mut v_00_u03b1_1814_: *mut LeanObject,
    mut v_ref_1815_: *mut LeanObject,
    mut v_constName_1816_: *mut LeanObject,
    mut v___y_1817_: *mut LeanObject,
    mut v___y_1818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    v___x_1820_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___redArg(v_ref_1815_, v_constName_1816_, v___y_1817_, v___y_1818_);
    return v___x_1820_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_1821_: *mut LeanObject,
    mut v_ref_1822_: *mut LeanObject,
    mut v_constName_1823_: *mut LeanObject,
    mut v___y_1824_: *mut LeanObject,
    mut v___y_1825_: *mut LeanObject,
    mut v___y_1826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1827_: *mut LeanObject = core::ptr::null_mut();
    v_res_1827_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1(v_00_u03b1_1821_, v_ref_1822_, v_constName_1823_, v___y_1824_, v___y_1825_);
    lean_dec(v___y_1825_);
    lean_dec_ref(v___y_1824_);
    lean_dec(v_ref_1822_);
    return v_res_1827_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03b1_1828_: *mut LeanObject,
    mut v_ref_1829_: *mut LeanObject,
    mut v_msg_1830_: *mut LeanObject,
    mut v_declHint_1831_: *mut LeanObject,
    mut v___y_1832_: *mut LeanObject,
    mut v___y_1833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    v___x_1835_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___redArg(v_ref_1829_, v_msg_1830_, v_declHint_1831_, v___y_1832_, v___y_1833_);
    return v___x_1835_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03b1_1836_: *mut LeanObject,
    mut v_ref_1837_: *mut LeanObject,
    mut v_msg_1838_: *mut LeanObject,
    mut v_declHint_1839_: *mut LeanObject,
    mut v___y_1840_: *mut LeanObject,
    mut v___y_1841_: *mut LeanObject,
    mut v___y_1842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1843_: *mut LeanObject = core::ptr::null_mut();
    v_res_1843_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4(v_00_u03b1_1836_, v_ref_1837_, v_msg_1838_, v_declHint_1839_, v___y_1840_, v___y_1841_);
    lean_dec(v___y_1841_);
    lean_dec_ref(v___y_1840_);
    lean_dec(v_ref_1837_);
    return v_res_1843_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(
    mut v_msg_1844_: *mut LeanObject,
    mut v_declHint_1845_: *mut LeanObject,
    mut v___y_1846_: *mut LeanObject,
    mut v___y_1847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    v___x_1849_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_msg_1844_, v_declHint_1845_, v___y_1847_);
    return v___x_1849_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6___boxed(
    mut v_msg_1850_: *mut LeanObject,
    mut v_declHint_1851_: *mut LeanObject,
    mut v___y_1852_: *mut LeanObject,
    mut v___y_1853_: *mut LeanObject,
    mut v___y_1854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1855_: *mut LeanObject = core::ptr::null_mut();
    v_res_1855_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__5_spec__6(v_msg_1850_, v_declHint_1851_, v___y_1852_, v___y_1853_);
    lean_dec(v___y_1853_);
    lean_dec_ref(v___y_1852_);
    return v_res_1855_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6(
    mut v_00_u03b1_1856_: *mut LeanObject,
    mut v_ref_1857_: *mut LeanObject,
    mut v_msg_1858_: *mut LeanObject,
    mut v___y_1859_: *mut LeanObject,
    mut v___y_1860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    v___x_1862_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___redArg(v_ref_1857_, v_msg_1858_, v___y_1859_, v___y_1860_);
    return v___x_1862_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6___boxed(
    mut v_00_u03b1_1863_: *mut LeanObject,
    mut v_ref_1864_: *mut LeanObject,
    mut v_msg_1865_: *mut LeanObject,
    mut v___y_1866_: *mut LeanObject,
    mut v___y_1867_: *mut LeanObject,
    mut v___y_1868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1869_: *mut LeanObject = core::ptr::null_mut();
    v_res_1869_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Elab_checkCbvSimprocType_spec__0_spec__0_spec__1_spec__4_spec__6(v_00_u03b1_1863_, v_ref_1864_, v_msg_1865_, v___y_1866_, v___y_1867_);
    lean_dec(v___y_1867_);
    lean_dec_ref(v___y_1866_);
    lean_dec(v_ref_1864_);
    return v_res_1869_;
}
pub unsafe fn _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    v___x_1870_ = lean_box(0);
    v___x_1871_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
    v___x_1872_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1872_, 0, v___x_1871_);
    lean_ctor_set(v___x_1872_, 1, v___x_1870_);
    return v___x_1872_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg()
-> *mut LeanObject {
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    v___x_1874_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0_once), _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___closed__0);
    v___x_1875_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1875_, 0, v___x_1874_);
    return v___x_1875_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg___boxed(
    mut v___y_1876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1877_: *mut LeanObject = core::ptr::null_mut();
    v_res_1877_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg();
    return v_res_1877_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0(
    mut v_00_u03b1_1878_: *mut LeanObject,
    mut v___y_1879_: *mut LeanObject,
    mut v___y_1880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    v___x_1882_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg();
    return v___x_1882_;
}
pub unsafe fn l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___boxed(
    mut v_00_u03b1_1883_: *mut LeanObject,
    mut v___y_1884_: *mut LeanObject,
    mut v___y_1885_: *mut LeanObject,
    mut v___y_1886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1887_: *mut LeanObject = core::ptr::null_mut();
    v_res_1887_ =
        l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0(
            v_00_u03b1_1883_,
            v___y_1884_,
            v___y_1885_,
        );
    lean_dec(v___y_1885_);
    lean_dec_ref(v___y_1884_);
    return v_res_1887_;
}
pub unsafe fn l_Lean_Elab_Command_elabCbvSimprocPattern___lam__0(
    mut v___x_1888_: *mut LeanObject,
    mut v___x_1889_: *mut LeanObject,
    mut v___y_1890_: *mut LeanObject,
    mut v___y_1891_: *mut LeanObject,
    mut v___y_1892_: *mut LeanObject,
    mut v___y_1893_: *mut LeanObject,
    mut v___y_1894_: *mut LeanObject,
    mut v___y_1895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1906_: u8 = 0;
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1910_: u8 = 0;
    let mut v_a_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1914_: u8 = 0;
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1918_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1897_ =
                    l_Lean_realizeGlobalConstNoOverload(v___x_1888_, v___y_1894_, v___y_1895_);
                if lean_obj_tag(v___x_1897_) == 0 {
                    v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
                    lean_inc_n(v_a_1898_, 2);
                    lean_dec_ref_known(v___x_1897_, 1);
                    v___x_1899_ =
                        l_Lean_Elab_checkCbvSimprocType(v_a_1898_, v___y_1894_, v___y_1895_);
                    if lean_obj_tag(v___x_1899_) == 0 {
                        lean_dec_ref_known(v___x_1899_, 1);
                        v___x_1900_ = l_Lean_Elab_elabCbvSimprocKeys(
                            v___x_1889_,
                            v___y_1892_,
                            v___y_1893_,
                            v___y_1894_,
                            v___y_1895_,
                        );
                        if lean_obj_tag(v___x_1900_) == 0 {
                            v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
                            lean_inc(v_a_1901_);
                            lean_dec_ref_known(v___x_1900_, 1);
                            v___x_1902_ = l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(
                                v_a_1898_,
                                v_a_1901_,
                                v___y_1894_,
                                v___y_1895_,
                            );
                            return v___x_1902_;
                        } else {
                            lean_dec(v_a_1898_);
                            v_a_1903_ = lean_ctor_get(v___x_1900_, 0);
                            v_isSharedCheck_1910_ = (!lean_is_exclusive(v___x_1900_)) as u8;
                            if v_isSharedCheck_1910_ == 0 {
                                v___x_1905_ = v___x_1900_;
                                v_isShared_1906_ = v_isSharedCheck_1910_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1903_);
                                lean_dec(v___x_1900_);
                                v___x_1905_ = lean_box(0);
                                v_isShared_1906_ = v_isSharedCheck_1910_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_1898_);
                        lean_dec(v___x_1889_);
                        return v___x_1899_;
                    }
                } else {
                    lean_dec(v___x_1889_);
                    v_a_1911_ = lean_ctor_get(v___x_1897_, 0);
                    v_isSharedCheck_1918_ = (!lean_is_exclusive(v___x_1897_)) as u8;
                    if v_isSharedCheck_1918_ == 0 {
                        v___x_1913_ = v___x_1897_;
                        v_isShared_1914_ = v_isSharedCheck_1918_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1911_);
                        lean_dec(v___x_1897_);
                        v___x_1913_ = lean_box(0);
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
                    v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
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
                    v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
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
    mut v___x_1919_: *mut LeanObject,
    mut v___x_1920_: *mut LeanObject,
    mut v___y_1921_: *mut LeanObject,
    mut v___y_1922_: *mut LeanObject,
    mut v___y_1923_: *mut LeanObject,
    mut v___y_1924_: *mut LeanObject,
    mut v___y_1925_: *mut LeanObject,
    mut v___y_1926_: *mut LeanObject,
    mut v___y_1927_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1928_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_1926_);
    lean_dec_ref(v___y_1925_);
    lean_dec(v___y_1924_);
    lean_dec_ref(v___y_1923_);
    lean_dec(v___y_1922_);
    lean_dec_ref(v___y_1921_);
    return v_res_1928_;
}
pub unsafe fn l_Lean_Elab_Command_elabCbvSimprocPattern(
    mut v_stx_1935_: *mut LeanObject,
    mut v_a_1936_: *mut LeanObject,
    mut v_a_1937_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: u8 = 0;
    v___x_1939_ = l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2;
    lean_inc(v_stx_1935_);
    v___x_1940_ = l_Lean_Syntax_isOfKind(v_stx_1935_, v___x_1939_);
    if v___x_1940_ == 0 {
        let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_stx_1935_);
        v___x_1941_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg();
        return v___x_1941_;
    } else {
        let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1944_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1946_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1947_: *mut LeanObject = core::ptr::null_mut();
        v___x_1942_ = lean_unsigned_to_nat(1);
        v___x_1943_ = l_Lean_Syntax_getArg(v_stx_1935_, v___x_1942_);
        v___x_1944_ = lean_unsigned_to_nat(3);
        v___x_1945_ = l_Lean_Syntax_getArg(v_stx_1935_, v___x_1944_);
        lean_dec(v_stx_1935_);
        v___f_1946_ = lean_alloc_closure(
            l_Lean_Elab_Command_elabCbvSimprocPattern___lam__0___boxed as *mut core::ffi::c_void,
            9,
            2,
        );
        lean_closure_set(v___f_1946_, 0, v___x_1945_);
        lean_closure_set(v___f_1946_, 1, v___x_1943_);
        v___x_1947_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_1946_, v_a_1936_, v_a_1937_);
        return v___x_1947_;
    }
}
pub unsafe fn l_Lean_Elab_Command_elabCbvSimprocPattern___boxed(
    mut v_stx_1948_: *mut LeanObject,
    mut v_a_1949_: *mut LeanObject,
    mut v_a_1950_: *mut LeanObject,
    mut v_a_1951_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1952_: *mut LeanObject = core::ptr::null_mut();
    v_res_1952_ = l_Lean_Elab_Command_elabCbvSimprocPattern(v_stx_1948_, v_a_1949_, v_a_1950_);
    lean_dec(v_a_1950_);
    lean_dec_ref(v_a_1949_);
    return v_res_1952_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1()
-> *mut LeanObject {
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    v___x_1962_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_1963_ = l_Lean_Elab_Command_elabCbvSimprocPattern___closed__2;
    v___x_1964_ = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1___closed__3;
    v___x_1965_ = lean_alloc_closure(
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
    mut v_a_1967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1968_: *mut LeanObject = core::ptr::null_mut();
    v_res_1968_ = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1();
    return v_res_1968_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4()
-> *mut LeanObject {
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    v___x_1978_ = lean_box(0);
    v___x_1979_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__3;
    v___x_1980_ = l_Lean_mkConst(v___x_1979_, v___x_1978_);
    return v___x_1980_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7()
-> *mut LeanObject {
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    v___x_1988_ = lean_box(0);
    v___x_1989_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__6;
    v___x_1990_ = l_Lean_mkConst(v___x_1989_, v___x_1988_);
    return v___x_1990_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10()
-> *mut LeanObject {
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    v___x_1998_ = lean_box(0);
    v___x_1999_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__9;
    v___x_2000_ = l_Lean_mkConst(v___x_1999_, v___x_1998_);
    return v___x_2000_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14()
-> *mut LeanObject {
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2009_: *mut LeanObject = core::ptr::null_mut();
    v___x_2007_ = lean_box(0);
    v___x_2008_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__13;
    v___x_2009_ = l_Lean_mkConst(v___x_2008_, v___x_2007_);
    return v___x_2009_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17()
-> *mut LeanObject {
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    v___x_2015_ = lean_box(0);
    v___x_2016_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__16;
    v___x_2017_ = l_Lean_mkConst(v___x_2016_, v___x_2015_);
    return v___x_2017_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20()
-> *mut LeanObject {
    let mut v___x_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    v___x_2025_ = lean_box(0);
    v___x_2026_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__19;
    v___x_2027_ = l_Lean_mkConst(v___x_2026_, v___x_2025_);
    return v___x_2027_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24()
-> *mut LeanObject {
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    v___x_2034_ = lean_box(0);
    v___x_2035_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__23;
    v___x_2036_ = l_Lean_mkConst(v___x_2035_, v___x_2034_);
    return v___x_2036_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27()
-> *mut LeanObject {
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut LeanObject = core::ptr::null_mut();
    v___x_2044_ = lean_box(0);
    v___x_2045_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__26;
    v___x_2046_ = l_Lean_mkConst(v___x_2045_, v___x_2044_);
    return v___x_2046_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30()
-> *mut LeanObject {
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    v___x_2054_ = lean_box(0);
    v___x_2055_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__29;
    v___x_2056_ = l_Lean_mkConst(v___x_2055_, v___x_2054_);
    return v___x_2056_;
}
pub unsafe fn _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33()
-> *mut LeanObject {
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut LeanObject = core::ptr::null_mut();
    v___x_2064_ = lean_box(0);
    v___x_2065_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__32;
    v___x_2066_ = l_Lean_mkConst(v___x_2065_, v___x_2064_);
    return v___x_2066_;
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0(
    mut v_nilFn_2067_: *mut LeanObject,
    mut v_consFn_2068_: *mut LeanObject,
    mut v_x_2069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2069_) == 0 {
                    lean_dec_ref(v_consFn_2068_);
                    lean_inc_ref(v_nilFn_2067_);
                    return v_nilFn_2067_;
                } else {
                    v_head_2070_ = lean_ctor_get(v_x_2069_, 0);
                    lean_inc(v_head_2070_);
                    v_tail_2071_ = lean_ctor_get(v_x_2069_, 1);
                    lean_inc(v_tail_2071_);
                    lean_dec_ref_known(v_x_2069_, 2);
                    match lean_obj_tag(v_head_2070_) {
                        0 => {
                            v___x_2076_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__4);
                            v___y_2073_ = v___x_2076_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v___x_2077_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__7);
                            v___y_2073_ = v___x_2077_;
                            state = 1;
                            continue;
                        }
                        2 => {
                            v_a_2078_ = lean_ctor_get(v_head_2070_, 0);
                            lean_inc_ref(v_a_2078_);
                            lean_dec_ref_known(v_head_2070_, 1);
                            v___x_2079_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__10);
                            if lean_obj_tag(v_a_2078_) == 0 {
                                v___x_2080_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__14);
                                v___x_2081_ = l_Lean_Expr_lit___override(v_a_2078_);
                                v___x_2082_ = l_Lean_Expr_app___override(v___x_2080_, v___x_2081_);
                                v___x_2083_ = l_Lean_Expr_app___override(v___x_2079_, v___x_2082_);
                                v___y_2073_ = v___x_2083_;
                                state = 1;
                                continue;
                            } else {
                                v___x_2084_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__17);
                                v___x_2085_ = l_Lean_Expr_lit___override(v_a_2078_);
                                v___x_2086_ = l_Lean_Expr_app___override(v___x_2084_, v___x_2085_);
                                v___x_2087_ = l_Lean_Expr_app___override(v___x_2079_, v___x_2086_);
                                v___y_2073_ = v___x_2087_;
                                state = 1;
                                continue;
                            }
                        }
                        3 => {
                            v_a_2088_ = lean_ctor_get(v_head_2070_, 0);
                            lean_inc(v_a_2088_);
                            v_a_2089_ = lean_ctor_get(v_head_2070_, 1);
                            lean_inc(v_a_2089_);
                            lean_dec_ref_known(v_head_2070_, 2);
                            v___x_2090_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__20);
                            v___x_2091_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__24);
                            v___x_2092_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_2088_);
                            v___x_2093_ = l_Lean_Expr_app___override(v___x_2091_, v___x_2092_);
                            v___x_2094_ = l_Lean_mkNatLit(v_a_2089_);
                            v___x_2095_ = l_Lean_mkAppB(v___x_2090_, v___x_2093_, v___x_2094_);
                            v___y_2073_ = v___x_2095_;
                            state = 1;
                            continue;
                        }
                        4 => {
                            v_a_2096_ = lean_ctor_get(v_head_2070_, 0);
                            lean_inc(v_a_2096_);
                            v_a_2097_ = lean_ctor_get(v_head_2070_, 1);
                            lean_inc(v_a_2097_);
                            lean_dec_ref_known(v_head_2070_, 2);
                            v___x_2098_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__27);
                            v___x_2099_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_a_2096_);
                            v___x_2100_ = l_Lean_mkNatLit(v_a_2097_);
                            v___x_2101_ = l_Lean_mkAppB(v___x_2098_, v___x_2099_, v___x_2100_);
                            v___y_2073_ = v___x_2101_;
                            state = 1;
                            continue;
                        }
                        5 => {
                            v___x_2102_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__30);
                            v___y_2073_ = v___x_2102_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_a_2103_ = lean_ctor_get(v_head_2070_, 0);
                            lean_inc(v_a_2103_);
                            v_a_2104_ = lean_ctor_get(v_head_2070_, 1);
                            lean_inc(v_a_2104_);
                            v_a_2105_ = lean_ctor_get(v_head_2070_, 2);
                            lean_inc(v_a_2105_);
                            lean_dec_ref_known(v_head_2070_, 3);
                            v___x_2106_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33), core::ptr::addr_of_mut!(l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33_once), _init_l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___closed__33);
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
                lean_inc_ref(v_consFn_2068_);
                v___x_2074_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0(v_nilFn_2067_, v_consFn_2068_, v_tail_2071_);
                v___x_2075_ = l_Lean_mkAppB(v_consFn_2068_, v___y_2073_, v___x_2074_);
                return v___x_2075_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0___boxed(
    mut v_nilFn_2111_: *mut LeanObject,
    mut v_consFn_2112_: *mut LeanObject,
    mut v_x_2113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2114_: *mut LeanObject = core::ptr::null_mut();
    v_res_2114_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0(v_nilFn_2111_, v_consFn_2112_, v_x_2113_);
    lean_dec_ref(v_nilFn_2111_);
    return v_res_2114_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7()
-> *mut LeanObject {
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    v___x_2126_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6;
    v___x_2127_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__5;
    v___x_2128_ = l_Lean_mkConst(v___x_2127_, v___x_2126_);
    return v___x_2128_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12()
-> *mut LeanObject {
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    v___x_2136_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6;
    v___x_2137_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__11;
    v___x_2138_ = l_Lean_mkConst(v___x_2137_, v___x_2136_);
    return v___x_2138_;
}
pub unsafe fn _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15()
-> *mut LeanObject {
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    v___x_2143_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__6;
    v___x_2144_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__14;
    v___x_2145_ = l_Lean_mkConst(v___x_2144_, v___x_2143_);
    return v___x_2145_;
}
pub unsafe fn l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0(
    mut v___x_2146_: *mut LeanObject,
    mut v___x_2147_: *mut LeanObject,
    mut v___x_2148_: *mut LeanObject,
    mut v___x_2149_: *mut LeanObject,
    mut v___y_2150_: *mut LeanObject,
    mut v___y_2151_: *mut LeanObject,
    mut v___y_2152_: *mut LeanObject,
    mut v___y_2153_: *mut LeanObject,
    mut v___y_2154_: *mut LeanObject,
    mut v___y_2155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nil_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cons_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2196_: u8 = 0;
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2200_: u8 = 0;
    let mut v_a_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2204_: u8 = 0;
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2208_: u8 = 0;
    let mut v_a_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2212_: u8 = 0;
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2216_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2157_ =
                    l_Lean_realizeGlobalConstNoOverload(v___x_2146_, v___y_2154_, v___y_2155_);
                if lean_obj_tag(v___x_2157_) == 0 {
                    v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
                    lean_inc_n(v_a_2158_, 2);
                    lean_dec_ref_known(v___x_2157_, 1);
                    v___x_2159_ =
                        l_Lean_Elab_checkCbvSimprocType(v_a_2158_, v___y_2154_, v___y_2155_);
                    if lean_obj_tag(v___x_2159_) == 0 {
                        lean_dec_ref_known(v___x_2159_, 1);
                        v___x_2160_ = l_Lean_Elab_elabCbvSimprocKeys(
                            v___x_2147_,
                            v___y_2152_,
                            v___y_2153_,
                            v___y_2154_,
                            v___y_2155_,
                        );
                        if lean_obj_tag(v___x_2160_) == 0 {
                            v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
                            lean_inc(v_a_2161_);
                            lean_dec_ref_known(v___x_2160_, 1);
                            v___x_2162_ = l_Lean_Elab_checkCbvSimprocType___closed__3;
                            v___x_2163_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__0;
                            v___x_2164_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__1;
                            v___x_2165_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__2;
                            lean_inc_ref(v___x_2148_);
                            v___x_2166_ = l_Lean_Name_mkStr5(
                                v___x_2148_,
                                v___x_2162_,
                                v___x_2163_,
                                v___x_2164_,
                                v___x_2165_,
                            );
                            v___x_2167_ = lean_box(0);
                            v___x_2168_ = l_Lean_mkConst(v___x_2166_, v___x_2167_);
                            lean_inc_n(v_a_2158_, 2);
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
                            v___x_2174_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7_once), _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__7);
                            v___x_2175_ = l_Lean_mkConst(v_a_2158_, v___x_2167_);
                            v___x_2176_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__9;
                            v___x_2177_ = l_Lean_Name_append(v_a_2158_, v___x_2176_);
                            v___x_2178_ =
                                l_Lean_Core_mkFreshUserName(v___x_2177_, v___y_2154_, v___y_2155_);
                            if lean_obj_tag(v___x_2178_) == 0 {
                                v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
                                lean_inc(v_a_2179_);
                                lean_dec_ref_known(v___x_2178_, 1);
                                v___x_2180_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12), core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12_once), _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__12);
                                lean_inc_ref_n(v___x_2173_, 2);
                                v_nil_2181_ = l_Lean_Expr_app___override(v___x_2180_, v___x_2173_);
                                v___x_2182_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15), core::ptr::addr_of_mut!(l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15_once), _init_l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___closed__15);
                                v_cons_2183_ = l_Lean_Expr_app___override(v___x_2182_, v___x_2173_);
                                v___x_2184_ = lean_array_to_list(v_a_2161_);
                                v___x_2185_ = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___00Lean_Elab_Command_elabCbvSimprocPatternBuiltin_spec__0(v_nil_2181_, v_cons_2183_, v___x_2184_);
                                lean_dec_ref(v_nil_2181_);
                                v___x_2186_ = l_Lean_mkAppB(v___x_2174_, v___x_2173_, v___x_2185_);
                                v___x_2187_ = lean_mk_empty_array_with_capacity(v___x_2149_);
                                v___x_2188_ = lean_array_push(v___x_2187_, v___x_2169_);
                                v___x_2189_ = lean_array_push(v___x_2188_, v___x_2186_);
                                v___x_2190_ = lean_array_push(v___x_2189_, v___x_2175_);
                                v___x_2191_ = l_Lean_mkAppN(v___x_2168_, v___x_2190_);
                                lean_dec_ref(v___x_2190_);
                                v___x_2192_ = l_Lean_declareBuiltin(
                                    v_a_2179_,
                                    v___x_2191_,
                                    v___y_2154_,
                                    v___y_2155_,
                                );
                                return v___x_2192_;
                            } else {
                                lean_dec_ref(v___x_2175_);
                                lean_dec_ref(v___x_2173_);
                                lean_dec_ref(v___x_2169_);
                                lean_dec_ref(v___x_2168_);
                                lean_dec(v_a_2161_);
                                v_a_2193_ = lean_ctor_get(v___x_2178_, 0);
                                v_isSharedCheck_2200_ = (!lean_is_exclusive(v___x_2178_)) as u8;
                                if v_isSharedCheck_2200_ == 0 {
                                    v___x_2195_ = v___x_2178_;
                                    v_isShared_2196_ = v_isSharedCheck_2200_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_2193_);
                                    lean_dec(v___x_2178_);
                                    v___x_2195_ = lean_box(0);
                                    v_isShared_2196_ = v_isSharedCheck_2200_;
                                    state = 1;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_2158_);
                            lean_dec_ref(v___x_2148_);
                            v_a_2201_ = lean_ctor_get(v___x_2160_, 0);
                            v_isSharedCheck_2208_ = (!lean_is_exclusive(v___x_2160_)) as u8;
                            if v_isSharedCheck_2208_ == 0 {
                                v___x_2203_ = v___x_2160_;
                                v_isShared_2204_ = v_isSharedCheck_2208_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_2201_);
                                lean_dec(v___x_2160_);
                                v___x_2203_ = lean_box(0);
                                v_isShared_2204_ = v_isSharedCheck_2208_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_2158_);
                        lean_dec_ref(v___x_2148_);
                        lean_dec(v___x_2147_);
                        return v___x_2159_;
                    }
                } else {
                    lean_dec_ref(v___x_2148_);
                    lean_dec(v___x_2147_);
                    v_a_2209_ = lean_ctor_get(v___x_2157_, 0);
                    v_isSharedCheck_2216_ = (!lean_is_exclusive(v___x_2157_)) as u8;
                    if v_isSharedCheck_2216_ == 0 {
                        v___x_2211_ = v___x_2157_;
                        v_isShared_2212_ = v_isSharedCheck_2216_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2209_);
                        lean_dec(v___x_2157_);
                        v___x_2211_ = lean_box(0);
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
                    v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
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
                    v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
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
                    v_reuseFailAlloc_2215_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2215_, 0, v_a_2209_);
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
    mut v___x_2217_: *mut LeanObject,
    mut v___x_2218_: *mut LeanObject,
    mut v___x_2219_: *mut LeanObject,
    mut v___x_2220_: *mut LeanObject,
    mut v___y_2221_: *mut LeanObject,
    mut v___y_2222_: *mut LeanObject,
    mut v___y_2223_: *mut LeanObject,
    mut v___y_2224_: *mut LeanObject,
    mut v___y_2225_: *mut LeanObject,
    mut v___y_2226_: *mut LeanObject,
    mut v___y_2227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2228_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2226_);
    lean_dec_ref(v___y_2225_);
    lean_dec(v___y_2224_);
    lean_dec_ref(v___y_2223_);
    lean_dec(v___y_2222_);
    lean_dec_ref(v___y_2221_);
    lean_dec(v___x_2220_);
    return v_res_2228_;
}
pub unsafe fn l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin(
    mut v_stx_2234_: *mut LeanObject,
    mut v_a_2235_: *mut LeanObject,
    mut v_a_2236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: u8 = 0;
    v___x_2238_ = l_Lean_Elab_checkCbvSimprocType___closed__2;
    v___x_2239_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1;
    lean_inc(v_stx_2234_);
    v___x_2240_ = l_Lean_Syntax_isOfKind(v_stx_2234_, v___x_2239_);
    if v___x_2240_ == 0 {
        let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_stx_2234_);
        v___x_2241_ = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Command_elabCbvSimprocPattern_spec__0___redArg();
        return v___x_2241_;
    } else {
        let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2246_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
        v___x_2242_ = lean_unsigned_to_nat(1);
        v___x_2243_ = l_Lean_Syntax_getArg(v_stx_2234_, v___x_2242_);
        v___x_2244_ = lean_unsigned_to_nat(3);
        v___x_2245_ = l_Lean_Syntax_getArg(v_stx_2234_, v___x_2244_);
        lean_dec(v_stx_2234_);
        v___f_2246_ = lean_alloc_closure(
            l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___lam__0___boxed
                as *mut core::ffi::c_void,
            11,
            4,
        );
        lean_closure_set(v___f_2246_, 0, v___x_2245_);
        lean_closure_set(v___f_2246_, 1, v___x_2243_);
        lean_closure_set(v___f_2246_, 2, v___x_2238_);
        lean_closure_set(v___f_2246_, 3, v___x_2244_);
        v___x_2247_ = l_Lean_Elab_Command_liftTermElabM___redArg(v___f_2246_, v_a_2235_, v_a_2236_);
        return v___x_2247_;
    }
}
pub unsafe fn l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___boxed(
    mut v_stx_2248_: *mut LeanObject,
    mut v_a_2249_: *mut LeanObject,
    mut v_a_2250_: *mut LeanObject,
    mut v_a_2251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2252_: *mut LeanObject = core::ptr::null_mut();
    v_res_2252_ =
        l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin(v_stx_2248_, v_a_2249_, v_a_2250_);
    lean_dec(v_a_2250_);
    lean_dec_ref(v_a_2249_);
    return v_res_2252_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1()
-> *mut LeanObject {
    let mut v___x_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    v___x_2260_ = l_Lean_Elab_Command_commandElabAttribute;
    v___x_2261_ = l_Lean_Elab_Command_elabCbvSimprocPatternBuiltin___closed__1;
    v___x_2262_ = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1___closed__1;
    v___x_2263_ = lean_alloc_closure(
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
    mut v_a_2265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2266_: *mut LeanObject = core::ptr::null_mut();
    v_res_2266_ = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1();
    return v_res_2266_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_CbvSimproc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_CbvSimproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPattern___regBuiltin_Lean_Elab_Command_elabCbvSimprocPattern__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_CbvSimproc_0__Lean_Elab_Command_elabCbvSimprocPatternBuiltin___regBuiltin_Lean_Elab_Command_elabCbvSimprocPatternBuiltin__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_CbvSimproc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_CbvSimproc(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_CbvSimproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Command(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_CbvSimproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_CbvSimproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_CbvSimproc(builtin);
}
